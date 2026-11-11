#!/usr/bin/env python3
"""TASK32 proof-build timing: fresh whole processes in two independent
snapshots of the tree (base and candidate), 15 workloads (task32_cases.py).

Not a release approval, and not the matrix runner: a unit is one fresh
process tree (a theory script rebuilt by Holmake from its prebuilt
dependencies, or a selftest command), measured from outside by `wait4` and
from inside by a tiny reporter (REPORTER) that enters the process through
POLY_CLINE_OPTIONS (theory units) or the argument slot before the last
argument (selftests) and writes one JSON line to $T32_STATS at exit.

  smoke      one process per side and unit; a harness check, never a draw;
             records the probe facts (one stats line, the reporter in
             Meta.fileDirMap, all four heaps) and the overheads of the
             scans and the snapshot audits;
  pilot      develop-only: 10 B/B pairs per unit (loading.jitter); checks
             the outputs and the 1 s unit floor and sizes R, the fresh
             processes per sample, under the cap R_CAP;
  control    the live negative control: 10 pairs of one unit, the candidate
             reporter busy-loops BUSY (6%) of the unit's median whole-tree
             CPU from the pilot, in absolute seconds, on the base snapshot;
             must be judged a fail;
  predeclare writes the counts file (R per unit, references, seals of the
             replayed smoke, pilot and control, overheads, the time
             estimate), which is committed alone before any decision
             process;
  run        the first stage: 20 pairs per unit, round-robin over the
             units, the two phases of a round in alternating order;
  extend     the second stage of the units whose B/B control missed the
             equivalence window (control-limited) and that did not fail;
  followup   (predeclare --followup, then `followup`) the targeted follow-up
             of the units inconclusive with a valid control after the
             first or the second stage: pairs from the grid's second-stage
             rule on the first stage's control (at least twice its pairs,
             at most the cap), a new seed, its own counts file, committed
             alone first;
  replay     recomputes every decision of an archive; runs no process;
  dispose    the per-unit and overall disposition of the stage chain, with
             every attempt, information run and redraw (rule R-1);
  recover    puts back what a killed or failed restore left in a journal.

A theory process is protected by a restore journal under
.agent-files/scratch/task32 (backups, written before any product is
deleted, kept when a restore fails); a run refuses to start while one is
pending. SIGTERM and SIGHUP kill the child's group, restore and close the
attempt.

Rules shared with loading.py, which this module reuses by import: the
equivalence policy (3% margin on inclusive CPU and wall; GC and maxrss are
reported, not gated), the AB/BA schedule, the layout padding, the pair
counts of the second stage, the hash-chained attempts ledger (one judged
attempt per stage and gate; an attempt that admitted no measurement is
void) and the serial lock. Per-process validation refuses the row, never
drops it. Interface to task32_snapshots.py: see `load_manifest`.
"""
import argparse
import contextlib
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import threading
import time
import uuid

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "compatibility"))
import acceptance as a
import loading
import performance_schema as ps
import task32_cases as cases
import task32_dat as dat
import task32_snapshots as snap
import timing_grid as tg

SCHEMA = "task32-downstream-v1"
COUNTS_SCHEMA = "task32-counts-v1"
STATS_SCHEMA = "task32-stats-v1"
TABLE = "task32-downstream"
POLICY = a.EQUIVALENCE_POLICY
PAIRS = 20
PILOT_PAIRS = 10  # the least that paired_statistics accepts
R_CAP = 4  # fresh processes per sample: a pilot asking for more refuses
CONTROL_PAIRS = 10
BUSY = 0.06
MIN_UNIT_CPU = 1.0
LAYOUT_SEED = "task32-1"
EXTENSION_SEED = LAYOUT_SEED + "-ext"
FOLLOWUP_SEED = LAYOUT_SEED + "-fu"
SEEDS = dict(smoke=LAYOUT_SEED + "-smoke", control=LAYOUT_SEED + "-control",
             pilot=LAYOUT_SEED + "-pilot", first=LAYOUT_SEED,
             second=EXTENSION_SEED, followup=FOLLOWUP_SEED)
COUNTS = HERE / "task32_counts.json"
FOLLOWUP_COUNTS = HERE / "task32_followup_counts.json"
COMPILED_REF = snap.C31  # C32's compiled sources must equal it
COUNTS_SCOPE = "src/simp/tests/performance/"
# The timed metrics, as loading.jitter names them (+ maxrss).
METRICS = loading.METRICS + ("maxrss",)
DECISIVE = ("first", "second", "followup")
INFO_MODES = ("smoke", "control", "pilot")
PROCESS_PHASES = ("control", "candidate")
JOURNALS = ".agent-files/scratch/task32"  # restore journals, not /dev/shm
TIMEOUT = 900
DECISIONS = loading.DECISIONS
FAILED, BLOCKED = loading.FAILED, loading.BLOCKED
# Code the counts file is bound to (replay refuses a changed one).
CODE = ("task32_cases.py", "task32_downstream.py", "task32_snapshots.py",
        "task32_dat.py", "startup_gate.py", "loading.py", "acceptance.py",
        "timing_grid.py", "performance_schema.py", "summarize.py")
# Per file of CODE, the seals it had when a record was made, once it has
# changed since (PROTOCOL "Seals and seal histories"): replay accepts the
# current seal or one listed here; a run needs the current one.
HISTORY = {}


def require(ok, message):
    if not ok:
        raise Refusal(message)


class Refusal(ValueError):
    """A process, row or run that must not be admitted. Nothing is dropped:
    the row is archived as rejected and the attempt closes failed."""


class Blocked(Refusal):
    """A finding about the candidate (an extension module loaded, or a
    different output): judged, never void."""


class Fatal(RuntimeError):
    """A snapshot could not be restored: stop everything."""


# The reporter: a sealed string, built per side by that side's Holmake.
REPORTER = r'''structure T32Report =
struct
  fun real t = String.map (fn #"~" => #"-" | c => c)
    (Real.fmt (StringCvt.SCI (SOME 12)) (Time.toReal t))
  fun js s = "\"" ^ String.translate
    (fn #"\"" => "\\\"" | #"\\" => "\\\\"
      | c => if Char.ord c < 32 then " " else str c) s ^ "\""
  fun jl f xs = "[" ^ String.concatWith "," (map f xs) ^ "]"
  fun env n = OS.Process.getEnv n
  fun padding () =
    case env "T32_LAYOUT" of
        NONE => ()
      | SOME s =>
        let
          val units = case Int.fromString s of
                          SOME n => n
                        | NONE => raise Fail ("bad T32_LAYOUT: " ^ s)
          fun unit i = "fun layout_pad" ^ Int.toString i ^
                       " (x : int) = x + " ^ Int.toString i ^ ";\n"
          val rest = ref (String.explode
                            (String.concat (List.tabulate (units, unit))))
          fun next () = case !rest of
                            [] => NONE
                          | c :: cs => (rest := cs; SOME c)
          fun loop () =
            if null (!rest) then ()
            else (PolyML.compiler
                    (next, [PolyML.Compiler.CPOutStream ignore]) ();
                  loop ())
        in loop () end
  val timer = Timer.totalCPUTimer ()
  val preloaded = Meta.loaded ()
  val filesPre = Binarymap.listItems (Meta.fileDirMap ())
  fun cpu () = let val {usr, sys} = Timer.checkCPUTimer timer
               in Time.toReal usr + Time.toReal sys end
  fun busy () =
    case env "T32_BUSY" of
        NONE => ()
      | SOME s =>
        (case Real.fromString s of
             NONE => raise Fail ("bad T32_BUSY: " ^ s)
           | SOME seconds =>
             let val target = cpu () + seconds
                 fun spin () = if cpu () < target then spin () else ()
             in spin () end)
  fun report () =
    case env "T32_STATS" of
        NONE => ()
      | SOME file =>
        let
          val _ = busy ()
          val {nongc = {usr = nu, sys = ns}, gc = {usr = gu, sys = gs}} =
            Timer.checkCPUTimes timer
          val st = PolyML.Statistics.getLocalStats ()
          fun fresh (f, d) =
            not (List.exists (fn x => x = (f, d)) filesPre)
          val files = List.filter fresh
                        (Binarymap.listItems (Meta.fileDirMap ()))
          val after = List.filter
            (fn n => not (List.exists (fn m => m = n) preloaded))
            (Meta.loaded ())
          val line = String.concat
            ["{\"schema\":\"task32-stats-v1\",",
             "\"nongc_usr\":", real nu, ",\"nongc_sys\":", real ns,
             ",\"gc_usr\":", real gu, ",\"gc_sys\":", real gs,
             ",\"gc_time\":", real (Timer.checkGCTime timer),
             ",\"gc_full\":", Int.toString (#gcFullGCs st),
             ",\"gc_partial\":", Int.toString (#gcPartialGCs st),
             ",\"gc_share\":", Int.toString (#gcSharePasses st),
             ",\"size_heap\":", LargeInt.toString (#sizeHeap st),
             ",\"holdir\":", js Systeml.HOLDIR,
             ",\"loaded_before\":", jl js preloaded,
             ",\"loaded\":", jl js after,
             ",\"files\":", jl (fn (f, d) => "[" ^ js f ^ "," ^ js d ^ "]")
                              files,
             "}\n"]
          val out = TextIO.openAppend file
        in TextIO.output (out, line); TextIO.closeOut out end
  val _ = padding ()
  val _ = OS.Process.atExit report
end
'''
REPORTER_SEAL = hashlib.sha256(REPORTER.encode()).hexdigest()
REPORTER_NAME = "T32Report"
STATS_NUMBERS = ("nongc_usr", "nongc_sys", "gc_usr", "gc_sys", "gc_time")
STATS_COUNTS = ("gc_full", "gc_partial", "gc_share", "size_heap")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dumps(value):
    return json.dumps(value, indent=2, allow_nan=False) + "\n"


def same(left, right):
    return json.dumps(left, sort_keys=True) == json.dumps(right,
                                                         sort_keys=True)


def finite(value):
    return value if math.isfinite(value) else None


def archive(folder, name, receipt):
    path = Path(folder) / (name + ".json.gz")
    path.write_bytes(gzip.compress(dumps(receipt).encode(), mtime=0))
    return {"receipt": path.name, "seal": a.seal(path)}


def seed_for(mode):
    return SEEDS[mode]


# ---------------------------------------------------------------- inputs

def load_manifest(path, base_root, cand_root):
    """The interface to task32_snapshots.py: its manifest (schema
    `snap.SCHEMA`), `{"sides": {"base": {...}, "cand": {...}}}`, each side
    complete (not `incomplete`), labelled, with `root`, `pin` and `tree`.
    The roots must equal `--base-root` and `--cand-root`, be named after
    their labels, differ and not be nested. Returns the sides and the
    manifest seal. The snapshots are re-audited by `snap verify` before and
    after every run (`default_verify`)."""
    path = Path(path).resolve(strict=True)
    data = a.load(path)
    require(isinstance(data, dict) and data.get("schema") == snap.SCHEMA,
            "not a snapshot manifest: " + str(path))
    sides = data.get("sides")
    require(isinstance(sides, dict) and set(sides) == set(snap.LABELS),
            "the manifest has no complete base and cand sides")
    found = {}
    for label, raw in (("base", base_root), ("cand", cand_root)):
        side = sides[label]
        require(isinstance(side, dict) and
                isinstance(side.get("root"), str), "no root: " + label)
        require(not side.get("incomplete") and
                side.get("label") == label, "incomplete or mislabelled "
                "side: " + label)
        root = Path(raw).resolve(strict=True)
        require(Path(side["root"]).resolve(strict=True) == root and
                root.name == label, "the manifest's %s root is not %s (a "
                "root is named after its label)" % (label, root))
        for key in ("pin", "tree"):
            a.exact_pin(side.get(key))
        found[label] = dict(root=root, pin=side["pin"], tree=side["tree"])
    one, two = found["base"]["root"], found["cand"]["root"]
    require(one != two and not one.is_relative_to(two) and
            not two.is_relative_to(one), "snapshot roots are nested or equal")
    return found, a.seal(path)


def gate_key(sides):
    """The identity of a measured gate: the two pins. The manifest is
    recorded beside it (a rebuilt snapshot of the same pins is the same
    gate, as `snap verify` is the authority on the trees)."""
    return sha(json.dumps([sides["base"]["pin"],
                           sides["cand"]["pin"]]).encode())


def default_verify(repo, manifest, sides):
    """The snapshot audit, with the arguments task32_snapshots.py's
    `verify` requires (pins, C31)."""
    return [sys.executable, "-B", str(HERE / "task32_snapshots.py"),
            "verify", "--repo", str(Path(repo).resolve()),
            "--manifest", str(Path(manifest).resolve()),
            "--base-pin", sides["base"]["pin"],
            "--cand-pin", sides["cand"]["pin"], "--c31", snap.C31]


def run_verify(argv, cwd, fds):
    """The snapshots-unchanged command; a nonzero exit refuses the run. It
    takes the serial lock again, so it inherits ours."""
    env = dict(os.environ, HOL4_PERF_LOCK_FDS=",".join(map(str, fds)))
    done = loading.execute(argv, cwd, env, 3600, fds)
    require(done["exit"] == 0 and not done["timed_out"],
            "snapshot verification failed: %s" % done["stdout"][-400:])
    return dict(argv=done["command"], exit=0, seconds=done["process_wall"],
                stdout_sha256=done["stdout_sha256"])


def check_candidate(repo, sides):
    """Base is the develop pin; the candidate's compiled sources equal C31's
    (everything outside the tests directories, snap.TEST_ONLY)."""
    require(sides["base"]["pin"] == a.BASE, "the baseline is not the pin")
    try:
        c31 = a.git(repo, "rev-parse", COMPILED_REF + "^{commit}")
        differs = subprocess.run(
            ["git", "-C", str(repo), "diff", "--quiet", c31,
             sides["cand"]["pin"], "--", ".", *snap.TEST_ONLY],
            stdin=subprocess.DEVNULL).returncode
    except subprocess.CalledProcessError as error:
        raise Refusal("cannot resolve %s: %s" % (COMPILED_REF, error))
    require(differs == 0, "the candidate's compiled sources differ from "
            "%s" % COMPILED_REF)
    return c31


def code_seals():
    return {n: a.seal(HERE / n) for n in CODE}


def check_code(recorded):
    """The seals a record carries are those of the code now or of an
    earlier version HISTORY names."""
    now = code_seals()
    require(isinstance(recorded, dict) and set(recorded) == set(CODE),
            "the recorded code is not " + ", ".join(CODE))
    changed = [n for n in CODE if recorded[n] != now[n] and
               recorded[n] not in HISTORY.get(n, ())]
    require(not changed, "the code changed since the record was made: %s; "
            "add the seal it was made by to task32_downstream.HISTORY: %s" %
            (", ".join(changed), "; ".join(
                "%s: %s" % (n, json.dumps(recorded[n], sort_keys=True))
                for n in changed)))


def check_counts_commit(repo, path, cand_pin):
    """The counts file is committed in the history of HEAD by exactly one
    commit that touched nothing else, and nothing outside
    src/simp/tests/performance changed from the candidate to HEAD. Returns
    the commit."""
    path = Path(path).resolve(strict=True)
    try:
        name = tg.repo_relative(repo, path)
        head = tg.git_head(repo)
        require(head is not None and tg.git_blob(repo, head, name) ==
                a.git(repo, "hash-object", str(path)),
                "the counts file is not committed at HEAD: " + name)
        commit = tg.git_introduced(repo, head, name)
        touched = set(tg.git_touched(repo, commit))
        require(touched == {name}, "commit the counts alone: %s also "
                "changes %s" % (commit[:12], ", ".join(
                    sorted(touched - {name}))))
        moved = a.git(repo, "diff", "--name-only", cand_pin, head).split()
    except (ValueError, subprocess.CalledProcessError) as error:
        if isinstance(error, Refusal):
            raise
        raise Refusal("counts commit check: %s" % error)
    stray = [p for p in moved if not p.startswith(COUNTS_SCOPE)]
    require(not stray, "HEAD changes %s beyond the candidate outside %s"
            % (", ".join(stray[:3]), COUNTS_SCOPE))
    return commit


def load_counts(path, sides, kind, repo=None, committed=True,
                mseal=None):
    """A counts file, checked against this gate: schema, pins, manifest, the
    code it is bound to and (committed=True) the commit rule."""
    counts = a.load(path)
    require(counts.get("schema") == COUNTS_SCHEMA and
            counts.get("kind") == kind, "not a %s counts file" % kind)
    require(counts["base"] == sides["base"]["pin"] and
            counts["cand"] == sides["cand"]["pin"],
            "the counts file is of another gate")
    require(mseal is None or counts.get("manifest") == mseal,
            "the snapshots were rebuilt since the counts file was made "
            "(its manifest seal is not the current one): predeclare again")
    require(counts["code"] == code_seals(), "the code changed since the "
            "counts file was made: " + ", ".join(
                n for n in CODE if counts["code"].get(n) !=
                code_seals()[n]))
    require(sorted(counts["reps"]) == sorted(counts["references"]) and
            set(counts["reps"]) <= set(cases.NAMES) and
            all(isinstance(r, int) and r >= 1
                for r in counts["reps"].values()), "malformed counts")
    if committed:
        counts["commit"] = check_counts_commit(repo, path,
                                               sides["cand"]["pin"])
    return counts


# --------------------------------------------------------- tree and scans

def stops_for(unit):
    """The directories below a unit's own that belong to another unit (src/real
    holds src/real/analysis): a scan does not enter them."""
    mine = Path(unit["dir"])
    return tuple(sorted(
        str(Path(u["dir"]).relative_to(mine)) for u in cases.UNITS
        if u["dir"] != unit["dir"] and Path(u["dir"]).is_relative_to(mine)))


def scan(top, stops=()):
    """rel path -> entry of everything below `top`: a regular file by
    (size, mtime_ns, sha256), a symlink by (target, mtime_ns), a directory
    by existence. Run-dependent `.hol` entries (snap.excluded: locks, build
    logs, other logs) are not listed; `stops` are relative directories of
    other units, not entered."""
    top = Path(top)
    found = {}

    def walk(folder, rel):
        try:
            names = sorted(os.listdir(folder))
        except OSError:
            return
        for name in names:
            path = os.path.join(folder, name)
            here = os.path.join(rel, name) if rel else name
            info = os.lstat(path)
            skip = snap.excluded(here)
            if stat.S_ISLNK(info.st_mode):
                if not skip:
                    found[here] = ["l", os.readlink(path), info.st_mtime_ns]
            elif stat.S_ISDIR(info.st_mode):
                if here in stops:
                    continue
                if not skip:
                    found[here] = ["d"]
                walk(path, here)
            elif not skip:
                with open(path, "rb") as stream:
                    digest = sha(stream.read())
                found[here] = ["f", info.st_size, info.st_mtime_ns, digest]

    walk(str(top), "")
    return found


def changed(before, after):
    return sorted(p for p in set(before) | set(after)
                  if before.get(p) != after.get(p))


def target_rels(name):
    """Every file the theory target `<name>Theory` writes (S1's list)."""
    return [t.format(n=name) for t in snap.THEORY_TARGET_TEMPLATES]


def back_up(folder, rels, store):
    meta = {}
    for rel in rels:
        src, dst = Path(folder) / rel, Path(store) / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dst)
        info = os.stat(src)
        meta[rel] = dict(mtime_ns=info.st_mtime_ns,
                         mode=stat.S_IMODE(info.st_mode),
                         sha256=sha(dst.read_bytes()))
    return meta


def restore(folder, meta, store, now):
    """Put back the saved products byte for byte with their mtimes, and
    remove products the process created that were not saved."""
    for rel in now:
        if rel not in meta:
            with contextlib.suppress(FileNotFoundError):
                (Path(folder) / rel).unlink()
    for rel, m in meta.items():
        dst = Path(folder) / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(Path(store) / rel, dst)
        os.chmod(dst, m["mode"])
        os.utime(dst, ns=(m["mtime_ns"], m["mtime_ns"]))


def settle(folder, stops, before, meta, store, name, stray_dir):
    """After a process, whatever its end: put the unit's products back,
    move every other new file (Holmake intermediates a failed process
    leaves, anything a selftest writes) into `stray_dir`, and remove the
    directories the process made. Returns the moved rel paths, the existing
    files outside the products that changed or vanished (`modified`), the
    products the process rewrote (`rewritten`: the Holmake churn of the
    target, e.g. its make-deps files) and whether the products are back as
    they were (`ok`)."""
    targets = set(target_rels(name)) if name else set()
    now = scan(folder, stops)
    restore(folder, meta, store, [p for p in now if p in targets])
    moved = []
    for rel in sorted(p for p, e in now.items()
                      if p not in before and p not in targets and
                      e[0] != "d"):
        src, dst = Path(folder) / rel, Path(stray_dir) / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(src), str(dst))
        moved.append(rel)
    for rel in sorted((p for p, e in now.items()
                       if p not in before and e[0] == "d"), reverse=True):
        with contextlib.suppress(OSError):
            (Path(folder) / rel).rmdir()
    final = scan(folder, stops)
    ok = all(final.get(r) == before.get(r) for r in meta) and not any(
        r in final and r not in before for r in targets)
    modified = sorted(p for p in changed(before, final)
                      if p not in meta and p in before and
                      before[p][0] != "d")
    rewritten = sorted(r for r in targets if r in now and
                       before.get(r) != now.get(r))
    return dict(moved=moved, modified=modified, ok=ok, rewritten=rewritten)


def normalize_text(data, root):
    """A selftest's output (bytes) with S1's rules: the root, ANSI codes,
    GC tags and durations masked. The one rule set, shared with
    `task32_snapshots compare`."""
    if isinstance(data, str):
        data = data.encode("latin-1", "replace")
    return snap.normalize_log(data, root)


def text_digest(data, root):
    return sha(normalize_text(data, root).encode("latin-1", "replace"))


def theory_digest(files, root, where=None):
    """sha256 of a theory's generated .sig and .sml with the root masked and
    of its .dat in canonical form (task32_dat: every table index resolved).
    A parent's hash is masked: the parents are separate theories, compared
    by `task32_snapshots compare`. `where` names the unit and folder in a
    refusal."""
    for ext in ("sig", "dat", "sml"):
        require(ext in files, "theory product missing: ." + ext +
                (" (%s)" % where if where else ""))
    try:
        canon = dat.canonical(snap.normalize_bytes(
            files["dat"], root).decode("latin-1"))
        shown = dat.digest(canon, [t for t, _ in canon["parents"]])[0]
    except (dat.Failure, ValueError, IndexError, KeyError,
            TypeError, AttributeError) as error:
        raise Refusal("unparsable .dat: %s%s" % (
            error, " (%s)" % where if where else ""))
    digest = hashlib.sha256()
    for ext in ("sig", "sml"):
        digest.update(ext.encode() + b"\0" +
                      snap.normalize_bytes(files[ext], root) + b"\0")
    digest.update(b"dat\0" + shown.encode() + b"\0")
    return digest.hexdigest()


def product_path(folder, name, ext):
    return Path(folder) / ".hol/objs" / ("%sTheory.%s" % (name, ext))


def where_of(unit, folder):
    """Where a unit's products are expected, for a refusal."""
    if unit["kind"] == "theory":
        return "unit %s: expected %s" % (unit["name"], product_path(
            folder, unit["theory"], "{sig,dat,sml}"))
    return "unit %s: expected %s" % (unit["name"],
                                      Path(folder) / "selftest.exe")


def read_products(folder, name):
    found = {}
    for ext in ("sig", "dat", "sml"):
        path = product_path(folder, name, ext)
        if path.is_file():
            found[ext] = path.read_bytes()
    return found


def build_log_digest(folder, unit, root):
    """The digest of the build's own selftest log of a unit, in the snapshot
    (`.hol/logs/<unit>.log`, or the one `*selftest.log`)."""
    logs = Path(folder) / ".hol/logs"
    path = logs / (unit["name"] + ".log")
    if not path.is_file():
        found = sorted(logs.glob("*selftest.log")) if logs.is_dir() else []
        require(len(found) == 1, "no build log of %s: expected %s or one "
                "*selftest.log in %s" % (unit["name"], path, logs))
        path = found[0]
    return text_digest(path.read_bytes(), root)


# ------------------------------------------------------------- processes

def group_members(pgid):
    """The live (not zombie) processes of a process group, as
    (pid, command) pairs, from /proc."""
    found = []
    for entry in os.listdir("/proc"):
        if not entry.isdigit():
            continue
        try:
            text = Path("/proc", entry, "stat").read_text()
        except OSError:
            continue
        head, _, tail = text.rpartition(")")
        fields = tail.split()
        if len(fields) > 2 and fields[0] != "Z" and \
                int(fields[2]) == pgid:
            found.append((int(entry), head.partition("(")[2]))
    return found


def kill_group(pid):
    """SIGKILL a process group, reap its leader if that is still to do and
    wait until no live process is left in the group, so that nothing still
    writes when the caller restores. Returns the survivors, as
    (pid, command) pairs (empty when the group is gone)."""
    with contextlib.suppress(ProcessLookupError):
        os.killpg(pid, signal.SIGKILL)
    with contextlib.suppress(ChildProcessError):
        os.waitpid(pid, 0)
    left = group_members(pid)
    for _ in range(500):
        if not left:
            break
        time.sleep(0.01)
        left = group_members(pid)
    return left


def launch(argv, cwd, env, timeout, out_path, fds=()):
    """One fresh process tree, from outside: monotonic wall time and the
    `wait4` resource usage of the child and the descendants it waited for.
    Output goes to a file; stdin is /dev/null. The timer kills only a child
    that has not exited yet (`done` and `waitid` under a lock), so a child
    that ended just before the deadline is not reported as timed out. An
    exception while waiting (a signal turned into Terminated, which only the
    wait itself can raise) kills the group and waits for it to be empty
    before it propagates. Whatever the
    leader's end, the group is killed afterwards, and any process that was
    still in it (`survivors`, by command name) makes the process refused."""
    with open(out_path, "wb") as out:
        lock = threading.Lock()
        state = dict(done=False, expired=False)
        # no signal can lose the child or the timer between their starts:
        # in DEFER mode one is only recorded
        with snap.deferred(raise_pending=False):
            started = time.perf_counter()
            proc = subprocess.Popen(
                argv, cwd=str(cwd), env=env, stdin=subprocess.DEVNULL,
                stdout=out, stderr=subprocess.STDOUT,
                start_new_session=True, pass_fds=tuple(fds))

            def kill():
                with lock:
                    if state["done"]:
                        return
                    try:
                        if os.waitid(os.P_PID, proc.pid, os.WEXITED |
                                     os.WNOWAIT | os.WNOHANG) is not None:
                            return  # already exited, only not reaped
                    except ChildProcessError:
                        return
                    state["expired"] = True
                    with contextlib.suppress(ProcessLookupError):
                        os.killpg(proc.pid, signal.SIGKILL)

            timer = threading.Timer(timeout, kill)
            timer.start()
        error = None
        try:
            with snap.raising():  # the only interruptible wait
                _, status, usage = os.wait4(proc.pid, 0)
                wall = time.perf_counter() - started
        except BaseException as caught:
            error = caught
        with snap.deferred(raise_pending=False):
            with lock:
                state["done"] = True
            timer.cancel()
            # always: a leader that is gone leaves its group behind, and
            # an interrupted wait leaves the leader itself
            leftover = [] if error else group_members(proc.pid)
            unkilled = kill_group(proc.pid)
        if error is not None:
            proc.returncode = -signal.SIGKILL  # reaped by kill_group
            raise error
    proc.returncode = os.waitstatus_to_exitcode(status)
    return dict(exit=proc.returncode, timed_out=state["expired"], wall=wall,
                utime=usage.ru_utime, stime=usage.ru_stime,
                maxrss=usage.ru_maxrss * 1024,
                survivors=sorted(set(c for _, c in leftover + unkilled)))


def process_env(scratch, extra):
    env = dict(snap.environment(Path(scratch) / "home",
                                Path(scratch) / "tmp"))
    env.update(extra)
    return env


def build_reporter(root, folder, env, timeout, fds):
    """The reporter's .uo, built by this side's own Holmake (not timed)."""
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=False)
    (folder / (REPORTER_NAME + ".sml")).write_text(REPORTER)
    done = loading.execute(
        [str(root / "bin/Holmake"), "--no-project", "--no-cache",
         REPORTER_NAME + ".uo"], folder, env, timeout, fds)
    require(done["exit"] == 0 and not done["timed_out"],
            "reporter build failed in %s: %s" % (root, done["stdout"][-300:]))
    uo = folder / (REPORTER_NAME + ".uo")
    require(uo.exists() or (folder / ".hol/objs" /
                            (REPORTER_NAME + ".uo")).exists(),
            "the reporter was not built")
    return dict(dir=str(folder), uo=str(uo), source_sha256=REPORTER_SEAL,
                build_stdout_sha256=done["stdout_sha256"])


def poly_version(env, cwd, fds):
    done = loading.execute(["poly", "-v"], cwd, env, 60, fds)
    require(done["exit"] == 0 and done["stdout"].strip(),
            "Poly/ML version query failed")
    return done["stdout"].strip()


def parse_selftest(text, root, unit):
    """The `hol run` command of a selftest.exe (4 lines, a fixed format),
    checked to stay inside `root` and in the unit's heap."""
    lines = text.splitlines()
    require(len(lines) == 4 and lines[:2] == ["#!/bin/sh", "set -e"] and
            lines[3] == "exit 0", "unexpected selftest.exe format")
    argv = shlex.split(lines[2])
    require(len(argv) >= 5 and argv[0] == str(root / "bin/hol") and
            argv[1] == "--gcthreads=1" and argv[2] == "run" and
            argv[-1] == "selftest", "unexpected selftest command: " +
            lines[2])
    heap = [x for x in argv if x.startswith("--holstate=")]
    require(heap == ["--holstate=" + str(root / unit["heap"])],
            "the selftest runs in %s, not in %s" % (
                heap, root / unit["heap"]))
    return argv


def unit_argv(unit, root, reporter_uo):
    """The command of a unit (and its working directory)."""
    folder = root / unit["dir"]
    if unit["kind"] == "theory":
        return [str(root / "bin/Holmake"), "--no-cache", "-j1",
                "%sTheory.uo" % unit["theory"]], folder
    argv = parse_selftest((folder / "selftest.exe").read_text(), root, unit)
    return argv[:-1] + [reporter_uo, argv[-1]], folder


def unit_env(ctx, unit, reporter_uo, stats, layout, busy):
    extra = dict(T32_STATS=str(stats), T32_LAYOUT=str(layout))
    if unit["kind"] == "theory":
        extra["POLY_CLINE_OPTIONS"] = reporter_uo
    if busy:
        extra["T32_BUSY"] = repr(float(busy))  # seconds of spin at exit
    return process_env(ctx["scratch"], extra)


def parse_stats(text):
    lines = [x for x in text.splitlines() if x.strip()]
    require(lines, "missing stats: the reporter wrote nothing")
    require(len(lines) == 1, "%d stats lines, not one" % len(lines))
    try:
        stats = json.loads(lines[0])
    except ValueError as error:
        raise Refusal("unreadable stats line: %s" % error)
    require(isinstance(stats, dict) and stats.get("schema") == STATS_SCHEMA,
            "stats of another schema")
    for key in STATS_NUMBERS:
        value = stats.get(key)
        require(type(value) in (int, float) and math.isfinite(value) and
                value >= 0, "bad stats field " + key)
    for key in STATS_COUNTS:
        require(type(stats.get(key)) is int and stats[key] >= 0,
                "bad stats field " + key)
    for key in ("loaded_before", "loaded"):
        require(isinstance(stats.get(key), list) and
                all(isinstance(x, str) for x in stats[key]),
                "bad stats field " + key)
    require(isinstance(stats.get("holdir"), str) and
            isinstance(stats.get("files"), list) and
            all(isinstance(x, list) and len(x) == 2 and
                all(isinstance(y, str) for y in x) for x in stats["files"]),
            "bad stats field files")
    return stats


def check_loaded(stats, root, reporter_dir, candidate):
    """Every loaded path inside the side's root (the reporter's own
    directory apart), and no extension module anywhere."""
    require(stats["holdir"] == str(root), "the process runs in %s, not %s"
            % (stats["holdir"], root))
    for name, folder in stats["files"]:
        inside = Path(folder).is_relative_to(root) or \
            Path(folder) == Path(reporter_dir)
        require(inside, "loaded %s from %s, outside the root" % (
            name, folder))
    names = stats["loaded_before"] + stats["loaded"] + [
        Path(n).name.split(".")[0] for n, _ in stats["files"]]
    found = sorted({n for n in names if loading.extension_name(n)})
    if found:
        error = Blocked if candidate else Refusal
        raise error("extension module(s) loaded: " + ", ".join(found))


def check_digest(digest, expected, candidate):
    if expected is not None and digest != expected:
        error = Blocked if candidate else Refusal
        raise error("output differs from the reference: %s != %s" % (
            digest[:12], expected[:12]))


def measure(receipt):
    """The timed metrics of an admitted process, from its receipt."""
    use, stats = receipt["usage"], receipt["stats"]
    return dict(cpu=use["utime"] + use["stime"], wall=use["wall"],
                gc_cpu=stats["gc_time"], maxrss=float(use["maxrss"]))


def validate(receipt, unit, root, reporter_dir, expected, candidate):
    """Every per-process check that needs only the receipt (replayable).
    Raises Refusal, or Blocked for a finding about the candidate."""
    require(receipt["usage"]["exit"] == 0 and
            not receipt["usage"]["timed_out"],
            "process failed: exit %s%s" % (
                receipt["usage"]["exit"],
                ", timed out" if receipt["usage"]["timed_out"] else ""))
    require(not receipt["usage"].get("survivors"),
            "the process left running descendants: %s" %
            ", ".join(receipt["usage"].get("survivors") or []))
    stats = receipt["stats"]
    require(stats is not None, "missing stats")
    check_loaded(stats, root, reporter_dir, candidate)
    require(not receipt["modified"], "modified existing file(s) outside "
            "the products: %s; the snapshot must be rebuilt" %
            ", ".join(receipt["modified"][:5]))
    require(not receipt["stray"], "stray write: " + ", ".join(
        receipt["stray"][:5]))
    check_digest(receipt["digest"], expected, candidate)


JOURNAL_SCHEMA = "task32-journal-v1"


def journal_read(folder):
    return json.loads((Path(folder) / "journal.json").read_text())


def journal_write(folder, data):
    """Atomic and durable: the journal is what recovery trusts."""
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    tmp = folder / "journal.json.tmp"
    with open(tmp, "w") as stream:
        stream.write(json.dumps(data, indent=2, sort_keys=True) + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(tmp, folder / "journal.json")


def journal_begin(ctx, entry):
    journal_write(ctx["journal"], dict(schema=JOURNAL_SCHEMA,
                                       attempt=ctx["attempt"],
                                       pending=entry))


def journal_end(ctx):
    journal_write(ctx["journal"], dict(schema=JOURNAL_SCHEMA,
                                       attempt=ctx["attempt"], pending=None))


def journals_dir(repo):
    return Path(repo).resolve() / JOURNALS


def pending_journals(repo):
    """The run journals that still hold a theory unit's products to restore
    (or that cannot be read: treated as pending)."""
    found = []
    for path in sorted(journals_dir(repo).glob("*/journal.json")):
        try:
            data = json.loads(path.read_text())
            pending = data["pending"] is not None
        except (OSError, ValueError, KeyError, TypeError):
            pending = True
        if pending:
            found.append(path.parent)
    return found


def execute_unit(ctx, unit, side, label, layout, busy, expected):
    """One process of a unit on a side, in a fresh scratch state, with its
    tree checks and, for a theory, the byte-for-byte restore of its
    products. The backups and a journal are written to disk before any
    product is deleted and are removed only after the restore was checked.
    Returns the receipt (accepted or with a rejection)."""
    root, reporter = ctx["roots"][side], ctx["reporter"][side]
    folder = root / unit["dir"]
    stops = stops_for(unit)
    work = Path(ctx["scratch"]) / "out"
    stats_path = work / (label + ".stats")
    out_path = work / (label + ".out")
    argv, cwd = unit_argv(unit, root, reporter["uo"])
    env = unit_env(ctx, unit, reporter["uo"], stats_path, layout, busy)
    receipt = dict(argv=argv, cwd=str(cwd), layout=layout, busy=busy or None,
                   env={k: v for k, v in env.items() if k.startswith(
                       ("T32_", "POLY_"))},
                   stats=None, stray=[], moved=[], modified=[],
                   rewritten=[], digest=None, accepted=False)
    theory = unit["kind"] == "theory"
    name = unit["theory"] if theory else None
    started = time.perf_counter()
    before = scan(folder, stops)
    sigobj_before = scan(root / "sigobj")
    scans = time.perf_counter() - started
    rels = snap.theory_target_files(folder, name) if theory else []
    store = Path(ctx["journal"]) / "backup" / label
    produced = {}
    settled = None
    # From the backup to the restore a signal is only recorded (DEFER);
    # only the process wait in launch can raise it. So the restore always
    # runs and completes, a Fatal stays the primary error (a recorded
    # signal is noted on it), and otherwise the signal is raised at the end
    # of the block.
    with snap.deferred():
        meta = back_up(folder, rels, store) if theory else {}
        if theory:
            journal_begin(ctx, dict(
                label=label, folder=str(folder), store=str(store),
                name=name, stops=list(stops), meta=meta,
                unit=unit["name"], before=sorted(
                    p for p, e in before.items() if e[0] != "d")))
        try:
            for rel in rels:
                (folder / rel).unlink()
            receipt["usage"] = launch(argv, cwd, env, ctx["timeout"],
                                      out_path, ctx["fds"])
            if theory:
                produced = read_products(folder, name)
        finally:
            started = time.perf_counter()
            settled = settle(folder, stops, before, meta, store, name,
                             Path(ctx["evidence"]) / "stray" / label)
            scans += time.perf_counter() - started
            if theory:
                if not settled["ok"]:
                    raise Fatal(
                        "could not restore the products of %s in %s: the "
                        "backups and the journal are kept in %s (`recover` "
                        "puts them back)" % (unit["name"], folder,
                                             ctx["journal"]))
                journal_end(ctx)
                shutil.rmtree(store, ignore_errors=True)
    started = time.perf_counter()
    sigobj = ["sigobj/" + p for p in changed(sigobj_before,
                                             scan(root / "sigobj"))]
    receipt["scan_seconds"] = scans + time.perf_counter() - started
    receipt.update(moved=settled["moved"], modified=settled["modified"],
                   rewritten=settled["rewritten"])
    receipt["stray"] = settled["modified"] + settled["moved"] + sigobj
    data = b""
    with contextlib.suppress(OSError):
        data = out_path.read_bytes()
    stats_text = ""
    with contextlib.suppress(OSError):
        stats_text = stats_path.read_text()
    text = data.decode("latin-1")
    receipt["stdout"] = text[-4000:] if theory else text
    receipt["stdout_sha256"] = sha(data)
    try:
        receipt["digest"] = theory_digest(
            produced, root, where_of(unit, folder)) if theory else \
            text_digest(data, root)
    except Refusal as error:
        receipt["digest_error"] = str(error)
    for path in (stats_path, out_path):
        with contextlib.suppress(OSError):
            path.unlink()
    try:
        receipt["stats"] = parse_stats(stats_text)
    except Refusal as error:
        receipt["stats_error"] = str(error)
    return receipt


def admit(receipt, unit, ctx, side, expected):
    """Validate; the receipt is accepted or carries a rejection."""
    root, reporter = ctx["roots"][side], ctx["reporter"][side]
    try:
        for key in ("stats_error", "digest_error"):
            if key in receipt and receipt["usage"]["exit"] == 0:
                raise Refusal(receipt[key])
        validate(receipt, unit, root, reporter["dir"], expected,
                 side == "cand")
        receipt["measurement"] = dict(raw=measure(receipt))
        receipt["accepted"] = True
    except Blocked as error:
        receipt["rejection"] = str(error)
        receipt["blocked"] = True
    except Refusal as error:
        receipt["rejection"] = str(error)
    return receipt


# ------------------------------------------------------ schedule, statistics

def side_of(phase, selection, busy=False):
    """The snapshot a process runs in: B/B phases use the base on both
    labels; the candidate phase and the smoke run use the candidate for its
    own label.  The negative control (busy) runs entirely on the base."""
    return "cand" if phase in ("candidate", "smoke") and \
        selection == "candidate" and not busy else "base"


def layout_for(seed, pair, selection, rep):
    return loading.layout_units(seed, "candidate", pair, selection, rep)


def expected_runs(names, pairs, reps, phases):
    """(workload, phase, pair, selection, rep) of every process, in
    execution order: round-robin over the workloads, so host drift spreads
    across all of them. In round i a workload runs its control pair and its
    candidate pair, each side of a pair being `reps` fresh processes; the
    pair's first side alternates (AB on even i, BA on odd i), as in
    loading.schedule, which this reuses, and so does the order of the two
    phases (control first on even i, candidate first on odd i)."""
    order = []
    for i in range(max(pairs[w] for w in names)):
        for w in names:
            if i >= pairs[w]:
                continue
            for phase in (phases if i % 2 == 0 else phases[::-1]):
                order += [(w, phase, p, side, r) for p, side, r in
                          loading.schedule(i + 1, reps[w]) if p == i]
    return order


def label_of(workload, phase, pair, selection, rep):
    return "%s-%s-%03d-%s-%02d" % (workload, phase, pair, selection, rep)


def sample(rows, pair, selection, metric):
    values = [r["measurement"]["raw"][metric] for r in rows
              if r["pair"] == pair and r["selection"] == selection]
    return math.fsum(values) / len(values)


def statistics(rows, pairs, reps):
    """Paired statistics of one workload's phase: the sample of a side is
    the mean of its `reps` fresh processes; nothing is dropped."""
    require(len(rows) == 2 * pairs * reps and
            [(r["pair"], r["selection"], r["rep"]) for r in rows] ==
            loading.schedule(pairs, reps),
            "missing/duplicate/reordered fresh pair")
    require(all(r["accepted"] for r in rows), "rejected process in rows")
    metrics = {}
    for metric in METRICS:
        margin, gated = a.timing_rule(POLICY, metric)
        paired = [{side: sample(rows, i, side, metric)
                   for side in ("baseline", "candidate")}
                  for i in range(pairs)]
        metrics[metric] = a.paired_statistics(paired, margin, gated)
    return {"metrics": metrics}


def gated_metrics(stats):
    return [m for m, d in stats["metrics"].items() if d.get("gated", True)]


def summarize(candidate):
    """pass / fail / inconclusive of a candidate result's gated metrics."""
    decisions = [candidate["metrics"][m]["decision"]
                 for m in gated_metrics(candidate)]
    return "fail" if "fail" in decisions else \
        "pass" if all(d == "pass" for d in decisions) else "inconclusive"


def analyze(control_rows, candidate_rows, pairs, reps):
    """One workload's result from its two phases: the candidate's decisions
    under the control rule (a control outside the equivalence window makes
    anything but a fail inconclusive), the control half width and the
    second-stage pair count the grid's rule gives."""
    control = statistics(control_rows, pairs, reps)
    cand = statistics(candidate_rows, pairs, reps)
    for metric, data in cand["metrics"].items():
        a.apply_control(data, control["metrics"][metric])
    valid = all(cand["metrics"][m].get("control_valid")
                for m in gated_metrics(cand))
    return dict(control=control, candidate=cand, decision=summarize(cand),
                control_valid=valid, pairs=pairs, reps=reps,
                half_log_width=finite(loading.control_width(control)),
                second_stage_pairs=loading.second_stage_count(control,
                                                              pairs))


def median(values):
    values = sorted(values)
    return (values[len(values) // 2] + values[(len(values) - 1) // 2]) / 2


def pilot_summary(rows_by_unit, reps_floor=1):
    """The pilot of each unit: B/B pairs only. loading.jitter at R = 1, the
    proposed R (n * R the sd bound asks for, over the stage's pairs), the
    median CPU and wall of a process and whether it reaches the 1 s floor."""
    out = {}
    for name, rows in rows_by_unit.items():
        pairs = len(rows) // 2
        control = statistics(rows, pairs, 1)
        jitter = loading.jitter(rows, control, pairs, 1)
        raw = [r["measurement"]["raw"] for r in rows]
        need = jitter["required_units"]
        reps = max(reps_floor, math.ceil(need / PAIRS)) \
            if need is not None else None
        cpu = median([m["cpu"] for m in raw])
        out[name] = dict(jitter=jitter, median_cpu=cpu,
                         median_wall=median([m["wall"] for m in raw]),
                         reps=reps, long_enough=cpu >= MIN_UNIT_CPU,
                         within_cap=reps is not None and reps <= R_CAP)
    return out


def second_stage_plan(first_results):
    """workload -> pairs of the second stage: the workloads that did not
    fail and whose control missed the equivalence window (TASK30/31)."""
    plan = {}
    for name, res in first_results.items():
        if res["decision"] != "fail" and not res["control_valid"]:
            plan[name] = res["second_stage_pairs"]
    return plan


NOTE_SECOND = "second stage owed"


def classify(chain):
    """(status, note) of a workload from its stages, [(stage, result)] in
    order, routed as TASK31 does: pass or fail when the last stage decided;
    "followup" (a targeted follow-up is owed) when it is inconclusive with a
    valid B/B control after the first or the second stage; a control-limited
    one (invalid control) is owed the second stage after the first and
    blocks after it; anything inconclusive after the follow-up blocks. The
    last stage decides; stages are never combined."""
    stage, last = chain[-1]
    if last["decision"] in ("pass", "fail"):
        return last["decision"], stage
    if stage in ("first", "second"):
        if last["control_valid"]:
            return "followup", ("inconclusive with a valid control after "
                                "the %s stage" % stage)
        if stage == "first":
            return "blocked", NOTE_SECOND
        return "blocked", "control-limited after the second stage"
    return "blocked", "inconclusive after the follow-up"


def second_owed(chains):
    return [w for w in cases.NAMES if w in chains and
            classify(chains[w]) == ("blocked", NOTE_SECOND)]


def followup_owed(chains):
    return [w for w in cases.NAMES if w in chains and
            classify(chains[w])[0] == "followup"]


def followup_pairs(first_results, owed):
    """Per owed workload the pairs of its follow-up: the grid's second-stage
    rule on the first stage's B/B control with that stage's pairs (at least
    twice them, at most the grid's cap), recorded as the first stage's
    `second_stage_pairs`. Nothing of a candidate enters."""
    return {w: first_results[w]["second_stage_pairs"] for w in owed}


# --------------------------------------------------------------- ledger

STR_OR_NONE = (str, type(None))
EVENT_FIELDS = {
    "open": dict(attempt=str, stage=str, key=str, seed=str, output=str,
                 checkout=str, first_attempt=STR_OR_NONE, counts=STR_OR_NONE),
    "close": dict(attempt=str, stage=str, status=str, seal=STR_OR_NONE,
                  output=str),
    "info": dict(attempt=str, mode=str, key=str, seed=str, output=str,
                 checkout=str),
    "info-end": dict(attempt=str, success=bool, seal=STR_OR_NONE)}


def ledger_path(repo):
    """The ledger of the table: below the checkout's ignored .agent-files."""
    return (Path(repo).resolve() / ".agent-files" / "evidence" / "task32" /
            "attempts.jsonl")


def table_lines(state):
    """The lines of this table, each of a known event with its fields of the
    right types; anything else is a corrupt ledger."""
    lines, infos, ends = [], set(), set()
    for record in state.records:
        if record.get("table") != TABLE:
            continue
        event = record.get("event")
        require(isinstance(event, str) and event in EVENT_FIELDS,
                "corrupt attempts ledger: unknown event %r" % (event,))
        for key, kind in EVENT_FIELDS[event].items():
            require(key in record and any(
                loading.right_type(record[key], k) for k in (
                    kind if isinstance(kind, tuple) else (kind,))),
                "corrupt attempts ledger: %r line lacks a valid %s" % (
                    event, key))
        if event == "info":
            require(record["attempt"] not in infos, "corrupt ledger: info "
                    "run %s recorded twice" % record["attempt"])
            infos.add(record["attempt"])
        elif event == "info-end":
            require(record["attempt"] in infos and
                    record["attempt"] not in ends, "corrupt ledger: info "
                    "run %s has no start or several ends" % record["attempt"])
            ends.add(record["attempt"])
        lines.append(record)
    return lines


def table_attempts(state):
    """(attempt, stage) -> its open and close lines."""
    found = {}
    for record in table_lines(state):
        if record["event"] in ("info", "info-end"):
            continue
        row = found.setdefault((record["attempt"], record["stage"]),
                               dict(opens=[], closes=[]))
        row[record["event"] + "s"].append(record)
    for (attempt, stage), row in found.items():
        require(len(row["opens"]) == 1 and len(row["closes"]) <= 1,
                "corrupt attempts ledger: attempt %s (%s stage) has %d "
                "opening and %d close lines" % (
                    attempt, stage, len(row["opens"]), len(row["closes"])))
    return found


def read_ledger(path):
    state = tg.Ledger(path)
    return state, table_attempts(state)


def judged_because(attempt, stage, row):
    """None when the attempt is void: it admitted no measurement, shown from
    its own output (exactly one close, status failed; the output's
    downstream.json of that seal and attempt, success false, no blocked
    finding, and every archived measuring process rejected). Otherwise why
    it counts as the draw. A close with no seal (its downstream.json could
    not be saved: a failed write, a signal during the save) is never void:
    nothing shows that no measurement was admitted, so it counts."""
    if len(row["closes"]) != 1:
        return "no close line" if not row["closes"] else "several closes"
    close = row["closes"][0]
    if close["status"] != FAILED:
        return "closed " + close["status"]
    if close["seal"] is None:
        return "its close has no seal: the report was not saved"
    folder = Path(close["output"])
    if close["output"] != row["opens"][0]["output"]:
        return "its close names another output"
    try:
        path = folder / "downstream.json"
        if not path.is_file():
            return "its output is missing: " + str(path)
        if a.seal(path)["sha256"] != close["seal"]:
            return "its downstream.json differs from the sealed one"
        report = a.load(path)
        if report["attempt"] != attempt or report["stage"] != stage:
            return "its downstream.json is of another attempt"
        if report["success"] is not False or "blocked" in report:
            return "its report is a success or a blocked one"
        listed = {r["receipt"]: r for r in report["runs"]
                  if r["phase"] in PROCESS_PHASES}
        present = {q.name for q in folder.iterdir()
                   if q.name.endswith(".json.gz")}
        if present != {r["receipt"] for r in report["runs"]}:
            return "its receipts are not those the report lists"
        for name, entry in listed.items():
            receipt = a.safe_child(folder, name)
            if a.seal(receipt) != entry["seal"]:
                return "a process receipt differs from its seal: " + name
            if entry["accepted"] is not False or \
                    a.load(receipt)["accepted"] is not False:
                return "a measuring process was admitted: " + name
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as e:
        return "its output cannot be read: %s" % e
    return None


def gate_attempts(found, key, stage):
    return {i: row for (i, st), row in found.items()
            if st == stage and row["opens"][0]["key"] == key}


def reasons(found):
    return {k: judged_because(k[0], k[1], row) for k, row in found.items()}


def judged(rows, stage, why):
    return sorted(i for i in rows if why[i, stage] is not None)


def info_runs(state):
    """Every information run (smoke, pilot, control) of the table with how
    it ended."""
    ends = {r["attempt"]: r for r in table_lines(state)
            if r["event"] == "info-end"}
    return [dict(attempt=r["attempt"], mode=r["mode"], key=r["key"],
                 output=r["output"], checkout=r["checkout"],
                 status="unclosed" if r["attempt"] not in ends else
                 "success" if ends[r["attempt"]]["success"] else "failed")
            for r in table_lines(state) if r["event"] == "info"]


def attempts_table(found, why):
    """Every decision attempt of the table, for the disposition (R-1)."""
    return [dict(attempt=i, stage=st, key=r["opens"][0]["key"],
                 checkout=r["opens"][0]["checkout"],
                 statuses=[c["status"] for c in r["closes"]] or ["unclosed"],
                 void=why[i, st] is None, judged_because=why[i, st],
                 output=r["opens"][0]["output"])
            for (i, st), r in found.items()]


def redraws(attempts, infos):
    """R-1: what was drawn again - the void decision attempts and the
    information runs that did not succeed - for the report to the owner."""
    return ([dict(attempt=r["attempt"], kind="decision " + r["stage"],
                  why="void: admitted no measurement")
             for r in attempts if r["void"]] +
            [dict(attempt=r["attempt"], kind=r["mode"],
                  why="information run " + r["status"])
             for r in infos if r["status"] != "success"])


def refuse_second_draw(path, key, stage):
    """The gate has no judged attempt at this stage yet: only a run that
    admitted no measurement is void; any other new draw needs a written
    policy decision (a follow-up is its own stage with its own counts)."""
    if not Path(path).exists():
        return
    found = read_ledger(path)[1]
    why = reasons(found)
    rows = gate_attempts(found, key, stage)
    counted = judged(rows, stage, why)
    require(not counted, "the %s stage of this gate has a judged attempt "
            "already (%s): a new draw needs a written policy decision" % (
                stage, ", ".join(counted)))


def open_attempt(path, kind, **fields):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    attempt = "%s-%s" % (fields.get("stage") or fields["mode"],
                         uuid.uuid4().hex[:12])
    tg.ledger_append(path, event=kind, table=TABLE, attempt=attempt,
                     **fields)
    return attempt


def end_attempt(path, report, output, saved):
    """The close of a decision attempt, or the end of an information run;
    when it cannot be written the attempt stays open (counts as judged)."""
    try:
        seal = a.seal(Path(output) / "downstream.json")["sha256"] \
            if saved else None
        if report["mode"] in INFO_MODES:
            tg.ledger_append(path, event="info-end", table=TABLE,
                             attempt=report["attempt"],
                             success=report["success"] is True, seal=seal)
            return
        status = BLOCKED if report.get("blocked") else FAILED
        if report["success"]:
            status = stage_status(report["outcome"]["results"])
        tg.ledger_append(path, event="close", table=TABLE,
                         attempt=report["attempt"], stage=report["stage"],
                         status=status, seal=seal, output=str(output))
    except Exception as error:
        print("ATTEMPT-NOT-CLOSED %s: %s" % (report.get("attempt"), error),
              file=sys.stderr, flush=True)


def stage_status(results):
    """pass only when every workload passes; fail when one fails."""
    decisions = [r["decision"] for r in results.values()]
    return "fail" if "fail" in decisions else \
        "pass" if all(d == "pass" for d in decisions) else "inconclusive"


def check_ledger(path, report, seal, status):
    """Replay: this run is the recorded attempt of its stage, closed with
    this seal and status, and no other judged attempt exists for the gate."""
    require(Path(path).is_file(), "no attempts ledger: %s" % path)
    found = read_ledger(path)[1]
    attempt, stage = report.get("attempt"), report["stage"]
    require((attempt, stage) in found, "the ledger has no opening of this "
            "run")
    row = found[attempt, stage]
    opened = row["opens"][0]
    first = report.get("first_stage") or report.get("replaces")
    require((opened["key"], opened["seed"], opened["first_attempt"],
             opened["counts"]) == (
        report["key"], report["layout_seed"],
        None if first is None else first["attempt"],
        None if report.get("counts") is None else
        report["counts"]["seal"]["sha256"]),
        "the ledger's opening disagrees with this run")
    closes = row["closes"]
    require(len(closes) == 1 and closes[0]["seal"] == seal["sha256"] and
            closes[0]["status"] == status, "the ledger's close does not "
            "name this downstream.json and status")
    why = reasons(found)
    counted = judged(gate_attempts(found, report["key"], stage), stage, why)
    others = [i for i in counted if i != attempt]
    require(not others and attempt in counted,
            "another judged attempt exists for this gate and stage: " +
            "; ".join("%s (%s)" % (i, why[i, stage]) for i in others))
    return dict(attempts=len(gate_attempts(found, report["key"], stage)),
                judged=len(counted))


# ------------------------------------------------------------------ outcome

def stems_of(receipt):
    stats = receipt["stats"]
    return set(stats["loaded_before"]) | set(stats["loaded"])


def check_new_stems(receipts):
    """loading.check_new_stems for these processes: what a candidate process
    loads, minus what any baseline process of the workload loads, is empty
    (the name-independent extension rule). A finding about the candidate."""
    base = {}
    for r in receipts:
        if r["side"] == "base":
            base.setdefault(r["workload"], set()).update(stems_of(r))
    for r in receipts:
        if r["side"] == "cand":
            extra = stems_of(r) - base.get(r["workload"], set()) - \
                set(loading.STEM_ALLOWANCE)
            if extra:
                raise Blocked("candidate loaded what no baseline process "
                              "loaded (%s): %s" % (
                                  r["workload"], ",".join(sorted(extra))))


def heap_anchors(root, heap):
    """The modules the heap `heap` (relative to `root`) preloads, from its
    own build: the module names in the `*DEPS` variables of the Holmakefile
    of its directory (the words `buildheap` is given). None for a heap with
    no Holmakefile of its own (those in bin/); an empty set if the
    Holmakefile names none."""
    directory = Path(root) / Path(heap).parent
    makefile = directory / "Holmakefile"
    if not makefile.is_file() or Path(heap).parent == Path("bin"):
        return None
    text = makefile.read_text().replace("\\\n", " ")
    values = {}
    for line in text.splitlines():
        found = re.match(r"\s*([A-Z_]*DEPS)\s*([+:]?)=(.*)", line)
        if found and found.group(1) != "DEPS":
            if found.group(2) != "+":
                values[found.group(1)] = set()  # `=` and `:=` replace
            values.setdefault(found.group(1), set()).update(
                Path(word).name for word in found.group(3).split()
                if "$" not in word)
    return set().union(*values.values()) if values else set()


def probe_facts(report, receipts):
    """What a smoke run shows about the harness itself, per unit and side:
    one stats line, the heap fingerprint (the modules loaded before it
    started), whether the reporter registered in Meta.fileDirMap, and what
    the process rewrote. `ok` needs the reporter in every process, a
    consistent heap fingerprint per declared heap (distinct between heaps)
    and, for all the workloads, all four heaps."""
    facts = {}
    for r in receipts:
        unit = cases.BY_NAME[r["workload"]]
        folder = Path(report["reporter"][r["side"]]["dir"])
        stats = r["stats"]
        facts.setdefault(unit["name"], {})[r["side"]] = dict(
            heap=unit["heap"], stats_lines=1,
            reporter_in_files=any(Path(d) == folder
                                  for _, d in stats["files"]),
            loaded_before=len(stats["loaded_before"]),
            new_modules=len(stats["loaded"]), files=len(stats["files"]),
            rewritten=r["rewritten"])
    heaps = sorted({cases.BY_NAME[w]["heap"] for w in report["workloads"]})
    complete = list(report["workloads"]) == list(cases.NAMES)
    # the heap is observed, with a positive anchor each: the modules a
    # process finds loaded before it starts are the same for the units of a
    # declared heap; a heap built from a Holmakefile preloads the modules
    # that file names (`heap_anchors`); a heap strictly contains the heap
    # it was built on (cases.HEAP_PARENTS)
    modules = {}
    for r in receipts:
        unit = cases.BY_NAME[r["workload"]]
        found = frozenset(r["stats"]["loaded_before"])
        facts[unit["name"]][r["side"]]["heap_fingerprint"] = sha(
            "\n".join(sorted(found)).encode())
        modules.setdefault((r["side"], unit["heap"]), set()).add(found)
    heap_ok = all(len(v) == 1 for v in modules.values())
    anchors = {}
    if heap_ok:
        for (side, heap), found in sorted(modules.items()):
            have = next(iter(found))
            want = heap_anchors(report["roots"][side], heap)
            parent = modules.get((side, cases.HEAP_PARENTS.get(heap)))
            anchors[side + ":" + heap] = dict(
                anchors=sorted(want or ()), contains_parent=None
                if parent is None else have > next(iter(parent)))
            heap_ok = heap_ok and (
                want is None or (bool(want) and want <= have)) and (
                parent is None or have > next(iter(parent)))
    ok = all(f["reporter_in_files"] for found in facts.values()
             for f in found.values()) and heap_ok and (
        not complete or heaps == list(cases.HEAPS))
    return dict(units=facts, heaps=heaps, complete=complete,
                heaps_observed=heap_ok, heap_anchors=anchors, ok=ok)


def overheads(report, receipts):
    """The cost of the harness around a process (not timed): scans of the
    unit directory per process and the snapshot verifications."""
    scans = {}
    for r in receipts:
        scans.setdefault(r["workload"], {})[r["side"]] = r["scan_seconds"]
    seconds = {k: v["seconds"] for k, v in (report.get("verify") or
                                            {}).items()}
    return dict(scan_seconds=scans, verify_seconds=seconds)


def outcome(report, receipts):
    """The numbers and decisions of a run, from its receipts alone (the one
    function a run and its replay share, so that they agree byte for byte).
    Refuses differing or nondeterministic outputs; a candidate that loads
    what no baseline process loaded is Blocked."""
    mode, names = report["mode"], report["workloads"]
    pairs, reps = report["pairs"], report["reps"]
    digests = {}
    for r in receipts:
        digests.setdefault(r["workload"], set()).add(r["digest"])
    odd = sorted(w for w, d in digests.items() if len(d) != 1)
    require(not odd, "outputs differ between processes (or sides) of: " +
            ", ".join(odd))
    found = {w: next(iter(d)) for w, d in sorted(digests.items())}
    refs = report.get("references")
    if refs:
        bad = sorted(w for w in found if refs[w] != found[w])
        require(not bad, "outputs differ from the references: " +
                ", ".join(bad))
    check_new_stems(receipts)
    out = dict(digests=found)
    if mode == "smoke":
        out["probe"] = probe_facts(report, receipts)
        out["overheads"] = overheads(report, receipts)
        return out
    rows = {}
    for r in receipts:
        rows.setdefault((r["workload"], r["phase"]), []).append(dict(
            pair=r["pair"], selection=r["selection"], rep=r["rep"],
            accepted=r["accepted"], measurement=r["measurement"]))
    if mode == "pilot":
        out["pilot"] = pilot_summary({w: rows[w, "control"]
                                      for w in names})
        out["covered"] = all(p["long_enough"] and p["reps"] is not None
                             for p in out["pilot"].values())
        return out
    out["results"] = {w: analyze(rows[w, "control"], rows[w, "candidate"],
                                 pairs[w], reps[w]) for w in names}
    if mode == "control":
        res = out["results"][names[0]]
        # Detected means the busy reporter was judged a fail. A fail stands
        # whatever the B/B control says (apply_control never turns it into
        # anything else), so requiring a valid control as well could only
        # lose a detection to host noise and never add certainty; the
        # control's validity is reported beside it.
        out["negative_control"] = dict(
            unit=names[0], expected="fail", decision=res["decision"],
            control_valid=res["control_valid"],
            detected=res["decision"] == "fail")
    return out


def phases_of(mode):
    return ("control",) if mode == "pilot" else PROCESS_PHASES


def planned_runs(report):
    if report["mode"] == "smoke":
        return [(w, "smoke", 0, side, 0) for w in report["workloads"]
                for side in ("baseline", "candidate")]
    return expected_runs(report["workloads"], report["pairs"],
                         report["reps"], phases_of(report["mode"]))


def new_report(mode, stage, spec, repo, sides, mseal, output):
    names = spec["names"]
    return {"schema": SCHEMA, "success": False, "mode": mode, "stage": stage,
            "claims": "NOT release acceptance: proof-build timing only",
            "repo": str(repo), "output": str(output), "key": spec["key"],
            "base": sides["base"]["pin"], "cand": sides["cand"]["pin"],
            "roots": {k: str(v["root"]) for k, v in sides.items()},
            "manifest": mseal, "layout_seed": spec["seed"],
            "workloads": names, "pairs": {w: spec["pairs"][w] for w in names},
            "reps": {w: spec["reps"][w] for w in names},
            "references": spec.get("references"), "busy": spec.get("busy"),
            "counts": spec.get("counts"), "first_stage": spec.get("first"),
            "replaces": spec.get("replaces"), "policy": POLICY,
            "outliers": "none removed", "runs": [], "argv": sys.argv,
            "reporter_seal": REPORTER_SEAL, "code": code_seals()}


def originals(ctx, names):
    """The digest of what each snapshot already holds, per side, before any
    process: a theory unit's prebuilt products, a selftest's own build log
    (the same normalization as the live output). The sides must agree."""
    found = {}
    for w in names:
        unit = cases.BY_NAME[w]
        for side in ("base", "cand"):
            root = ctx["roots"][side]
            folder = root / unit["dir"]
            if unit["kind"] == "theory":
                found[w, side] = theory_digest(
                    read_products(folder, unit["theory"]), root,
                    "%s side, %s" % (side, where_of(unit, folder)))
            else:
                require((folder / "selftest.exe").is_file(),
                        "selftest.exe missing: %s side, %s" % (
                            side, where_of(unit, folder)))
                unit_argv(unit, root, "-")  # format check
                found[w, side] = build_log_digest(folder, unit, root)
        require(found[w, "base"] == found[w, "cand"],
                "what the snapshots already hold of %s differs (%s)" % (
                    w, "prebuilt theory" if unit["kind"] == "theory" else
                    "build log"))
    return found


def run_stage(args, spec):
    """One run (smoke, control, pilot or a decision stage): lock, ledger,
    reporters, the processes in order (failing fast on a rejection), the
    outcome, the verification of the snapshots before and after. SIGTERM and
    SIGHUP end the run the way a failure does: the child's group is killed,
    the products restored, the attempt closed."""
    repo = Path(args.repo).resolve(strict=True)
    sides, mseal = load_manifest(args.manifest, args.base_root,
                                 args.cand_root)
    check_candidate(repo, sides)
    require(args.authorize_measurements, "measurement authorization "
            "required")
    mode, stage = spec["mode"], spec.get("stage")
    spec = dict(spec, key=gate_key(sides))
    output = Path(args.output).resolve()
    ledger = ledger_path(repo)
    loading.require_ignored(ledger, repo)
    loading.require_ignored(journals_dir(repo), repo)
    decisive = stage in DECISIVE
    verify = None if args.no_verify else (
        args.verify_argv or default_verify(repo, args.manifest, sides))
    require(verify is not None or (not decisive and args.only),
            "a decision stage, and any run that feeds the counts, needs "
            "the snapshot verification (--no-verify is for a --only subset "
            "of an information run)")
    with a.serial_lock(repo) as fds:
        pending = pending_journals(repo)
        require(not pending, "a restore journal is pending: %s; run "
                "`recover` first" % ", ".join(map(str, pending)))
        if decisive:
            refuse_second_draw(ledger, spec["key"], stage)
        output.mkdir(parents=True, exist_ok=False)
        report = new_report(mode, stage, spec, repo, sides, mseal, output)
        fields = dict(key=spec["key"], seed=spec["seed"],
                      output=str(output), checkout=str(repo))
        if decisive:
            link = spec.get("first") or spec.get("replaces")
            report["attempt"] = open_attempt(
                ledger, "open", stage=stage, first_attempt=None
                if link is None else link["attempt"],
                counts=None if spec.get("counts") is None else
                spec["counts"]["seal"]["sha256"], **fields)
        else:
            report["attempt"] = open_attempt(ledger, "info", mode=mode,
                                             **fields)
        scratch = Path(args.scratch) / ("run-" + report["attempt"])
        journal = journals_dir(repo) / report["attempt"]
        saved = False
        with snap.terminating():
            try:
                body(args, spec, report, sides, scratch, fds, verify,
                     journal)
                report["success"] = True
            except (Refusal, OSError, ValueError, KeyError, IndexError,
                    TypeError, subprocess.SubprocessError, Fatal,
                    snap.Terminated) as error:
                report["failure"] = "%s: %s" % (type(error).__name__, error)
                for note in getattr(error, "__notes__", ()):
                    report["failure"] += " (%s)" % note
                if isinstance(error, Blocked):
                    report["blocked"] = str(error)
            finally:
                # a signal here is only recorded: the save and the close
                # complete, and `terminating` raises it afterwards
                with snap.deferred(raise_pending=False):
                    try:
                        shutil.rmtree(scratch, ignore_errors=True)
                        with contextlib.suppress(OSError):
                            Path(args.scratch).rmdir()  # only if empty
                        if journal.exists() and \
                                not pending_journals_in(journal):
                            shutil.rmtree(journal, ignore_errors=True)
                        elif journal.exists():
                            report["journal"] = str(journal)
                        a.save(output / "downstream.json", report)
                        saved = True
                    finally:
                        end_attempt(ledger, report, output, saved)
    return report


def pending_journals_in(folder):
    try:
        return journal_read(folder)["pending"] is not None
    except (OSError, ValueError, KeyError, TypeError):
        return True


def body(args, spec, report, sides, scratch, fds, verify, journal):
    scratch.mkdir(parents=True, exist_ok=False)
    for sub in ("home", "tmp", "out"):
        (scratch / sub).mkdir()
    ctx = dict(roots={k: v["root"] for k, v in sides.items()},
               scratch=str(scratch), timeout=args.timeout, fds=fds,
               reporter={}, journal=journal, attempt=report["attempt"],
               evidence=Path(report["output"]))
    journal_end(ctx)
    if verify is not None:
        report["verify"] = {"before": run_verify(verify, report["repo"],
                                                 fds)}
    env = process_env(scratch, {})
    report["poly_version"] = poly_version(env, report["repo"], fds)
    for side in ("base", "cand"):
        ctx["reporter"][side] = build_reporter(
            ctx["roots"][side], scratch / ("probe-" + side), env,
            args.timeout, fds)
    report["reporter"] = ctx["reporter"]
    origin = originals(ctx, report["workloads"])
    report["prebuilt"] = {w: origin[w, "base"] for w in report["workloads"]}
    refs = report["references"]
    if refs:
        for w in report["workloads"]:
            require(refs[w] == origin[w, "base"], "what the snapshots "
                    "already hold of %s differs from the reference" % w)
    receipts = []
    busy_spec = report["busy"]
    for w, phase, pair, selection, rep in planned_runs(report):
        unit = cases.BY_NAME[w]
        side = side_of(phase, selection, bool(busy_spec))
        label = label_of(w, phase, pair, selection, rep)
        busy = busy_spec["seconds"] if busy_spec and \
            phase == "candidate" and selection == "candidate" else None
        layout = layout_for(report["layout_seed"], pair, selection, rep)
        expected = (refs or {}).get(w) or origin[w, side]
        receipt = execute_unit(ctx, unit, side, label, layout, busy,
                               expected)
        receipt.update(workload=w, phase=phase, pair=pair,
                       selection=selection, rep=rep, side=side)
        admit(receipt, unit, ctx, side, expected)
        evidence = archive(Path(report["output"]), label, receipt)
        report["runs"].append(dict(
            evidence, workload=w, phase=phase, pair=pair,
            selection=selection, rep=rep, accepted=receipt["accepted"]))
        if not receipt["accepted"]:
            if receipt.get("blocked"):
                report["blocked"] = receipt["rejection"]
            raise Refusal("process rejected: %s: %s" % (
                label, receipt["rejection"]))
        receipts.append(receipt)
    if verify is not None:
        report["verify"]["after"] = run_verify(verify, report["repo"], fds)
    report["outcome"] = outcome(report, receipts)


# ------------------------------------------------------------------ replay

def check_receipt(folder, report, entry, refs):
    """One archived process: seal, label, recorded fields, command shape,
    layout, and every per-process validation again from the stored data."""
    path = a.safe_child(folder, entry["receipt"])
    require(a.seal(path) == entry["seal"], "changed process receipt")
    label = label_of(entry["workload"], entry["phase"], entry["pair"],
                     entry["selection"], entry["rep"])
    require(entry["receipt"] == label + ".json.gz", "relabelled process: " +
            entry["receipt"])
    receipt = a.load(path)
    require(all(receipt[k] == entry[k] for k in (
        "workload", "phase", "pair", "selection", "rep")) and
        receipt["accepted"] is entry["accepted"] is True,
        "process receipt disagrees with the report: " + label)
    unit = cases.BY_NAME[entry["workload"]]
    side = side_of(entry["phase"], entry["selection"],
                   bool(report["busy"]))
    require(receipt["side"] == side, "wrong snapshot: " + label)
    root = Path(report["roots"][side])
    reporter = report["reporter"][side]
    want = unit_argv_shape(unit, root, reporter["uo"], receipt["argv"])
    require(want, "unexpected command: " + label)
    layout = layout_for(report["layout_seed"], entry["pair"],
                        entry["selection"], entry["rep"])
    busy = report["busy"]["seconds"] if report["busy"] and \
        entry["phase"] == "candidate" and \
        entry["selection"] == "candidate" else None
    require(receipt["layout"] == layout and
            receipt["env"].get("T32_LAYOUT") == str(layout) and
            receipt["busy"] == busy and
            ("T32_BUSY" in receipt["env"]) is (busy is not None) and
            (busy is None or
             receipt["env"]["T32_BUSY"] == repr(float(busy))),
            "wrong layout or busy setting: " + label)
    expected = (refs or {}).get(entry["workload"]) or \
        report["prebuilt"][entry["workload"]]
    validate(receipt, unit, root, reporter["dir"], expected, side == "cand")
    if unit["kind"] == "selftest":
        require(text_digest(receipt["stdout"].encode("latin-1"), root) ==
                receipt["digest"], "the stored output does not give the "
                "digest: " + label)
    require(same(measure(receipt), receipt["measurement"]["raw"]),
            "changed measurement: " + label)
    return receipt


def unit_argv_shape(unit, root, uo, argv):
    if unit["kind"] == "theory":
        return argv == [str(root / "bin/Holmake"), "--no-cache", "-j1",
                        "%sTheory.uo" % unit["theory"]]
    return (len(argv) >= 6 and argv[0] == str(root / "bin/hol") and
            argv[2] == "run" and argv[-2:] == [uo, "selftest"] and
            argv[3] == "--holstate=" + str(root / unit["heap"]))


def counts_file_for(report, counts, followup_counts):
    """The counts file a decision run used: the one named, else the
    committed default of its stage. A run that used counts is not replayed
    without them."""
    stage = report["stage"]
    if report.get("counts") is None or stage not in ("first", "followup"):
        return None
    file = counts if stage == "first" else followup_counts
    file = Path(file or (COUNTS if stage == "first" else FOLLOWUP_COUNTS))
    require(file.is_file(), "the %s stage used a counts file; %s is absent "
            "(name it with --%s)" % (stage, file, "counts" if stage ==
                                     "first" else "followup-counts"))
    return file


def replay_one(folder, ledger=None, counts=None, followup_counts=None,
               repo=None):
    """Recompute every observation, check and decision of one finished run
    from its archived receipts (no process runs). Returns (info, report)."""
    folder = Path(folder).resolve(strict=True)
    seal = a.seal(folder / "downstream.json")
    report = a.load(folder / "downstream.json")
    require(report.get("schema") == SCHEMA and report["success"] is True,
            "not a successful " + SCHEMA + " run")
    mode, stage = report["mode"], report["stage"]
    require(stage == (None if mode in INFO_MODES else mode) and
            mode in INFO_MODES + DECISIVE, "malformed run")
    require(report["policy"] == POLICY and
            report["reporter_seal"] == REPORTER_SEAL and
            report["layout_seed"] == SEEDS[stage or mode],
            "the policy, reporter or seed changed")
    check_code(report["code"])
    require(sorted(report["prebuilt"]) == sorted(report["workloads"]) and
            all(not report["references"] or
                report["references"][w] == report["prebuilt"][w]
                for w in report["workloads"]),
            "what the snapshots held does not match the references")
    if mode == "control":
        busy = report["busy"]
        require(busy and busy["seconds"] == round(
            BUSY * busy["median_cpu"], 6) and busy["fraction"] == BUSY,
            "the negative control's busy time is not %.0f%% of the "
            "pilot's median CPU" % (100 * BUSY))
    else:
        require(not report["busy"], "only the negative control is busy")
    require(report["workloads"] == [w for w in cases.NAMES
                                    if w in report["workloads"]] and
            report["workloads"], "malformed workloads")
    require(all(r >= 1 for r in report["reps"].values()),
            "too few repetitions")
    order = planned_runs(report)
    require([(r["workload"], r["phase"], r["pair"], r["selection"],
              r["rep"]) for r in report["runs"]] == order,
            "missing, extra or reordered processes")
    least = dict(smoke=1, pilot=PILOT_PAIRS, control=CONTROL_PAIRS)
    require(mode not in DECISIVE or all(
        report["verify"][k]["exit"] == 0 for k in ("before", "after")),
        "a decision stage ran without the snapshot verification")
    require(all(report["pairs"][w] >= least.get(mode, 10)
                for w in report["workloads"]), "too few pairs")
    refs = report["references"]
    receipts = [check_receipt(folder, report, e, refs)
                for e in report["runs"]]
    require(same(outcome(report, receipts), report["outcome"]),
            "recomputed outcome differs from the report")
    info = dict(replayed=len(receipts), mode=mode, stage=stage, seal=seal)
    if mode in DECISIVE:
        info["exit"] = stage_status(report["outcome"]["results"])
        info["attempts"] = check_ledger(
            ledger or ledger_path(report["repo"]), report, seal,
            info["exit"])
        file = counts_file_for(report, counts, followup_counts)
        if file is not None:
            check_counts_use(report, file, repo)
    return info, report


def check_counts_use(report, path, repo):
    """The run used this counts file: its seal, and that its values are the
    run's; the commit rule where the repository is at hand."""
    used = report["counts"]
    require(used is not None and a.seal(path) == used["seal"],
            "the counts file is not the one the run used")
    data = a.load(path)
    check_code(data["code"])
    require(data["reps"] == report["reps"] if report["stage"] == "first"
            else all(data["reps"][w] == report["reps"][w] and
                     data["pairs"][w] == report["pairs"][w]
                     for w in report["workloads"]), "changed repetitions")
    require(data["references"] == report["references"],
            "changed references")
    repo = repo or report["repo"]
    if Path(repo).is_dir():
        require(check_counts_commit(repo, path, report["cand"]) ==
                used["commit"], "changed counts commit")


def replay_chain(folder, ledger=None, counts=None, followup_counts=None,
                 repo=None):
    """The stage chain ending in `folder`, each stage replayed and tied to
    its parent: the second stage is exactly the plan of its first; a
    follow-up is of the workloads left owed by the stages before it (first
    or second), at the pairs the grid's rule gives. [{stage, report, info,
    folder}] in order."""
    folder = Path(folder).resolve(strict=True)
    info, report = replay_one(folder, ledger, counts, followup_counts, repo)
    here = dict(stage=report["stage"], report=report, info=info,
                folder=folder)
    stage = report["stage"]
    require(stage in DECISIVE, "only decision stages form a chain")
    if stage == "first":
        require(report["workloads"] == list(cases.NAMES) and
                set(report["pairs"].values()) == {PAIRS},
                "a first stage is all 15 workloads of %d pairs" % PAIRS)
        return [here]
    link = report["first_stage"] if stage == "second" else report["replaces"]
    parent = replay_chain(link["run"], ledger, counts, followup_counts, repo)
    last = parent[-1]
    require(a.seal(Path(link["run"]) / "downstream.json") == link["seal"]
            and link["attempt"] == last["report"]["attempt"],
            "the stage names another parent")
    for key in ("base", "cand", "key", "roots", "manifest"):
        require(report[key] == last["report"][key],
                "the stage changes " + key)
    require(all(report["references"][w] == last["report"]["references"][w]
                for w in report["workloads"]), "the stage changes the "
            "references")
    chains = workload_chains(parent)
    if stage == "second":
        require(last["stage"] == "first", "a second stage follows a first")
        plan = second_stage_plan(last["report"]["outcome"]["results"])
        require(plan and report["pairs"] == plan and
                report["workloads"] == [w for w in cases.NAMES if w in plan]
                and link["plan"] == plan and
                all(report["reps"][w] == last["report"]["reps"][w]
                    for w in plan), "the second stage is not the plan of "
                "its first stage")
    else:
        require(last["stage"] in ("first", "second"), "a follow-up follows "
                "the first or the second stage")
        require(not second_owed(chains), "a workload is still owed its "
                "second stage")
        owed = followup_owed(chains)
        pairs = followup_pairs(parent[0]["report"]["outcome"]["results"],
                               owed)
        require(owed and report["workloads"] == owed and
                report["pairs"] == pairs and all(
                    report["reps"][w] == parent[0]["report"]["reps"][w]
                    for w in owed), "the follow-up is not of the workloads "
                "owed, at the grid's pairs")
    return parent + [here]


def workload_chains(chain):
    """workload -> [(stage, result)] over a stage chain, in order."""
    found = {}
    for entry in chain:
        for w, result in entry["report"]["outcome"]["results"].items():
            found.setdefault(w, []).append((entry["stage"], result))
    return found


# ------------------------------------------------------- counts, disposition

def pins_of(args):
    sides, mseal = load_manifest(args.manifest, args.base_root,
                                 args.cand_root)
    return sides, mseal


def info_run(folder, key, mode, ledger, names=None, *, mseal):
    """A replayed information run of this gate, verified before and after
    (a run without the audit cannot feed the counts)."""
    info, report = replay_one(folder, ledger=ledger)
    require(report["mode"] == mode and report["key"] == key,
            "--%s is not a %s run of this gate" % (mode, mode))
    require(report["manifest"] == mseal, "the %s run was made on other "
            "snapshots (the manifest seal differs): the snapshots were "
            "rebuilt since" % mode)
    require(report["workloads"] == (names or list(cases.NAMES)),
            "the %s run is not of the workloads the counts need" % mode)
    require(all(k in (report.get("verify") or {})
                for k in ("before", "after")),
            "the %s run did not verify the snapshots" % mode)
    path = Path(ledger or ledger_path(report["repo"]))
    require(path.is_file(), "no attempts ledger: %s" % path)
    lines = table_lines(tg.Ledger(path))
    attempt = report["attempt"]
    starts = [r for r in lines if r["event"] == "info" and
              r["attempt"] == attempt]
    ends = [r for r in lines if r["event"] == "info-end" and
            r["attempt"] == attempt]
    require(len(starts) == 1 and (starts[0]["mode"], starts[0]["key"]) ==
            (mode, key), "the ledger has no `info` line of this %s run" %
            mode)
    require(len(ends) == 1 and ends[0]["success"] is True and
            ends[0]["seal"] == info["seal"]["sha256"],
            "the ledger has no successful `info-end` with the seal of this "
            "%s run" % mode)
    return info, report


def predeclare_first(args):
    """The counts file of the first stage, from a smoke, a pilot and a
    negative control that all ran, verified, on this gate."""
    sides, mseal = pins_of(args)
    key = gate_key(sides)
    pilot_info, pilot = info_run(args.pilot, key, "pilot", args.ledger,
                                 mseal=mseal)
    smoke_info, smoke = info_run(args.smoke, key, "smoke", args.ledger,
                                 mseal=mseal)
    control_info, control = info_run(args.control, key, "control",
                                     args.ledger, [cases.CONTROL_UNIT],
                                     mseal=mseal)
    require(pilot["outcome"]["covered"], "the pilot is not usable: a unit "
            "is under %.0f s of CPU" % MIN_UNIT_CPU)
    over = sorted(w for w, p in pilot["outcome"]["pilot"].items()
                  if not p["within_cap"])
    require(not over, "R above the cap of %d for: %s (the first stage would "
            "take %d times longer than planned)" % (R_CAP, ", ".join(over),
                                                    R_CAP))
    require(smoke["outcome"]["probe"]["ok"] and
            smoke["outcome"]["probe"]["complete"],
            "the smoke run did not pass the probe facts (reporter in "
            "fileDirMap, all four heaps)")
    require(pilot["outcome"]["digests"] == smoke["outcome"]["digests"],
            "the pilot and the smoke run disagree on an output")
    found = control["outcome"]["negative_control"]
    require(found["detected"], "the negative control was not detected "
            "(decision %s)" % found["decision"])
    require(control["busy"]["pilot"] == dict(
        attempt=pilot["attempt"], seal=pilot_info["seal"]),
        "the negative control was sized from another pilot")
    reps = {w: pilot["outcome"]["pilot"][w]["reps"] for w in cases.NAMES}
    over = smoke["outcome"]["overheads"]
    estimate = {w: 4 * PAIRS * reps[w] *
                pilot["outcome"]["pilot"][w]["median_wall"]
                for w in cases.NAMES}
    # the harness around the timed processes: scans (3 baseline and 1
    # candidate process per pair and repetition) and the two verifications
    scanning = {w: PAIRS * reps[w] * (
        3 * over["scan_seconds"][w]["base"] +
        over["scan_seconds"][w]["cand"]) for w in cases.NAMES}
    verifying = sum(over["verify_seconds"].values())
    estimate = {w: estimate[w] + scanning[w] for w in cases.NAMES}
    return {
        "schema": COUNTS_SCHEMA, "kind": "first", "base": pilot["base"],
        "cand": pilot["cand"], "manifest": mseal, "pairs": PAIRS,
        "seed": LAYOUT_SEED, "extension_seed": EXTENSION_SEED,
        "reps": reps, "r_cap": R_CAP,
        "time_estimate_seconds": dict(
            total=sum(estimate.values()) + verifying, per_unit=estimate,
            scan_seconds=sum(scanning.values()),
            verify_seconds=verifying),
        "references": smoke["outcome"]["digests"],
        "pilot": dict(attempt=pilot["attempt"], seal=pilot_info["seal"]),
        "smoke": dict(attempt=smoke["attempt"], seal=smoke_info["seal"],
                      overheads=smoke["outcome"]["overheads"]),
        "control": dict(attempt=control["attempt"],
                        seal=control_info["seal"],
                        busy_seconds=control["busy"]["seconds"],
                        detected=True),
        "jitter": {w: pilot["outcome"]["pilot"][w]["jitter"]["metrics"]
                   for w in cases.NAMES},
        "code": code_seals()}


def followup_plan(chain):
    """(owed workloads, their pairs) after the chain: refused unless the
    last stage is a first or a second and none is owed its second stage."""
    require(chain[-1]["stage"] in ("first", "second"), "a follow-up "
            "follows a first or a second stage")
    chains = workload_chains(chain)
    require(not second_owed(chains), "a workload is still owed its second "
            "stage")
    owed = followup_owed(chains)
    require(owed, "no workload is owed a follow-up")
    return owed, followup_pairs(chain[0]["report"]["outcome"]["results"],
                                owed)


def predeclare_followup(args):
    """The counts file of a follow-up: the workloads owed after the chain
    ending in --stage, at the grid's pairs (the second-stage rule on the
    first stage's control, twice its pairs at least, capped), a new seed."""
    sides, mseal = pins_of(args)
    chain = replay_chain(args.stage, ledger=args.ledger, counts=args.counts,
                         repo=args.repo)
    owed, pairs = followup_plan(chain)
    first, last = chain[0]["report"], chain[-1]
    return {"schema": COUNTS_SCHEMA, "kind": "followup",
            "base": first["base"], "cand": first["cand"],
            "manifest": mseal, "seed": FOLLOWUP_SEED, "workloads": owed,
            "pairs": pairs, "reps": {w: first["reps"][w] for w in owed},
            "references": {w: first["references"][w] for w in owed},
            "replaces": dict(run=str(last["folder"]),
                             attempt=last["report"]["attempt"],
                             seal=last["info"]["seal"]),
            "code": code_seals()}


def disposition(chain, ledger):
    """Per workload and overall: pass, fail or blocked (the R-1 table of
    every attempt of the gate, the information runs and the redraws
    included)."""
    chains = workload_chains(chain)
    require(sorted(chains) == sorted(cases.NAMES), "not all workloads")
    rows = {}
    for w in cases.NAMES:
        status, note = classify(chains[w])
        rows[w] = dict(status=status, note=note, stages=[
            dict(stage=s, decision=r["decision"],
                 control_valid=r["control_valid"], pairs=r["pairs"],
                 reps=r["reps"],
                 ratios={m: r["candidate"]["metrics"][m][
                     "median_paired_ratio"] for m in METRICS},
                 intervals={m: r["candidate"]["metrics"][m][
                     "paired_ratio_bootstrap_95_percent"]
                     for m in METRICS}) for s, r in chains[w]])
    statuses = [r["status"] for r in rows.values()]
    overall = "fail" if "fail" in statuses else \
        "pass" if set(statuses) == {"pass"} else "blocked"
    state, found = read_ledger(ledger)
    attempts = attempts_table(found, reasons(found))
    infos = info_runs(state)
    return dict(status=overall, workloads=rows, attempts=attempts,
                info_runs=infos, redraws=redraws(attempts, infos),
                chain=[dict(stage=e["stage"], run=str(e["folder"]),
                            seal=e["info"]["seal"],
                            attempt=e["report"]["attempt"])
                       for e in chain],
                counts={s: sum(1 for r in rows.values()
                               if r["status"] == s)
                        for s in ("pass", "fail", "followup", "blocked")})


# --------------------------------------------------------------------- CLI

def selected(args):
    only = getattr(args, "only", None)
    if not only:
        return list(cases.NAMES)
    require(set(only) <= set(cases.NAMES), "unknown workload in --only")
    return [w for w in cases.NAMES if w in only]


def busy_spec(args, key, mseal):
    """The negative control's busy time: BUSY of the median whole-tree CPU
    of the control unit's base processes in this gate's pilot, in absolute
    seconds, so that the tree-level slowdown is BUSY."""
    info, pilot = replay_one(args.pilot)
    require(pilot["mode"] == "pilot" and pilot["key"] == key and
            cases.CONTROL_UNIT in pilot["workloads"],
            "--pilot is not a pilot of this gate with %s" %
            cases.CONTROL_UNIT)
    require(pilot["manifest"] == mseal, "--pilot was made on other "
            "snapshots (the manifest seal differs)")
    cpu = pilot["outcome"]["pilot"][cases.CONTROL_UNIT]["median_cpu"]
    return dict(seconds=round(BUSY * cpu, 6), fraction=BUSY, median_cpu=cpu,
                pilot=dict(attempt=pilot["attempt"], seal=info["seal"]))


def info_spec(args, mode):
    if mode == "control":
        names = [cases.CONTROL_UNIT]
        pairs, reps = CONTROL_PAIRS, args.reps
        sides, mseal = pins_of(args)
        busy = busy_spec(args, gate_key(sides), mseal)
    else:
        names = selected(args)
        pairs, reps = (1, 1) if mode == "smoke" else (PILOT_PAIRS, 1)
        busy = None
    return dict(mode=mode, stage=None, names=names, seed=SEEDS[mode],
                pairs={w: pairs for w in names},
                reps={w: reps for w in names}, busy=busy, references=None)


def counts_use(path, counts):
    return dict(path=str(Path(path).resolve()), seal=a.seal(path),
                commit=counts["commit"])


def first_spec(args):
    sides, mseal = pins_of(args)
    path = Path(args.counts or COUNTS).resolve(strict=True)
    counts = load_counts(path, sides, "first", args.repo, mseal=mseal)
    require(counts["pairs"] == PAIRS and counts["seed"] == LAYOUT_SEED and
            sorted(counts["reps"]) == sorted(cases.NAMES) and
            max(counts["reps"].values()) <= counts["r_cap"] <= R_CAP,
            "the counts file is not the first stage's")
    require(not getattr(args, "only", None), "a decision stage measures all "
            "the workloads")
    return dict(mode="first", stage="first", names=list(cases.NAMES),
                pairs={w: PAIRS for w in cases.NAMES}, reps=counts["reps"],
                seed=LAYOUT_SEED, references=counts["references"],
                counts=counts_use(path, counts))


def second_spec(args):
    sides, mseal = pins_of(args)
    chain = replay_chain(args.first, None, args.counts,
                         repo=args.repo)
    first = chain[-1]
    require(first["stage"] == "first", "--first must be a first stage")
    require(first["report"]["manifest"] == mseal, "the snapshots were "
            "rebuilt since the first stage ran")
    plan = second_stage_plan(first["report"]["outcome"]["results"])
    require(plan, "no workload is owed a second stage")
    names = [w for w in cases.NAMES if w in plan]
    rep = first["report"]
    return dict(mode="second", stage="second", names=names, pairs=plan,
                reps={w: rep["reps"][w] for w in names},
                seed=EXTENSION_SEED, references=rep["references"],
                first=dict(run=str(first["folder"]),
                           seal=first["info"]["seal"],
                           attempt=rep["attempt"], plan=plan))


def followup_spec(args):
    sides, mseal = pins_of(args)
    path = Path(args.followup_counts or FOLLOWUP_COUNTS).resolve(strict=True)
    counts = load_counts(path, sides, "followup", args.repo,
                         mseal=mseal)
    require(counts["seed"] == FOLLOWUP_SEED, "the follow-up seed is fixed")
    chain = replay_chain(counts["replaces"]["run"], None, args.counts,
                         repo=args.repo)
    last = chain[-1]
    require(last["report"]["manifest"] == mseal, "the snapshots were "
            "rebuilt since the stage this follow-up replaces ran")
    require(a.seal(last["folder"] / "downstream.json") ==
            counts["replaces"]["seal"] and last["report"]["attempt"] ==
            counts["replaces"]["attempt"],
            "the counts file replaces another stage")
    owed, pairs = followup_plan(chain)
    require(owed == counts["workloads"] and counts["pairs"] == pairs and all(
        counts["reps"][w] == chain[0]["report"]["reps"][w] for w in owed),
        "the counts file is not the follow-up of the workloads owed")
    return dict(mode="followup", stage="followup", names=owed,
                pairs=pairs, reps=counts["reps"], seed=FOLLOWUP_SEED,
                references=counts["references"],
                counts=counts_use(path, counts),
                replaces=dict(run=str(last["folder"]),
                              seal=last["info"]["seal"],
                              attempt=last["report"]["attempt"],
                              stage=last["stage"]))


def exit_of(report):
    if not report["success"]:
        return 3
    out = report["outcome"]
    if report["mode"] == "control":
        return 0 if out["negative_control"]["detected"] else 1
    if report["mode"] == "pilot":
        return 0 if out["covered"] else 2
    if report["mode"] == "smoke":
        return 0
    return {"pass": 0, "fail": 1}.get(stage_status(out["results"]), 2)


def summary_line(report):
    out = report.get("outcome", {})
    head = "TASK32 %s%s: attempt %s, %d processes, success %s" % (
        report["mode"], "" if report["stage"] is None else
        " (" + report["stage"] + ")", report.get("attempt"),
        len(report["runs"]), report["success"])
    if not report["success"]:
        return head + "\nfailure: " + report.get("failure", "?")
    if "results" in out:
        return head + "\n" + "\n".join(
            "  %-18s %-12s control_valid=%s next=%s" % (
                w, r["decision"], r["control_valid"],
                r["second_stage_pairs"]) for w, r in out["results"].items())
    return head


def add_common(parser):
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--base-root", type=Path, required=True)
    parser.add_argument("--cand-root", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--counts", type=Path)


def add_ledger(parser):
    """The ledger of a run is fixed (below the checkout's ignored
    .agent-files); only the read-only commands may be pointed at a copy."""
    parser.add_argument("--ledger", type=Path)


def add_run(parser):
    add_common(parser)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--scratch", type=Path, default=Path("/dev/shm/t32"))
    parser.add_argument("--timeout", type=int, default=TIMEOUT)
    parser.add_argument("--verify-argv", type=shlex.split,
                        help="command that exits 0 while the snapshots are "
                        "the built, unchanged ones")
    parser.add_argument("--no-verify", action="store_true")
    parser.add_argument("--authorize-measurements", action="store_true")
    parser.add_argument("--only", action="append", default=[])


def build_parser():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("smoke", "pilot", "control", "run", "extend", "followup"):
        add_run(sub.add_parser(name))
    sub.choices["control"].add_argument("--reps", type=int, default=1)
    sub.choices["control"].add_argument(
        "--pilot", type=Path, required=True,
        help="this gate's pilot: the busy time is %.0f%% of its median "
        "CPU of the control unit" % (100 * BUSY))
    sub.choices["extend"].add_argument("--first", type=Path, required=True)
    sub.choices["followup"].add_argument("--followup-counts", type=Path)
    pre = sub.add_parser("predeclare")
    add_common(pre)
    add_ledger(pre)
    pre.add_argument("--pilot", type=Path)
    pre.add_argument("--smoke", type=Path)
    pre.add_argument("--control", type=Path)
    pre.add_argument("--stage", type=Path, help="follow-up: the second "
                     "stage")
    pre.add_argument("--followup", action="store_true")
    pre.add_argument("--out", type=Path, required=True)
    rec = sub.add_parser("recover", help="put back the products a killed "
                         "or failed restore left in a journal")
    rec.add_argument("--repo", type=Path, required=True)
    rep = sub.add_parser("replay")
    rep.add_argument("runs", type=Path, nargs="+")
    rep.add_argument("--ledger", type=Path)
    rep.add_argument("--counts", type=Path)
    rep.add_argument("--followup-counts", type=Path)
    rep.add_argument("--repo", type=Path)
    dis = sub.add_parser("dispose")
    dis.add_argument("--stage", type=Path, required=True)
    dis.add_argument("--out", type=Path, required=True)
    dis.add_argument("--ledger", type=Path)
    dis.add_argument("--counts", type=Path)
    dis.add_argument("--followup-counts", type=Path)
    dis.add_argument("--repo", type=Path)
    return parser


def main(argv=None):
    args = build_parser().parse_args(argv)
    try:
        return dispatch(args)
    except (Refusal, a.Blocked, ValueError, OSError) as error:
        print("REFUSED: %s" % error, file=sys.stderr)
        return 3


def dispatch(args):
    command = args.command
    if command in ("smoke", "pilot", "control"):
        spec = info_spec(args, command)
    elif command == "run":
        spec = first_spec(args)
    elif command == "extend":
        spec = second_spec(args)
    elif command == "followup":
        spec = followup_spec(args)
    elif command == "recover":
        return recover(args.repo)
    elif command == "predeclare":
        require_ledger(args)
        data = predeclare_followup(args) if args.followup else \
            predeclare_first(args)
        with args.out.open("x") as stream:
            stream.write(dumps(data))
        print("wrote %s; commit it alone before any decision process" %
              args.out)
        return 0
    elif command == "replay":
        require_ledger(args)
        chain = replay_chain(args.runs[-1], args.ledger, args.counts,
                             args.followup_counts, args.repo) \
            if len(args.runs) == 1 and json_stage(args.runs[0]) else None
        for folder in args.runs if chain is None else ():
            print(json.dumps(replay_one(folder, args.ledger, args.counts,
                                        args.followup_counts,
                                        args.repo)[0], sort_keys=True))
        for entry in chain or ():
            print(json.dumps(entry["info"], sort_keys=True))
        return 0
    else:
        require_ledger(args)
        chain = replay_chain(args.stage, args.ledger, args.counts,
                             args.followup_counts, args.repo)
        data = disposition(chain, args.ledger or ledger_path(
            chain[0]["report"]["repo"]))
        with args.out.open("x") as stream:
            stream.write(dumps(data))
        print("TASK32 disposition: %s %s" % (data["status"],
                                             json.dumps(data["counts"])))
        return {"pass": 0, "fail": 1}.get(data["status"], 2)
    report = run_stage(args, spec)
    print(summary_line(report))
    return exit_of(report)


def require_ledger(args):
    if args.ledger is not None:
        loading.require_ignored(args.ledger.resolve(), Path(
            getattr(args, "repo", None) or HERE.parents[3]))


def recover(repo):
    """Restore every pending journal: the products of the interrupted
    theory unit from the backups, the files the process left moved into the
    journal's `strays`; then clear the journal. Takes the serial lock."""
    repo = Path(repo).resolve(strict=True)
    with a.serial_lock(repo):
        pending = pending_journals(repo)
        for folder in pending:
            data = journal_read(folder)
            entry = data["pending"]
            unit_dir = Path(entry["folder"])
            before = {p: None for p in entry["before"]}
            targets = set(target_rels(entry["name"]))
            now = scan(unit_dir, tuple(entry["stops"]))
            restore(unit_dir, entry["meta"], entry["store"],
                    [p for p in now if p in targets])
            for rel, e in sorted(now.items()):
                if e[0] != "d" and rel not in before and rel not in targets:
                    dst = folder / "strays" / rel
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.move(str(unit_dir / rel), str(dst))
            for rel, m in entry["meta"].items():
                path = unit_dir / rel
                require(path.is_file() and sha(path.read_bytes()) ==
                        m["sha256"] and path.stat().st_mtime_ns ==
                        m["mtime_ns"], "recovery failed for " + str(path))
            journal_write(folder, dict(data, pending=None))
            print("recovered %s: %s" % (folder, entry["unit"]))
        if not pending:
            print("no pending restore journal")
    return 0


def json_stage(folder):
    """True for the output of a decision stage (replayed with its chain)."""
    return a.load(Path(folder) / "downstream.json").get("stage") in DECISIVE


if __name__ == "__main__":
    sys.exit(main())
