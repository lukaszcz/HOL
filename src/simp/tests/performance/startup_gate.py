#!/usr/bin/env python3
"""TASK31 ordinary-startup allocation gate (exact words, TASK29B counter).

Compares ordinary HOL startup, fresh `load "simpLib"` / `load "congLib"`
from hol.state0 and the first simplifier calls of a baseline and a candidate
HOL build in every counter field. The instrument is the TASK29B private
patched runtime, bracket shim and controls receipt; the trees are built here
by the procedure of `allocator-counter/bootstrap_probe` (`build_native_hol`),
once per tree, never in place.

  build    one native Poly/ML, the private runtime and shim, and any number
           of clean HOL trees (label=rev[+mktool]); writes lineage.json
  gate     the decision (rules R1 to R3 below) over at least two baseline
           and two candidate images
  replay   recomputes the decision from the archive alone
  cell     the TASK29B startup bracket under chosen path lengths

Independent clean builds of one tree give images whose fresh-load counts can
differ, so the decision separates what the image does from what the sources
do. The sources are exchanged over a fixed image (`Overlay`):

  R1  hol-startup, hol-first-use and the startup/empty brackets of every
      hol.state0 process are identical on every image of both sides.
  R2  over each image, the candidate sources minus the baseline sources: the
      bracket of every file outside the reviewed declaration is exactly 0,
      each declared delta is exact and the same on every image, the file
      deltas add up to the load delta with a loader gap of exactly 0, and
      the post-load brackets are exactly 0. A declared entry that measures
      0 fails.
  R3  with the baseline sources every bracket is identical across all images
      except the declared noise files. A noise file without a shown
      mechanism makes the decision `blocked`, never `pass`.

A module or structure that only the candidate loads fails unless declared.
There is no tolerance, subtraction or outlier removal.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
for sub in ("allocator-counter", "../compatibility"):
    sys.path.insert(0, str((HERE / sub).resolve()))
import acceptance as a
import allocation_schema as sc
import loading
import private_runtime as pr
import run_paired as rp
from prepare_patch import DEFAULT_SOURCE

SCHEMA = "task31-startup-gate-v4"
LINEAGE_SCHEMA = "task31-startup-toolchain-v1"
MKTOOL = ("src/portableML/rawtheory/mktool.ML",
          'useB "theorystats";', 'useB "theoryfiles";\nuseB "theorystats";')
CLIENT = HERE / "StartupGate.sml"
SNAPSHOT_ABI = 1  # first field of the counter snapshot
PAIRS = 10  # acceptance minimum; fewer pairs is a smoke only
CONFIGURE = ("--without-x", "--disable-compact32bit", "--enable-shared")
# Ordinary clients: process kind -> (heap, what the script brackets).
KINDS = {
    "hol-startup": ("hol.state", ()),
    "hol-first-use": ("hol.state", ("SIMP_CONV", "SIMP_TAC")),
    "load-simpLib": ("hol.state0", ("simpLib", "SIMP_CONV", "SIMP_TAC")),
    "load-congLib": ("hol.state0", ("congLib",)),
}
# Modules and caches that exist only in the extension, and so must be absent
# from every ordinary process (patterns on Meta.loaded module names).
EXTENSION_SUFFIX = "Ext"
EXTENSION_NAMES = ("simpExtLib", "congExtLib", "SimpTracking",
                   "TraverseExt", "Cond_rewrExt", "OpeningExt",
                   "TravrulesExt", "boolSimpsExt", "combinSimpsExt",
                   "pureSimpsExt", "splitLib", "splitPersistLib",
                   "SplitData", "simpMarkerLib", "simpMarkerScript",
                   "trackedSimpDefaults")


def require(ok, message):
    sc.require(ok, message)


def is_extension(module, allowed=()):
    """A module of the extension, unless the baseline has it too."""
    if module in allowed:
        return False
    return module.endswith(EXTENSION_SUFFIX) or module in EXTENSION_NAMES


# ---------------------------------------------------------------- building

def tool_env(tmpdir):
    """The environment of every build command: that of the toolchain
    (`allocation_matrix.toolchain`), HOLDIR added per tree."""
    env = dict(PATH=pr.PATH, HOME="/nonexistent", TMPDIR=str(tmpdir),
               TERM="dumb", LC_ALL="C", TZ="UTC", CONFIG_SITE="/dev/null")
    for key, name in (("CC", "gcc"), ("CXX", "g++")):
        env[key] = shutil.which(name, path=env["PATH"]) or ""
        require(bool(env[key]), "missing compiler: " + name)
    return env


def build_native(pristine, root, run, report):
    """Native Poly/ML from the sealed source (as build_native_hol)."""
    source, prefix = root / "native-source", root / "native-install"
    shutil.copytree(pristine, source)
    pr.verify_source(source)
    run([str(source / "configure"), *CONFIGURE, "--prefix=" + str(prefix)],
        source)
    report["native_configuration"] = (source / "config.h").read_text()
    pr.reject_compact32(report["native_configuration"])
    result = run(["make", "-j2"], source)
    report["native_stages"] = len(result["stdout"].splitlines())
    run(["make", "install"], source)
    report["native_products"] = {
        str(p): a.seal(p) for p in prefix.rglob("*") if p.is_file()}
    return prefix


DETERMINISM = (
    ("tools-poly/hol.ML",
     '  p "Sharing common data";\n  PolyML.shareCommonData '
     'PolyML.rootFunction;\n',
     '  PolyML.fullGC (); PolyML.fullGC ();\n'
     '  p "Sharing common data";\n  PolyML.shareCommonData '
     'PolyML.rootFunction;\n  PolyML.fullGC (); PolyML.fullGC ();\n'),
    ("src/proofman/Holmakefile",
     "$(protect $(HOLDIR)/bin/hol) buildheap",
     "$(protect $(HOLDIR)/bin/hol) --gcthreads=1 buildheap"),
    ("src/boss/Holmakefile",
     "$(protect $(HOLDIR)/bin/hol) buildheap",
     "$(protect $(HOLDIR)/bin/hol) --gcthreads=1 buildheap"),
    ("src/num/termination/Holmakefile",
     "$(protect $(HOLDIR)/bin/hol) buildheap",
     "$(protect $(HOLDIR)/bin/hol) --gcthreads=1 buildheap"))


def make_deterministic(hol, run):
    """Optional image-export edits of a private tree (off unless
    GATE_BUILD_DETERMINISTIC=1): one GC thread for every `buildheap` and two
    full collections around `shareCommonData` before the heap export; the
    build then also runs under `setarch -R`. They touch image creation only,
    never a tracked file, and are applied identically to every tree. Returns
    the recorded diff."""
    for name, old, new in DETERMINISM:
        path = hol / name
        text = path.read_text()
        require(text.count(old) >= 1, "determinism: no " + name)
        path.write_text(text.replace(old, new))
    return a.git(hol, "diff")


def deterministic_polyc(prefix, det):
    """In the directory `det` (inside the tree's own root, never in the
    native install): poly (a link) and a polyc whose compile step runs one
    GC thread and two full collections before each export. Returns the poly
    path to use and the seal of the polyc copy."""
    det.mkdir(exist_ok=True)
    poly = det / "poly"
    if not poly.exists():
        poly.symlink_to(prefix / "bin/poly")
    text = (prefix / "bin/polyc").read_text()
    require(text.count("PolyML.export(") == 1 and
            text.count('"${COMPILER}" -q --error-exit') == 1,
            "unexpected polyc")
    text = text.replace("PolyML.export(", "PolyML.fullGC (); "
                        "PolyML.fullGC (); PolyML.export(")
    text = text.replace('"${COMPILER}" -q --error-exit',
                        '"${COMPILER}" -q --gcthreads=1 --error-exit')
    (det / "polyc").write_text(text)
    (det / "polyc").chmod(0o755)
    return poly, a.seal(det / "polyc")


def apply_mktool(hol):
    """The develop `mktool` fix on a baseline that lacks it: one counted
    text replacement in a private tree (build tooling no client loads).
    Returns the seal of the resulting `git diff`."""
    name, old, new = MKTOOL
    path = hol / name
    text = path.read_text()
    require(text.count(old) == 1 and 'useB "theoryfiles"' not in text,
            "mktool: the replacement does not apply once")
    path.write_text(text.replace(old, new))
    diff = subprocess.run(["git", "diff"], cwd=hol, check=True,
                          capture_output=True).stdout
    require(diff.count(b"\n+++ ") == 1, "mktool: more than one file")
    return {"sha256": hashlib.sha256(diff).hexdigest(),
            "bytes": len(diff), "name": "mktool"}


def build_hol(repo, rev, hol, prefix, env, run, report, patch=None):
    """A fresh HOL tree: shared clone at rev (plus the mktool fix when
    `patch` is set),
    the configuration override, smart-configure and a no-cache build
    (the commands of build_native_hol; HOME, include override included)."""
    head = a.git(repo, "rev-parse", rev + "^{commit}")
    run(["git", "clone", "--shared", "--no-checkout", str(repo), str(hol)],
        repo)
    run(["git", "checkout", "--detach", head], hol)
    patch_seal = None
    if patch is not None:
        patch_seal = apply_mktool(hol)
    require(not (hol / "bin/hol.state0").exists(), "prebuilt HOL image")
    deterministic = os.environ.get("GATE_BUILD_DETERMINISTIC", "0") == "1"
    if deterministic:
        report["hol_determinism_diff"] = make_deterministic(hol, run)
    report["hol_build_deterministic"] = deterministic
    env = dict(env, HOLDIR=str(hol))
    report.update(hol_snapshot=head,
                  hol_patch=patch_seal,
                  hol_tree=a.git(hol, "rev-parse", "HEAD^{tree}"))
    overrides = hol / "tools-poly/poly-includes.ML"
    tool_poly = prefix / "bin/poly"
    if deterministic:
        tool_poly, report["hol_polyc_seal"] = deterministic_polyc(
            prefix, hol.parent / "detbin")
    overrides.write_text(
        'val poly = ' + json.dumps(str(tool_poly)) + ';\n' +
        'val polymllibdir = ' + json.dumps(str(prefix / "lib")) + ';\n')
    report["hol_configuration_override"] = overrides.read_text()
    run((["setarch", "-R"] if deterministic else []) +
        [str(tool_poly), "--error-exit", "--use",
         "tools/smart-configure.sml"], hol, env)
    jobs = os.environ.get("GATE_BUILD_JOBS", "2")
    report["hol_build_jobs"] = jobs
    run((["setarch", "-R"] if deterministic else []) +
        [str(hol / "bin/build"), "--no-cache", "-j" + jobs,
         "--seq=" + pr.HOL_SEQUENCE], hol, env)
    report["hol_products"] = {str(hol / n): a.seal(hol / n) for n in (
        "bin/hol", "bin/hol.state0", "bin/hol.state", "bin/Holmake")}
    report["hol_state_bytes"] = (hol / "bin/hol.state").stat().st_size
    return head


def split_tree(spec):
    """label=rev[+mktool] -> (label, rev, patch or None)."""
    label, _, rest = spec.partition("=")
    rev, _, patch = rest.partition("+")
    require(label.isalnum() and rev, "bad tree spec: " + spec)
    require(patch in ("", "mktool"), "bad tree spec: " + spec)
    return label, rev, patch or None


def build(args):
    pr.use_fixed_path()
    repo = args.repo.resolve(strict=True)
    root = args.toolchain.resolve()
    env = tool_env(args.tmpdir)
    require(platform.machine() == "aarch64", "unsupported host")
    report = dict(schema=LINEAGE_SCHEMA, environment=env, commands=[],
                  trees={}, success=False)
    with a.serial_lock(repo) as fds:
        def run(command, cwd=None, runtime_env=None):
            command_env, cwd = runtime_env, cwd or root
            started = time.time()
            receipt = loading.execute(command, cwd, command_env or env,
                                      args.timeout, fds)
            row = dict(command=receipt["command"], cwd=str(cwd),
                       exit=receipt["exit"],
                       wall=round(time.time() - started, 1),
                       tail=receipt["stdout"][-400:])
            if command_env:
                row["HOLDIR"] = command_env.get("HOLDIR")
            report["commands"].append(row)
            print("RUN", row["exit"], row["wall"], " ".join(row["command"]),
                  flush=True)
            require(receipt["exit"] == 0 and not receipt["timed_out"],
                    "failed command: " + str(command))
            return receipt
        root.mkdir(parents=True, exist_ok=False)
        try:
            if args.reuse:
                # More trees under another root (HOLDIR length sweeps) on
                # the native compiler, runtime and shim of a toolchain.
                old = a.load(args.reuse.resolve(strict=True) /
                             "lineage.json")
                require(old["success"] is True, "reused toolchain failed")
                prefix = args.reuse.resolve() / "native-install"
                lib = Path(old["library"])
                loading.check_seals({old["library"]: old["runtime"],
                                     old["shim"]: old["shim_seal"]})
                for key in ("runtime", "native_configuration", "library",
                            "shim", "shim_seal", "shim_libraries"):
                    report[key] = old[key]
                report["reused"] = str(args.reuse)
                run_env = dict(env, LD_LIBRARY_PATH=str(lib.parent))
            else:
                patched = pr.verify_source(args.source)
                prefix = build_native(args.source, root, run, report)
                lib, _, _ = pr.build_runtime(args.source, root, run, report,
                                             patched)
                fixture = root / "fixture"
                fixture.mkdir()
                run_env = dict(env, LD_LIBRARY_PATH=str(lib.parent))
                shim, report["shim_libraries"] = pr.build_shim(
                    env, run, fixture, lib, run_env, report)
                report.update(library=str(lib.resolve()), shim=str(shim),
                              shim_seal=a.seal(shim))
            for spec in args.tree:
                label, rev, patch = split_tree(spec)
                hol = root / label / "hol-source"
                hol.parent.mkdir()
                tree = report["trees"][label] = dict(rev=rev, hol=str(hol))
                tree["head"] = build_hol(repo, rev, hol, prefix, env, run,
                                         tree, patch)
                tree["libraries"] = pr.bind_runtime(
                    run, hol, lib.resolve(), run_env,
                    dict(runtime=report["runtime"]))
            report["success"] = True
        finally:
            name = "lineage.json" if report["success"] else \
                "lineage-failed.json"
            (root / name).write_text(json.dumps(report, indent=1))
    return 0


# --------------------------------------------------------------- measuring

OUT_FIELDS = sc.COUNTS + ("heap",)
KINDS["files-simpLib"] = ("hol.state0", ("simpLib", "pureSimps"))
KINDS["files-congLib"] = ("hol.state0", ("congLib",))
# Fresh-load kind -> (per-file kind, the load brackets that the per-file
# brackets plus the loader gap add up to).
LOADS = {"load-simpLib": ("files-simpLib",
                          ("load_simpLib", "load_pureSimps")),
         "load-congLib": ("files-congLib", ("load_congLib",))}
IMAGE_KINDS = ("hol-startup", "hol-first-use")
FILES_KINDS = tuple(v[0] for v in LOADS.values())
SOURCE_KINDS = tuple(LOADS) + FILES_KINDS
IMAGE_BRACKETS = ("startup", "empty")
DECLARED = HERE / "startup_gate_declared.json"
DECLARED_SCHEMA = "task31-startup-declared-v2"
USES_SIMP = ("hol-first-use", "load-simpLib")
VARIANTS = ("base", "candidate")
MIN_IMAGES = 2  # per side, for an acceptance decision
OVERLAY_ROOT = "src/simp/src"
OVERLAY_SUFFIXES = (".sig", ".sml", ".ui", ".uo")
HEX40 = frozenset("0123456789abcdef")


def holstate_args(hol, kind):
    heap = KINDS[kind][0]
    return [] if heap == "hol.state" else \
        ["--holstate=" + str(Path(hol) / "bin" / heap)]


def command(hol, kind, client):
    return [str(Path(hol) / "bin/hol"), "--gcthreads=1", "run",
            *holstate_args(hol, kind), str(client)]


def numbers(text, count):
    parts = text.split(",")
    require(len(parts) == count and all(
        p.isdigit() and (p == "0" or not p.startswith("0")) for p in parts),
        "malformed counter fields: " + text)
    return [int(p) for p in parts]


def parse_process(stdout, kind, holdir, library, aliases):
    """The record of one client process, strictly; no value is repaired."""
    require(stdout.endswith("@@GATE\tend\n"), "client did not finish")
    rows = [l.split("\t") for l in stdout.splitlines()
            if l.startswith("@@GATE\t")]
    record = dict(kind=kind, brackets=[], loaded=None, files=None)
    for row in rows[:-1]:
        require(len(row) == 5 and row[1] == kind, "malformed row: %r" % row)
        _, _, event, name, payload = row
        if event == "alloc":
            start, end = payload.split(";")
            record["brackets"].append(dict(
                name=name.replace(holdir, "$HOLDIR"),
                start=numbers(start, 8), end=numbers(end, 8)))
        elif event == "foreign":
            require(payload == sc.FOREIGN, "foreign-thread entries")
        elif event == "live":
            size, free, area, area_free = numbers(payload, 4)
            live = size - free - area
            # The formula is exact only if the allocation area is the
            # fresh one: no allocation space survived the collections (a
            # survivor is counted at its free size in both `free` and
            # `area`), so the area is all free.
            require(name == "heap" and live >= 0 and live % sc.WORD_BYTES == 0
                    and area > 0 and area_free == area,
                    "live heap reading: " + payload)
            record["live"] = dict(size_heap=size, free_last_gc=free,
                                  alloc_area=area, words=live // sc.WORD_BYTES)
        elif event == "holdir":
            require(payload == holdir, "wrong HOLDIR: " + payload)
        elif event == "result":
            record["result"] = payload if name == "ok" else name
        elif event in ("loaded", "files", "structures"):
            if name == "count":
                record[event + "_count"] = int(payload)
            else:
                names = payload.split(",") if payload else []
                require(len(names) == record[event + "_count"],
                        event + " count mismatch")
                record[event] = names
        else:
            require(False, "unknown event " + event)
    for key in ("loaded", "files", "structures", "result"):
        require(record.get(key) is not None, "missing " + key)
    require(("live" in record) == kind.startswith("load-"),
            "live heap reading of a %s process" % kind)
    require(record["brackets"][0]["name"] == "startup" and
            record["brackets"][1]["name"] == "empty",
            "first brackets are not startup and empty")
    for b in record["brackets"]:
        for snap in (b["start"], b["end"]):
            require(snap[:3] == [SNAPSHOT_ABI, sc.WORD_BYTES, 0],
                    "counter ABI, word size or overflow: %r" % snap[:3])
    sc.check_runtime(stdout, str(library), aliases)
    record["files_sha"] = sha(record["files"])
    return record


def bracket_fields(bracket):
    """The words of one bracket in every counter field (startup: absolute
    at the first probe, as TASK29B), as a dict."""
    return sc.deltas(dict(
        name="startup" if bracket["name"] == "startup" else bracket["name"],
        start=dict(zip(sc.FIELDS, bracket["start"])),
        end=dict(zip(sc.FIELDS, bracket["end"]))))


def signature(record):
    return tuple((b["name"], tuple(bracket_fields(b)[k] for k in OUT_FIELDS))
                 for b in record["brackets"])


def sha(names):
    return hashlib.sha256("\n".join(names).encode()).hexdigest()


# ------------------------------------------------------------- declarations

def parse_declared(text):
    """The reviewed declaration (data file, never the command line).

    entries: files whose fresh-load words may differ between baseline and
    candidate sources, keyed by repository path and the exact baseline and
    candidate blobs (null for a file that only the other side has), with the
    kinds they may affect. noise: files whose
    bracket may differ between images with the source fixed, each with the
    mechanism that explains it (null when none is shown). candidate_only:
    modules, structures or files that the candidate alone may load."""
    data = json.loads(text)
    require(isinstance(data, dict) and data.get("schema") == DECLARED_SCHEMA
            and sorted(data) == ["candidate_only", "entries", "noise",
                                 "schema"], "declaration schema")
    paths = set()

    def blob_ok(x, none=False):
        return (none and x is None) or (
            isinstance(x, str) and len(x) == 40 and set(x) <= HEX40)

    def joined(x):
        """A mechanism may be a list of lines (a JSON string cannot wrap)."""
        if isinstance(x, list) and x and all(isinstance(l, str) for l in x):
            return " ".join(l.strip() for l in x)
        return x

    for e in data["entries"]:
        if isinstance(e, dict) and "mechanism" in e:
            e["mechanism"] = joined(e["mechanism"])
        require(sorted(e) == ["baseline_blob", "candidate_blob", "kinds",
                              "mechanism", "path", "reason"] and
                blob_ok(e["baseline_blob"], True) and
                blob_ok(e["candidate_blob"], True) and
                (e["baseline_blob"] or e["candidate_blob"])
                and e["path"].startswith("src/") and e["path"] not in paths
                and e["kinds"] and set(e["kinds"]) <= set(LOADS) and
                e["reason"].strip() and isinstance(e["mechanism"], str)
                and e["mechanism"].strip(),
                "bad declaration entry: %r" % (e,))
        paths.add(e["path"])
    for n in data["noise"]:
        if isinstance(n, dict) and "mechanism" in n:
            n["mechanism"] = joined(n["mechanism"])
        require(sorted(n) == ["blob", "mechanism", "path", "reason"] and
                blob_ok(n["blob"]) and n["path"].startswith("src/") and
                n["path"] not in paths and n["reason"].strip() and
                (n["mechanism"] is None or (
                    isinstance(n["mechanism"], str) and
                    n["mechanism"].strip())),
                "bad noise entry: %r" % (n,))
        paths.add(n["path"])
    require(all(isinstance(c, str) and c.split(" ")[0] in (
        "module", "structure", "file") for c in data["candidate_only"]),
        "bad candidate_only entry")
    return data


def load_declared(path=DECLARED):
    text = Path(path).read_text()
    return text, parse_declared(text)


def bracket_name(path):
    return "$(HOLDIR)/" + path


# ----------------------------------------------------------------- analysis

def split_cells(records):
    cells = {}
    for r in records:
        cells.setdefault((r["kind"], r["image"], r["variant"]), []).append(r)
    for rs in cells.values():
        rs.sort(key=lambda r: r["pair"])
    return cells


def zero_row():
    return {k: 0 for k in OUT_FIELDS}


def is_zero(row):
    return not any(row.values())


def add_rows(rows):
    total = zero_row()
    for row in rows:
        for k in OUT_FIELDS:
            total[k] += row[k]
    return total


def diff_tables(left, right, whole=False):
    """right minus left by bracket name, every field: (deltas, names only on
    the left, names only on the right). A bracket on one side only has no
    delta; the caller turns it into a reason. With `whole` it is a file
    that only one side compiles, and its whole bracket is its delta
    (negative for a left-only file)."""
    out = {n: {k: right[n][i] - left[n][i]
               for i, k in enumerate(OUT_FIELDS)}
           for n in left if n in right}
    if whole:
        for n in set(left) - set(right):
            out[n] = {k: -left[n][i] for i, k in enumerate(OUT_FIELDS)}
        for n in set(right) - set(left):
            out[n] = {k: right[n][i] for i, k in enumerate(OUT_FIELDS)}
    return (out, sorted(set(left) - set(right)),
            sorted(set(right) - set(left)))


def cell_table(rs, reasons, label):
    """name -> fields of one cell (kind, image, variant): every process of
    the cell must give the same signature, modules and compiled files."""
    sigs = {signature(r) for r in rs}
    lists = {(tuple(r["loaded"]), r["files_sha"]) for r in rs}
    if len(sigs) != 1 or len(lists) != 1:
        reasons.append("nondeterministic: %s (%d distinct)" % (
            label, max(len(sigs), len(lists))))
    return dict(signature(rs[0]))


def variants_of(kind):
    return (None,) if kind in IMAGE_KINDS else VARIANTS


def analyse(records, sides, declared, sources, pairs, null=False,
            record=None):
    """Every decision of one run from its process records alone.

    records: parsed processes with kind, image (label), variant (the
    simplifier sources compiled, base or candidate; None for kinds that
    compile none) and pair. sides: {base: [labels], candidate: [labels]}.
    record: sha256 of the not-client-visible record, required for an
    attributed decision.
    sources: {variant: {repository path: blob}} for every file the
    declaration names and every file the two source trees differ in.

      R1  hol-startup, hol-first-use and the startup/empty brackets of the
          hol.state0 processes are identical on every image of both sides.
      R2  over each image, candidate sources minus baseline sources: every
          file bracket outside the declaration is exactly 0, each declared
          delta is exact and the same on every image, the per-file deltas
          add up to the load delta with the loader gap exactly 0, and the
          post-load brackets are exactly 0.
      R3  with the baseline sources, every bracket is identical across all
          images except the declared noise files, whose mechanism must be
          shown or the decision is `blocked`.
    A candidate-only module, structure or file fails unless declared."""
    reasons, notes, blockers, report = [], [], [], {}
    images = list(sides["base"]) + list(sides["candidate"])
    kinds = sorted({r["kind"] for r in records},
                   key=lambda k: list(KINDS).index(k))
    cells = split_cells(records)
    for kind in kinds:
        for image in images:
            for variant in variants_of(kind):
                rs = cells.get((kind, image, variant))
                require(rs is not None and [r["pair"] for r in rs] ==
                        list(range(pairs)),
                        "incomplete cell: %s %s %s" % (kind, image, variant))
    require(set(cells) == {(k, i, v) for k in kinds for i in images
                           for v in variants_of(k)}, "unexpected cells")
    tables = {key: cell_table(rs, reasons, "%s %s %s" % key)
              for key, rs in cells.items()}
    if null:
        declared = dict(declared, entries=[])
    # Declared entries that apply to this run (blobs as recorded).
    valid, stale = {}, []
    for e in declared["entries"]:
        got = (sources["base"].get(e["path"]),
               sources["candidate"].get(e["path"]))
        if got != (e["baseline_blob"], e["candidate_blob"]):
            if set(e["kinds"]) & set(kinds):
                reasons.append(
                    "declared entry %s does not match the sources "
                    "(baseline %s, candidate %s)" % (e["path"], got[0],
                                                     got[1]))
            stale.append(e["path"])
            continue
        for kind in e["kinds"]:
            valid[(kind, bracket_name(e["path"]))] = e
    noise = {}
    for n in declared["noise"]:
        got = (sources["base"].get(n["path"]),
               sources["candidate"].get(n["path"]))
        if got != (n["blob"], n["blob"]):
            reasons.append("noise file %s is not byte-identical to its "
                           "declaration (baseline %s, candidate %s)" % (
                               n["path"], got[0], got[1]))
            continue
        noise[bracket_name(n["path"])] = n
        if not n["mechanism"]:
            blockers.append("noise file %s has no mechanism" % n["path"])

    # R1 ------------------------------------------------------------------
    r1 = report["R1"] = {}
    for kind in kinds:
        keep = None if kind in IMAGE_KINDS else IMAGE_BRACKETS
        ref = None
        for image in images:
            for variant in variants_of(kind):
                t = {n: v for n, v in tables[(kind, image, variant)].items()
                     if keep is None or n in keep}
                if ref is None:
                    ref = (image, variant, t)
                    r1[kind] = {n: dict(zip(OUT_FIELDS, v))
                                for n, v in t.items()}
                    continue
                d, lo, ro = diff_tables(ref[2], t)
                bad = {n: {k: x for k, x in row.items() if x}
                       for n, row in d.items() if not is_zero(row)}
                if bad or lo or ro:
                    reasons.append(
                        "R1 %s: %s/%s differs from %s/%s: %s%s" % (
                            kind, image, variant, ref[0], ref[1],
                            json.dumps(bad, sort_keys=True),
                            " (brackets on one side only: %s)" % ", ".join(
                                lo + ro) if lo or ro else ""))

    # R2 ------------------------------------------------------------------
    r2 = report["R2"] = {}
    attributed = report["attributed"] = {}
    zero_declared = report["declared_zero"] = []
    for kind in (k for k in LOADS if k in kinds):
        fk, load_brackets = LOADS[kind]
        if fk not in kinds:
            reasons.append("R2 %s: per-file kind %s not measured" % (
                kind, fk))
            continue
        per_image = r2[kind] = {}
        for image in images:
            fd, lo, ro = diff_tables(tables[(fk, image, "base")],
                                     tables[(fk, image, "candidate")], True)
            ld, llo, lro = diff_tables(tables[(kind, image, "base")],
                                       tables[(kind, image, "candidate")])
            for names in (llo, lro):
                if names:
                    reasons.append(
                        "R2 %s image %s: brackets on one side only: %s" % (
                            kind, image, ", ".join(names)))
            # A file that only one side compiles: its whole bracket is its
            # delta, and it needs a declaration like any other.
            for n in lo + ro:
                if (kind, n) not in valid:
                    reasons.append(
                        "R2 %s image %s: file %s is compiled by the %s "
                        "sources only and is not declared" % (
                            kind, image, n,
                            "baseline" if n in lo else "candidate"))
            files = {n: row for n, row in fd.items()
                     if n not in IMAGE_BRACKETS and not is_zero(row)}
            for n, row in sorted(files.items()):
                if (kind, n) not in valid and n not in lo + ro:
                    reasons.append(
                        "R2 %s image %s: undeclared file %s carries %s" % (
                            kind, image, n, json.dumps(row, sort_keys=True)))
            for n, row in sorted(ld.items()):
                if n not in IMAGE_BRACKETS and n not in load_brackets and \
                        not is_zero(row):
                    reasons.append(
                        "R2 %s image %s: bracket %s outside the load "
                        "brackets carries %s" % (
                            kind, image, n, json.dumps(row, sort_keys=True)))
                if n in IMAGE_BRACKETS and not is_zero(row):
                    reasons.append("R2 %s image %s: %s differs between "
                                   "sources" % (kind, image, n))
            load = add_rows([ld[n] for n in load_brackets if n in ld])
            summed = add_rows(files.values())
            gap = {k: load[k] - summed[k] for k in OUT_FIELDS}
            if not is_zero(gap):
                reasons.append(
                    "R2 %s image %s: load delta %s but file deltas sum to "
                    "%s (loader gap %s)" % (
                        kind, image, json.dumps(load, sort_keys=True),
                        json.dumps(summed, sort_keys=True),
                        json.dumps(gap, sort_keys=True)))
            per_image[image] = dict(load=load, files=files, gap=gap)
        for (k, name), e in sorted(valid.items()):
            if k != kind:
                continue
            rows = [json.dumps(per_image[i]["files"].get(name, zero_row()),
                               sort_keys=True) for i in images]
            if len(set(rows)) != 1:
                reasons.append("R2 %s: declared delta of %s differs "
                               "between images: %s" % (
                                   kind, name, "; ".join(
                                       "%s %s" % x for x in zip(images,
                                                                rows))))
            elif is_zero(json.loads(rows[0])):
                zero_declared.append("%s %s" % (kind, name))
                reasons.append("R2 %s: declared entry %s measures 0 words" % (
                    kind, name))
            else:
                attributed.setdefault(kind, {})[name] = dict(
                    delta=json.loads(rows[0]), reason=e["reason"],
                    mechanism=e["mechanism"])

    # R3 ------------------------------------------------------------------
    r3 = report["R3"] = {}
    observed = report["noise"] = {}
    ref_image = images[0]
    for kind in (k for k in SOURCE_KINDS if k in kinds):
        per = r3[kind] = {}
        for image in images[1:]:
            d, lo, ro = diff_tables(tables[(kind, ref_image, "base")],
                                    tables[(kind, image, "base")])
            if lo or ro:
                reasons.append("R3 %s image %s: brackets on one side only: "
                               "%s" % (kind, image, ", ".join(lo + ro)))
            nz = {n: row for n, row in d.items()
                  if n not in IMAGE_BRACKETS and not is_zero(row)}
            per[image] = nz
            if kind in FILES_KINDS:
                for n, row in sorted(nz.items()):
                    if n in noise:
                        observed.setdefault(n, {})[image] = row
                    else:
                        reasons.append(
                            "R3 %s image %s: %s differs from image %s: %s" % (
                                kind, image, n, ref_image,
                                json.dumps(row, sort_keys=True)))
                continue
            fk, load_brackets = LOADS[kind]
            if fk not in kinds:
                continue
            fd = diff_tables(tables[(fk, ref_image, "base")],
                             tables[(fk, image, "base")])[0]
            allowed = add_rows(row for n, row in fd.items() if n in noise)
            load = add_rows([nz.get(n, zero_row()) for n in load_brackets])
            if load != allowed:
                reasons.append(
                    "R3 %s image %s: load brackets differ from image %s by "
                    "%s but the noise files by %s" % (
                        kind, image, ref_image,
                        json.dumps(load, sort_keys=True),
                        json.dumps(allowed, sort_keys=True)))
            for n, row in sorted(nz.items()):
                if n not in load_brackets:
                    reasons.append(
                        "R3 %s image %s: bracket %s differs from image %s: "
                        "%s" % (kind, image, n, ref_image,
                                json.dumps(row, sort_keys=True)))
    for path, n in sorted(noise.items()):
        if any(path in report["R2"].get(k, {}).get(i, {}).get("files", {})
               for k in report["R2"] for i in images):
            reasons.append("noise file %s depends on the changed sources "
                           "(non-zero R2 delta)" % path)

    # Candidate-only modules, structures and files ---------------------
    allowed_extra = set(declared["candidate_only"])
    extension = report["extension"] = {}
    for kind in kinds:
        base = [(k, rs) for k, rs in sorted(cells.items(), key=str)
                if k[0] == kind and k[1] in sides["base"] and
                k[2] in (None, "base")]
        known = {"module": set(), "structure": set(), "file": set()}
        for _, rs in base:
            known["module"] |= set(rs[0]["loaded"])
            known["structure"] |= set(rs[0]["structures"])
            known["file"] |= set(rs[0]["files"] or [])
        for key, rs in sorted(cells.items(), key=str):
            if key[0] != kind or not (key[1] in sides["candidate"] or
                                      key[2] == "candidate"):
                continue
            found = []
            for label, field in (("module", "loaded"),
                                 ("structure", "structures")):
                found += ["%s %s" % (label, name) for name in rs[0][field]
                          if name not in known[label]]
            found += ["file %s" % name for name in rs[0]["files"] or []
                      if name not in known["file"]]
            found = sorted(f for f in found if f not in allowed_extra)
            extension["%s/%s/%s" % key] = found
            if found:
                reasons.append(
                    "candidate-only in ordinary process %s %s %s: %s" % (
                        key[0], key[1], key[2], ", ".join(found)))
    for r in records:
        want = "true" if r["kind"] in USES_SIMP else "none"
        if r["kind"] not in FILES_KINDS and r["result"] != want:
            reasons.append("wrong simplifier result: %s %s" % (
                r["kind"], r["image"]))
    if any(attributed.values()) and not record:
        reasons.append("declared words need the sha256 of the "
                       "not-client-visible record (--record)")
    report["live"] = live_report(records)
    report["images"] = dict(sides)
    report["acceptance"] = (len(sides["base"]) >= MIN_IMAGES and
                            len(sides["candidate"]) >= MIN_IMAGES and
                            pairs >= PAIRS)
    report["blockers"] = sorted(set(blockers))
    report["notes"] = sorted(set(notes))
    report["reasons"] = sorted(set(reasons))
    if report["reasons"]:
        report["decision"] = "fail"
    elif not report["acceptance"]:
        report["decision"] = "smoke"
    elif report["blockers"]:
        report["decision"] = "blocked"
    elif any(attributed.values()):
        report["decision"] = "attributed"
    else:
        report["decision"] = "pass"
    return report


def live_report(records):
    """Live words after full collections at the end of the load kinds,
    candidate minus baseline sources, per image: a measured figure, not a
    decision input.  The reading is (sizeHeap - sizeHeapFreeLastFullGC -
    sizeAllocation) / 8, the heap sizes being bytes and sizeAllocation the
    allocation area, which sizeHeap includes.  Per image and kind: the
    sorted distinct readings of each variant, the allocation-area sizes
    seen, and the differences of the smallest and of the largest readings."""
    cells = {}
    for r in records:
        if r.get("live"):
            cell = cells.setdefault((r["kind"], r["image"]), dict(
                base=[], candidate=[], area=set()))
            cell[r["variant"]].append(r["live"]["words"])
            cell["area"].add(r["live"]["alloc_area"])
    out = {}
    for (kind, image), c in sorted(cells.items()):
        row = dict(base=sorted(set(c["base"])),
                   candidate=sorted(set(c["candidate"])),
                   alloc_area=sorted(c["area"]),
                   comparable=len(c["area"]) == 1,
                   runs=[len(c["base"]), len(c["candidate"])])
        if c["base"] and c["candidate"]:
            row["delta_min"] = min(c["candidate"]) - min(c["base"])
            row["delta_max"] = max(c["candidate"]) - max(c["base"])
        out.setdefault(kind, {})[image] = row
    return out


# ------------------------------------------------------------------ setup

def check_setup(trees, sides, null=False):
    """The setup rules of one run: distinct images, one revision and patch
    per side, equal HOLDIR lengths and equal build flags on every image.
    trees: {label: build report of the tree}."""
    labels = list(sides["base"]) + list(sides["candidate"])
    require(sides["base"] and sides["candidate"], "a side has no image")
    require(len(set(labels)) == len(labels), "image labels are not distinct")
    require(all(l in trees for l in labels), "unknown image label")
    require(len({len(trees[l]["hol"]) for l in labels}) == 1,
            "HOLDIR lengths differ between images")
    ident = {}
    for side in sides:
        ids = {(trees[l]["rev"], (trees[l].get("hol_patch") or {}).get(
            "sha256")) for l in sides[side]}
        require(len(ids) == 1, "more than one revision/patch on side " + side)
        ident[side] = ids.pop()
    if null:
        require(ident["base"] == ident["candidate"],
                "null control: the sides differ in revision or patch")
    else:
        require(ident["base"] != ident["candidate"],
                "the sides have the same revision and patch")
    flags = {(trees[l].get("hol_build_deterministic"),
              trees[l].get("hol_build_jobs"),
              hashlib.sha256(trees[l].get(
                  "hol_determinism_diff", "").encode()).hexdigest(),
              trees[l].get("hol_configuration_override", "").replace(
                  trees[l]["hol"], "")) for l in labels}
    require(len(flags) == 1, "build flags differ between images")
    return ident


# ---------------------------------------------------------------- overlay

def blob_id(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def overlay_files(hol):
    """{repository path: path} of the source and load-plan files under the
    simplifier directory of a tree."""
    root = Path(hol) / OVERLAY_ROOT
    return {p.relative_to(hol).as_posix(): p for p in sorted(root.rglob("*"))
            if p.is_file() and p.suffix in OVERLAY_SUFFIXES}


CLOCK_NAMES = (b"hol_clock", b"checkCPUTimer")


class Overlay:
    """The simplifier sources of the two sides over one image: the files
    (and load plans) in which the reference trees differ, written into a
    tree before each process. A file that only one side has is written for
    that side and removed for the other, so the per-file brackets cover it
    (the analysis then needs it declared). `clock` lists the overlaid and
    extra files that mention the image's CPU timer: the source kinds reset
    its stored readings, which is sound only if no file under test uses it.
    """

    def __init__(self, base_hol, candidate_hol, extra=()):
        b, c = overlay_files(base_hol), overlay_files(candidate_hol)
        self.content = {"base": {}, "candidate": {}}
        self.only = {"base": [], "candidate": []}
        for rel in sorted(set(b) | set(c)):
            if rel in b and rel in c:
                x, y = b[rel].read_bytes(), c[rel].read_bytes()
                if x != y:
                    self.content["base"][rel] = x
                    self.content["candidate"][rel] = y
            else:
                side = "base" if rel in b else "candidate"
                self.content[side][rel] = (b if rel in b else c)[
                    rel].read_bytes()
                self.only[side].append(rel)
        self.blobs = {v: {rel: blob_id(d) for rel, d in files.items()}
                      for v, files in self.content.items()}
        mentions = {rel for files in self.content.values()
                    for rel, d in files.items()
                    if any(n in d for n in CLOCK_NAMES)}
        for v, hol in zip(VARIANTS, (base_hol, candidate_hol)):
            for rel in extra:
                p = Path(hol) / rel
                if p.is_file():
                    data = p.read_bytes()
                    self.blobs[v][rel] = blob_id(data)
                    if any(n in data for n in CLOCK_NAMES):
                        mentions.add(rel)
        self.clock = sorted(mentions)

    def paths(self):
        return sorted(set(self.content["base"]) |
                      set(self.content["candidate"]))

    def other(self, variant):
        return "candidate" if variant == "base" else "base"

    def apply(self, hol, variant):
        """Make the overlay files of a tree those of a side; returns the
        number of files rewritten or removed."""
        changed = 0
        for rel, data in self.content[variant].items():
            path = Path(hol) / rel
            if not path.is_file() or path.read_bytes() != data:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                changed += 1
        for rel in self.only[self.other(variant)]:
            path = Path(hol) / rel
            if path.is_file():
                path.unlink()
                changed += 1
        return changed

    def check(self, hol, variant):
        return all((Path(hol) / rel).is_file() and
                   (Path(hol) / rel).read_bytes() == data
                   for rel, data in self.content[variant].items()) and \
            not any((Path(hol) / rel).exists()
                    for rel in self.only[self.other(variant)])


# ---------------------------------------------------------------- running

def harness_state(root):
    """The harness checkout: clean and committed, with the blob of every
    file of the gate and of the instrument it uses."""
    root = Path(root).resolve(strict=True)
    head = a.git(root, "rev-parse", "HEAD")
    identity = pr.harness_identity(root, head)
    files = sorted(set(pr.harness_inputs()) | {
        HERE / n for n in ("startup_gate.py", "StartupGate.sml",
                           "StartupGateUse.sml",
                           "startup_gate_declared.json",
                           "allocation_matrix.py")})
    blobs = {}
    for path in files:
        rel = Path(path).resolve(strict=True).relative_to(root).as_posix()
        blobs[rel] = a.git(root, "hash-object", rel)
        require(a.git(root, "rev-parse", "HEAD:" + rel) == blobs[rel],
                "harness file differs from its commit: " + rel)
    return dict(identity, blobs=blobs)


def process_env(base, hol, lib, shim, tmpdir, kind):
    return dict(base, HOLDIR=str(hol), LD_LIBRARY_PATH=str(lib.parent),
                TASK29_ALLOC_SHIM=str(shim), GATE_KIND=kind,
                GATE_USE=str(HERE / "StartupGateUse.sml"), TMPDIR=str(tmpdir))


def plan_runs(kinds, sides, pairs):
    """(kind, image, variant, pair) in execution order: per kind and pair
    every image, the two source variants of an image back to back and the
    order alternating (AB/BA) with the pair and with the image."""
    images = list(sides["base"]) + list(sides["candidate"])
    plan = []
    for kind in kinds:
        for pair in range(pairs):
            order = images if pair % 2 == 0 else images[::-1]
            for image in order:
                vs = variants_of(kind)
                for v in (vs if pair % 2 == 0 else vs[::-1]):
                    plan.append((kind, image, v, pair))
    return plan


def sha_file(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def gate(args):
    import allocation_matrix as am
    pr.use_fixed_path()
    repo = args.repo.resolve(strict=True)
    root = args.toolchain.resolve(strict=True)
    lineage = a.load(root / "lineage.json")
    require(lineage.get("schema") == LINEAGE_SCHEMA and
            lineage.get("success") is True, "toolchain not built")
    sides = dict(base=list(args.base), candidate=list(args.candidate))
    labels = sides["base"] + sides["candidate"]
    ident = check_setup(lineage["trees"], sides, args.null)
    trees = {l: lineage["trees"][l] for l in labels}
    lib, shim = Path(lineage["library"]), Path(lineage["shim"])
    aliases = sorted(str(p) for p in lib.parent.iterdir()
                     if p.name.startswith("libpolyml.so") and
                     p.resolve(strict=True) == lib and p != lib)
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    declared_text, declared = load_declared()
    record_sha = sha_file(args.record) if args.record else None
    env = tool_env(args.tmpdir)
    harness = harness_state(HERE.parents[3])
    seals = {str(lib): lineage["runtime"], str(shim): lineage["shim_seal"]}
    for tree in trees.values():
        seals.update(tree["hol_products"])
    overlay = Overlay(
        trees[sides["base"][0]]["hol"], trees[sides["candidate"][0]]["hol"],
        extra=[e["path"] for e in declared["entries"]] +
        [n["path"] for n in declared["noise"]])
    require_no_clock(overlay)
    for side, variant in zip(("base", "candidate"), VARIANTS):
        for l in sides[side]:
            require(overlay.check(trees[l]["hol"], variant),
                    "image %s does not hold the %s sources" % (l, side))
    plan = plan_runs(args.kinds, sides, args.pairs)
    records, started = [], time.time()
    with a.serial_lock(repo) as fds:
        loading.check_seals(seals)
        tree_hash = pr.tree_outside_performance(
            HERE.parents[3], harness["head"])
        any_tree = next(iter(trees.values()))
        controls = am.controls_receipt(
            args.controls_receipt, lineage["runtime"], tree_hash,
            any_tree["libraries"], lineage["native_configuration"])
        args.work.mkdir(parents=True, exist_ok=True)
        try:
            for position, (kind, image, variant, pair) in enumerate(plan, 1):
                tree = trees[image]
                if variant is not None:
                    overlay.apply(tree["hol"], variant)
                receipt = loading.execute(
                    command(tree["hol"], kind, CLIENT), args.work,
                    process_env(env, tree["hol"], lib, shim, args.tmpdir,
                                kind), args.timeout, fds)
                require(receipt["exit"] == 0 and not receipt["timed_out"],
                        "client failed: %s %s %s\n%s" % (
                            kind, image, variant, receipt["stdout"][-600:]))
                rec = parse_process(receipt["stdout"], kind, tree["hol"],
                                    lib, aliases)
                rec.update(image=image, variant=variant, pair=pair,
                           position=position,
                           side="base" if image in sides["base"]
                           else "candidate",
                           wall=round(receipt["process_wall"], 2),
                           stdout_sha256=receipt["stdout_sha256"])
                if pair:
                    rec["files"] = None
                records.append(rec)
                print(position, len(plan), kind, image, variant, pair,
                      rec["brackets"][0]["end"][3], flush=True)
        finally:
            for side, variant in zip(("base", "candidate"), VARIANTS):
                for l in sides[side]:
                    overlay.apply(trees[l]["hol"], variant)
        loading.check_seals(seals)
    header = dict(
        schema=SCHEMA, sides=sides, null=bool(args.null), pairs=args.pairs,
        kinds=list(args.kinds), identity={s: list(i) for s, i in
                                          ident.items()},
        hol={l: t["hol"] for l, t in trees.items()},
        trees={l: dict(rev=t["rev"], head=t["head"], tree=t["hol_tree"],
                       patch=t["hol_patch"], products=t["hol_products"],
                       deterministic=t.get("hol_build_deterministic"),
                       jobs=t.get("hol_build_jobs"),
                       determinism_diff=t.get("hol_determinism_diff", ""))
               for l, t in trees.items()},
        holdir_length=len(any_tree["hol"]),
        tmpdir=str(args.tmpdir), tmpdir_length=len(str(args.tmpdir)),
        lineage_sha256=sha_file(root / "lineage.json"),
        library=str(lib), runtime=lineage["runtime"],
        shim=lineage["shim_seal"], controls=controls, harness=harness,
        declared_text=declared_text,
        declared_sha256=hashlib.sha256(declared_text.encode()).hexdigest(),
        sources=overlay.blobs, overlay=overlay.paths(),
        clock_mentions=overlay.clock,
        record_sha256=record_sha,
        environment=dict(env), seconds=round(time.time() - started, 1))
    report = analyse(records, sides, declared, overlay.blobs, args.pairs,
                     args.null, record_sha)
    write_archive(out, records, header, report)
    print("DECISION", report["decision"], *report["reasons"],
          *report["blockers"], sep="\n  ")
    return 0 if report["decision"] in ("pass", "attributed") else 1


def write_archive(out, records, header, report):
    """records.json.gz, header.json, decisions.json, RESULTS.md and a
    receipt with the sha256 of each."""
    import allocation_matrix as am
    (out / "records.json.gz").write_bytes(am.compact(records))
    (out / "header.json").write_text(json.dumps(header, indent=1))
    (out / "decisions.json").write_text(json.dumps(report, indent=1))
    (out / "RESULTS.md").write_text(render(report, header))
    names = ("records.json.gz", "header.json", "decisions.json", "RESULTS.md")
    (out / "receipt.json").write_text(json.dumps(
        {n: sha_file(out / n) for n in names}, indent=1))


def render(report, header):
    """RESULTS.md: the decision and the figures behind it."""
    lines = ["# TASK31 ordinary-startup allocation gate", "",
             "Decision: **%s**" % report["decision"], "",
             "Absolute source-kind figures are under the reset of the "
             "image's stored CPU timer readings (Globals.hol_clock) and "
             "are not client figures; only deltas and the hol-* kinds "
             "are.", ""]
    lines += ["- " + r for r in report["reasons"]]
    lines += ["- blocker: " + b for b in report["blockers"]]
    lines += ["", "Images: " + json.dumps(report["images"], sort_keys=True),
              "", "R1 (identical on every image):", ""]
    for kind, table in sorted(report["R1"].items()):
        for name, row in table.items():
            lines.append("- %s %s: %s" % (kind, name, json.dumps(
                row, sort_keys=True)))
    lines += ["", "R2 (candidate minus baseline sources, per image):", ""]
    for kind, per in sorted(report["R2"].items()):
        for image, got in sorted(per.items()):
            lines.append("- %s %s: load %s, loader gap %s" % (
                kind, image, json.dumps(got["load"], sort_keys=True),
                json.dumps(got["gap"], sort_keys=True)))
            for name, row in sorted(got["files"].items()):
                lines.append("    %s %s" % (name, json.dumps(
                    row, sort_keys=True)))
    lines += ["", "R3 noise files (difference to the first image):", ""]
    for name, per in sorted(report["noise"].items()):
        for image, row in sorted(per.items()):
            lines.append("- %s %s: %s" % (name, image, json.dumps(
                row, sort_keys=True)))
    if report["declared_zero"]:
        lines += ["", "Declared entries that measure 0: " + ", ".join(
            report["declared_zero"])]
    lines += ["", "Live words after full collections at the end of the load "
              "kinds (measured, not a decision input; words = (sizeHeap - "
              "sizeHeapFreeLastFullGC - sizeAllocation) / 8, the sizes "
              "being bytes; live words are data of the local heap and "
              "exclude compiled code, which is in code spaces; comparable "
              "is false where the allocation-area sizes differ):", ""]
    for kind, per in sorted(report.get("live", {}).items()):
        for image, row in sorted(per.items()):
            lines.append("- %s %s: %s" % (kind, image, json.dumps(
                row, sort_keys=True)))
    return "\n".join(lines) + "\n"


def require_no_clock(overlay):
    """Refuse files under test that mention the image's CPU timer."""
    require(not overlay.clock,
            "files under test mention the image's CPU timer (the source "
            "kinds reset its readings): " + ", ".join(overlay.clock))


def replay(args):
    """Recompute every decision from the archive alone."""
    out = args.output
    receipt = a.load(out / "receipt.json")
    for name, digest in receipt.items():
        require(sha_file(out / name) == digest, "receipt differs: " + name)
    records = a.load(out / "records.json.gz")
    header = a.load(out / "header.json")
    require(header.get("schema") == SCHEMA,
            "archive schema %r is not %r: re-run the gate" % (
                header.get("schema"), SCHEMA))
    require(hashlib.sha256(header["declared_text"].encode()).hexdigest() ==
            header["declared_sha256"], "declaration differs from its seal")
    sides = header["sides"]
    require(len(set(sides["base"] + sides["candidate"])) ==
            len(sides["base"]) + len(sides["candidate"]), "images")
    require(len({len(h) for h in header["hol"].values()}) == 1 and
            len(next(iter(header["hol"].values()))) ==
            header["holdir_length"], "HOLDIR lengths")
    report = analyse(records, sides, parse_declared(header["declared_text"]),
                     header["sources"], header["pairs"], header["null"],
                     header["record_sha256"])
    require(header["clock_mentions"] == [],
            "files under test mention the image's CPU timer (the source "
            "kinds reset its readings): " + ", ".join(
                header["clock_mentions"]))
    if header["record_sha256"]:
        require(args.record is not None,
                "the archive is sealed to a record: pass --record")
    if args.record:
        require(sha_file(args.record) == header["record_sha256"],
                "the record differs from its seal")
    stored = a.load(out / "decisions.json")
    require(json.loads(json.dumps(report)) == stored,
            "stored decisions differ from a replay")
    require((out / "RESULTS.md").read_text() == render(report, header),
            "RESULTS.md differs from a replay")
    print("replayed", report["decision"])
    return 0

# ----------------------------------------------------- TASK29B cell replica

def install_cell_fixtures(repo, rev, dst, am):
    """The fixtures of a cell directory: those of this checkout, or with
    `rev` those that revision's own runner installs.  Both the paired
    runner files and the matrix fixtures.  For a past revision the
    revision's `run_paired.py` is loaded from a temporary tree (beside its
    `paired/` files and its signature probe, in the job directory above
    `dst`, whose path length matters) and its own `install_fixtures` is
    called: a replay of that revision's installation, not a
    reconstruction.  The matrix fixtures are that revision's blobs."""
    import importlib.util
    import shutil
    import tempfile
    if rev is None:
        rp.install_fixtures(dst)
        for fx in am.FIXTURES:
            target = "Performance.sml" if fx == am.FIXTURES[0] else fx
            shutil.copyfile(am.HERE / fx, dst / target)
        return

    def blob(path):
        return subprocess.run(["git", "show", rev + ":" + path], cwd=repo,
                              check=True, capture_output=True).stdout

    compat = "src/simp/tests/compatibility/"
    perf = "src/simp/tests/performance/"
    with tempfile.TemporaryDirectory(prefix="fixtures-",
                                     dir=dst.parent) as raw:
        top = Path(raw)
        (top / "compatibility/paired").mkdir(parents=True)
        (top / "performance/review-20261021").mkdir(parents=True)
        for path in a.git(repo, "ls-tree", "--name-only", rev,
                          compat + "paired/").splitlines():
            name = Path(path).name
            if name.endswith(".sml") or name == "Holmakefile":
                (top / "compatibility/paired" / name).write_bytes(
                    blob(path))
        (top / "performance/review-20261021/abicheck.sml").write_bytes(
            blob(perf + "review-20261021/abicheck.sml"))
        runner = top / "compatibility/run_paired.py"
        runner.write_bytes(blob(compat + "run_paired.py"))
        spec = importlib.util.spec_from_file_location(
            "run_paired_" + rev[:12], runner)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        module.install_fixtures(dst)
    for fx in am.FIXTURES:
        target = "Performance.sml" if fx == am.FIXTURES[0] else fx
        (dst / target).write_bytes(blob(perf + fx))


def sized_tmpdir(base, length):
    """A directory whose path has exactly `length` characters: `base`
    padded with "x" (created if missing); the path of `base` itself when
    `length` is None.  The base is resolved first (as the private
    directories are), so the length is that of the real path."""
    base = Path(base).resolve()
    if length is None:
        return base
    text = str(base)
    require(len(text) <= length,
            "tmpdir %s is longer than %d characters" % (text, length))
    path = Path(text + "x" * (length - len(text)))
    path.mkdir(parents=True, exist_ok=True)
    return path


def cell_startup(args):
    """The TASK29B startup bracket of `base` and `candidate` revisions as
    the matrix measures it (sources compiled by `use` in a fresh process
    over one hol.state0, equal-length selection directories), repeated
    under chosen path lengths: the delta and the absolute words as a
    function of TMPDIR, HOLDIR, runtime and shim path lengths. Prints one
    JSON line per measurement."""
    import allocation_matrix as am
    import shutil
    import tempfile
    pr.use_fixed_path()
    args.tmpdir = sized_tmpdir(args.tmpdir, args.tmpdir_length)
    repo = args.repo.resolve(strict=True)
    lineage = a.load(args.toolchain.resolve(strict=True) / "lineage.json")
    hol = Path(lineage["trees"][args.tree]["hol"])
    lib = Path(lineage["library"])
    env = tool_env(args.tmpdir)
    env["HOLDIR"] = str(hol)
    lib_dir = Path(args.lib_alias) if args.lib_alias else lib.parent
    shim = Path(args.shim_copy) if args.shim_copy else Path(lineage["shim"])
    if args.shim_copy:
        shutil.copyfile(lineage["shim"], shim)
    run_env = dict(env, LD_LIBRARY_PATH=str(lib_dir))
    revs = {"base": args.baseline, "cand": args.candidate}
    out = []
    with a.serial_lock(repo) as fds:
        scratch = Path(tempfile.mkdtemp(prefix="task29b-",
                                        dir=args.tmpdir)).resolve()
        job = scratch / "j00"
        job.mkdir()
        dirs = {}
        try:
            for side, name in (("base", "sel-b0"), ("cand", "sel-c0")):
                d = job / name
                d.mkdir()
                rp.extract(repo, revs[side], d)
                install_cell_fixtures(repo, args.fixtures_rev, d, am)
                with (d / "Holmakefile").open("a") as f:
                    f.write("\npaired.exe: Performance.uo\n")
                receipt = loading.execute(
                    [str(hol / "bin/Holmake"), "--no-project", "--no-cache",
                     "--no_prereqs", "--holstate=" +
                     str(hol / "bin/hol.state0"), "-C", str(d), "-j1",
                     "paired.exe"], job, env, args.timeout, fds)
                require(receipt["exit"] == 0, "Holmake failed: " +
                        receipt["stdout"][-500:])
                dirs[side] = (d, name)
            for rep in range(args.n):
                for side in (("base", "cand") if rep % 2 == 0
                             else ("cand", "base")):
                    d, name = dirs[side]
                    penv = dict(run_env, PAIR_SELECTION=name,
                                PAIR_FIXTURE="performance",
                                PAIR_CONTROL="none", PAIR_PRIVATE=str(d),
                                PAIR_TARGET="Performance",
                                PERF_CASE="exclude_empty", PERF_SIZE="1000",
                                ALLOC_STEADY="16", ALLOC_REPEATS="4",
                                TASK29_ALLOC_SHIM=str(shim))
                    r = loading.execute([str(d / "paired.exe")], d, penv,
                                        args.timeout, fds)
                    require(r["exit"] == 0, "cell failed: " +
                            r["stdout"][-500:])
                    start = [l.split("\t") for l in r["stdout"].splitlines()
                             if l.startswith("@@PAIR\t")]
                    row = [f for f in start if len(f) > 4 and
                           f[2] == "observation" and f[3] == "alloc.startup"]
                    require(len(row) == 1, "no startup observation")
                    words = [int(x) for x in row[0][4].split(";")[1]
                             .split(",")]
                    out.append(dict(side=side, rep=rep, startup=words[3:]))
        finally:
            shutil.rmtree(scratch, ignore_errors=True)
    base = {tuple(o["startup"]) for o in out if o["side"] == "base"}
    cand = {tuple(o["startup"]) for o in out if o["side"] == "cand"}
    require(len(base) == 1 and len(cand) == 1, "nondeterministic startup")
    b, c = base.pop(), cand.pop()
    result = dict(
        tree=args.tree, fixtures=args.fixtures_rev or "current",
        lengths=dict(tmpdir=len(str(args.tmpdir)), holdir=len(str(hol)),
                     library=len(str(lib_dir)) +
                     len("/libpolyml.so.16.0.0"), shim=len(str(shim)),
                     private=len(str(dirs["cand"][0]))),
        base=list(b), cand=list(c), delta=[y - x for x, y in zip(b, c)],
        revs=revs, runs=len(out))
    print(json.dumps(result))
    return 0


def main(argv=None):
    pr.use_fixed_path()
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    b = sub.add_parser("build")
    b.add_argument("--toolchain", type=Path, required=True)
    b.add_argument("--repo", type=Path, default=HERE.parents[3])
    b.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    b.add_argument("--tmpdir", type=Path, required=True)
    b.add_argument("--reuse", type=Path, default=None,
                   help="existing toolchain: build only the trees")
    b.add_argument("--timeout", type=int, default=3600)
    b.add_argument("--tree", action="append", default=[],
                   help="label=rev[+mktool]; one clean build each")
    m = sub.add_parser("gate")
    m.add_argument("--toolchain", type=Path, required=True)
    m.add_argument("--repo", type=Path, default=HERE.parents[3])
    m.add_argument("--output", type=Path, required=True)
    m.add_argument("--work", type=Path, required=True)
    m.add_argument("--tmpdir", type=Path, required=True)
    m.add_argument("--controls-receipt", type=Path, required=True)
    m.add_argument("--base", nargs="+", required=True,
                   help="labels of the independent baseline images")
    m.add_argument("--candidate", nargs="+", required=True,
                   help="labels of the independent candidate images")
    m.add_argument("--record", type=Path, default=None,
                   help="the not-client-visible record (sealed by sha256)")
    m.add_argument("--null", action="store_true",
                   help="baseline against baseline (null control)")
    m.add_argument("--pairs", type=int, default=PAIRS)
    m.add_argument("--kinds", nargs="+", default=list(KINDS),
                   choices=list(KINDS))
    m.add_argument("--timeout", type=int, default=1800)
    c = sub.add_parser("cell")
    c.add_argument("--toolchain", type=Path, required=True)
    c.add_argument("--tree", required=True, help="label of the HOL tree")
    c.add_argument("--repo", type=Path, default=HERE.parents[3])
    c.add_argument("--tmpdir", type=Path, required=True)
    c.add_argument("--tmpdir-length", type=int, default=None,
                   help="pad --tmpdir with x to exactly this many "
                   "characters (the private directories live under it)")
    c.add_argument("--baseline", default=a.BASE)
    c.add_argument("--candidate", required=True)
    c.add_argument("--lib-alias", default=None,
                   help="symlink to the runtime directory (path length)")
    c.add_argument("--shim-copy", default=None,
                   help="copy of the shim at this path (path length)")
    c.add_argument("--fixtures-rev", default=None,
                   help="take the paired and matrix fixtures from this "
                   "revision (those of a past run), not from this checkout")
    c.add_argument("-n", type=int, default=2)
    c.add_argument("--timeout", type=int, default=3600)
    r = sub.add_parser("replay")
    r.add_argument("--output", type=Path, required=True)
    r.add_argument("--record", type=Path, default=None)
    args = parser.parse_args(argv)
    return {"build": build, "gate": gate, "replay": replay,
            "cell": cell_startup}[args.action](args)


if __name__ == "__main__":
    sys.exit(main())
