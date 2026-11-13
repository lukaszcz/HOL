#!/usr/bin/env python3
"""TASK37 D7: recorded, attributed build timing (not a gate).

How long do the routine and the full regression builds take on the
candidate against the base? Two commands, each timed as one process tree:

  routine   bin/build -t --seq=tools/sequences/upto-parallel   3 pairs
  full      bin/build -t -F                                    2 pairs

  run        builds the pairs. Every side of a pair is a fresh
             `git clone --shared --no-checkout` of --repo (the main
             worktree: never a clone that itself borrows objects), detached
             at the pin, configured with `poly < tools/smart-configure.sml`,
             built once, and deleted after its pair. Pairs alternate AB, BA,
             AB (A = base, B = candidate). One build at a time, one pair at
             a time, so this run holds at most two trees in /dev/shm. A build
             waits (up to --wait-s) while what /dev/shm holds (the other
             streams' trees included) plus --reserve-gb (default 5, one
             more tree's growth) would exceed --shm-limit-gb (default 20),
             and is refused after that. Per build the receipt records
             wall seconds, CPU seconds of the whole process tree
             (wait4 rusage: user, system) and the exit status, with the host
             load averages at the start and the end and the nice value.
             Builds start in a new session (setsid) with SIGINT, SIGHUP,
             SIGTERM and SIGPIPE at their default dispositions, whatever the
             runner inherited (a runner started under nohup would otherwise
             hand the build ignored signals).
  attribute  joins the per-directory `Building directory D [time]` lines of
             the base and candidate logs of a receipt and reports the
             per-directory durations and deltas (median over the runs of a
             command), the directories that exist only on the candidate (or
             only on the base) and the totals.

Not a gate: nothing here passes or fails the candidate. The numbers are
recorded and attributed (the extra Ext modules and the selftest targets
come to the directories listed by `attribute`); a nonzero build exit is
recorded and the run goes on. Wall time on a shared host is noisy: the load
averages are in the receipt so that a reader can judge.

Receipt (`task37-builds-v1`, written to OUT/receipt.json after every pair;
the build logs are OUT/logs/<kind>-p<pair>-<label>.log):
  {schema, host{uname, cpus, nice}, pins{base, cand, repo, repo_head},
   limits{shm_gb, reserve_gb}, plan[{kind, pairs, argv}],
   runs[{kind, pair, order, position, side, label, pin, tree, steps[{name,
   argv, exit, wall_s, user_s, sys_s, start_utc, end_utc, load_start,
   load_end, log}], build{...as a step...}, tree_kb, shm_used_bytes,
   deleted}], complete}

TASK37 recipe (D7 stream, own clone, its own /dev/shm root, nice 19; the
routine and full pairs may run back to back):
  nice -n 19 python3 -B task37_builds.py run --repo MAIN --base cccaa27d70
      --cand FINAL --root /dev/shm/t37-d7 --out EVIDENCE/d7
  python3 -B task37_builds.py attribute EVIDENCE/d7/receipt.json
      --out EVIDENCE/d7/attribution.json
Expected /dev/shm peak: two trees of the larger command (about 2 x 3-5 GB
for the full build, 2 x 1 GB for the routine one; the receipt records the
measured size of every tree and /dev/shm usage).
"""
import argparse
import datetime
import json
import os
from pathlib import Path
import re
import shutil
import signal
import statistics
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "compatibility"))
import acceptance as a

SCHEMA = "task37-builds-v1"
BASE = a.BASE
SHM = Path("/dev/shm")
SHM_LIMIT_GB = 20
RESERVE_GB = 5
WAIT_S = 7200   # how long a build waits for room before it is refused
POLL_S = 60
GB = 10 ** 9
LABELS = ("base", "cand")
CONFIGURE = ["poly"]
CONFIGURE_INPUT = "tools/smart-configure.sml"
KINDS = {
    "routine": dict(argv=["bin/build", "-t",
                          "--seq=tools/sequences/upto-parallel"], pairs=3),
    "full": dict(argv=["bin/build", "-t", "-F"], pairs=2),
}
DEFAULT_SIGNALS = (signal.SIGINT, signal.SIGHUP, signal.SIGTERM,
                   signal.SIGPIPE)
ANSI = re.compile(r"\x1b(?:\[[0-9;?]*[ -/]*[@-~]|.)")
BUILDING = re.compile(
    r"Building directory (\S+)\s+\[(\d+) (\w+), (\d+):(\d+):(\d+)\]")
MONTHS = {m: i + 1 for i, m in enumerate(
    "Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec".split())}


class Refusal(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise Refusal(message)


# ------------------------------------------------------------ plan

def build_argv(kind):
    require(kind in KINDS, "unknown build kind %r (one of %s)" % (
        kind, ", ".join(KINDS)))
    return list(KINDS[kind]["argv"])


def pair_order(pair):
    """AB for an even pair, BA for an odd one (A = base, B = candidate)."""
    return ("base", "cand") if pair % 2 == 0 else ("cand", "base")


def tree_path(root, kind, pair, label):
    return Path(root) / ("%s-p%d-%s" % (kind, pair, label))


def step_commands(repo, tree, pin, kind):
    """[(name, argv, cwd, stdin file or None)] of one side: the clone, the
    detached checkout, the configure and the timed build."""
    return [
        ("clone", ["git", "clone", "--shared", "--no-checkout", "-q",
                   str(repo), str(tree)], None, None),
        ("checkout", ["git", "-C", str(tree), "checkout", "-q", "--detach",
                      pin], None, None),
        ("configure", list(CONFIGURE), tree,
         str(Path(tree) / CONFIGURE_INPUT)),
        ("build", build_argv(kind), tree, None)]


def plan(kinds, pairs=None):
    """[{kind, pairs, argv}] of the kinds to run, in order."""
    pairs = pairs or {}
    out = []
    for kind in kinds:
        n = pairs.get(kind, KINDS[kind]["pairs"])
        require(isinstance(n, int) and n >= 1, "pairs of %s: %r" % (
            kind, n))
        out.append(dict(kind=kind, pairs=n, argv=build_argv(kind)))
    return out


# ------------------------------------------------------------ host

def restore_default_signals():
    """The child's preexec: default dispositions, so that an ignored
    SIGINT or SIGHUP of the runner (nohup, a background shell) is not
    inherited by the build."""
    for number in DEFAULT_SIGNALS:
        signal.signal(number, signal.SIG_DFL)


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ")


def loadavg():
    try:
        return [round(x, 2) for x in os.getloadavg()]
    except OSError:
        return None


def shm_used(path=SHM):
    return shutil.disk_usage(path).used


def tree_kb(path):
    """du -sk of a tree (None when it cannot be read)."""
    done = subprocess.run(["du", "-sk", str(path)], stdin=subprocess.DEVNULL,
                          stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    try:
        return int(done.stdout.split()[0])
    except (IndexError, ValueError):
        return None


def real_runner(argv, cwd, env, log, stdin_path=None):
    """Run argv in a new session, default signals, stdout and stderr to
    `log`; wait4 gives the exit and the CPU of the whole process tree."""
    started, t0 = utc_now(), time.monotonic()
    load = loadavg()
    stdin = open(stdin_path, "rb") if stdin_path else subprocess.DEVNULL
    try:
        with open(log, "wb") as out:
            proc = subprocess.Popen(
                argv, cwd=cwd, env=env, stdin=stdin, stdout=out,
                stderr=subprocess.STDOUT, start_new_session=True,
                preexec_fn=restore_default_signals)
            try:
                _, status, usage = os.wait4(proc.pid, 0)
            except BaseException:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except OSError:
                    pass
                os.waitpid(proc.pid, 0)
                raise
            proc.returncode = os.waitstatus_to_exitcode(status)
    finally:
        if stdin_path:
            stdin.close()
    return dict(exit=proc.returncode, wall_s=round(time.monotonic() - t0, 3),
                user_s=round(usage.ru_utime, 3),
                sys_s=round(usage.ru_stime, 3), start_utc=started,
                end_utc=utc_now(), load_start=load, load_end=loadavg())


# ------------------------------------------------------------ the run

def check_repo(repo, pins):
    """The repository is the main worktree's store: it borrows no objects
    (a clone of a clone dies with its source), and holds the pins."""
    repo = Path(repo).resolve(strict=True)
    common = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "--git-common-dir"],
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, check=True
    ).stdout.decode().strip()
    common = (repo / common).resolve()
    require(not (common / "objects/info/alternates").exists(),
            "%s borrows objects (a --shared clone): clone only from the "
            "main worktree" % repo)
    full = {}
    for name, pin in pins.items():
        done = subprocess.run(
            ["git", "-C", str(repo), "rev-parse", "--verify",
             pin + "^{commit}"], stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        require(done.returncode == 0, "cannot resolve %s in %s" % (pin, repo))
        full[name] = done.stdout.decode().strip()
        a.exact_pin(full[name])
    head = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"],
        stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
        check=True).stdout.decode().strip()
    return repo, full, head


def new_receipt(repo, head, pins, limits, plans):
    uname = os.uname()
    return {"schema": SCHEMA,
            "host": dict(uname=" ".join(uname[:3] + uname[4:]),
                         cpus=os.cpu_count(), nice=os.nice(0),
                         load_start=loadavg()),
            "pins": dict(base=pins["base"], cand=pins["cand"],
                         repo=str(repo), repo_head=head),
            "limits": limits, "plan": plans, "runs": [], "complete": False}


def write_receipt(out, receipt):
    path = Path(out) / "receipt.json"
    tmp = Path(str(path) + ".tmp")
    tmp.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)
    return path


def check_room(limit_gb, reserve_gb, used=None):
    """Refuse a build that could take /dev/shm over the limit: what is used
    now plus the reserve (the most one more tree is expected to grow by)."""
    used = shm_used() if used is None else used
    require(used + reserve_gb * GB <= limit_gb * GB,
            "/dev/shm holds %.1f GB; with the %d GB reserve that exceeds "
            "the %d GB limit" % (used / GB, reserve_gb, limit_gb))
    return used


def await_room(limit_gb, reserve_gb, wait_s=None, poll_s=None,
               sleep=time.sleep, used=None):
    """`check_room`, retried every `poll_s` for up to `wait_s` seconds: other
    streams (the startup gate, loading) hold /dev/shm for a while. Returns
    (bytes in use when the build may start, seconds waited)."""
    wait_s = WAIT_S if wait_s is None else wait_s
    poll_s = POLL_S if poll_s is None else poll_s
    used = used or (lambda: shm_used())
    waited = 0
    while True:
        try:
            return check_room(limit_gb, reserve_gb, used()), waited
        except Refusal:
            if waited >= wait_s:
                raise
            sleep(poll_s)
            waited += poll_s


def run_side(receipt, out, repo, root, kind, pair, position, label, pin,
             runner, limits):
    """One side: clone, checkout, configure, build (every step recorded);
    the tree is left for the caller to delete after the pair."""
    tree = tree_path(root, kind, pair, label)
    require(not os.path.lexists(tree), "tree exists: %s" % tree)
    logs = Path(out) / "logs"
    logs.mkdir(exist_ok=True)
    env = dict(os.environ, TMPDIR=str(Path(root) / "tmp"))
    env.pop("HOLDIR", None)
    run = dict(kind=kind, pair=pair, order="".join(
        "AB"[LABELS.index(x)] for x in pair_order(pair)),
        position=position, side="AB"[LABELS.index(label)], label=label,
        pin=pin, tree=str(tree), steps=[], build=None, tree_kb=None,
        shm_used_bytes=None, deleted=False)
    receipt["runs"].append(run)
    for name, argv, cwd, stdin in step_commands(repo, tree, pin, kind):
        used = waited = None
        if name == "build":
            used, waited = await_room(
                limits["shm_gb"], limits["reserve_gb"],
                limits.get("wait_s"))
        log = logs / ("%s-p%d-%s.log" % (kind, pair, label)
                      if name == "build" else
                      "%s-p%d-%s.%s.log" % (kind, pair, label, name))
        step = dict(runner(argv, cwd or str(root), env, str(log), stdin),
                    name=name, argv=argv, log=str(log.relative_to(out)))
        if name == "build":
            step["shm_used_before"] = used
            step["waited_for_room_s"] = waited
            run["build"] = step
        run["steps"].append(step)
        if step["exit"] != 0 and name != "build":
            break   # a tree that did not clone, check out or configure
    run["tree_kb"] = tree_kb(tree) if tree.exists() else None
    run["shm_used_bytes"] = shm_used()


def run_all(repo, base, cand, root, out, kinds=tuple(KINDS), pairs=None,
            limits=None, runner=real_runner, keep=False):
    """The whole D7 run; returns the receipt (also OUT/receipt.json)."""
    limits = limits or dict(shm_gb=SHM_LIMIT_GB, reserve_gb=RESERVE_GB)
    repo, full, head = check_repo(repo, dict(base=base, cand=cand))
    plans = plan(kinds, pairs)
    root, out = Path(root), Path(out)
    require(not root.exists() or not any(root.iterdir()),
            "%s is not empty" % root)
    out.mkdir(parents=True, exist_ok=False)
    root.mkdir(parents=True, exist_ok=True)
    (root / "tmp").mkdir(exist_ok=True)
    receipt = new_receipt(repo, head, full, limits, plans)
    write_receipt(out, receipt)
    live = []

    def cleanup():
        for tree in live:
            if not keep and tree.exists():
                shutil.rmtree(tree, ignore_errors=True)
        live.clear()
    try:
        for entry in plans:
            for pair in range(entry["pairs"]):
                for position, label in enumerate(pair_order(pair)):
                    live.append(tree_path(root, entry["kind"], pair, label))
                    run_side(receipt, out, repo, root, entry["kind"], pair,
                             position, label, full[label], runner, limits)
                    write_receipt(out, receipt)
                if not keep:
                    cleanup()
                    for r in receipt["runs"]:
                        if r["kind"] == entry["kind"] and \
                                r["pair"] == pair:
                            r["deleted"] = True
                write_receipt(out, receipt)
        receipt["complete"] = True
    finally:
        cleanup()
        receipt["host"]["load_end"] = loadavg()
        write_receipt(out, receipt)
        shutil.rmtree(root / "tmp", ignore_errors=True)
        if not keep:
            try:
                root.rmdir()
            except OSError:
                pass
    return receipt


def validate_receipt(receipt):
    """The problems of a receipt (a list of texts; empty when sound)."""
    bad = []
    if receipt.get("schema") != SCHEMA:
        return ["schema is not " + SCHEMA]
    for key in ("host", "pins", "limits", "plan", "runs", "complete"):
        if key not in receipt:
            bad.append("lacks " + key)
    if bad:
        return bad
    for k in ("base", "cand", "repo", "repo_head"):
        if k not in receipt["pins"]:
            bad.append("pins lack " + k)
    wanted = {e["kind"]: e["pairs"] for e in receipt["plan"]}
    seen = {}
    for r in receipt["runs"]:
        for k in ("kind", "pair", "order", "label", "pin", "steps",
                  "build", "tree_kb", "deleted"):
            if k not in r:
                bad.append("a run lacks " + k)
        if r.get("build") is not None:
            for k in ("exit", "wall_s", "user_s", "sys_s", "load_start",
                      "load_end", "log"):
                if k not in r["build"]:
                    bad.append("%s p%s %s: build lacks %s" % (
                        r.get("kind"), r.get("pair"), r.get("label"), k))
        seen.setdefault((r.get("kind"), r.get("pair")), []).append(
            r.get("label"))
    if receipt["complete"]:
        for kind, n in wanted.items():
            for pair in range(n):
                if seen.get((kind, pair)) != list(pair_order(pair)):
                    bad.append("%s pair %d is not %s" % (
                        kind, pair, "/".join(pair_order(pair))))
    return bad


# ------------------------------------------------------------ attribution

def building_times(text):
    """[(directory, seconds since the first line)] of the `Building
    directory D [DD Mon, HH:MM:SS]` lines of a build log, in order, day
    wraps (a build across midnight) handled; the year is not printed and
    is not needed."""
    found, day, last = [], 0, None
    for line in ANSI.sub("", text).splitlines():
        m = BUILDING.search(line)
        if not m:
            continue
        d, dd, mon, hh, mm, ss = m.groups()
        stamp = (MONTHS.get(mon, 0), int(dd), int(hh), int(mm), int(ss))
        secs = int(hh) * 3600 + int(mm) * 60 + int(ss)
        day_key = (stamp[0], stamp[1])
        if last is not None and day_key != last[0]:
            day += 1
        found.append((d, day * 86400 + secs))
        last = (day_key, secs)
    if found:
        t0 = found[0][1]
        found = [(d, t - t0) for d, t in found]
    return found


def durations(times, wall):
    """{directory: seconds}: the time to the next directory's line; the
    last directory runs to the end of the build (`wall` seconds after its
    first line, an upper bound at one-second resolution). A directory
    built twice sums."""
    out = {}
    for i, (d, t) in enumerate(times):
        end = times[i + 1][1] if i + 1 < len(times) else max(wall, t)
        out[d] = out.get(d, 0) + (end - t)
    return out


def attribute(receipt, read=None, top=None):
    """The per-directory attribution of a receipt: per kind, per
    directory the median duration on each side over the runs of the kind,
    the delta, the directories on one side only and the totals."""
    bad = validate_receipt(receipt)
    require(not bad, "malformed receipt: " + "; ".join(bad))
    read = read or (lambda p: Path(p).read_text(errors="replace"))
    out = {}
    for kind in sorted({r["kind"] for r in receipt["runs"]}):
        per = {l: [] for l in LABELS}
        walls = {l: [] for l in LABELS}
        exits = {l: [] for l in LABELS}
        for r in receipt["runs"]:
            b = r["build"]
            if r["kind"] != kind or b is None:
                continue
            times = building_times(read(b["log"]))
            per[r["label"]].append(durations(times, b["wall_s"]))
            walls[r["label"]].append(b["wall_s"])
            exits[r["label"]].append(b["exit"])
        dirs = {l: sorted({d for run in per[l] for d in run})
                for l in LABELS}
        med = {l: {d: statistics.median(run[d] for run in per[l]
                                        if d in run) for d in dirs[l]}
               for l in LABELS if per[l]}
        rows = []
        for d in sorted(set(dirs["base"]) & set(dirs["cand"])):
            rows.append(dict(directory=d, base_s=med["base"][d],
                             cand_s=med["cand"][d],
                             delta_s=med["cand"][d] - med["base"][d]))
        rows.sort(key=lambda r: -abs(r["delta_s"]))
        only = {l: sorted(
            ({"directory": d, "seconds": med[l][d]} for d in dirs[l]
             if d not in dirs[o]), key=lambda x: -x["seconds"])
            for l, o in (("cand", "base"), ("base", "cand")) if l in med}
        out[kind] = dict(
            runs={l: len(per[l]) for l in LABELS},
            exits=exits,
            wall_s={l: statistics.median(walls[l]) for l in LABELS
                    if walls[l]},
            common=rows[:top] if top else rows,
            common_delta_total_s=sum(r["delta_s"] for r in rows),
            only_cand=only.get("cand", []), only_base=only.get("base", []),
            only_cand_total_s=sum(x["seconds"] for x in only.get("cand", [])),
            resolution_s=1)
    return dict(schema=SCHEMA + "-attribution", pins=receipt["pins"],
                kinds=out)


def summary_text(attribution, top=15):
    lines = []
    for kind, k in attribution["kinds"].items():
        lines.append("%s: wall median %s; common directories' delta "
                     "%+.0f s; candidate-only directories %.0f s" % (
                         kind, k["wall_s"], k["common_delta_total_s"],
                         k["only_cand_total_s"]))
        for r in k["common"][:top]:
            lines.append("  %+6.0f s  %-40s base %6.0f  cand %6.0f" % (
                r["delta_s"], r["directory"], r["base_s"], r["cand_s"]))
        for x in k["only_cand"][:top]:
            lines.append("  cand-only %-40s %6.0f s" % (
                x["directory"], x["seconds"]))
    return "\n".join(lines)


# ------------------------------------------------------------ CLI

def parse_pairs(items):
    out = {}
    for item in items or ():
        kind, _, n = item.partition("=")
        require(kind in KINDS and n.isdigit(), "--pairs KIND=N: " + item)
        out[kind] = int(n)
    return out


def build_parser():
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="command", required=True)
    r = sub.add_parser("run")
    r.add_argument("--repo", type=Path, required=True,
                   help="the main worktree (not a --shared clone)")
    r.add_argument("--base", default=BASE)
    r.add_argument("--cand", required=True)
    r.add_argument("--root", type=Path, required=True,
                   help="the /dev/shm directory of the trees (this "
                   "stream's own)")
    r.add_argument("--out", type=Path, required=True,
                   help="evidence directory (receipt.json, logs/)")
    r.add_argument("--kinds", nargs="+", choices=sorted(KINDS),
                   default=list(KINDS))
    r.add_argument("--pairs", action="append", metavar="KIND=N")
    r.add_argument("--shm-limit-gb", type=int, default=SHM_LIMIT_GB)
    r.add_argument("--reserve-gb", type=int, default=RESERVE_GB)
    r.add_argument("--wait-s", type=int, default=WAIT_S,
                   help="how long a build waits for /dev/shm room")
    r.add_argument("--keep", action="store_true",
                   help="do not delete the trees (debugging)")
    r.add_argument("--dry-run", action="store_true",
                   help="print the plan and the commands, build nothing")
    t = sub.add_parser("attribute")
    t.add_argument("receipt", type=Path)
    t.add_argument("--out", type=Path, required=True)
    t.add_argument("--top", type=int)
    return p


def main(argv=None):
    args = build_parser().parse_args(argv)
    try:
        if args.command == "attribute":
            receipt = json.loads(args.receipt.read_text())
            base = args.receipt.parent
            data = attribute(receipt, lambda p: (base / p).read_text(
                errors="replace"), args.top)
            with args.out.open("x") as stream:
                stream.write(json.dumps(data, indent=2, sort_keys=True) +
                             "\n")
            print(summary_text(data))
            return 0
        pairs = parse_pairs(args.pairs)
        if args.dry_run:
            repo, full, _ = check_repo(args.repo, dict(
                base=args.base, cand=args.cand))
            for entry in plan(args.kinds, pairs):
                for pair in range(entry["pairs"]):
                    for pos, label in enumerate(pair_order(pair)):
                        tree = tree_path(args.root, entry["kind"], pair,
                                         label)
                        for name, cmd, cwd, stdin in step_commands(
                                repo, tree, full[label], entry["kind"]):
                            print(entry["kind"], pair, label, name,
                                  " ".join(cmd), "<" + stdin if stdin
                                  else "")
            return 0

        def stop(number, frame):
            raise KeyboardInterrupt("signal %d" % number)
        for number in (signal.SIGTERM, signal.SIGHUP):
            signal.signal(number, stop)
        try:
            receipt = run_all(
                args.repo, args.base, args.cand, args.root, args.out,
                args.kinds, pairs, dict(shm_gb=args.shm_limit_gb,
                                        reserve_gb=args.reserve_gb,
                                        wait_s=args.wait_s),
                keep=args.keep)
        except KeyboardInterrupt as stopped:
            print("INTERRUPTED (%s): trees deleted, the receipt so far "
                  "is kept, incomplete" % stopped, file=sys.stderr)
            return 4
        bad = validate_receipt(receipt)
        print("D7: %d builds recorded%s" % (
            len(receipt["runs"]), "; receipt problems: " + "; ".join(bad)
            if bad else ""))
        return 1 if bad else 0
    except (Refusal, ValueError, OSError,
            subprocess.CalledProcessError) as error:
        print("REFUSED: %s" % error, file=sys.stderr)
        return 3


if __name__ == "__main__":
    sys.exit(main())
