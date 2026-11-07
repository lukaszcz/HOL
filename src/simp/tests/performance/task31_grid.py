#!/usr/bin/env python3
"""TASK31 gates 1 and 3: source identity of every cell, and the timing of a
stratified sample.

Gate 3 is the TASK31 table for timing_grid.py (read that module, and the
"Shared timing grid and the TASK30 table" and "TASK31" sections of
PROTOCOL.md): the 28 cells of task31_cases.SAMPLE, the warmup schedule,
20 first-stage pairs of 5 samples, the policy and second stage of TASK30
(3% on inclusive CPU and wall, GC reported, no outlier removal, a second
stage whose pair counts come from the develop/develop control). Its counts
file task31_iterations.json is made by `pilot` and `predeclare` and
committed before any candidate observation. The table names no `sources`:
a candidate whose sources differ from the baseline's is exactly what the
sample measures (gate 1 says where they differ); the difference below
src/ is published by the table's `tree`.

Gate 1 is the `identity` command. For every cell of task31_cases.CASES
(feasible ones) one fresh process per side, through the real paired runner
(task31_snapshot.py, which runs it unchanged and records the private
trees), is compared by task31_identity.py: the closure of the sources the
process elaborated and their products, and the work row. A cell whose
closure or work differs is `different`: it is not passed by identity and
needs the timing sample. The 33 cells of task31_cases.INFEASIBLE are not
run (their setup alone exceeds the process timeout); their identity is
that of the size-0 cell of the same case, provided that the loaded closure
is the same in every measured cell of the grid, which the grid checks.

  prepare          configure, build and stamp the checkout   (takes the lock)
  identity         gate 1: --output DIR --candidate COMMIT   (authorized)
                   [--only CELL ...: a diagnostic, any checkout]
  identity-replay  re-derive every identity decision offline (--output DIR)
  pilot, predeclare, verify-counts, run, extend, replay: the timing table's

The exit status of `identity` and `identity-replay` is 0 when every cell is
identical, 1 when one is different, 2 when the grid is not conclusive (a
cell missing, an uncovered source, a closure that is not cell-independent).
A command that is refused prints one REFUSED line and exits 3.
"""
import argparse
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
import acceptance as a
import evidence_bundle as bundle
import matrix_schema as ms
import task31_cases as cases
import task31_identity as idt
import timing_grid as tg

PAIRS, SAMPLES = 20, 5
LAYOUT_SEED = "task31-layout-1"
SECONDS = 0.3
COUNTS = a.HERE / "task31_iterations.json"
# The files installed into the private directories of every process, as in
# task30_grid.py; a test installs the fixtures and compares.
PAIRED = a.HERE.parent / "compatibility" / "paired"
INSTALLED = (
    "MatrixPerformance.sml", "MatrixSupport.sml", "RuntimeMetrics.sml",
    "ClientPerformance.sml", "client_dependencies.py",
    "review-20261021/abicheck.sml", "../compatibility/run_paired.py",
    "matrix.json") + tuple(
    "../compatibility/paired/" + p.name for p in sorted(PAIRED.iterdir())
    if p.suffix == ".sml" or p.name == "Holmakefile")
SEALED = ("task31_cases.py", "task29_gate.py", "matrix_schema.py",
          "performance_schema.py", "evidence_bundle.py") + INSTALLED
TABLE = tg.Table(
    "task31", "TASK31", cases.CASES, __file__, COUNTS, seconds=SECONDS,
    fixed_seconds=True, schedule="warmup", headroom=1, pairs=PAIRS,
    samples=SAMPLES, seed=LAYOUT_SEED, baseline=a.BASE, engine=True,
    tree="src", sealed=SEALED, cells=cases.SAMPLE, require_seed=True,
    allocation="the separate gate of allocation_matrix.py --task task31; "
    "task31_dispose.py joins the two")
ENGINE = tg.Grid(TABLE, doc=__doc__)

# Gate 1 ------------------------------------------------------------------
SCHEMA = "task31-identity-v1"
DECISIONS = "task31-identity-decisions-v1"
# One pair, three samples, free ramp calibration of 0.1 s batches: nothing
# is timed for a decision; the process loads, runs the fixture and is audited.
ID_PAIRS, ID_SAMPLES, ID_SECONDS = 1, 3, 0.1
IDENTITY_CODE = ("task31_grid.py", "task31_identity.py",
                 "task31_snapshot.py", "task31_cases.py", "acceptance.py",
                 "audit_evidence.py", "performance_schema.py",
                 "evidence_bundle.py", "client_dependencies.py",
                 "../compatibility/run_paired.py")


def every():
    """Every cell of the task, in order: (case, size)."""
    return [(case, size) for case in cases.CASES for size in
            ms.SIZE_SETS[ms.EXPECTED_CASES[case]["sizes"]]]


def name_of(case, size):
    return "%s-%d" % (case, size)


def anchor(name):
    """The cell whose identity an infeasible cell takes: the size-0 cell of
    its case."""
    return name.rsplit("-", 1)[0] + "-0"


def code_seals():
    return {n: a.seal(a.HERE / n) for n in IDENTITY_CODE}


def source_blobs(repo, baseline, candidate):
    """The git blob of each file of cases.SOURCES at both commits (None where
    absent): published beside the closures, which are what decides."""
    return {p: dict(baseline=tg.git_blob(repo, baseline, p),
                    candidate=tg.git_blob(repo, candidate, p))
            for p in cases.SOURCES}


def derived(name, anchored, invariant):
    """The identity row of an infeasible cell: the anchor's, when the
    closure is the same in every measured cell."""
    cost = cases.INFEASIBLE_COST[name]
    row = dict(
        route="derived from %s: the loaded closure is the same in every "
        "measured cell" % anchor(name), work="not run: infeasible",
        survey=dict(zip(("op1000", "setup1000", "check1000", "op10000",
                         "setup10000", "check10000"), cost)),
        process_timeout=cases.PROCESS_TIMEOUT)
    if anchored is None:
        return dict(row, status="unresolved",
                    reason="the anchor %s was not measured" % anchor(name))
    if not invariant:
        return dict(row, status="unresolved",
                    reason="the closure is not the same in every cell")
    return dict(row, status=anchored["status"],
                closure_differences=anchored["closure_differences"],
                closure=anchored["closure"])


def decide(inventory):
    """The decisions of an identity inventory: one entry per expected cell
    and the checks of the grid as a whole. Pure; `identity-replay` calls it
    again on the inventory it has verified."""
    measured = {name_of(r["case"], r["size"]): r["row"]
                for r in inventory["runs"]}
    expected = inventory["expected"]
    sides = ("baseline", "candidate")
    digests = {s: sorted({row["closure"][s]["digest"]
                          for row in measured.values()}) for s in sides}
    invariant = all(len(d) <= 1 for d in digests.values())
    found = {}
    for name in expected:
        if name in measured:
            row = measured[name]
            found[name] = dict(
                status=row["status"], route="run",
                closure_differences=row["closure_differences"],
                work_differences=row["work_differences"],
                closure=row["closure"])
        elif name in cases.INFEASIBLE:
            found[name] = derived(name, measured.get(anchor(name)),
                                  invariant)
        else:
            found[name] = dict(status="unresolved", route="not run")
    elaborated = {s: sorted({p for row in measured.values()
                             for p in row["repo_files"][s]}) for s in sides}
    outside = set(cases.SOURCES)
    uncovered = sorted(set(elaborated["baseline"]) - outside)
    only_candidate = sorted(set(elaborated["candidate"]) - outside -
                            set(elaborated["baseline"]))
    blobs = inventory["sources"]
    counts = {k: sum(v["status"] == k for v in found.values())
              for k in ("identical", "different", "unresolved")}
    conclusive = (not counts["unresolved"] and not uncovered and invariant)
    status = ("identical" if conclusive and not counts["different"] else
              "different" if conclusive else "inconclusive")
    return dict(
        schema=DECISIONS, baseline=inventory["baseline"],
        candidate=inventory["candidate"],
        diagnostic=inventory["diagnostic"], status=status, counts=counts,
        closure_digests=digests, closure_invariant=invariant,
        uncovered=uncovered, candidate_only=only_candidate,
        unused_sources=sorted(outside - set(cases.HEAP) -
                              set(elaborated["baseline"]) -
                              set(elaborated["candidate"])),
        git_differing=sorted(p for p, b in blobs.items()
                             if b["baseline"] != b["candidate"]),
        cells=found)


def status_code(decisions):
    return {"identical": 0, "different": 1}.get(decisions["status"], 2)


def report(decisions):
    c = decisions["counts"]
    print("TASK31 identity: %s (%d identical, %d different, %d unresolved; "
          "candidate %s)" % (decisions["status"], c["identical"],
                             c["different"], c["unresolved"],
                             decisions["candidate"]))
    for name, found in sorted(decisions["cells"].items()):
        if found["status"] != "identical":
            files = sorted({d["name"].split(" ")[0] for d in
                            found.get("closure_differences", [])})
            print("  %s: %s %s" % (name, found["status"],
                                   ", ".join(files[:6])))
    for key in ("uncovered", "candidate_only"):
        if decisions[key]:
            print("  %s: %s" % (key, ", ".join(decisions[key])))
    if not decisions["closure_invariant"]:
        print("  the loaded closure differs between measured cells")


def run_one(command, log, fds, timeout):
    """Run the snapshot wrapper of one cell (a test replaces this)."""
    return a.run_logged(command, log, fds, timeout)


def measure(args, case, size, root, inventory, fds):
    name = name_of(case, size)
    print("IDENTITY %s" % name, flush=True)
    options = argparse.Namespace(
        repo=args.repo, baseline=args.baseline, pairs=ID_PAIRS,
        samples=ID_SAMPLES, batch_seconds=ID_SECONDS, timeout=args.timeout)
    with tempfile.TemporaryDirectory(prefix="task31-identity-") as scratch:
        folder = Path(scratch) / name
        command = a.matrix_command(options, case, size, args.candidate,
                                   folder)
        command[1] = str(a.HERE / "task31_snapshot.py")
        log = Path(scratch) / (name + ".log")
        ran = run_one(command, log, fds, None)
        failed = ran["exit"] != 0 or ran["timed_out"]
        if folder.is_dir():
            shutil.copy(log, folder / "runner.log")
        archive = root / (name + ".json.xz")
        files = ENGINE.h.archive(folder, archive, scratch) \
            if folder.is_dir() else None
        try:
            a.require(not failed and files is not None,
                      "identity runner failed: " + name)
            row = idt.cell(folder, case, size, args.baseline,
                           args.candidate, ID_SAMPLES)
        except BaseException:
            if archive.exists():
                tg.set_aside(archive, "failed")
            raise
    inventory["runs"].append(dict(
        case=case, size=size, archive=archive.name, seal=a.seal(archive),
        files=files, row=row))
    tg.checkpoint(root / "inventory.json", inventory)
    print("END %s %s" % (name, row["status"]), flush=True)


def feasible(names):
    return [n for n in names if n not in cases.INFEASIBLE]


def identity(args):
    a.require(args.authorize_measurements,
              "measurement authorization required")
    a.exact_pin(args.baseline)
    a.exact_pin(args.candidate)
    root = args.output.resolve()
    names = [name_of(*k) for k in every()]
    only = args.only
    if only:
        a.require(set(only) <= set(names) and len(set(only)) == len(only),
                  "unknown or repeated cell in --only")
        names = [n for n in names if n in only]
    inventory = dict(
        schema=SCHEMA, baseline=args.baseline, candidate=args.candidate,
        diagnostic=bool(only), expected=names, pairs=ID_PAIRS,
        samples=ID_SAMPLES, seconds=ID_SECONDS, code=code_seals(),
        sources=source_blobs(args.repo, args.baseline, args.candidate),
        runs=[])
    ENGINE.h.check_output(args)
    if not only:
        inventory["checkout"] = ENGINE.h.bind_checkout(
            args.repo, args.candidate, args.resume)
    done = set()
    with ENGINE.h.locked(args.repo) as fds:
        if not only:
            ENGINE.h.recheck(args.repo, args.candidate, inventory)
        if args.resume:
            old = a.load(root / "inventory.json")
            a.require({k: v for k, v in old.items() if k != "runs"} ==
                      {k: v for k, v in inventory.items() if k != "runs"},
                      "resume with different settings")
            for run in old["runs"]:
                a.require(a.seal(a.safe_child(root, run["archive"])) ==
                          run["seal"], "changed archive")
            inventory["runs"] = old["runs"]
            done = {name_of(r["case"], r["size"]) for r in old["runs"]}
            ENGINE.h.sweep(root, [r["archive"] for r in old["runs"]])
        else:
            root.mkdir(parents=True, exist_ok=False)
        tg.checkpoint(root / "inventory.json", inventory)
        try:
            for name in feasible(names):
                if name not in done:
                    case, size = name.rsplit("-", 1)
                    measure(args, case, int(size), root, inventory, fds)
            if not only:
                ENGINE.h.judge_end(root, args.repo, None, inventory)
        finally:
            tg.checkpoint(root / "inventory.json", inventory)
    decisions = decide(inventory)
    tg.checkpoint(root / "decisions.json", decisions)
    report(decisions)
    return status_code(decisions)


def identity_replay(args):
    root = args.output.resolve()
    inventory = a.load(root / "inventory.json")
    a.require(inventory["schema"] == SCHEMA, "not a TASK31 identity grid")
    a.require(inventory["code"] == code_seals(),
              "the identity code changed since the grid")
    a.require(inventory["pairs"] == ID_PAIRS and
              inventory["samples"] == ID_SAMPLES and
              inventory["seconds"] == ID_SECONDS, "changed settings")
    if not inventory["diagnostic"]:
        a.require(inventory["expected"] ==
                  [name_of(*k) for k in every()], "changed cell list")
        a.require("checkout" in inventory, "unbound checkout")
        a.require(not inventory.get("checkout_changed"),
                  "the checkout changed during the grid")
    names = [name_of(r["case"], r["size"]) for r in inventory["runs"]]
    a.require(len(set(names)) == len(names) and
              set(names) <= set(feasible(inventory["expected"])),
              "repeated or unexpected cell")
    a.require(inventory["sources"] == source_blobs(
        args.repo, inventory["baseline"], inventory["candidate"]),
        "changed source blobs")
    for run in inventory["runs"]:
        archive = a.safe_child(root, run["archive"])
        a.require(a.seal(archive) == run["seal"], "changed archive")
        with tempfile.TemporaryDirectory(prefix="task31-replay-") as scratch:
            folder = Path(scratch) / "cell"
            a.require(bundle.unpack(archive, folder) == run["files"],
                      "archive does not unpack to its inventory")
            row = idt.cell(folder, run["case"], run["size"],
                           inventory["baseline"], inventory["candidate"],
                           inventory["samples"])
        a.require(tg.canonical(row) == tg.canonical(run["row"]),
                  "the identity row of %s differs on replay"
                  % name_of(run["case"], run["size"]))
    decisions = decide(inventory)
    a.require(tg.canonical(decisions) ==
              tg.canonical(a.load(root / "decisions.json")),
              "the decisions differ on replay")
    report(decisions)
    return status_code(decisions)


def commands():
    """The actions of this task besides the engine's."""
    repo = a.HERE.parents[3]

    def configure(p):
        p.add_argument("--output", type=Path, required=True)
        p.add_argument("--baseline", default=a.BASE)
        p.add_argument("--candidate", required=True)
        p.add_argument("--only", action="append", metavar="CELL",
                       help="diagnostic subset in any checkout; never a "
                       "grid decision")
        p.add_argument("--resume", action="store_true")
        p.add_argument("--authorize-measurements", action="store_true")
        p.add_argument("--repo", type=Path, default=repo)
        p.add_argument("--timeout", type=int, default=1800)

    def again(p):
        p.add_argument("--output", type=Path, required=True)
        p.add_argument("--repo", type=Path, default=repo)
    return {"identity": (configure, identity),
            "identity-replay": (again, identity_replay)}


def main(argv=None):
    return ENGINE.main(argv, extra=commands())


if __name__ == "__main__":
    sys.exit(main())
