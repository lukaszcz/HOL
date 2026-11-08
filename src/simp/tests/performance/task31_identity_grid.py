#!/usr/bin/env python3
"""TASK31 gate 1: source identity of every cell.

For every cell of task31_cases.CASES (feasible ones) one fresh process per
side, through the real paired runner (task31_snapshot.py, which runs it
unchanged and records the private trees), is compared by task31_identity.py:
the closure of the sources the process elaborated and their products, and
the work row. A cell is `identical`, `attributed` (every difference is of a
file of the reviewed table, task31_attribution.py) or `different`. Beside the
cells the grid accounts for every tracked file that differs between the two
commits, outside the reviewed exclusions (the shared and heap files are the
candidate's on both sides, so only this accounting sees them): each is
attributed, or provably not loaded by any cell (derived from the receipts),
or the grid is `different`. The 33 cells of task31_cases.INFEASIBLE are not
run; their identity derives from every measured cell of their case, provided
that the loaded closure is the same in every measured cell of the grid,
which the grid checks.

The grid is made with the committed reviewed table (task31_attributed.json)
and no other: `--attributed FILE` is a diagnostic of `--only` runs. The
engine and the ledger are the timing driver's (task31_grid.py, which this
module imports and which does not import it), so that a change to this
module alters no seal of a timing grid. The timing commands are that
module's; this one has none.

  prepare          configure, build and stamp the checkout   (takes the lock)
  identity         gate 1: --output DIR --candidate COMMIT   (authorized)
                   [--only CELL ...: a diagnostic, any checkout]
  identity-replay  re-derive every identity decision offline (--output DIR)
  sources          print the files the grid's cells elaborated (--output DIR)

The exit status of `identity` and `identity-replay` is 0 when every cell is
identical or attributed, 1 when one is different (or a file is
unaccounted), 2 when the grid is not conclusive (a cell missing, an
uncovered or unused source, a closure that is not cell-independent). A
command that is refused prints one REFUSED line and exits 3.
"""
import argparse
from pathlib import Path
import shutil
import sys
import tempfile
import uuid

sys.dont_write_bytecode = True
import acceptance as a
import evidence_bundle as bundle
import matrix_schema as ms
import task31_attribution as attr
import task31_cases as cases
import task31_grid as timing
import task31_identity as idt
import timing_grid as tg

ENGINE = timing.ENGINE

SCHEMA = "task31-identity-v1"
DECISIONS = "task31-identity-decisions-v1"
IDENTITY_TABLE = "task31-identity"
# One pair, three samples, free ramp calibration of 0.1 s batches: nothing
# is timed for a decision; the process loads, runs the fixture and is audited.
ID_PAIRS, ID_SAMPLES, ID_SECONDS = 1, 3, 0.1
# (a test pins that every local module the identity modules import, to the
# transitive closure, is here or is on its short list of reviewed exemptions)
IDENTITY_CODE = ("task31_identity_grid.py", "task31_grid.py",
                 "task31_identity.py",
                 "task31_snapshot.py", "task31_cases.py",
                 "task31_attribution.py", "task31_pins.py", "acceptance.py",
                 "audit_evidence.py", "performance_schema.py",
                 "evidence_bundle.py", "client_dependencies.py",
                 "timing_grid.py", "matrix_schema.py", "summarize.py",
                 "runtime_metrics.py", "task29_gate.py",
                 "../compatibility/run_paired.py")
# Per file of IDENTITY_CODE, the seals it had when an identity grid was
# recorded, once it has changed since (a reviewed change that alters no
# decision): then, in the same commit, add the old seal here so that the
# grid still replays.
CODE_HISTORY = {}
STATUS_ORDER = ("identical", "attributed", "different")


def every():
    """Every cell of the task, in order: (case, size)."""
    return [(case, size) for case in cases.CASES for size in
            ms.SIZE_SETS[ms.EXPECTED_CASES[case]["sizes"]]]


def name_of(case, size):
    return "%s-%d" % (case, size)


def case_of(name):
    return name.rsplit("-", 1)[0]


def anchor(name):
    """The size-0 cell of a cell's case: the first of the cells an
    infeasible cell derives from."""
    return case_of(name) + "-0"


def code_seals():
    return {n: a.seal(a.HERE / n) for n in IDENTITY_CODE}


def check_code(recorded):
    """The recorded seals of the identity code are those of the code now or
    of an earlier version CODE_HISTORY names."""
    now = code_seals()
    a.require(isinstance(recorded, dict) and set(recorded) == set(now),
              "the identity code recorded is not %s" % ", ".join(now))
    changed = [n for n in now if recorded[n] != now[n] and
               recorded[n] not in CODE_HISTORY.get(n, ())]
    a.require(not changed, "the identity code changed since the grid: %s "
              "(add the seal the grid was made by to CODE_HISTORY)"
              % ", ".join(changed))


def source_tree(repo, baseline, candidate):
    """Every tracked file that differs between the two commits."""
    return dict(tree=".", changes=tg.git_difference(
        repo, baseline, candidate, "."))


def source_blobs(repo, baseline, candidate, entries, tree):
    """The git blob of each file at both commits (None where absent) of
    cases.SOURCES, of the reviewed table, and of every tracked file that
    differs."""
    wanted = set(cases.SOURCES) | {e["path"] for e in entries} | {
        p for _, p in tree["changes"]}
    return {p: dict(baseline=tg.git_blob(repo, baseline, p),
                    candidate=tg.git_blob(repo, candidate, p))
            for p in sorted(wanted)}


def worst(rows):
    """The row of the worst status among rows."""
    return max(rows, key=lambda r: STATUS_ORDER.index(r["status"]))


def derived(name, measured, expected, invariant):
    """The identity row of an infeasible cell: the worst of its case's
    measured cells, when the closure is the same in every measured cell and
    every other cell of the case was measured."""
    siblings = [n for n in expected if case_of(n) == case_of(name) and
                n not in cases.INFEASIBLE]
    row = dict(
        route="derived from %s: the loaded closure is the same in every "
        "measured cell" % ", ".join(siblings), derived_from=siblings,
        work="not run: infeasible", process_timeout=cases.PROCESS_TIMEOUT)
    if not invariant:
        return dict(row, status="unresolved",
                    reason="the closure is not the same in every cell")
    missing = [n for n in siblings if n not in measured]
    if missing or not siblings:
        return dict(row, status="unresolved",
                    reason="not measured: " + (", ".join(missing) or
                                               "no cell of the case"))
    rows = [measured[n] for n in siblings]
    chosen = worst(rows)
    found = {}
    for one in rows:
        for record in one["attributed"]:
            found.setdefault(record["path"], record)
    return dict(row, status=chosen["status"],
                closure_differences=chosen["closure_differences"],
                work_differences=[d for one in rows
                                  for d in one["work_differences"]],
                attributed=[found[p] for p in sorted(found)],
                closure=measured[siblings[0]]["closure"])


def accounting(inventory, measured):
    """The classes of the files below src/ that differ between the commits
    (task31_attribution.account), from the files the receipts show were
    loaded, and the files elaborated on each side."""
    sides = idt.SIDES
    elaborated = {s: sorted({p for row in measured.values()
                             for p in row["repo_files"][s]}) for s in sides}
    loaded = {p for row in measured.values() for s in sides
              for key in ("repo_files", "loaded_files", "heap_files")
              for p in row[key][s]}
    entries = inventory["attributed"]["table"]
    return elaborated, attr.account(inventory["sources"], entries, loaded)


def decide(inventory):
    """The decisions of an identity inventory: one entry per expected cell
    and the checks of the grid as a whole. Pure; `identity-replay` calls it
    again on the inventory it has verified."""
    measured = {name_of(r["case"], r["size"]): r["row"]
                for r in inventory["runs"]}
    expected = inventory["expected"]
    sides = idt.SIDES
    a.require(all(row["attribution_table"] == inventory["attributed"]
                  ["digest"] for row in measured.values()),
              "a cell was judged by another attribution table")
    digests = {s: sorted({row["closure"][s]["digest"]
                          for row in measured.values()}) for s in sides}
    invariant = all(len(d) <= 1 for d in digests.values())
    harness = {key: sorted({tg.canonical(row.get(key))
                            for row in measured.values()})
               for key in ("inputs", "tools", "head", "dirty")}
    consistent = all(len(v) <= 1 for v in harness.values())
    found = {}
    for name in expected:
        if name in measured:
            row = measured[name]
            found[name] = dict(
                status=row["status"], route="run",
                closure_differences=row["closure_differences"],
                work_differences=row["work_differences"],
                attributed=row["attributed"], closure=row["closure"])
        elif name in cases.INFEASIBLE:
            found[name] = derived(name, measured, expected, invariant)
        else:
            found[name] = dict(status="unresolved", route="not run")
    elaborated, accounted = accounting(inventory, measured)
    outside = set(cases.SOURCES)
    uncovered = sorted(set(elaborated["baseline"]) - outside)
    only_candidate = sorted(set(elaborated["candidate"]) - outside -
                            set(elaborated["baseline"]))
    unused = sorted(outside - set(elaborated["baseline"]) -
                    set(elaborated["candidate"]))
    blobs = inventory["sources"]
    unaccounted = sorted(p for p, (kind, _) in accounted.items()
                         if kind in attr.DECISIVE)
    counts = {k: sum(v["status"] == k for v in found.values())
              for k in (*STATUS_ORDER, "unresolved")}
    full = not inventory["diagnostic"]
    conclusive = (not counts["unresolved"] and not uncovered and
                  invariant and consistent and not (full and unused))
    reviewed = sorted(p for p, (kind, _) in accounted.items()
                      if kind == "attributed")
    status = ("inconclusive" if not conclusive else
              "different" if counts["different"] or unaccounted else
              "attributed" if counts["attributed"] or reviewed else
              "identical")
    return dict(
        schema=DECISIONS, baseline=inventory["baseline"],
        candidate=inventory["candidate"],
        diagnostic=inventory["diagnostic"], status=status, counts=counts,
        closure_digests=digests, closure_invariant=invariant,
        harness=harness, harness_consistent=consistent,
        uncovered=uncovered, candidate_only=only_candidate,
        unused_sources=unused, unaccounted=unaccounted,
        attributed=reviewed,
        attribution_table=inventory["attributed"]["digest"],
        tree={p: list(v) for p, v in accounted.items()},
        build_files={p: v[0] for p, v in accounted.items()
                     if attr.is_build(p)},
        git_differing=sorted(p for p, b in blobs.items()
                             if b["baseline"] != b["candidate"]),
        cells=found)


def status_code(decisions):
    return {"identical": 0, "attributed": 0, "different": 1}.get(
        decisions["status"], 2)


def report(decisions):
    c = decisions["counts"]
    print("TASK31 identity: %s (%d identical, %d attributed, %d different, "
          "%d unresolved; candidate %s)" % (
              decisions["status"], c["identical"], c["attributed"],
              c["different"], c["unresolved"], decisions["candidate"]))
    for path in decisions["attributed"]:
        print("  ATTRIBUTED %s: %s" % (path, decisions["tree"][path][1]))
    for name, found in sorted(decisions["cells"].items()):
        if found["status"] not in ("identical", "attributed"):
            files = sorted({d["name"].split(" ")[0] for d in
                            found.get("closure_differences", [])})
            print("  %s: %s %s" % (name, found["status"],
                                   ", ".join(files[:6])))
    for path in decisions["unaccounted"]:
        kind, note = decisions["tree"][path]
        print("  UNACCOUNTED %s: %s (%s)" % (path, kind, note))
    for key in ("uncovered", "candidate_only", "unused_sources"):
        if decisions[key]:
            print("  %s: %s" % (key, ", ".join(decisions[key][:20])))
    if not decisions["closure_invariant"]:
        print("  the loaded closure differs between measured cells")
    if not decisions["harness_consistent"]:
        print("  the cells ran with different inputs, tools or checkouts")


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
                           args.candidate, ID_SAMPLES,
                           inventory["attributed"]["table"])
            if not inventory["diagnostic"]:
                a.require(row["head"] == args.candidate and
                          not row["dirty"],
                          "the cell ran in another checkout than the "
                          "candidate's, or a dirty one: " + name)
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


def attribution(args, diagnostic):
    """The reviewed table of a command: the committed file, and its seal.
    `--attributed` names another file in a diagnostic (`--only`) only: a
    full grid is judged by the committed table, which the disposition binds
    to the table the timing grid pins."""
    path = getattr(args, "attributed", None)
    a.require(path is None or diagnostic,
              "--attributed is for diagnostics (--only); a full grid and "
              "the disposition use the committed task31_attributed.json")
    return attr.load(attr.FILE if path is None else Path(path))


def record(path, event, inventory, root, repo, **more):
    """One line of the attempts ledger about an identity grid (the lines of
    this table are kept apart from the timing table's by `table`)."""
    if path is not None:
        tg.ledger_append(
            path, event=event, stage="identity", table=IDENTITY_TABLE,
            attempt=inventory["attempt"], candidate=inventory["candidate"],
            output=str(root), checkout=str(Path(repo).resolve()), **more)


def attempt_counts(path, candidate):
    """(identity attempts, those of the candidate) in a ledger."""
    found = tg.Ledger(path).attempts(IDENTITY_TABLE)
    return len(found), sum(1 for row in found.values()
                           if row["candidate"] == candidate)


def prepare_table(args, document):
    """The reviewed table against git at the two commits, before anything
    is measured: no placeholder is left, and every entry names the blobs
    git has."""
    entries = document["entries"]
    open_ = attr.unfilled(entries)
    a.require(not open_, "the attribution file has placeholder candidate "
              "blobs (to be filled at integration): %s; git has: %s" % (
                  ", ".join(open_), ", ".join(
                      "%s %s" % (p, tg.git_blob(args.repo, args.candidate,
                                                p)) for p in open_)))
    attr.check_blobs(args.repo, args.baseline, args.candidate, entries)


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
    document = attribution(args, bool(only))
    prepare_table(args, document)
    entries = document["entries"]
    tree = source_tree(args.repo, args.baseline, args.candidate)
    inventory = dict(
        schema=SCHEMA, baseline=args.baseline, candidate=args.candidate,
        diagnostic=bool(only), expected=names, pairs=ID_PAIRS,
        samples=ID_SAMPLES, seconds=ID_SECONDS, code=code_seals(),
        attributed=dict(file=document["seal"], table=entries,
                        digest=attr.digest(entries)),
        sources=source_blobs(args.repo, args.baseline, args.candidate,
                             entries, tree),
        source_tree=tree, runs=[])
    ENGINE.h.check_output(args)
    ledger = ENGINE.h.attempts_file(args, True)
    if not only:
        inventory["checkout"] = ENGINE.h.bind_checkout(
            args.repo, args.candidate, args.resume)
    done = set()
    with ENGINE.h.locked(args.repo) as fds:
        if not only:
            ENGINE.h.recheck(args.repo, args.candidate, inventory)
        if args.resume:
            old = a.load(root / "inventory.json")
            a.require({k: v for k, v in old.items()
                       if k not in ("runs", "attempt")} ==
                      {k: v for k, v in inventory.items() if k != "runs"},
                      "resume with different settings")
            for run in old["runs"]:
                a.require(a.seal(a.safe_child(root, run["archive"])) ==
                          run["seal"], "changed archive")
            inventory["runs"] = old["runs"]
            inventory["attempt"] = old["attempt"]
            done = {name_of(r["case"], r["size"]) for r in old["runs"]}
            ENGINE.h.sweep(root, [r["archive"] for r in old["runs"]])
        else:
            inventory["attempt"] = uuid.uuid4().hex
            root.mkdir(parents=True, exist_ok=False)
        tg.checkpoint(root / "inventory.json", inventory)
        record(ledger, "resume" if args.resume else "open", inventory,
               root, args.repo, only=only)
        status = "interrupted"
        try:
            for name in feasible(names):
                if name not in done:
                    case, size = name.rsplit("-", 1)
                    measure(args, case, int(size), root, inventory, fds)
            if not only:
                ENGINE.h.judge_end(root, args.repo, None, inventory)
            decisions = decide(inventory)
            tg.checkpoint(root / "decisions.json", decisions)
            status = decisions["status"]
        finally:
            tg.checkpoint(root / "inventory.json", inventory)
            record(ledger, "close", inventory, root, args.repo,
                   status=status)
    report(decisions)
    return status_code(decisions)


def check_opening(path, inventory):
    """The ledger holds the opening of this grid."""
    a.require(Path(path).is_file(), "no attempts ledger: %s" % path)
    found = tg.Ledger(path).attempts(IDENTITY_TABLE)
    a.require((inventory["attempt"], "identity") in found and
              found[(inventory["attempt"], "identity")]["candidate"] ==
              inventory["candidate"],
              "the attempts ledger has no opening of this identity grid")


def identity_replay(args):
    root = args.output.resolve()
    inventory = a.load(root / "inventory.json")
    a.require(inventory["schema"] == SCHEMA, "not a TASK31 identity grid")
    check_code(inventory["code"])
    a.require(inventory["pairs"] == ID_PAIRS and
              inventory["samples"] == ID_SAMPLES and
              inventory["seconds"] == ID_SECONDS, "changed settings")
    repo = args.repo
    if not inventory["diagnostic"]:
        a.require(inventory["expected"] ==
                  [name_of(*k) for k in every()], "changed cell list")
        a.require("checkout" in inventory, "unbound checkout")
        a.require(not inventory.get("checkout_changed"),
                  "the checkout changed during the grid")
        ENGINE.h.check_checkout(inventory, repo)
    names = [name_of(r["case"], r["size"]) for r in inventory["runs"]]
    a.require(len(set(names)) == len(names) and
              set(names) <= set(feasible(inventory["expected"])),
              "repeated or unexpected cell")
    recorded = inventory["attributed"]
    entries = attr.entries_of(
        attribution(args, inventory["diagnostic"]), recorded["file"])
    a.require(recorded["table"] == entries and
              recorded["digest"] == attr.digest(entries),
              "the recorded attribution is not the file's")
    a.require(inventory["source_tree"] == source_tree(
        repo, inventory["baseline"], inventory["candidate"]),
        "changed source difference")
    a.require(inventory["sources"] == source_blobs(
        repo, inventory["baseline"], inventory["candidate"], entries,
        inventory["source_tree"]), "changed source blobs")
    if getattr(args, "ledger", None) is not None:
        check_opening(args.ledger, inventory)
    for run in inventory["runs"]:
        archive = a.safe_child(root, run["archive"])
        a.require(a.seal(archive) == run["seal"], "changed archive")
        with tempfile.TemporaryDirectory(prefix="task31-replay-") as scratch:
            folder = Path(scratch) / "cell"
            a.require(bundle.unpack(archive, folder) == run["files"],
                      "archive does not unpack to its inventory")
            row = idt.cell(folder, run["case"], run["size"],
                           inventory["baseline"], inventory["candidate"],
                           inventory["samples"], entries)
        a.require(tg.canonical(row) == tg.canonical(run["row"]),
                  "the identity row of %s differs on replay"
                  % name_of(run["case"], run["size"]))
    decisions = decide(inventory)
    a.require(tg.canonical(decisions) ==
              tg.canonical(a.load(root / "decisions.json")),
              "the decisions differ on replay")
    report(decisions)
    return status_code(decisions)


def sources(args):
    """The files the cells of an identity grid elaborated on either side,
    sorted, one per line (task31_cases.SOURCES is this list); with
    `--heap` the files of the initial heap too."""
    inventory = a.load(args.output.resolve() / "inventory.json")
    a.require(inventory["schema"] == SCHEMA, "not a TASK31 identity grid")
    found = set()
    for run in inventory["runs"]:
        for side in idt.SIDES:
            found |= set(run["row"]["repo_files"][side])
            if args.heap:
                found |= set(run["row"]["heap_files"][side])
    for path in sorted(found):
        print(path)
    return 0


def parser():
    """The commands of this gate (the timing table's are not among them)."""
    repo = a.HERE.parents[3]
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="action", required=True)

    build = sub.add_parser(
        "prepare", help="configure and build the checkout and stamp it "
        "for the measuring commands")
    build.add_argument("--repo", type=Path, default=repo)
    build.add_argument("--timeout", type=int, default=tg.BUILD_TIMEOUT,
                       help="seconds each of the two commands, configure "
                       "and the build, may take")

    run = sub.add_parser("identity", help="gate 1, every cell")
    run.add_argument("--output", type=Path, required=True)
    run.add_argument("--baseline", default=a.BASE)
    run.add_argument("--candidate", required=True)
    run.add_argument("--only", action="append", metavar="CELL",
                     help="diagnostic subset in any checkout; never a "
                     "grid decision")
    run.add_argument("--resume", action="store_true")
    run.add_argument("--authorize-measurements", action="store_true")
    run.add_argument("--repo", type=Path, default=repo)
    run.add_argument("--timeout", type=int, default=1800)
    run.add_argument("--attributed", type=Path, help="the reviewed "
                     "table, if not task31_attributed.json (a diagnostic "
                     "run only)")

    again = sub.add_parser("identity-replay", help="re-derive the "
                           "decisions of an identity grid offline")
    again.add_argument("--output", type=Path, required=True)
    again.add_argument("--repo", type=Path, default=repo)
    again.add_argument("--attributed", type=Path, help="the reviewed "
                       "table a diagnostic grid was made with")
    again.add_argument("--ledger", type=Path, help="require that this "
                       "attempts ledger holds the opening of the grid")

    listing = sub.add_parser("sources", help="the files the cells "
                             "elaborated")
    listing.add_argument("--output", type=Path, required=True)
    listing.add_argument("--heap", action="store_true",
                         help="add the files of the initial heap")
    return p


def prepare(args):
    return ENGINE.h.prepare(args)


HANDLERS = {"prepare": prepare, "identity": identity,
            "identity-replay": identity_replay, "sources": sources}


def main(argv=None):
    """The status of the command, or `REFUSED` (3) with one line on the
    standard error for one that decided nothing (as the engine's `main`).

    The handler below copies `timing_grid.Grid.main`'s error wrapper (that
    file is sealed for TASK30, so it cannot be factored out): keep the two
    in step, so that a refusal reads the same from either command."""
    with tg.terminating_as_interrupt():
        try:
            args = parser().parse_args(argv)
            return HANDLERS[args.action](args)
        except Exception as error:
            text = str(error)
            if not isinstance(error, ValueError):
                import traceback
                traceback.print_exc()
                text = "%s: %s" % (type(error).__name__, text)
            print("REFUSED: " + " ".join(text.split()), file=sys.stderr,
                  flush=True)
            return tg.REFUSED


if __name__ == "__main__":
    sys.exit(main())
