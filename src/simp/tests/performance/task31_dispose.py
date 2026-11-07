#!/usr/bin/env python3
"""The TASK31 decision per cell: identity, allocation and timing together.

A cell passes if and only if

- gate 1: its identity row is `identical` (task31_grid.py `identity`);
- gate 2: the allocation grid measured it and decided `pass`, where that
  gate measures it (every cell but the infeasible ones);
- gate 3: the timing table decided `pass`, where the cell is sampled
  (task31_cases.SAMPLE).

The 33 infeasible cells (task31_cases.INFEASIBLE) pass by identity alone and
are recorded as "untimed, unallocated: infeasible", with the numbers of the
cost survey. Nothing is excused here: a cell whose identity differs is a
cell that does not pass, whatever the timing says (the timing sample is where
such a cell is measured, and its result is printed beside it).

The command replays what it reads: the identity grid (every archive, every
decision), and the timing grid (`task31_grid.py replay`, in full, with its
pilot). The allocation grid is read through its `decisions.json`, whose
contract is the following and nothing more (PROTOCOL.md, "TASK31"):

    {"candidate": COMMIT,                 # optional: checked when present
     "rows": [{"case": CASE, "size": N, "decision": "pass" | "fail"}, ...]}

One row per cell, no repeated cell, and each cell one the allocation gate
measures; any other decision is refused. The gate's own replay (and the
grid's other fields) are not this module's: the allocation gate is run and
replayed by allocation_matrix.py, whose verdict the caller reads.

The exit status is 0 when every cell passes, 1 when a cell does not, 2 when
the evidence is not conclusive (a gate has no decision for a cell it must
decide), 3 when the command is refused. The last line printed is the verdict.
"""
import argparse
import contextlib
import io
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task31_cases as cases
import task31_grid as grid
import timing_grid as tg

SCHEMA = "task31-disposition-v1"
INFEASIBLE_TEXT = "untimed, unallocated: infeasible"


def allocation_rows(decisions, candidate):
    """The allocation decisions as {cell name: "pass" | "fail"}, refusing a
    malformed file."""
    a.require(isinstance(decisions, dict) and
              isinstance(decisions.get("rows"), list),
              "the allocation decisions have no rows")
    a.require("candidate" not in decisions or
              decisions["candidate"] == candidate,
              "the allocation grid is of another candidate (%s, not %s)"
              % (decisions.get("candidate"), candidate))
    known = {grid.name_of(*k) for k in grid.every()}
    found = {}
    for row in decisions["rows"]:
        a.require(isinstance(row, dict) and isinstance(row.get("case"), str)
                  and isinstance(row.get("size"), int) and
                  row.get("decision") in ("pass", "fail"),
                  "malformed allocation row: %r" % (row,))
        name = grid.name_of(row["case"], row["size"])
        a.require(name in known, "allocation row of an unknown cell: "
                  + name)
        a.require(name not in cases.INFEASIBLE,
                  "allocation row of an infeasible cell: " + name)
        a.require(name not in found, "repeated allocation row: " + name)
        found[name] = row["decision"]
    return found


def timing_rows(decisions):
    """{cell name: class} of a timing grid's decisions."""
    found = {}
    for kind, names in tg.classify(decisions).items():
        for name in names:
            if name != "retained_scaling":
                found[name] = kind
    return found


def judge(name, identity, allocated, timed):
    """One cell: its record. `identity` is the cell's identity decision,
    `allocated` the allocation decision or None, `timed` the timing class or
    None. A gate with no decision for a cell it must decide leaves the cell
    `incomplete`; a gate that decided against it makes it `fail`."""
    infeasible = name in cases.INFEASIBLE
    found = dict(identity=identity["status"], allocation=allocated,
                 timing=timed)
    failed, missing = [], []
    if identity["status"] == "different":
        failed.append("identity: the loaded closure or the work differs")
    elif identity["status"] != "identical":
        missing.append("identity: " + identity["status"])
    if infeasible:
        found["note"] = INFEASIBLE_TEXT
        found["survey"] = identity.get("survey")
        found["route"] = identity.get("route")
    else:
        if allocated is None:
            missing.append("allocation: no decision")
        elif allocated != "pass":
            failed.append("allocation: " + allocated)
    if name in cases.SAMPLE:
        if timed is None:
            missing.append("timing: no decision")
        elif timed != "pass":
            failed.append("timing: " + timed)
    elif timed is not None:
        failed.append("timing: a cell outside the sample")
    found["failed"], found["missing"] = failed, missing
    found["status"] = ("fail" if failed else
                       "incomplete" if missing else "pass")
    return found


def dispose(identity, allocated, timed):
    """Every cell's record and the status of the whole, from the decisions
    of the three gates."""
    names = [grid.name_of(*k) for k in grid.every()]
    a.require(set(identity["cells"]) == set(names) and
              not identity["diagnostic"],
              "the identity grid is not the whole grid")
    records = {n: judge(n, identity["cells"][n], allocated.get(n),
                        timed.get(n)) for n in names}
    counts = {k: sum(r["status"] == k for r in records.values())
              for k in ("pass", "fail", "incomplete")}
    status = ("fail" if counts["fail"] else
              "incomplete" if counts["incomplete"] or
              identity["status"] == "inconclusive" else "pass")
    return dict(schema=SCHEMA, status=status, counts=counts,
                infeasible=sum(n in cases.INFEASIBLE for n in names),
                cells=records)


def lines(record):
    out = []
    for name, found in record["cells"].items():
        if found["status"] == "pass" and name not in cases.INFEASIBLE:
            continue
        why = found["failed"] + found["missing"]
        if name in cases.INFEASIBLE:
            cost = found.get("survey") or {}
            why = why or [INFEASIBLE_TEXT + " (survey: op %.3g s, setup "
                          "%.3g s, check %.3g s at 10000; timeout %d s)"
                          % (cost.get("op10000", float("nan")),
                             cost.get("setup10000", float("nan")),
                             cost.get("check10000", float("nan")),
                             cases.PROCESS_TIMEOUT)]
        out.append("%s %s: %s" % (found["status"].upper(), name,
                                  "; ".join(why)))
    return out


def derive(args):
    repo = args.repo
    with contextlib.redirect_stdout(io.StringIO()):
        a.require(grid.identity_replay(argparse.Namespace(
            output=args.identity, repo=repo)) in (0, 1),
            "the identity grid is not conclusive")
    identity = a.load(args.identity.resolve() / "decisions.json")
    inventory = a.load(args.identity.resolve() / "inventory.json")
    timing = a.load(args.grid.resolve() / "inventory.json")
    a.require(timing["candidate"] == inventory["candidate"] and
              timing["baseline"] == inventory["baseline"],
              "the timing grid and the identity grid have another "
              "candidate or baseline")
    tg_code = grid.ENGINE.replay(argparse.Namespace(
        output=args.grid.resolve(), partial=False, repo=repo,
        pilot=args.pilot.resolve(), ledger=args.ledger))
    timed_decisions = a.load(args.grid.resolve() / "decisions.json")
    a.require(set(timing_rows(timed_decisions)) ==
              set(grid.TABLE.names()), "the timing grid is not the sample")
    allocated = allocation_rows(
        a.load(args.allocation.resolve() / "decisions.json"),
        inventory["candidate"])
    record = dispose(identity, allocated, timing_rows(timed_decisions))
    record["candidate"] = inventory["candidate"]
    record["baseline"] = inventory["baseline"]
    record["timing_status"] = timed_decisions["status"]
    record["timing_replay_exit"] = tg_code
    return record


def disposition(args):
    record = derive(args)
    for line in lines(record):
        print(line)
    if args.record:
        a.require(not args.record.exists(), "refusing to replace "
                  + str(args.record))
        a.save(args.record, record)
    elif args.check:
        a.require(tg.canonical(a.load(args.check)) ==
                  tg.canonical(record), "changed TASK31 disposition")
    print("TASK31 disposition: %s %s (candidate %s; timing %s)" % (
        record["status"], json.dumps(record["counts"]), record["candidate"],
        record["timing_status"]))
    return {"pass": 0, "fail": 1}.get(record["status"], 2)


def parser():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    add = p.add_argument
    add("--identity", type=Path, required=True,
        help="the identity grid (task31_grid.py identity --output)")
    add("--grid", type=Path, required=True,
        help="the timing grid, its second stage where there is one")
    add("--pilot", type=Path, required=True, help="the timing pilot")
    add("--allocation", type=Path, required=True,
        help="the allocation output directory (its decisions.json)")
    add("--repo", type=Path, default=a.HERE.parents[3])
    add("--ledger", type=Path, help="read this attempts ledger, of the "
        "checkout the timing grid was made in")
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--record", type=Path,
                      help="write the disposition to this new file")
    mode.add_argument("--check", type=Path,
                      help="require that this recorded disposition is "
                      "derived again")
    return p


def main(argv=None):
    """The status of the disposition, or `REFUSED` (3) with one line on the
    standard error for a command that decided nothing."""
    with tg.terminating_as_interrupt():
        try:
            return disposition(parser().parse_args(argv))
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
