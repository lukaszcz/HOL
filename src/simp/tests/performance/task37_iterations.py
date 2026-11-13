#!/usr/bin/env python3
"""The predeclared steady counts of the TASK37 allocation grids.

  task37_iterations.py {matrix,client,downstream,all} [--check]
                       [--directory DIR]

writes (`all`: all three) the counts files the allocation tasks
`task37-matrix`, `task37-client` and `task37-downstream` of
allocation_matrix.py name:

  allocation_iterations_task37_matrix.json
  allocation_iterations_task37_client.json
  allocation_iterations_task37_downstream.json

in the format of the other allocation counts files (`task29b-iterations-v1`:
`repeats`, `rule`, `steady`, which `allocation_matrix.load_iterations`
reads). The counts are a policy of the case and the size, never a
measurement of the grid: the same count for both sides and every pair,
fixed before any observation (design decision 25). A file is written only
if it does not exist (a counts file is committed alone, in the main
worktree, before the allocation starts, and is then sealed); one that exists
and differs is refused, never overwritten. `--check` writes nothing and
verifies that each committed file equals the output of the rule: exit 0
when they all do, 1 otherwise (a missing file, or a different one).
`--directory` names another place for the files (a test).

Rule. TASK37 measures every cell exactly as its originating task did, so
each matrix and client cell takes the steady count that task predeclared,
read from its counts file:

  matrix      the 162 cells of TASK29B's cases: allocation_iterations.json;
              the 144 cells of TASK30's cases:
              allocation_iterations_task30.json;
  client      the 245 allocated cells of TASK31's cases:
              allocation_iterations_task31.json (whose own rule halves or
              quarters the reuse and complete stages of some tactic
              families at 1000 to fit the process timeout);
  downstream  no predecessor (the `downstream_*` workloads are new in
              TASK37): the TASK30 size rule, 32 for size <= 100 (size 0
              included), 16 for 1000 and 8 for 10000.

The case sets of the TASK37 tasks are those of their predecessors (the
matrix is the union of TASK29B's and TASK30's cases, the client is TASK31's,
all with the same sizes and infeasible cells), so no cell is without a
predecessor count; if one ever were, the cell is refused (there is no
default), as is a predecessor file whose repeats differ from another's of
the table. The repeats of a file are its predecessors'.
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import acceptance as a

SCHEMA = "task29b-iterations-v1"
# table -> (allocation task, the tasks whose counts its cells take)
TABLES = {
    "matrix": ("task37-matrix", ("task29b", "task30")),
    "client": ("task37-client", ("task31",)),
    "downstream": ("task37-downstream", ()),
}
# the predecessor whose repeats the downstream file takes (it has no
# counts to take; its size rule is TASK30's)
DOWNSTREAM_REPEATS_FROM = "task30"
RULES = {
    "matrix": (
        "each cell takes the steady count its originating task "
        "predeclared: the TASK29B cases' cells those of "
        "allocation_iterations.json, the TASK30 cases' cells those of "
        "allocation_iterations_task30.json, so that TASK37 measures every "
        "cell exactly as its task did; a cell without a predecessor count "
        "is refused; fixed before any observation, identical for both "
        "sides, never calibrated"),
    "client": (
        "each cell takes the steady count TASK31 predeclared "
        "(allocation_iterations_task31.json: the TASK30 size rule, <=100 "
        "-> 32, 1000 -> 16, 10000 -> 8, with the reuse and complete "
        "stages of some tactic families at 1000 halved or quartered to "
        "fit the process timeout), so that TASK37 measures every cell "
        "exactly as TASK31 did; a cell without a predecessor count is "
        "refused; fixed before any observation, identical for both sides, "
        "never calibrated"),
    "downstream": (
        "TASK30 size rule (<=100 -> 32, size 0 included, 1000 -> 16, "
        "10000 -> 8); the downstream workloads have no predecessor count; "
        "fixed before any observation, identical for both sides, never "
        "calibrated"),
}


def size_rule(size):
    """The TASK30 size rule."""
    return 32 if size <= 100 else 16 if size == 1000 else 8


def predecessor(task):
    """(task, its validated counts document) of the predecessor `task`."""
    import allocation_matrix as m
    found = m.TASKS[task]
    return found, m.load_iterations(task=found)


def counts_of(table):
    """(repeats, {cell name: steady count}) of `table`, in the order of the
    task's cells."""
    import allocation_matrix as m
    name, predecessors = TABLES[table]
    task = m.TASKS[name]
    keys = m.keys(task)
    if not predecessors:
        _, base = predecessor(DOWNSTREAM_REPEATS_FROM)
        return base["repeats"], {m.name_of(*k): size_rule(k[1])
                                 for k in keys}
    found = [predecessor(p) for p in predecessors]
    repeats = {doc["repeats"] for _, doc in found}
    a.require(len(repeats) == 1, "the predecessors of %s have different "
              "repeats: %s" % (table, sorted(repeats)))
    steady = {}
    for case, size in keys:
        cell = m.name_of(case, size)
        owners = [doc for t, doc in found if case in t.cases]
        a.require(len(owners) == 1 and cell in owners[0]["steady"],
                  "no predecessor count for the cell %s of %s: refused "
                  "(there is no default count)" % (cell, table))
        steady[cell] = owners[0]["steady"][cell]
    return repeats.pop(), steady


def document(table):
    repeats, steady = counts_of(table)
    return dict(schema=SCHEMA, repeats=repeats, rule=RULES[table],
                steady=steady)


def text(table):
    return json.dumps(document(table), indent=1, allow_nan=False) + "\n"


def path_of(table, directory=None):
    """The counts file of `table`: the one its allocation task names (in
    `directory`, if given)."""
    import allocation_matrix as m
    path = m.TASKS[TABLES[table][0]].iterations
    return path if directory is None else Path(directory) / path.name


def write(table, directory=None):
    """Write the counts file of `table`; a file that exists must be what the
    rule gives (it is then left as it is)."""
    path = path_of(table, directory)
    wanted = text(table)
    if path.exists():
        a.require(path.read_text() == wanted,
                  "%s exists and is not the rule's output: a counts file "
                  "is never overwritten (--check shows the difference)"
                  % path)
        return path
    path.write_text(wanted)
    return path


def check(table, directory=None):
    """The problems of the committed counts file of `table` (none when it is
    the rule's output)."""
    path = path_of(table, directory)
    if not path.is_file():
        return ["%s is missing" % path]
    if path.read_text() != text(table):
        return ["%s is not the output of the rule" % path]
    return []


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("table", choices=sorted(TABLES) + ["all"])
    parser.add_argument("--check", action="store_true",
                        help="verify the committed files, write nothing")
    parser.add_argument("--directory", type=Path,
                        help="the place of the files (default: here)")
    args = parser.parse_args(argv)
    tables = sorted(TABLES) if args.table == "all" else [args.table]
    try:
        if args.check:
            problems = [p for t in tables
                        for p in check(t, args.directory)]
            for problem in problems:
                print("FAIL " + problem, file=sys.stderr)
            return 1 if problems else 0
        for t in tables:
            print("wrote " + str(write(t, args.directory)))
    except ValueError as error:
        print("REFUSED: %s" % error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
