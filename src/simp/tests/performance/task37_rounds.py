#!/usr/bin/env python3
"""TASK37 follow-up rounds (design decision 47): a targeted follow-up of the
cells that stay inconclusive after a shard's follow-up (round 1,
task37_followup.py, whose text this module never changes), and of the cells
that stay so after round 2, and so on.

A round R >= 2 is a table of timing_grid.py with NO `replaces` link: the
engine cannot replay a follow-up of a follow-up (its binding of a replaced
grid replays that grid with the pilot of the grid it replaces, and a
follow-up replaced in turn would need a chain of replaced pilots), so a
round measures its cells as a fresh targeted table. What binds it to the
rounds before it is its declaration, the commit order and the pairs rule,
all checked here and again by task37_dispose.py. The table of round R is
`task37-<shard>-followup<R>` (label `TASK37-<SHARD>-FOLLOWUP<R>`), its
counts file `task37_<kind>_<n>_followup<R>_iterations.json`, its layout seed
`<table name>-layout-1`, and it takes the shard's family (so its attempts go
into the shard's ledger), seconds, samples, schedule, baseline, sources, pins
and limits exactly as round 1 does. Its command line key is `SHARD.R`
(`matrix-4.2`); round 1 keeps `SHARD` (task37_followup.py).

Each round R >= 2 needs its own recorded decision of the user (the policy
owner); nothing else limits the number of rounds. A round declared without
one is out of protocol, and the disposition record cites the decision of
each round (the "decision" field below).

A round is declared by one data file, committed alone,
`task37_<kind>_<n>_followup<R>_cells.json`:

  {"schema": "task37-followup-round-v1", "shard": "matrix-4", "round": 2,
   "cells": ["compile_ac-1000"], "pairs": 80,
   "decision": "<reference to the recorded user decision>"}

where "shard" and "round" are those of the file name (R >= 2), the cells are
EXACTLY the cells round R-1 left inconclusive (a cell cannot be left out
after the candidate is seen; the file names them, without repeats, a subset
of the cells round R-1 declared: round 1's is
task37_followup.load_declaration; that they are all the inconclusive ones is
checked against round R-1's decisions by `derive-pairs`, `predeclare` and
task37_dispose.py), "pairs" is a positive integer (the table has one pair
count for all its cells) and "decision" is a non-empty reference to the
recorded user decision that authorized the round. Round R is declared only
if rounds 1..R-1 are (a gap is refused). This module discovers the files
that exist; its text never changes on a declaration.

The pairs rule. The pairs are fixed by the develop/develop control of the
round before, and nothing of a candidate: for a cell of round R-1, w is the
control half width (`timing_grid.control_half_width`) of its report in
round R-1's decisive stage (its second stage if the cell had one, else its
first), P the pairs of that report, and the cell's pairs are
`timing_grid.second_stage_pairs(w, P, target, cap)` with the target and cap
of the shard (the limits the stage's counts record). The table has one pair
count, so the declared "pairs" is the largest of the cells' (a cell with
fewer is measured with more than its rule, none with less). `derive-pairs`
prints them and the declaration to commit:

  task37_rounds.py SHARD.R derive-pairs --grid DIR

(read-only; DIR is the LAST stage of round R-1, its extension where it has
one, and a first stage whose second stage is still to come is refused; the
cells are every cell that stage left inconclusive; it recomputes the cells'
reports from the archives, as the replay of that stage does, without the
checks of its code and checkout, which `replay` and task37_dispose.py make;
the declaration it prints has a placeholder "decision" to replace). The
`predeclare` command of a round takes the same stage as a required
`--after DIR` and checks the declaration's cells and pairs against it before
anything else, so a wrong declaration is found before a decision-grade
measurement.

Order. The declaration of round R is committed alone, is a descendant of the
commit of EVERY counts file of round R-1 (its first file, round 1's:
task37_followup.file_of, and each revision of it) in the candidate's
history, is an ancestor of the pilot's checkout head, and of the commit of
round R's counts file. The engine (`Rounds`) checks that wherever it reads
a counts commit, and task37_dispose.py again.

  task37_rounds.py SHARD.R COMMAND ...

with the engine's commands (`prepare`, `pilot`, `predeclare`,
`verify-counts`, `run`, `extend`, `replay`; none takes `--replaces`: a round
replaces no grid). Round R seals the shard's sealed files, task37_followup.py
and every declaration file of rounds 1..R. GRIDS holds the engines declared,
by table name; task37_dispose.py takes them (`--followup SHARD.R=DIR`,
`--followup-pilot SHARD.R=DIR`).
"""
import argparse
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task37_cases as cases
import task37_followup as followup
import task37_grid as base
import timing_grid as tg

SCHEMA = "task37-followup-round-v1"
# The latest round a file name can declare (a guard, not a policy).
MAX_ROUND = 9
# The round pattern below is one digit.
assert 2 <= MAX_ROUND <= 9
# What `derive-pairs` prints for "decision"; no declaration holds it.
PLACEHOLDER = "REPLACE-WITH-THE-RECORDED-USER-DECISION"


def parse_key(text):
    """(shard key, round) of a command line key: `matrix-4` is round 1
    (task37_followup.py's), `matrix-4.2` round 2; `.1` is refused (round 1
    has no suffix)."""
    shard, sep, number = str(text).partition(".")
    a.require(shard in base.SHARD_KEYS, "no such shard: %r" % (text,))
    if not sep:
        return shard, 1
    a.require(re.fullmatch("[2-%d]" % MAX_ROUND, number) is not None and
              int(number) <= MAX_ROUND,
              "no such follow-up round: %r (rounds are 2..%d; round 1 is "
              "the shard key alone)" % (text, MAX_ROUND))
    return shard, int(number)


def key_text(key, number):
    return key if number == 1 else "%s.%d" % (key, number)


def declaration_file(key, number):
    """The declaration file of round `number` >= 2 of a shard."""
    a.require(key in base.SHARD_KEYS and 2 <= number <= MAX_ROUND,
              "no such follow-up round: %s.%r" % (key, number))
    kind, shard = key.split("-")
    return a.HERE / ("task37_%s_%s_followup%d_cells.json" % (
        kind, shard, number))


def declaration_name(key, number):
    """The file name of the declaration of any round (1 included)."""
    return (followup.declaration_file(key) if number == 1 else
            declaration_file(key, number)).name


def name_of(key, number):
    """The table name of round `number` >= 2."""
    a.require(2 <= number <= MAX_ROUND, "no such follow-up round")
    return base.name_of(key) + "-followup%d" % number


def file_of(key, number):
    """The counts file of round `number` >= 2 (round 1's:
    task37_followup.file_of)."""
    kind, shard = key.split("-")
    return a.HERE / ("task37_%s_%s_followup%d_iterations.json" % (
        kind, shard, number))


def previous_cells(key, number):
    """The cells round `number` - 1 declared: a refusal if it is not
    declared (a gap)."""
    if number == 2:
        a.require(followup.declaration_file(key).exists(),
                  "round 2 of %s needs the follow-up (round 1) declared "
                  "first" % key)
        return followup.load_declaration(key)
    path = declaration_file(key, number - 1)
    a.require(path.exists(), "round %d of %s is declared while round %d is "
              "not (a gap): declare the rounds in order" % (
                  number, key, number - 1))
    return load_declaration(key, number - 1)["cells"]


def load_declaration(key, number, path=None, previous=None):
    """{cells, pairs, decision} the declaration file of round `number` of
    shard `key` (or `path`, for a test; `previous`: the cells of the round
    before, for a test) declares, validated: the schema, the shard and round
    of the file name, a non-empty subset of the cells of the round before
    without repeats (that they are all the cells it left inconclusive needs
    its decisions: `check_cells`), a positive integer of pairs and the
    reference to the recorded user decision. Round `number` needs the rounds
    before it declared."""
    a.require(key in base.SHARD_KEYS, "no such shard: %r" % (key,))
    path = declaration_file(key, number) if path is None else path
    before = previous_cells(key, number) if previous is None else previous
    found = a.load(path)
    a.require(isinstance(found, dict) and set(found) == {
        "schema", "shard", "round", "cells", "pairs", "decision"} and
        found["schema"] == SCHEMA,
        "%s is not a %s declaration" % (path, SCHEMA))
    a.require(found["shard"] == key and type(found["round"]) is int and
              found["round"] == number,
              "%s declares round %r of %r, not round %d of the shard %s of "
              "its file name" % (path, found["round"], found["shard"],
                                 number, key))
    cells, pairs = found["cells"], found["pairs"]
    decision = found["decision"]
    a.require(isinstance(decision, str) and decision.strip() and
              decision != PLACEHOLDER,
              "%s declares no decision: \"decision\" is a non-empty "
              "reference to the recorded user decision of the round" % path)
    a.require(isinstance(cells, list) and cells and all(
        isinstance(c, str) for c in cells) and
        len(set(cells)) == len(cells) and set(cells) <= set(before),
        "%s declares cells that are not a non-empty subset of the cells "
        "of round %d of shard %s, or repeats one" % (path, number - 1, key))
    a.require(type(pairs) is int and pairs > 0,
              "%s declares pairs that are not a positive integer" % path)
    return dict(cells=tuple(cells), pairs=pairs, decision=decision)


def declared():
    """{shard key: {round: declaration}} of the declaration files that
    exist (a round after a gap is refused)."""
    found = {}
    for key in base.SHARD_KEYS:
        for number in range(2, MAX_ROUND + 1):
            if declaration_file(key, number).exists():
                found.setdefault(key, {})[number] = load_declaration(
                    key, number)
    return found


# -------------------------------------------------------------- the order

def declaration_commit(repo, candidate, path):
    """The one commit of the history of `candidate` that introduced the
    declaration file `path`; the file is the committed one and that commit
    changed nothing else (as task37_followup.declaration_commit, for the
    file of any round)."""
    name = tg.repo_relative(repo, path)
    try:
        commit = tg.git_introduced(repo, candidate, name)
    except ValueError as error:
        raise ValueError("the declaration file %s is not committed in the "
                         "history of %s (an untracked or uncommitted "
                         "declaration declares nothing): %s" % (
                             name, str(candidate)[:12], error)) from None
    a.require(tg.git_blob(repo, candidate, name) ==
              a.git(repo, "hash-object", str(path)),
              "the declaration file %s is not the committed one" % name)
    a.require(set(tg.git_touched(repo, commit)) == {name},
              "the commit %s that introduced %s must change only that "
              "file: commit the declaration alone" % (commit[:12], name))
    return commit


def previous_counts_files(key, number):
    """Every counts file of round `number` - 1: its first file and each
    revision of it."""
    return engine_before(key, number).t.files()


def previous_counts_commits(repo, candidate, key, number):
    """{counts file name: the commit that introduced it, in the history of
    `candidate`} for every counts file of round `number` - 1."""
    found = {}
    for path in previous_counts_files(key, number):
        name = tg.repo_relative(repo, path)
        found[name] = tg.git_introduced(repo, candidate, name)
    return found


def check_after_previous(repo, candidate, key, number, commit):
    """The declaration commit follows the commit of every counts file of
    round `number` - 1 (so no revision of it is made after round
    `number` is declared)."""
    for name, prior in previous_counts_commits(
            repo, candidate, key, number).items():
        a.require(prior != commit and
                  followup.is_ancestor(repo, prior, commit),
                  "the declaration of round %d of %s (commit %s) is not a "
                  "descendant of the commit %s of round %d's counts file "
                  "%s: declare a round after the one before it, revisions "
                  "included" % (number, key, commit[:12], prior[:12],
                                number - 1, name))


def check_declaration_order(repo, candidate, key, number, counts_commit):
    """The declaration of round `number` was committed alone, after every
    counts file of round `number` - 1 and before (an ancestor of) the commit
    of this round's counts file `counts_commit`."""
    path = declaration_file(key, number)
    commit = declaration_commit(repo, candidate, path)
    a.require(commit != counts_commit and
              followup.is_ancestor(repo, commit, counts_commit),
              "the declaration %s (commit %s) is not an ancestor of the "
              "commit %s of the round's counts file: declare the round "
              "before its counts are made" % (
                  path.name, commit[:12], counts_commit[:12]))
    check_after_previous(repo, candidate, key, number, commit)


def check_declaration_at_pilot(repo, key, number, head):
    """The declaration of round `number` was committed alone before the
    pilot (an ancestor of, or, `head`), after every counts file of round
    `number` - 1."""
    path = declaration_file(key, number)
    commit = declaration_commit(repo, head, path)
    a.require(followup.is_ancestor(repo, commit, head),
              "the declaration %s (commit %s) is not an ancestor of the "
              "pilot's checkout head %s" % (path.name, commit[:12],
                                            head[:12]))
    check_after_previous(repo, head, key, number, commit)


# ----------------------------------------------------------------- tables

def table(key, number, cells, pairs, revisions=None):
    """The table of round `number` >= 2 of shard `key` for `cells` with
    `pairs`: a targeted table (no `replaces`), the constants of round 1's
    (task37_followup.table) apart from the pairs."""
    a.require(2 <= number <= MAX_ROUND, "no such follow-up round")
    cells = tuple(cells)
    kind = base.KIND[key]
    first = base.GRIDS[base.name_of(key)].t
    a.require(cells and set(cells) <= set(base.PARTS[key]),
              "a follow-up measures cells of its shard")
    a.require(type(pairs) is int and 0 < pairs <= first.max_pairs,
              "the pairs of a round are positive and at most the cap")
    found = tuple(dict.fromkeys(cases.split(c)[0] for c in cells))
    if revisions is None:
        revisions = base.revisions_of(file_of(key, number))
    name = name_of(key, number)
    return tg.Table(
        name, "TASK37-%s-FOLLOWUP%d" % (key.upper(), number), found,
        __file__, file_of(key, number), revisions=revisions, cells=cells,
        family=first.family, seconds=base.SECONDS,
        seconds_by_case={c: base.LONG_SECONDS for c in found
                         if c in base.LONG[kind]},
        fixed_seconds=True, schedule="warmup", headroom=1,
        target=first.target, max_pairs=first.max_pairs,
        pairs=pairs, samples=base.SAMPLES,
        seed="%s-layout-1" % name, baseline=a.BASE, engine=True,
        engines=base.ENGINES, drivers=base.DRIVERS,
        layout_acceptance=base.ACCEPTANCE,
        sealed_history=base.SEALED_HISTORY, tree="src",
        sealed=followup.SEALED[key] + ("task37_followup.py",) + tuple(
            declaration_name(key, i) for i in range(1, number + 1)),
        require_seed=True, sources=first.sources,
        pinned=first.pinned, pin_file=first.pin_file,
        pin_history=first.pin_history, allocation=first.allocation)


class Rounds(tg.Grid):
    """The engine of a round: the shared engine, and the declaration order
    is checked at the pilot and at every counts commit it reads."""

    def __init__(self, table, key, number, doc=None):
        super().__init__(table, doc=doc)
        self.key, self.number = key, number

    def pilot(self, args):
        head = a.git(args.repo, "rev-parse", "HEAD").strip()
        check_declaration_at_pilot(args.repo, self.key, self.number, head)
        return super().pilot(args)

    def check_pilot_settings(self, inventory, seconds=None):
        super().check_pilot_settings(inventory, seconds)
        head = (inventory.get("checkout") or {}).get("head")
        a.require(isinstance(head, str) and head,
                  "the pilot inventory records no checkout head")
        check_declaration_at_pilot(followup.repo_of_code(), self.key,
                                   self.number, head)

    def counts_commit(self, repo, candidate, path):
        commit = super().counts_commit(repo, candidate, path)
        check_declaration_order(repo, candidate, self.key, self.number,
                                commit)
        return commit

    def parser(self):
        """`predeclare` names the last stage of the round before
        (`--after`), required."""
        parser, sub = super().parser()
        sub.choices["predeclare"].add_argument(
            "--after", type=Path, required=True, metavar="DIR",
            help="the LAST stage of round %d (its extension where it has "
            "one): the declaration's cells and pairs are checked against it "
            "before anything else" % (self.number - 1))
        return parser, sub

    def check_after(self, grid):
        """The declaration's cells and pairs agree with the last stage of
        the round before (`derive_pairs` gives the same)."""
        before = engine_before(self.key, self.number)
        root = Path(grid).resolve()
        check_cells(open_cells(a.load(root / "decisions.json")),
                    self.t.names(), self.number)
        check_pairs(before, stage_reports(before, root), self.t.names(),
                    self.t.pairs)

    def dispatch(self, args):
        if args.action == "predeclare":
            self.check_after(args.after)
        return super().dispatch(args)


def declare(key, number, declaration):
    """The (table, engine) of round `number` of shard `key`."""
    built = table(key, number, declaration["cells"], declaration["pairs"])
    return built, Rounds(built, key, number, doc=__doc__)


# The rounds of each shard, {shard key: {round: declaration}}, read from the
# declaration files; none until a policy decision declares one.
DECLARED = declared()
TABLES, GRIDS = {}, {}
for _key, _rounds in DECLARED.items():
    for _number, _declaration in _rounds.items():
        _found = declare(_key, _number, _declaration)
        TABLES[_found[0].name], GRIDS[_found[0].name] = _found


def commands():
    """The engines by the key a command line gives them (`matrix-4.2`)."""
    return {key_text(k, n): GRIDS[name_of(k, n)]
            for k, rounds in DECLARED.items() for n in rounds}


# ------------------------------------------------------------ pairs rule

def engine_before(key, number):
    """The engine of round `number` - 1 (round 1's is task37_followup's)."""
    name = (followup.name_of(key) if number == 2 else
            name_of(key, number - 1))
    found = {**followup.GRIDS, **GRIDS}.get(name)
    a.require(found is not None, "round %d of %s is not declared: no "
              "engine for %s" % (number - 1, key, name))
    return found


def stage_reports(engine, grid):
    """What the last stage `grid` of `engine`'s table holds, recomputed
    from its archives (as its replay does, but without the checks of its
    code and checkout; a first stage with a second stage still to come is
    refused, as `bind_replaced` refuses it): {inventory, first (the first
    stage's inventory), stage1, stage2: {(case, size): report}}."""
    root = Path(grid).resolve()
    inventory = a.load(root / "inventory.json")
    if inventory["schema"] == engine.t.schema("extension"):
        first_root = (root / inventory["grid"]).resolve()
        a.require(a.seal(first_root / "inventory.json") ==
                  inventory["grid_inventory"] and
                  a.seal(first_root / "decisions.json") ==
                  inventory["grid_decisions"],
                  "changed first-stage grid")
        first = a.load(first_root / "inventory.json")
        return dict(inventory=inventory, first=first,
                    stage1=engine.replay_rows(first_root, first),
                    stage2=engine.replay_rows(root, inventory))
    a.require(inventory["schema"] == engine.t.schema("experiment"),
              "%s is not a stage of %s" % (root, engine.t.name))
    stage1 = engine.replay_rows(root, inventory)
    a.require(not engine.planned(stage1, inventory),
              "%s is not final: its second stage is still to come, name "
              "the second stage" % root)
    return dict(inventory=inventory, first=inventory, stage1=stage1,
                stage2={})


def decisive_pairs(engine, found, names):
    """{cell name: pairs the rule gives it} from the decisive stage `found`
    (`stage_reports`, or the `replayed` of the engine's replay): a cell's
    report is that of the second stage where it has one, its pairs those of
    the plan, else those of the first stage's counts."""
    first, inventory = found["first"], found["inventory"]
    plan = {(c, s): p for c, s, p in inventory.get("plan") or []}
    limits = engine.limits_of(first) or (engine.t.target,
                                         engine.t.max_pairs)
    reports = {"%s-%d" % k: (k, r) for k, r in found["stage1"].items()}
    reports.update({"%s-%d" % k: (k, r) for k, r in found["stage2"].items()})
    result = {}
    for name in names:
        a.require(name in reports, "round %s has no report of the cell %s"
                  % (engine.t.name, name))
        key, report = reports[name]
        a.require(report["success"], "a cell the previous round did not "
                  "measure: " + name)
        pairs = plan[key] if key in found["stage2"] else engine.cell_pairs(
            first["iterations"], key, first["pairs"])
        (workload,) = report["workloads"]
        result[name] = tg.second_stage_pairs(
            tg.control_half_width(workload), pairs, *limits)
    return result


def declared_pairs(engine, found, names):
    """The one pair count of a round measuring `names`: the largest the
    rule gives a cell, with the per-cell values."""
    per = decisive_pairs(engine, found, sorted(names))
    return max(per.values()), per


def check_pairs(engine, found, names, pairs):
    """The pairs a round declares are the rule's for the cells it measures,
    from the decisive stage of the round before (`engine`, `found`)."""
    want, per = declared_pairs(engine, found, names)
    a.require(pairs == want, "the round declares %d pairs; the rule gives "
              "%d (per cell %s) from %s" % (
                  pairs, want, json.dumps(per, sort_keys=True),
                  engine.t.name))


def open_cells(decisions):
    """The cells a stage's decisions leave inconclusive, sorted."""
    return sorted("%s-%d" % (w["case"], w["size"])
                  for w in decisions["workloads"]
                  if tg.classify_row(w) == "inconclusive")


def check_cells(opened, names, number):
    """The cells of round `number` are exactly the cells round `number` - 1
    left inconclusive (`opened`): a round cannot take a subset, which could
    be chosen after the candidate is seen."""
    a.require(opened and sorted(names) == sorted(opened),
              "the cells of round %d must be exactly the cells round %d "
              "left inconclusive (%s), not %s" % (
                  number, number - 1, ", ".join(opened) or "none",
                  ", ".join(sorted(names)) or "none"))


def derive_pairs(key, number, grid):
    """(declaration, per-cell pairs) for round `number` from `grid`, the
    last stage of round `number` - 1: the cells are all the cells it left
    inconclusive. The declaration's "decision" is a placeholder."""
    engine = engine_before(key, number)
    root = Path(grid).resolve()
    chosen = open_cells(a.load(root / "decisions.json"))
    check_cells(chosen, chosen, number)
    pairs, per = declared_pairs(engine, stage_reports(engine, root), chosen)
    return dict(schema=SCHEMA, shard=key, round=number, cells=chosen,
                pairs=pairs, decision=PLACEHOLDER), per


def derive_main(key, number, argv):
    parser = argparse.ArgumentParser(
        prog="task37_rounds.py %s derive-pairs" % key_text(key, number),
        description="the cells and pairs of a round from the last stage of "
        "the round before (read-only)")
    parser.add_argument("--grid", type=Path, required=True,
                        help="the LAST stage of round %d (its extension "
                        "where it has one)" % (number - 1))
    args = parser.parse_args(argv)
    declaration, per = derive_pairs(key, number, args.grid)
    for name, pairs in sorted(per.items()):
        print("%s: %d pairs by the rule" % (name, pairs))
    print("declare (all the cells it left inconclusive, the largest pairs "
          "for all of them; replace \"decision\" by the reference to the "
          "recorded user decision):")
    print(json.dumps(declaration, sort_keys=True))
    return 0


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    found = commands()
    try:
        key, number = parse_key(argv[0]) if argv else (None, 1)
    except ValueError:
        key = None
    if key is not None and number >= 2 and argv[1:2] == ["derive-pairs"]:
        return derive_main(key, number, argv[2:])
    if not argv or argv[0] not in found:
        print("REFUSED: no such TASK37 follow-up round is declared "
              "(declared: %s; the declaration files): task37_rounds.py "
              "SHARD.R COMMAND ..." % (",".join(found) or "none"),
              file=sys.stderr)
        return tg.REFUSED
    return found[argv[0]].main(argv[1:])


if __name__ == "__main__":
    sys.exit(main())
