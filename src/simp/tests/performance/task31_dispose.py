#!/usr/bin/env python3
"""The TASK31 decision per cell: identity, allocation and timing together.

A cell passes if and only if

- gate 1: its identity row is `identical` or `attributed`
  (task31_grid.py `identity`; `different` fails);
- gate 2: the allocation grid measured it and decided `pass`, where that
  gate measures it (every cell but the infeasible ones);
- gate 3: the timing table decided `pass`, where the cell is sampled
  (task31_cases.SAMPLE).

A gate that decided against a cell makes it `fail`. A gate with no decision
for a cell it must decide leaves it `incomplete`: that is also a timing
class that is not a decision (`inconclusive`, `control_limited`,
`protocol`), named in the cell's record, and an identity grid that is
inconclusive. Nothing is excused here.

The 33 infeasible cells (task31_cases.INFEASIBLE) pass by identity alone and
are recorded as "untimed, unallocated: infeasible", with the numbers of the
cost survey the command is given (`--survey`, a file of the shape
survey_cells below; its sha256 is recorded and `--check` reads it again).
When their identity is `attributed`, the record names the attribution and the
cells of the same family that measured it (allocation cells of at most 1000
assumptions that passed with an attributed identity, and the family's cells of
the timing sample that passed); an infeasible attributed cell with none of
either is `incomplete`.

The command replays what it reads: the identity grid (every archive, every
decision), and the timing grid (`task31_grid.py replay`, in full, with its
pilot). A follow-up (`--followup`, `--followup-pilot`: task31_followup.py)
replaces the cells of the first grid that it measured again. The allocation
grid is read through its `decisions.json`, whose contract is the following
and nothing more (PROTOCOL.md, "TASK31"):

    {"candidate": COMMIT,                 # optional: checked when present
     "rows": [{"case": CASE, "size": N, "decision": "pass" | "fail"}, ...]}

One row per cell, no repeated cell, and each cell one the allocation gate
measures; any other decision is refused. The gate's own replay (and the
grid's other fields) are not this module's: the allocation gate is run and
replayed by allocation_matrix.py, whose verdict the caller reads.

The record carries the seals of the code (`CODE`, with `HISTORY` for earlier
versions a record was made by) and of every input it read. The exit status
is 0 when every cell passes, 1 when a cell does not, 2 when the evidence is
not conclusive (a gate has no decision for a cell it must decide), 3 when the
command is refused. The last line printed is the verdict.
"""
import argparse
import contextlib
import io
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import acceptance as a
import task31_attribution as attr
import task31_cases as cases
import task31_followup as follow
import task31_grid as grid
import timing_grid as tg

SCHEMA = "task31-disposition-v1"
SURVEY_SCHEMA = "task31-cost-survey-v1"
SURVEY_FIELDS = ("op1000", "setup1000", "check1000", "op10000",
                 "setup10000", "check10000")
INFEASIBLE_TEXT = "untimed, unallocated: infeasible"
# The measurement of an attribution in a family stops at this size of
# assumptions for the allocation cells.
ALLOCATION_LIMIT = 1000
# The code whose change must be named in HISTORY once a disposition is
# recorded.
CODE = ("task31_dispose.py", "task31_grid.py", "task31_followup.py",
        "task31_identity.py", "task31_attribution.py", "task31_cases.py",
        "timing_grid.py", "acceptance.py")
# Per file of CODE, the seals it had when a disposition was recorded, once it
# has changed since.
HISTORY = {}


def seals():
    return {name: a.seal(a.HERE / name) for name in CODE}


def check_code(recorded):
    """The seals a disposition records are those of the code now or of an
    earlier version HISTORY names; the refusal names every file that is not
    and the entry to add."""
    now = seals()
    a.require(isinstance(recorded, dict) and set(recorded) == set(CODE),
              "changed TASK31 disposition: the recorded code is not %s"
              % ", ".join(CODE))
    changed = [n for n in CODE if recorded[n] != now[n] and
               recorded[n] not in HISTORY.get(n, ())]
    a.require(not changed, "changed TASK31 disposition: %s changed since it "
              "was recorded; add the seal it was recorded by to "
              "task31_dispose.HISTORY: %s" % (", ".join(changed), "; ".join(
                  "%s: %s" % (n, json.dumps(recorded[n], sort_keys=True))
                  for n in changed)))


def load_survey(path):
    """The cost survey: {cell: {op1000, ..., check10000}} for each
    infeasible cell and the process timeout, as the file says."""
    found = json.loads(Path(path).read_text())
    a.require(isinstance(found, dict) and
              found.get("schema") == SURVEY_SCHEMA and
              isinstance(found.get("cells"), dict) and
              isinstance(found.get("process_timeout"), (int, float)),
              "not a TASK31 cost survey: %s" % path)
    for name in cases.INFEASIBLE:
        row = found["cells"].get(name)
        a.require(isinstance(row, dict) and set(row) == set(SURVEY_FIELDS)
                  and all(isinstance(v, (int, float)) and v >= 0
                          for v in row.values()),
                  "the survey has no usable numbers for " + name)
    return dict(cells={n: found["cells"][n] for n in cases.INFEASIBLE},
                process_timeout=found["process_timeout"],
                seal=a.seal(Path(path)))


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


def family_of(name):
    """The family of a tactic cell: tactic_FAMILY_STAGE-SIZE."""
    case = grid.case_of(name)
    for family in cases.FAMILIES:
        if case in ("tactic_%s_%s" % (family, stage)
                    for stage in cases.STAGES):
            return family
    return None


def size_of(name):
    return int(name.rsplit("-", 1)[1])


def measured_by(name, identity, allocated, timed):
    """The cells of the family of an infeasible cell that measured its
    attribution: allocation cells of at most ALLOCATION_LIMIT assumptions
    that passed with an attributed identity (the grid has one reviewed
    table), and the cells of the timing sample that passed (the sample's
    `complete` stage at 100 assumptions and any other cell of the family)."""
    family = family_of(name)
    if family is None:
        return dict(allocation=[], timing=[])
    cells = [n for n in identity if family_of(n) == family and
             n not in cases.INFEASIBLE]
    return dict(
        allocation=sorted(
            n for n in cells if size_of(n) <= ALLOCATION_LIMIT and
            allocated.get(n) == "pass" and
            identity[n]["status"] == "attributed"),
        timing=sorted(n for n in cells if n in cases.SAMPLE and
                      timed.get(n) == "pass"))


def judge(name, identity, allocated, timed, survey, groups):
    """One cell: its record. `identity` is the cell's identity decision,
    `allocated` the allocation decision or None, `timed` the timing class or
    None, `survey` the numbers of the cost survey, `groups` what measured
    the attribution (see `measured_by`). A gate with no decision for a cell
    it must decide leaves the cell `incomplete`; a gate that decided
    against it makes it `fail`."""
    infeasible = name in cases.INFEASIBLE
    found = dict(identity=identity["status"], allocation=allocated,
                 timing=timed)
    failed, missing = [], []
    if identity["status"] == "different":
        failed.append("identity: the loaded closure or the work differs")
    elif identity["status"] not in ("identical", "attributed"):
        missing.append("identity: " + identity["status"])
    found["attribution"] = [
        dict(path=r["path"], reason=r["reason"])
        for r in identity.get("attributed", [])]
    if infeasible:
        found["note"] = INFEASIBLE_TEXT
        found["survey"] = survey
        found["route"] = identity.get("route")
        found["derived_from"] = identity.get("derived_from")
        if identity["status"] == "attributed":
            found["measured_by"] = groups
            if not (groups["allocation"] and groups["timing"]):
                missing.append("attribution not measured in its family: "
                               "allocation %d cell(s), timing %d cell(s)"
                               % (len(groups["allocation"]),
                                  len(groups["timing"])))
    else:
        if allocated is None:
            missing.append("allocation: no decision")
        elif allocated != "pass":
            failed.append("allocation: " + allocated)
    if name in cases.SAMPLE:
        if timed is None:
            missing.append("timing: no decision")
        elif timed == "fail":
            failed.append("timing: fail")
        elif timed != "pass":
            missing.append("timing: " + timed.replace("_", "-"))
    elif timed is not None:
        failed.append("timing: a cell outside the sample")
    found["failed"], found["missing"] = failed, missing
    found["status"] = ("fail" if failed else
                       "incomplete" if missing else "pass")
    return found


def dispose(identity, allocated, timed, survey):
    """Every cell's record and the status of the whole, from the decisions
    of the three gates. `survey` is the numbers of the infeasible cells."""
    names = [grid.name_of(*k) for k in grid.every()]
    a.require(set(identity["cells"]) == set(names) and
              not identity["diagnostic"],
              "the identity grid is not the whole grid")
    cells = identity["cells"]
    records = {}
    for n in names:
        groups = measured_by(n, cells, allocated, timed) \
            if n in cases.INFEASIBLE else None
        records[n] = judge(n, cells[n], allocated.get(n), timed.get(n),
                           survey.get(n), groups)
    counts = {k: sum(r["status"] == k for r in records.values())
              for k in ("pass", "fail", "incomplete")}
    grid_failed = identity["status"] == "different"
    status = ("fail" if counts["fail"] or grid_failed else
              "incomplete" if counts["incomplete"] or
              identity["status"] == "inconclusive" else "pass")
    return dict(schema=SCHEMA, status=status, counts=counts,
                infeasible=sum(n in cases.INFEASIBLE for n in names),
                identity_status=identity["status"],
                identity_unaccounted=identity.get("unaccounted", []),
                attributed=identity.get("attributed", []),
                attribution_table=identity.get("attribution_table"),
                cells=records)


def lines(record, timeout=cases.PROCESS_TIMEOUT):
    out = []
    for path in record["identity_unaccounted"]:
        out.append("FAIL identity grid: unaccounted difference " + path)
    for name, found in record["cells"].items():
        if found["status"] == "pass" and name not in cases.INFEASIBLE:
            continue
        why = found["failed"] + found["missing"]
        if name in cases.INFEASIBLE:
            cost = found.get("survey") or {}
            note = INFEASIBLE_TEXT + " (survey: op %.3g s, setup %.3g s, " \
                "check %.3g s at 10000; timeout %d s)" % (
                    cost.get("op10000", float("nan")),
                    cost.get("setup10000", float("nan")),
                    cost.get("check10000", float("nan")), timeout)
            if found["identity"] == "attributed":
                note += "; attributed " + ", ".join(
                    r["path"] for r in found["attribution"])
            why = why or [note]
        out.append("%s %s: %s" % (found["status"].upper(), name,
                                  "; ".join(why)))
    return out


def seal_of(path):
    return a.seal(Path(path))


def derive(args):
    repo = args.repo
    survey = load_survey(args.survey)
    with contextlib.redirect_stdout(io.StringIO()):
        a.require(grid.identity_replay(argparse.Namespace(
            output=args.identity, repo=repo, attributed=args.attributed,
            ledger=None)) in (0, 1, 2), "the identity grid is not replayable")
    identity = a.load(args.identity.resolve() / "decisions.json")
    inventory = a.load(args.identity.resolve() / "inventory.json")
    timing = a.load(args.grid.resolve() / "inventory.json")
    a.require(timing["candidate"] == inventory["candidate"] and
              timing["baseline"] == inventory["baseline"],
              "the timing grid and the identity grid have another "
              "candidate or baseline")
    a.require(timing.get("checkout") == inventory.get("checkout"),
              "the identity grid and the timing grid ran in different "
              "checkouts (head, tree outside the performance area, "
              "products)")
    tg_code = grid.ENGINE.replay(argparse.Namespace(
        output=args.grid.resolve(), partial=False, repo=repo,
        pilot=args.pilot.resolve(), ledger=args.ledger))
    timed_decisions = a.load(args.grid.resolve() / "decisions.json")
    inputs = dict(
        identity_inventory=seal_of(args.identity / "inventory.json"),
        identity_decisions=seal_of(args.identity / "decisions.json"),
        timing_inventory=seal_of(args.grid / "inventory.json"),
        timing_decisions=seal_of(args.grid / "decisions.json"),
        allocation_decisions=seal_of(args.allocation / "decisions.json"),
        survey=survey["seal"])
    followup = None
    if args.followup is not None:
        a.require(follow.ENGINE is not None and
                  args.followup_pilot is not None,
                  "a follow-up needs task31_followup.CELLS and "
                  "--followup-pilot")
        follow.ENGINE.replay(argparse.Namespace(
            output=args.followup.resolve(), partial=False, repo=repo,
            ledger=args.ledger, pilot=args.followup_pilot.resolve(),
            replaces_pilot=args.pilot.resolve()))
        first, second = grid.ENGINE.replayed, follow.ENGINE.replayed
        a.require(first is not None and second is not None,
                  "nothing was replayed")
        reports = {**first["stage1"], **first["stage2"],
                   **second["stage1"], **second["stage2"]}
        timed_decisions = grid.ENGINE.h.with_sources(
            grid.ENGINE.h.summary(reports), first["inventory"])
        followup = dict(cells=sorted(follow.TABLE.names()),
                        status=second["decisions"]["status"])
        inputs["followup_inventory"] = seal_of(
            args.followup / "inventory.json")
    rows = timing_rows(timed_decisions)
    a.require(set(rows) == set(grid.TABLE.names()),
              "the timing grid is not the sample")
    allocated = allocation_rows(
        a.load(args.allocation.resolve() / "decisions.json"),
        inventory["candidate"])
    record = dispose(identity, allocated, rows, survey["cells"])
    path = grid.ENGINE.h.attempts_file(argparse.Namespace(
        repo=repo, ledger=args.ledger), False)
    a.require(path is not None and Path(path).is_file(),
              "no attempts ledger: %s" % path)
    record.update(
        candidate=inventory["candidate"], baseline=inventory["baseline"],
        harness=(inventory.get("checkout") or {}).get("head"),
        timing_status=timed_decisions["status"], timing_replay_exit=tg_code,
        followup=followup, inputs=inputs, code=seals(),
        survey=dict(seal=survey["seal"],
                    process_timeout=survey["process_timeout"]),
        attempts=dict(
            timing=list(grid.ENGINE.attempt_counts(
                tg.Ledger(path), inventory["candidate"])),
            identity=list(grid.attempts_of(path, inventory["candidate"]))))
    return record


def verdict(record):
    """The last line: the statuses of the gates, the infeasible count and
    the attributions, the candidate and the harness, and the attempts of the
    ledger (against cherry-picking)."""
    paths = record["attributed"]
    return ("TASK31 disposition: %s %s (identity %s%s; allocation %d pass "
            "of %d cells; timing %s; infeasible %d by identity; candidate "
            "%s; harness %s; attempts: timing %d in the ledger, %d of the "
            "candidate; identity %d, %d of the candidate)" % (
                record["status"], json.dumps(record["counts"]),
                record["identity_status"],
                " [%s]" % ", ".join(paths) if paths else "",
                sum(c["allocation"] == "pass"
                    for c in record["cells"].values()),
                sum(n not in cases.INFEASIBLE for n in record["cells"]),
                record["timing_status"], record["infeasible"],
                record["candidate"], record["harness"],
                *record["attempts"]["timing"],
                *record["attempts"]["identity"]))


def disposition(args):
    if args.check:
        check_code(a.load(args.check).get("code"))
    record = derive(args)
    survey = load_survey(args.survey)
    for line in lines(record, survey["process_timeout"]):
        print(line)
    if args.record:
        a.require(not args.record.exists(), "refusing to replace "
                  + str(args.record))
        a.save(args.record, record)
    elif args.check:
        held = a.load(args.check)
        a.require(tg.canonical(dict(held, code=record["code"])) ==
                  tg.canonical(record), "changed TASK31 disposition")
    print(verdict(record))
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
    add("--survey", type=Path, required=True,
        help="the cost survey of the infeasible cells (cost-survey/"
        "survey.json beside REPORT.md): its numbers and its sha256 are "
        "recorded")
    add("--followup", type=Path, help="the follow-up's final stage "
        "(task31_followup.py), whose cells replace the first grid's")
    add("--followup-pilot", type=Path, help="the follow-up's pilot")
    add("--attributed", type=Path, help="the reviewed table the identity "
        "grid was made with, if not task31_attributed.json")
    add("--repo", type=Path, default=a.HERE.parents[3])
    add("--ledger", type=Path, help="read this attempts ledger, of the "
        "checkout the grids were made in")
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
