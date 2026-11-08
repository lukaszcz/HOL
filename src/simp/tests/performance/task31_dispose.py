#!/usr/bin/env python3
"""The TASK31 decision per cell: identity, allocation and timing together.

A cell passes if and only if

- gate 1: its identity row is `identical` or `attributed`
  (task31_identity_grid.py `identity`; `different` fails), the grid being
  judged by the committed reviewed table;
- gate 2: the allocation grid measured it and decided `pass`, and its
  structural work row is `equal`, where that gate measures it (every cell but
  the infeasible ones);
- gate 3: the timing table decided `pass`, where the cell is sampled
  (task31_cases.SAMPLE).

A gate that decided against a cell makes it `fail`: allocation words that
fail, or a work row that `differs`. A gate with no decision for a cell it
must decide leaves it `incomplete`: an allocation row that is `inconclusive`
or whose work row is `inconclusive` or missing, a timing class that is not a
decision (`inconclusive`, `control_limited`, `protocol`), named in the cell's
record, and an identity grid that is inconclusive. Nothing is excused here.

The 33 infeasible cells (task31_cases.INFEASIBLE) pass by identity alone and
are recorded as "untimed, unallocated: infeasible", with the numbers of the
cost survey the command is given (`--survey`, a file of the shape
load_survey below; its sha256 is recorded and `--check` reads it again).
When their identity is `attributed`, the record names the attribution and the
cells of the same family that measured it (allocation cells of at most 1000
assumptions that passed with an attributed identity, and the family's cells of
the timing sample that passed); an infeasible attributed cell with none of
either is `incomplete`.

The command replays what it reads: the identity grid (every archive, every
decision, the opening line in the ledger), the timing grid (`task31_grid.py
replay`, in full, with its pilot) and the allocation grid
(`allocation_matrix.replay`, which derives the decisions again from the
archives). A follow-up (`--followup`,
`--followup-pilot`: task31_followup.py) replaces the cells of the first grid
that it measured again. The allocation grid must be a complete, non-partial
grid of task `task31`, of the same candidate, baseline and harness as the
other two; its `decisions.json` is then read (PROTOCOL.md, "TASK31"):

    {"candidate": REV, "baseline": REV, "complete": true,
     "infeasible": [NAME, ...],
     "rows": [{"case": CASE, "size": N, "pairs": P,
               "decision": "pass" | "fail" | "inconclusive",
               "work": "equal" | "differs" | "inconclusive" | null}, ...]}

`infeasible` is the infeasible set and `rows` has exactly one row for every
other cell, none repeated; a row of any other shape is refused.

The identity grid's recorded table must be the committed file, by sha256
(its seal is recorded as the `attribution` input). The pins of the timing
grid (and of the follow-up), with those of every resumption and of an
extension's first stage, must be the committed table's projection onto the
sources the grid measures (task31_pins.pins, the function the driver uses;
recorded as the `pins` input): an entry added for the shared heap or a build
file voids no timing grid, and a change to the entry of a measured source
does. Every attempt of the first stage's table and of the follow-up's that
the command does not judge must be void (void_attempts.py, the rule of the
TASK30 disposition): at most one attempt that is not void per table and
stage. An unresolved allocation row may carry `"pairs": null`.

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
import task30_grid as base30
import task31_cases as cases
import task31_followup as follow
import task31_grid as grid
import task31_identity_grid as idgrid
import task31_pins as reviewed
import timing_grid as tg
from void_attempts import attempts_of

SCHEMA = "task31-disposition-v1"
SURVEY_SCHEMA = "task31-cost-survey-v1"
SURVEY_FIELDS = ("op1000", "setup1000", "check1000", "op10000",
                 "setup10000", "check10000")
INFEASIBLE_TEXT = "untimed, unallocated: infeasible"
# The measurement of an attribution in a family stops at this size of
# assumptions for the allocation cells.
ALLOCATION_LIMIT = 1000
# The code whose change must be named in HISTORY once a disposition is
# recorded: this module and every module it takes a decision from (a test
# pins that every module it, the timing driver and the follow-up import is
# here or is sealed by the identity grid).
CODE = ("task31_dispose.py", "task31_grid.py", "task31_identity_grid.py",
        "task31_followup.py", "task31_identity.py", "task31_attribution.py",
        "task31_cases.py", "task31_pins.py", "task30_grid.py",
        "timing_grid.py", "acceptance.py", "void_attempts.py",
        "allocation_matrix.py", "allocation_analysis.py",
        "allocation_schema.py", "allocation_boundary.py", "path_schema.py")
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


WORK = ("equal", "differs", "inconclusive", None)
DECISIONS = ("pass", "fail", "inconclusive")


def allocation_rows(decisions, candidate, baseline):
    """The allocation decisions as {cell name: {decision, work, pairs}},
    refusing a malformed file, one of another candidate or baseline, an
    incomplete one, or one whose infeasible set or cells are not the
    task's."""
    import allocation_matrix as am
    a.require(isinstance(decisions, dict) and
              isinstance(decisions.get("rows"), list),
              "the allocation decisions have no rows")
    a.require(decisions.get("candidate") == candidate and
              decisions.get("baseline") == baseline,
              "the allocation grid is of another candidate or baseline "
              "(%s against %s, not %s against %s)" % (
                  decisions.get("candidate"), decisions.get("baseline"),
                  candidate, baseline))
    a.require(decisions.get("complete") is True,
              "the allocation grid is not complete")
    a.require(decisions.get("infeasible") == sorted(cases.INFEASIBLE),
              "the allocation grid's infeasible cells are not the task's")
    known = {idgrid.name_of(*k) for k in idgrid.every()}
    found = {}
    for row in decisions["rows"]:
        a.require(isinstance(row, dict) and isinstance(row.get("case"), str)
                  and isinstance(row.get("size"), int) and
                  row.get("decision") in DECISIONS and
                  row.get("work") in WORK and
                  (isinstance(row.get("pairs"), int) or (
                      row.get("pairs") is None and
                      row.get("decision") == "inconclusive")),
                  "malformed allocation row: %r" % (row,))
        name = idgrid.name_of(row["case"], row["size"])
        a.require(name in known, "allocation row of an unknown cell: "
                  + name)
        a.require(name not in cases.INFEASIBLE,
                  "allocation row of an infeasible cell: " + name)
        a.require(name not in found, "repeated allocation row: " + name)
        a.require(row["decision"] != "pass" or row["pairs"] >= am.PAIRS,
                  "a passing allocation row of fewer than %d pairs: %s"
                  % (am.PAIRS, name))
        found[name] = dict(decision=row["decision"], work=row["work"],
                           pairs=row["pairs"])
    missing = sorted(known - set(cases.INFEASIBLE) - set(found))
    a.require(not missing, "the allocation grid has no row for: "
              + ", ".join(missing[:5]))
    return found


def allocation_passed(row):
    """Whether an allocation row passes its cell: the words pass and the
    work row is equal."""
    return row is not None and row["decision"] == "pass" and \
        row["work"] == "equal"


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
    case = idgrid.case_of(name)
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
            allocation_passed(allocated.get(n)) and
            identity[n]["status"] == "attributed"),
        timing=sorted(n for n in cells if n in cases.SAMPLE and
                      timed.get(n) == "pass"))


def judge(name, identity, allocated, timed, survey, groups):
    """One cell: its record. `identity` is the cell's identity decision,
    `allocated` the allocation row or None, `timed` the timing class or
    None, `survey` the numbers of the cost survey, `groups` what measured
    the attribution (see `measured_by`). A gate with no decision for a cell
    it must decide leaves the cell `incomplete`; a gate that decided
    against it makes it `fail`."""
    infeasible = name in cases.INFEASIBLE
    found = dict(identity=identity["status"],
                 allocation=None if allocated is None
                 else allocated["decision"],
                 allocation_work=None if allocated is None
                 else allocated["work"], timing=timed)
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
        else:
            if allocated["decision"] == "fail":
                failed.append("allocation: fail")
            if allocated["work"] == "differs":
                failed.append("allocation: the work row differs")
            if allocated["decision"] == "inconclusive":
                missing.append("allocation: inconclusive")
            elif allocated["decision"] == "pass" and \
                    allocated["work"] not in ("equal", "differs"):
                missing.append("allocation: the work row is %s" % (
                    allocated["work"] or "missing"))
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
    names = [idgrid.name_of(*k) for k in idgrid.every()]
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
    for label, key in (("TIMING-ATTEMPT", "timing_attempts"),
                       ("FOLLOW-UP-ATTEMPT", "followup_attempts")):
        for found in record.get(key, []):
            out.append("%s %s status %s output %s: %s" % (
                label, found["attempt"], found["status"], found["output"],
                "void (no measurement admitted)" if found["void"] else
                "judged"))
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


def allocation_inventory(root, identity, timing):
    """The inventory of the allocation grid, which must be a complete grid
    of this task, of the candidate and baseline of the other two gates, made
    in the harness of the timing grid; the checks come before any replay."""
    a.require((root / "decisions.json").exists(),
              "the allocation grid is partial: it has no decisions")
    counted = a.load(root / "inventory.json")
    a.require(counted.get("task") == "task31",
              "the allocation grid is not a TASK31 grid")
    a.require(counted["candidate"] == identity["candidate"] and
              counted["baseline"] == identity["baseline"],
              "the allocation grid has another candidate or baseline than "
              "the identity grid")
    base30.harness_match(timing, counted)
    return counted


def pin_codes(engine, root):
    """The records of a timing grid that carry the seal of the reviewed
    table it was judged by: its inventory, each resumption, and for an
    extension those of its first stage too."""
    root = Path(root).resolve()
    found = a.load(root / "inventory.json")
    codes = [found, *found.get("resumed", [])]
    if found.get("schema") == engine.t.schema("extension"):
        codes += pin_codes(engine, (root / found["grid"]).resolve())
    return codes


def identity_binding(identity, document):
    """The seal of the reviewed table the identity grid recorded, which must
    be the committed file (by sha256)."""
    held = identity["attributed"]["file"]
    a.require(isinstance(held, dict) and held.get("sha256"),
              "the identity grid records no reviewed table")
    a.require(held["sha256"] == document["seal"]["sha256"],
              "the identity grid was judged by the reviewed table %s, not "
              "the committed %s: run it again" % (
                  held["sha256"], document["seal"]["sha256"]))
    return held


def pins_binding(engine, label, root, document):
    """The pins a timing grid (and each resumption and first stage of it)
    was judged by must be the committed table's projection onto the sources
    the grid measures (`task31_pins.pins`, the function the driver uses).
    The seal of the file may be an earlier one, if its history keeps it:
    adding an entry that is no source of the grid changes no pin, while any
    change to the entry of a measured source does. Returns the pins."""
    expected = reviewed.pins(document["entries"], cases.SOURCES)
    for code in pin_codes(engine, root):
        found = engine.h.pins_for(code)
        a.require(found == expected,
                  "the %s was judged by pins that are not the committed "
                  "table's for the sources it measures (%s against %s): "
                  "a measured source's reviewed entry changed, so the "
                  "grid is void" % (label, json.dumps(found, sort_keys=True),
                                    json.dumps(expected, sort_keys=True)))
    return expected


def judged_attempts(engine, root):
    """{attempt id: output} of the grid in `root`, a final stage of
    `engine`'s table and, for a second stage, of its first."""
    root = Path(root).resolve()
    found = a.load(root / "inventory.json")
    judged = {found["attempt"]: root}
    if found.get("schema") == engine.t.schema("extension"):
        first = (root / found["grid"]).resolve()
        judged[a.load(first / "inventory.json")["attempt"]] = first
    return judged


def table_attempts(engine, root, repo, ledger):
    """Every attempt of `engine`'s table in the ledger: the judged ones
    (`judged_attempts` of `root`) and the others, which must be void
    (void_attempts.py). One rule for the first stage's table and a
    follow-up's alike: at most one attempt that is not void per table and
    stage."""
    return attempts_of(argparse.Namespace(repo=repo, ledger=ledger), engine,
                       judged_attempts(engine, root))


def derive(args):
    repo = args.repo
    survey = load_survey(args.survey)
    ledger = grid.ENGINE.h.attempts_file(argparse.Namespace(
        repo=repo, ledger=args.ledger), False)
    a.require(ledger is not None and Path(ledger).is_file(),
              "no attempts ledger: %s" % ledger)
    # Every comparison that needs no replay comes first.
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
    counted = allocation_inventory(args.allocation.resolve(), inventory,
                                   timing)
    committed = reviewed.load()
    table = identity_binding(inventory, committed)
    pins = pins_binding(grid.ENGINE, "timing grid", args.grid, committed)
    if args.followup is not None:
        a.require(follow.ENGINE is not None and
                  args.followup_pilot is not None,
                  "a follow-up needs task31_followup.CELLS and "
                  "--followup-pilot")
        pins_binding(follow.ENGINE, "follow-up", args.followup, committed)
    # Every attempt of the first stage's table that is not judged must be
    # void, and so must those of the follow-up's table, whether or not a
    # follow-up is named.
    timing_attempts = table_attempts(grid.ENGINE, args.grid, repo,
                                     args.ledger)
    attempts = []
    if follow.ENGINE is not None:
        attempts = attempts_of(
            argparse.Namespace(repo=repo, ledger=args.ledger),
            follow.ENGINE,
            judged_attempts(follow.ENGINE, args.followup)
            if args.followup is not None else {})
    with contextlib.redirect_stdout(io.StringIO()):
        a.require(idgrid.identity_replay(argparse.Namespace(
            output=args.identity, repo=repo, attributed=None,
            ledger=ledger)) in (0, 1, 2),
            "the identity grid is not replayable")
    identity = a.load(args.identity.resolve() / "decisions.json")
    tg_code = grid.ENGINE.replay(argparse.Namespace(
        output=args.grid.resolve(), partial=False, repo=repo,
        pilot=args.pilot.resolve(), ledger=args.ledger))
    timed_decisions = a.load(args.grid.resolve() / "decisions.json")
    import allocation_matrix as am
    with contextlib.redirect_stdout(io.StringIO()):
        alloc_code = am.replay(argparse.Namespace(
            output=args.allocation.resolve()))
    inputs = dict(
        identity_inventory=seal_of(args.identity / "inventory.json"),
        identity_decisions=seal_of(args.identity / "decisions.json"),
        timing_inventory=seal_of(args.grid / "inventory.json"),
        timing_decisions=seal_of(args.grid / "decisions.json"),
        allocation_inventory=seal_of(args.allocation / "inventory.json"),
        allocation_decisions=seal_of(args.allocation / "decisions.json"),
        attribution=table, pins=pins, survey=survey["seal"])
    followup = None
    if args.followup is not None:
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
        inventory["candidate"], inventory["baseline"])
    record = dispose(identity, allocated, rows, survey["cells"])
    record.update(
        candidate=inventory["candidate"], baseline=inventory["baseline"],
        harness=(inventory.get("checkout") or {}).get("head"),
        timing_status=timed_decisions["status"], timing_replay_exit=tg_code,
        allocation_status=a.load(args.allocation.resolve() /
                                 "decisions.json")["status"],
        allocation_replay_exit=alloc_code,
        followup=followup, followup_attempts=attempts,
        timing_attempts=timing_attempts, inputs=inputs,
        code=seals(),
        survey=dict(seal=survey["seal"],
                    process_timeout=survey["process_timeout"]),
        attempts=dict(
            timing=list(grid.ENGINE.attempt_counts(
                tg.Ledger(ledger), inventory["candidate"])),
            identity=list(idgrid.attempt_counts(ledger,
                                                inventory["candidate"]))))
    return record


def verdict(record):
    """The last line: the statuses of the gates, the infeasible count and
    the attributions, the candidate and the harness, and the attempts of the
    ledger (against cherry-picking)."""
    paths = record["attributed"]
    return ("TASK31 disposition: %s %s (identity %s%s; allocation %s, %d "
            "pass of %d cells; timing %s; infeasible %d by identity; "
            "candidate %s; harness %s; attempts: timing %d in the ledger, "
            "%d of the candidate; identity %d, %d of the candidate)" % (
                record["status"], json.dumps(record["counts"]),
                record["identity_status"],
                " [%s]" % ", ".join(paths) if paths else "",
                record["allocation_status"],
                sum(c["allocation"] == "pass" and
                    c["allocation_work"] == "equal"
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
        help="the identity grid (task31_identity_grid.py identity "
        "--output)")
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
