#!/usr/bin/env python3
"""TASK30 disposition: the policy owner's decision of 2026-11-05 on the
TASK30 grid and its follow-up, and the evidence it rests on.

The timing gate's own verdict stays what it is (`task30_grid.py close` says
"not pass" while any cell is not a pass). This is the final one: the TASK30
decision with the follow-up's cells in place of the cells they replaced
(`final.json`), every cell classified (`timing_grid.dispose`), and the 13
control-limited cells attributed one by one, each only while deterministic
structural evidence against develop holds, which is re-derived from the
replayed records every time (PROTOCOL.md, "Structural evidence and the TASK30
disposition"). Nothing here measures, appends to a ledger or changes a
record.

  python3 -B task30_dispose.py --grid E/stage2 --pilot E/pilot \\
      --allocation E/alloc --followup E/followup \\
      --followup-pilot E/followup-pilot --followup-allocation E/alloc-z \\
      [--ledger FILE] [--record]

It replays the follow-up in full (which replays the TASK30 grid in full, by
its own table, with its pilot), and the two allocation grids; requires that
each timing grid ran in the harness of its own allocation grid (TASK30 at Y
with `alloc/`, the follow-up at Z with `alloc-z/`; `task30_grid.
harness_match`); builds `final.json` and `disposition.json` and prints the
class report, every attempt (the replays' report), the evidence of each
attributed cell and one line, `TASK30 disposition: pass|fail|blocked
{counts}`. Exit status 0 pass, 1 fail, 2 blocked, 3 a refusal. `final.json`
and `disposition.json` are in the follow-up's output directory
(`--followup`). `--record` writes them (and refuses to replace files that
exist); without it both are derived again and any difference from the files
is refused: "changed TASK30 disposition".

This module is in neither table's seals: it is downstream of the replays
and its code is not on the replay path, so `task30_grid.py` stays as it is.
`disposition.json` records the seals of the code that derived it (`CODE`);
a later change to one of those files appends the seal it had when the
disposition was recorded to `HISTORY`, in the same commit, or the check
refuses it.
"""
import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import acceptance as a
import allocation_analysis as an
import allocation_matrix as am
import task30_followup as follow
import task30_grid as base
import timing_grid as tg

# What the evidence for a cell is made of; recorded in the disposition.
EVIDENCE = ("sources", "allocation", "work", "result")
# The classes, fixed per case (never read from the rows: a hook that
# regressed to "no use" gives empty rows that are equal on both sides).
DELETION, DPROC, OPERATION = "deletion", "dproc-deletion", "operation"
CASE_CLASS = {
    "exclude_missing": DELETION, "exclude_matching": DELETION,
    "exclude_batch": DELETION, "exclude_qualified": DELETION,
    "exclude_literal_exact": DELETION, "exclude_literal_namespace": DELETION,
    "history_excluded": DELETION,
    "exclude_dproc": DPROC, "exclude_mixed": DPROC,
    "exclude_marker": OPERATION, "exclude_marker_reuse": OPERATION,
    "exclude_tactic_reuse": OPERATION, "exclude_tactic_complete": OPERATION}
# The phases whose words are compared between the two allocation grids: the
# setup bracket is not (the fixture's setup changed between Y and Z).
OPERATION_PHASES = ("operation_first", "operation_steady", "apply")
# The code whose change must be named in HISTORY once a disposition is
# recorded: this module, the two tables and the engine, the acceptance
# rules, and the allocation modules that replay the allocation grids and
# read their rows. The rest of what this module imports is the replay path
# of the timing grids (sealed by their own records) or the allocation
# matrix's building of a toolchain (test_timing_followup.py names it).
CODE = ("task30_dispose.py", "task30_grid.py", "task30_followup.py",
        "timing_grid.py", "acceptance.py", "allocation_matrix.py",
        "allocation_analysis.py", "allocation_schema.py",
        "allocation_boundary.py", "path_schema.py")
# Per file of CODE, the seals it had when a disposition was recorded, once
# it has changed since (empty until then).
HISTORY = {}

TAIL = (
    "Not shown by any row: CPU that neither allocates nor traces, net node "
    "visits and the candidates a match hides, live heap and retention (the "
    "candidate's startup heap is about 1.01M words larger in every cell: "
    "GC, reported and not gated; its attribution belongs to TASK_31), work "
    "outside Trace and the kernel counter. Equal rows show equal work and "
    "result, not equal time.")


def note(text, residual=""):
    return " ".join(text.split() + ([residual] if residual else []) +
                    [TAIL])


def build(rows):
    """{cell: dict(evidence_class, note)}: the class of a cell is its case's
    (CASE_CLASS)."""
    return {cell: dict(evidence_class=CASE_CLASS[cell.rsplit("-", 1)[0]],
                       note=text) for cell, text in rows}


# The residual of exclude_literal_exact-10000 and exclude_dproc-10000: the
# candidate's interval reaches above the margin.
LITERAL_RESIDUAL = (
    "Residual: the candidate's CPU and wall intervals extend to 1.041, "
    "beyond the 3% margin; the rows show the same work and result, not the "
    "same time, and do not explain it.")
DPROC_RESIDUAL = (
    "Residual: the candidate's CPU and wall intervals extend to 1.075, "
    "beyond the 3% margin; the rows show the same work and result, not the "
    "same time, and do not explain it.")

DISPOSITION = dict(
    schema="task30-disposition-v1", decided="2026-11-05", evidence=EVIDENCE,
    attributed=build([
        ("exclude_missing-10000", note(
            "-* of an absent name. The operation fires no traced event, "
            "inference, maker or collector. The use of the result is 10000 "
            "net lookups that all rewrite (no inference). Digest: names "
            "[matrix_data], the set of lookups the net leaves alone empty. "
            "The same result and the same traced use as develop.")),
        ("exclude_matching-10000", note(
            "-* of one rule name. The operation fires nothing. The use is "
            "10000 lookups: 9999 rewrite and one (index 0) leaves the term "
            "alone. Digest: names [matrix_data], that set {0}.")),
        ("exclude_batch-10000", note(
            "-* of 3 rule names and one absent name. The operation fires "
            "nothing. The use is 10000 lookups: 9997 rewrite and 3 leave "
            "the term alone. Digest: that set {0, 5000, 9999}.")),
        ("exclude_qualified-10000", note(
            "-* of a qualified name (bool.matrix_r0). The operation fires "
            "nothing. The use is 10000 lookups: 9999 rewrite and one leaves "
            "the term alone. Digest: that set {0}.")),
        ("exclude_literal_exact-10000", note(
            "-* of an exact namespaced name. The operation fires nothing. "
            "The use is 10000 lookups: 9999 rewrite and one leaves the "
            "term alone. Digest: names [anonymous], that set {0}.",
            LITERAL_RESIDUAL)),
        ("history_excluded-10000", note(
            "exclude_ssfrags [matrix_data]. The operation fires nothing and "
            "calls no maker or collector, so no replay of the history. The "
            "use is 10000 lookups that all leave the term alone (the data "
            "entries are gone). Digest: names [matrix_drop], that set "
            "0-9999.")),
        ("exclude_literal_namespace-1", note(
            "-* of the literal matrix_ns::, which removes nothing. The "
            "operation fires nothing. The use is one lookup that rewrites. "
            "Digest: names [anonymous], that set empty.")),
        ("exclude_dproc-10000", note(
            "-* of one dproc name. The operation fires no event and calls "
            "no maker, collector or dproc. The net is empty by "
            "construction, so the 10000 lookups (one traversal and one "
            "term left alone each) show nothing about the dprocs. The "
            "deletion is shown by the dproc count of the use (3 sampled "
            "terms times the 9999 retained dprocs, each applied through "
            "the traversal data of the simpset; this restates the length "
            "of the digest's dproc names dp1..dp9999, it is not an "
            "independent witness), by the exact allocation words and by "
            "source identity.", DPROC_RESIDUAL)),
        ("exclude_mixed-10000", note(
            "-* of one dproc and one rule. The operation fires nothing. The "
            "use is 10000 lookups: 9999 rewrite and one (rule 0, gone from "
            "the net) leaves the term alone. The dproc count of the use is "
            "that of 9999 retained dprocs on 3 sampled terms (it restates "
            "the digest's dproc names). Digest: names [matrix_data, "
            "matrix_setup], dprocs dp1..dp9999, that set {0}.")),
        ("exclude_marker-10000", note(
            "A timed SIMP_CONV with Excl: it builds the marker (EQ_MP, "
            "SPEC, SYM), runs the -* of the 10000-entry source inside "
            "process_tags (untraced), then makes one traversal of the "
            "target: one REDUCE and 4 inferences per run, on both sides. "
            "There is no use. Digest: |- c0 = c0. The deletion, the "
            "dominant cost, is shown only by the operation words and the "
            "source identity.")),
        ("exclude_marker_reuse-10000", note(
            "The reused conversion still runs the -* of the 10000-entry "
            "source in every call (SIMP_CONV processes its tags on each "
            "application); only the Excl construction is saved. Traced: "
            "one REDUCE and one term left alone per run. There is no use. "
            "Digest: |- c0 = c0. The deletion is shown only by the "
            "operation words and the source identity.")),
        ("exclude_tactic_reuse-10000", note(
            "The reused tactic runs the -* in every application (only the "
            "Excl construction is saved). Traced: one REDUCE and the "
            "fixture's ASSUME. There is no use. Digest: the residual goal "
            "?- c0 and the proof c0 |- c0. The deletion is shown only by "
            "the operation words and the source identity.")),
        ("exclude_tactic_complete-10000", note(
            "The tactic is built (Excl: EQ_MP, SPEC, SYM), applied and "
            "checked: one REDUCE and 4 inferences. There is no use. "
            "Digest: as exclude_tactic_reuse. The deletion is shown only "
            "by the operation words and the source identity."))]))
SECTIONS = ("first", "second", "use")


# What each class must show of the work rows of its cell (`groups`: the
# non-empty row groups, allocation_analysis.work_groups).
def class_failure(kind, groups):
    """None when the work rows of a cell show what its class needs, else
    the text of what they lack."""
    if groups is None:
        return "the cell has no work rows"
    first, second, use = (groups[k] for k in SECTIONS)
    if kind in (DELETION, DPROC):
        if first or second:
            return ("class %s: work.first/work.second are not empty (%s)"
                    % (kind, ", ".join(first + second)))
        if "work.use.trace.4.REDUCE" not in use:
            return ("class %s: work.use has no work.use.trace.4.REDUCE "
                    "(an empty use shows nothing)" % kind)
        if kind == DPROC and "work.use.dproc" not in use:
            return ("class %s: work.use has no work.use.dproc" % kind)
        return None
    if kind == OPERATION:
        if not first or not second:
            return ("class %s: work.first or work.second is empty"
                    % kind)
        if use:
            return ("class %s: work.use is not empty (%s)"
                    % (kind, ", ".join(use)))
        return None
    return "unknown evidence class %r" % kind


def split(cell):
    """(case, size) of a cell name."""
    case, size = cell.rsplit("-", 1)
    return case, int(size)


def row(decisions, cell):
    case, size = split(cell)
    return decisions["cases"].get(case, {}).get("cells", {}).get(str(size))


class Evidence:
    """The evidence for the attributed cells, derived from replayed records:
    the final decision (source identity), the allocation grid of Y (`old`,
    its decisions) and that of Z (`new`, with the work rows)."""

    def __init__(self, spec, final, old, new):
        self.spec, self.final, self.old, self.new = spec, final, old, new
        self.groups = an.cells_work_groups(new)

    def sources(self, cell):
        found = self.final.get("source_identity")
        if found is None:
            return "no source record"
        if found["differing"]:
            return ("source differs from develop: %s (pinned and reviewed: "
                    "%s)" % (", ".join(found["differing"]),
                             ", ".join(found.get("reviewed", {})) or
                             "none"))
        return None

    def allocation(self, cell):
        here, there = row(self.new, cell), row(self.old, cell)
        if here is None:
            return "alloc-z has no row for the cell"
        if there is None:
            return "alloc has no row for the cell"
        for phase, metrics in here["phases"].items():
            for metric, m in metrics.items():
                if m["decision"] != "pass":
                    return ("allocation row %s.%s of alloc-z is %s"
                            % (phase, metric, m["decision"]))
        for phase in OPERATION_PHASES:
            for metric, m in here["phases"][phase].items():
                o = there["phases"][phase][metric]
                for side in ("baseline", "candidate"):
                    if o[side] != m[side]:
                        return ("operation row %s.%s differs between alloc "
                                "and alloc-z (%s: %s, not %s)" % (
                                    phase, metric, side, o[side], m[side]))
        return None

    def work(self, cell):
        case, size = split(cell)
        section = self.new.get("work")
        if section is None:
            return "alloc-z has no work section"
        name = am.name_of(case, size)
        if name in section["missing"] or name in section["unresolved"]:
            return "work rows are missing or unresolved"
        if section["cells"].get(name) != "equal":
            return "work status is %s, not equal" % section["cells"].get(
                name)
        for entry in section["nondeterminism"]:
            if entry[:2] == [case, size]:
                return ("work row %s is not reproducible (%s)"
                        % (entry[2], entry[3]))
        rows = row(self.new, cell).get("work") or {}
        for key, found in rows.items():
            if found["decision"] != "equal":
                return "work row %s is %s" % (key, found["decision"])
        return class_failure(self.spec["attributed"][cell]["evidence_class"],
                             self.groups[case, size])

    def holds(self, cell):
        """None when the evidence for the cell holds, else the text naming
        the row or file that fails."""
        for name in self.spec["evidence"]:
            failed = getattr(self, name)(cell)
            if failed is not None:
                return "%s: %s" % (name, failed)
        return None

    def result(self, cell):
        """The digest of the result is a work row (`result.digest`): equal
        and present."""
        rows = (row(self.new, cell) or {}).get("work") or {}
        found = rows.get("result.digest")
        if found is None:
            return "no result.digest row"
        if found["decision"] != "equal" or len(found["candidate"]) != 1:
            return "result.digest row is %s" % found["decision"]
        return None


def counts(rows):
    """{run: {key: count}} of the nonzero count rows of a cell, as the
    candidate has them."""
    found = {k: {} for k in SECTIONS}
    for name, value in sorted((rows or {}).items()):
        if name == "result.digest":
            continue
        _, run, key = name.split(".", 2)
        count, = value["candidate"]
        if count != "0":
            found[run][key] = int(count)
    return found


def metrics(report):
    """The candidate's and the control's CPU, wall and GC of one cell:
    decision, median ratio and 95% interval; the control's interval and
    decision beside."""
    result, = report["workloads"]
    found = {}
    for key, m in result["candidate"]["metrics"].items():
        control = result["control"]["metrics"][key]
        found[key] = dict(
            decision=m["decision"], reason=m["reason"],
            median=m["median_paired_ratio"],
            interval=m["paired_ratio_bootstrap_95_percent"],
            control_decision=control["decision"],
            control_interval=control["paired_ratio_bootstrap_95_percent"])
    return found


def record_of(spec, final, reports, new, evidence, result):
    """The disposition record: `result` is timing_grid.dispose's, the
    per-cell record is the evidence class, the note, the metrics of the
    final report, the work counts and the digest, the number of allocation
    rows and what failed, if anything."""
    cells = {}
    for cell, listed in spec["attributed"].items():
        case, size = split(cell)
        found = row(new, cell) or {}
        work = found.get("work")
        digest = None if not work or "result.digest" not in work else \
            next(iter(work["result.digest"]["candidate"]))
        cells[cell] = dict(
            listed, decision=("attributed" if cell in
                              result["cells"]["attributed"] else "blocking"),
            failed=evidence.holds(cell), metrics=metrics(reports[case, size]),
            work=None if work is None else counts(work), digest=digest,
            allocation_rows=sum(len(m) for m in
                                found.get("phases", {}).values()))
    return dict(
        schema=spec["schema"], decided=spec["decided"],
        evidence=list(spec["evidence"]), status=result["status"],
        counts=result["counts"], cells=result["cells"],
        blocking=result["blocking"], attributed=cells,
        pinned=final.get("source_identity", {}).get("reviewed", {}),
        replaced=final["replaced"])


def seals(here=None):
    here = a.HERE if here is None else Path(here)
    return {name: a.seal(here / name) for name in CODE}


def check_code(recorded, here=None):
    """The seals a disposition records are those of the code now or of
    the earlier code HISTORY names."""
    now = seals(here)
    a.require(isinstance(recorded, dict) and set(recorded) == set(CODE),
              "changed TASK30 disposition: the recorded code is not %s"
              % ", ".join(CODE))
    for name, seal in recorded.items():
        a.require(seal == now[name] or seal in HISTORY.get(name, ()),
                  "changed TASK30 disposition: %s changed since it was "
                  "recorded; append the old seal to HISTORY in the same "
                  "commit" % name)


def pair(timing, counted, label):
    """One timing grid and the allocation grid of its harness: the same
    task, candidate and baseline, and one clean harness (head and tree),
    which `harness_match` compares exactly."""
    a.require(counted.get("task") == "task30",
              "the %s allocation grid is not a TASK30 grid" % label)
    a.require(timing["candidate"] == counted["candidate"],
              "the %s timing grid measured %s, its allocation grid %s"
              % (label, timing["candidate"], counted["candidate"]))
    a.require(timing["baseline"] == counted["baseline"],
              "the %s grids have different baselines" % label)
    return base.harness_match(timing, counted)


def loaded(path, what):
    a.require((path / "inventory.json").exists() and
              (path / "decisions.json").exists(),
              "%s is not a complete grid: %s" % (what, path))
    return a.load(path / "inventory.json")


def derive(args, old=base.ENGINE, new=follow.ENGINE, spec=DISPOSITION):
    """Replay everything and derive (final, disposition, lines). `old` and
    `new` are the engines of the TASK30 table and of its follow-up."""
    grid, pilot = args.grid.resolve(), args.pilot.resolve()
    followup = args.followup.resolve()
    allocation = args.allocation.resolve()
    allocz = args.followup_allocation.resolve()
    # The cheap comparisons come first.
    a.require(allocation != allocz, "one allocation grid cannot serve both "
              "harnesses: --allocation (Y) and --followup-allocation (Z)")
    timing_y, timing_z = loaded(grid, "--grid"), loaded(followup,
                                                        "--followup")
    a.require("replaces" in timing_z, "--followup is not a follow-up grid")
    a.require((followup / timing_z["replaces"]["grid"]).resolve() == grid,
              "--grid is not the grid the follow-up replaced (%s)"
              % (followup / timing_z["replaces"]["grid"]).resolve())
    counted_y = loaded(allocation, "--allocation")
    counted_z = loaded(allocz, "--followup-allocation")
    pair(timing_y, counted_y, "TASK30 (Y)")
    pair(timing_z, counted_z, "follow-up (Z)")
    a.require(new.t.replaces is not None and new.t.replaces.engine is old,
              "the follow-up does not replace the TASK30 table's grid")
    # The follow-up's replay replays the TASK30 grid in full first.
    new.replay(argparse.Namespace(
        output=followup, partial=False, repo=args.repo, ledger=args.ledger,
        pilot=args.followup_pilot.resolve(), replaces_pilot=pilot))
    y, z = old.replayed, new.replayed
    a.require(y is not None and z is not None, "nothing was replayed")
    a.require(new.bound()["grid"] == grid, "--grid is not the grid the "
              "follow-up replaced")
    for path in (allocation, allocz):
        am.replay(argparse.Namespace(output=path))
    decisions_y = a.load(allocation / "decisions.json")
    decisions_z = a.load(allocz / "decisions.json")
    a.require(decisions_y.get("complete") and decisions_z.get("complete"),
              "an allocation grid is not complete")
    reports = {**y["stage1"], **y["stage2"], **z["stage1"], **z["stage2"]}
    final = old.h.with_sources(old.h.summary(reports), y["inventory"])
    if "remeasured" in y["decisions"]:
        final["remeasured"] = y["decisions"]["remeasured"]
    first_y, first_z = y["first"], z["first"]
    final["replaced"] = dict(
        cells=sorted(new.t.names()),
        replaced_seed=first_y.get("layout_seed"),
        followup_seed=first_z.get("layout_seed"),
        replaced_counts=first_y["iterations_seal"],
        followup_counts=first_z["iterations_seal"],
        replaced_candidate=first_y["candidate"],
        followup_candidate=first_z["candidate"],
        followup_status=z["decisions"]["status"])
    evidence = Evidence(spec, final, decisions_y, decisions_z)
    result = tg.dispose(final, spec["attributed"], evidence.holds)
    record = record_of(spec, final, reports, decisions_z, evidence, result)
    record["code"] = seals()
    lines = tg.class_report("%s final" % old.t.label, final)
    for cell, found in record["attributed"].items():
        lines.append("%s %s (%s)%s" % (
            found["decision"].upper(), cell, found["evidence_class"],
            "" if found["failed"] is None else ": " + found["failed"]))
    return final, record, lines


def canon(value):
    """What a file holds of a value (JSON keeps no tuple)."""
    return json.loads(json.dumps(value))


def disposition(args, **engines):
    final, record, lines = derive(args, **engines)
    followup = args.followup.resolve()
    for line in lines:
        print(line)
    files = {"final.json": final, "disposition.json": record}
    if args.record:
        for name in files:
            a.require(not (followup / name).exists(), "refusing to replace "
                      "the recorded %s; remove it to record again" % name)
        for name, value in files.items():
            a.save(followup / name, value)
    else:
        for name in files:
            a.require((followup / name).exists(), "no recorded %s: record "
                      "it with --record" % name)
        recorded = a.load(followup / "disposition.json")
        check_code(recorded.get("code"))
        for name, value in files.items():
            held = a.load(followup / name)
            if name == "disposition.json":
                held = dict(held, code=record["code"])
            a.require(canon(value) == held,
                      "changed TASK30 disposition: %s" % name)
    print("TASK30 disposition: %s %s" % (
        record["status"], json.dumps(record["counts"])))
    return {"pass": 0, "fail": 1}.get(record["status"], 2)


def parser():
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    add = p.add_argument
    add("--grid", type=Path, required=True,
        help="the TASK30 grid, its second stage")
    add("--pilot", type=Path, required=True, help="the TASK30 pilot")
    add("--allocation", type=Path, required=True,
        help="the allocation grid at Y (alloc/)")
    add("--followup", type=Path, required=True,
        help="the follow-up's final stage; final.json and disposition.json "
        "are kept here")
    add("--followup-pilot", type=Path, required=True,
        help="the follow-up's pilot")
    add("--followup-allocation", type=Path, required=True,
        help="the allocation grid at Z (alloc-z/)")
    add("--repo", type=Path, default=a.HERE.parents[3])
    add("--ledger", type=Path, help="read this attempts ledger, of the "
        "checkout the grids were made in")
    add("--record", action="store_true",
        help="write final.json and disposition.json instead of checking")
    return p


def main(argv=None, **engines):
    """The status of the disposition, or `REFUSED` (3) with one line on the
    standard error for a command that decided nothing."""
    with tg.terminating_as_interrupt():
        try:
            return disposition(parser().parse_args(argv), **engines)
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
