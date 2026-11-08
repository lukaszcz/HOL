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
      --allocation E/alloc --followup E/followup-FINAL \\
      --followup-pilot E/followup-pilot --followup-allocation E/alloc-z \\
      [--ledger FILE] [--record]

(`E/followup-FINAL` is the follow-up's final judged stage directory: here
a rerun, `followup-r2`, as the first attempt `followup` was void.)

It makes every comparison that needs no replay first (the arguments, the
pairing, every attempt of the follow-up's table in the ledger, and in check
mode the recorded files and the code seals), then
replays the follow-up in full (which replays the TASK30 grid in full, by its
own table, with its pilot), and the two allocation grids. It requires that
each timing grid ran in the harness of its own allocation grid (TASK30 at Y
with `alloc/`, the follow-up at Z with `alloc-z/`;
`task30_grid.harness_match`), that `--followup` is the follow-up's final
stage, and that each allocation grid is complete: an incomplete one has only
`decisions-partial.json` and is refused before any replay, as is one with a
partial decision beside `decisions.json` (stale, and may be removed). Each
allocation grid that is complete is gated by its own status
(`allocation_matrix.replay`'s): a fail makes the disposition fail, and any
other status but pass (too few pairs, inconclusive) makes it blocked.
It builds `final.json` and `disposition.json`
and prints the replays' reports (every attempt of both tables, first), the
class report, the follow-up's status, each allocation gate, the evidence and
numbers of each attributed cell (all from `disposition.json`; the notes carry
none) and one line, `TASK30 disposition: pass|fail|blocked {counts,
"allocation": {"alloc": OUTCOME, "alloc-z": OUTCOME}}`. Every
attempt of the follow-up's table that is not judged (its id is not the
`attempt` of the inventory of `--followup`, nor of that stage's first stage)
must be void, shown from its output: the inventory there is of that attempt
and has a row for every cell it measures (the follow-up's, or for a second
stage its plan's), every row is a protocol failure whose archive exists and
is the sealed one, acceptance's own `success` in each archive is false, each
command it recorded did not time out and left a runner manifest in the
folder of its `--output`, and no runner manifest records an admitted run
(`runs` empty, `success` false); and the ledger closes the attempt
`inconclusive`, the status of a grid whose every cell is a protocol failure
(an attempt with no close is refused). An attempt id is of one output (every
output its ledger lines name), and a judged one is of the output of
`--followup`, or of its first stage. Anything else is refused, as it needs a
new policy decision (name the follow-up's final stage; an attempt that
measured, or may have, is no void attempt); the attempts are recorded as
`followup_attempts` and printed. Exit
status 0 pass, 1 fail, 2 blocked, 3 a refusal. `final.json` and
`disposition.json` are in the follow-up's output directory (`--followup`).
`--record` writes them (and refuses to replace files that exist); without it
both are derived again and any difference from the files is refused:
"changed TASK30 disposition".

This module is in neither table's seals: it is downstream of the replays
and its code is not on the replay path, so `task30_grid.py` stays as it is.
`disposition.json` records the seals of the code that derived it (`CODE`);
a later change to one of those files appends the seal it had when the
disposition was recorded to `HISTORY`, in the same commit, or the check
refuses it, naming every such file with the entries to paste into the
constants and the tests that pin them (PROTOCOL.md, "Seal histories").
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
from void_attempts import attempts_of

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
# of the timing grids (re-derived by the replay, or TASK30's sealed files,
# which have their own seals) or the allocation matrix's building of a
# toolchain (test_timing_followup.py names it).
CODE = ("task30_dispose.py", "task30_grid.py", "task30_followup.py",
        "timing_grid.py", "acceptance.py", "allocation_matrix.py",
        "allocation_analysis.py", "allocation_schema.py",
        "allocation_boundary.py", "path_schema.py", "void_attempts.py")
# Files of CODE that a record made before they existed does not carry:
# {file: (the file whose code held theirs, its seals in those records)}. The
# rule for the attempts of the follow-up's table was part of this module and
# is now void_attempts.py, shared with TASK31's disposition. A record may
# lack the file only if its seal of the host is one of those listed (the
# one `followup-r2/disposition.json` carries); a record made by code that
# has the file carries it.
ADDED = {"void_attempts.py": ("task30_dispose.py", (dict(
    bytes=50202, sha256="687e5e64c85b571d305b6e00fe1d2c34"
                   "8e864bf5d9298ce73366c88a069cef59"),))}
# Per file of CODE, the seals it had when a disposition was recorded, once
# it has changed since. The seals of 40e176538f are those before the harness
# gave its children /dev/null for stdin and dropped the "exclusive window"
# wording, except allocation_matrix.py's, which is the version before the
# TASK31 task and the client fixture family (and each file's own entries for
# the histories below).
HISTORY = {
    "task30_dispose.py": (dict(
        bytes=50202, sha256="687e5e64c85b571d305b6e00fe1d2c34"
                       "8e864bf5d9298ce73366c88a069cef59"),),
    "task30_grid.py": (dict(
        bytes=11833, sha256="1022124dc9a7f051da45166f1ad254eb"
                       "ca43853d5b5cccf4e0dc34cd38dc9978"),),
    "task30_followup.py": (dict(
        bytes=6360, sha256="287a3140d4bd12567ca4fcf8510d2c6a"
                       "111b96116db8ebff9461905920fe8ebd"),),
    "timing_grid.py": (dict(
        bytes=190317, sha256="6fbc62fac47439a5a7ad13dd1f2edf61"
                       "62729a15f7cb7d6c28434f1a4ee06ac3"),),
    "acceptance.py": (dict(
        bytes=39557, sha256="1076ad0d8f984a9081eaa2408554a483"
                       "2a0f3c092f6c5be25820537fa3c1a8e6"),),
    "allocation_matrix.py": (dict(
        bytes=67973, sha256="45d1fc4045f4b2dc57ce77f9ffd71211"
                       "6561ec3bd652aa5ebfd37b96a818221f"),)}

TAIL = (
    "Not shown by any row: CPU that neither allocates nor traces, net node "
    "visits and the candidates a match hides, live heap and retention (the "
    "candidate's startup heap is larger in every cell: GC, reported and not "
    "gated; its attribution belongs to TASK_31), work outside Trace and the "
    "kernel counter, the context (the work phase runs inside the "
    "allocation process, after all bracketed runs: not cold and not the "
    "timed process), and the code-layout and heap effects of the files "
    "outside the compared sources (the list SOURCES of the cases module) "
    "that the candidate changes, which are timing-only. Equal rows show "
    "equal work and result, not equal time. Every number of the cell (the "
    "counts, the intervals, the digest and the allocation rows) is in "
    "disposition.json, derived from the rows, never from this note.")


def note(text):
    return " ".join(text.split() + [TAIL])


def build(rows):
    """{cell: dict(evidence_class, note)}: the class of a cell is its case's
    (CASE_CLASS)."""
    return {cell: dict(evidence_class=CASE_CLASS[cell.rsplit("-", 1)[0]],
                       note=text) for cell, text in rows}


# The residual a cell's note gets when its recorded candidate CPU or wall CI
# upper bound exceeds 1 + the policy's margin (`residual_applies`; the
# stage-2 cells it applies to are exclude_literal_exact-10000 and
# exclude_dproc-10000). The notes of DISPOSITION carry none of it. They
# carry no number the rows do not check (a test pins that): the margin is the
# policy's, the intervals are in disposition.json.
RESIDUAL = (
    "Residual: the candidate CI upper bound exceeds the 3% margin; "
    "structural equality shows identical work, not identical timing; the "
    "candidate startup heap is larger, GC reported not gated, attribution "
    "in TASK_31.")
# What a deletion's rows show, in a note.
FIRES_NOTHING = (
    "The operation filters the net untraced and rebuilds nothing, and the "
    "workload installs no counted maker or collector, so the operation's "
    "rows are empty by construction and are no observation. What "
    "discriminates is the use of the result (which installed left sides "
    "still rewrite), traced with the same counts as develop, the same "
    "result digest and the exact allocation words.")

DISPOSITION = dict(
    schema="task30-disposition-v1", decided="2026-11-05", evidence=EVIDENCE,
    attributed=build([
        ("exclude_missing-10000", note(
            "-* of an absent name. " + FIRES_NOTHING)),
        ("exclude_matching-10000", note(
            "-* of one rule name. " + FIRES_NOTHING)),
        ("exclude_batch-10000", note(
            "-* of several rule names and one absent name. " +
            FIRES_NOTHING)),
        ("exclude_qualified-10000", note(
            "-* of a qualified name. " + FIRES_NOTHING)),
        ("exclude_literal_exact-10000", note(
            "-* of an exact namespaced name. " + FIRES_NOTHING)),
        ("history_excluded-10000", note(
            "exclude_ssfrags of a data theory. It rebuilds the simpset "
            "from the filtered history, as on develop and by the same "
            "source. The filtered history it rebuilds from carries only the "
            "empty matrix_drop fragment: no rule, no counted maker and no "
            "collector, so the work rows cannot show the rebuild, and "
            "their empty operation counts say nothing about it. The case "
            "rests on source identity, the exact allocation words and a "
            "use whose counts equal develop's (the data entries are "
            "gone), with the same result digest.")),
        ("exclude_literal_namespace-1", note(
            "-* of a literal namespace, which removes nothing. " +
            FIRES_NOTHING + " At this size the use is a single lookup, so "
            "the work evidence is thin. What is specific to this cell is "
            "that its control interval reaches above the margin, while the "
            "other controls fall only below the window: the case rests on "
            "source identity and the exact allocation words.")),
        ("exclude_dproc-10000", note(
            "-* of one dproc name. The rows show the operation firing no "
            "event and calling no maker, collector or dproc (the fixture is "
            "built so that a rebuild of the history would call every "
            "collector; it would call no maker, as no data follows, and no "
            "rebuild applies a dproc). The net is empty by construction, "
            "so the traced lookups show nothing about the dprocs. The "
            "deletion is shown by the dproc count of "
            "the use (equal to develop's; it restates the length of the "
            "digest's dproc names, it is not an independent witness), by "
            "the exact allocation words and by source identity.")),
        ("exclude_mixed-10000", note(
            "-* of one dproc and one rule. The rows show the operation "
            "firing nothing and a use with the same counts as develop's, "
            "its dproc count included (it restates the digest's dproc "
            "names), and the same result digest. The fixture is built so "
            "that a rebuild would call the maker and every collector.")),
        ("exclude_marker-10000", note(
            "A timed SIMP_CONV with Excl: the rows show the traced events "
            "and inferences of the operation, equal to develop's in both "
            "runs, and no use. The -* of the source runs inside "
            "process_tags, untraced; the deletion, the dominant cost, is "
            "shown only by the operation words and the source identity.")),
        ("exclude_marker_reuse-10000", note(
            "The reused conversion still runs the -* of the source in "
            "every call (SIMP_CONV processes its tags on each "
            "application); only the Excl construction is saved. The rows "
            "show the traced events of the operation, equal to develop's "
            "in both runs, and no use. The deletion is shown only by the "
            "operation words and the source identity.")),
        ("exclude_tactic_reuse-10000", note(
            "The reused tactic runs the -* in every application (only the "
            "Excl construction is saved). The rows show its traced events "
            "and inferences, equal to develop's in both runs, and no use. "
            "The deletion is shown only by the operation words and the "
            "source identity.")),
        ("exclude_tactic_complete-10000", note(
            "The tactic is built, applied and checked. The rows show its "
            "traced events and inferences, equal to develop's in both "
            "runs, and no use. The deletion is shown only by the "
            "operation words and the source identity."))]))
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


def residual_applies(found):
    """Whether the candidate's CPU or wall CI upper bound, as `metrics`
    records it, exceeds 1 + the policy's margin."""
    limit = 1 + a.EQUIVALENCE_POLICY["margin"]
    return any(found[key]["interval"][1] > limit for key in ("cpu", "wall"))


def with_residual(text):
    """The note with the residual sentence before its closing TAIL."""
    a.require(text.endswith(TAIL), "a note must end with TAIL")
    return " ".join([text[:-len(TAIL)].strip(), RESIDUAL, TAIL])


def split(cell):
    """(case, size) of a cell name."""
    case, size = cell.rsplit("-", 1)
    return case, int(size)


def row(decisions, cell):
    case, size = split(cell)
    return decisions["cases"].get(case, {}).get("cells", {}).get(str(size))


def phrase(decision):
    """What a row or cell decision other than `equal` says, as a predicate:
    the baseline is develop."""
    return {"differs": "differs from develop",
            "inconclusive": "is inconclusive"}.get(
                decision, "has decision %s" % decision)


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
            if phase not in here["phases"] or phase not in there["phases"]:
                return "operation phase %s is missing from %s" % (
                    phase, "alloc-z" if phase not in here["phases"] else
                    "alloc")
            if set(here["phases"][phase]) != set(there["phases"][phase]):
                return ("operation phase %s has other metrics in alloc (%s)"
                        " than in alloc-z (%s)" % (
                            phase, ", ".join(sorted(there["phases"][phase])),
                            ", ".join(sorted(here["phases"][phase]))))
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
        # What names a row comes first: a row that does not reproduce, then
        # a row that is not equal; the cell's status is the backstop.
        sides = {}
        for e in section["nondeterminism"]:
            if e[:2] == [case, size]:
                sides.setdefault(e[2], []).append(e[3])
        varying = ["work row %s is not reproducible (%s)" % (
            key, ", ".join(found)) for key, found in sides.items()]
        if varying:
            return "; ".join(varying)
        rows = row(self.new, cell).get("work") or {}
        for key, found in rows.items():
            if found["decision"] != "equal":
                return ("work row %s %s (candidate %s, baseline %s, "
                        "control %s)" % (key, phrase(found["decision"]), *(
                            json.dumps(sorted(found[side]))
                            for side in ("candidate", "baseline",
                                         "control"))))
        if section["cells"].get(name) != "equal":
            return "the cell's work status is %r, not 'equal'" % (
                section["cells"].get(name),)
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
        if found["decision"] != "equal":
            return "result.digest row %s" % phrase(found["decision"])
        if len(found["candidate"]) != 1 or len(found["baseline"]) != 1:
            return "result.digest row is not reproducible (%d candidate " \
                "and %d baseline values)" % (len(found["candidate"]),
                                             len(found["baseline"]))
        return None


def counts(rows):
    """{run: {key: [count, ...]}} of the count rows of a cell that are not
    zero throughout, as the candidate has them: every distinct value, sorted
    (one for a row that reproduces; several are not an error here, the
    evidence of the cell names that)."""
    found = {k: {} for k in SECTIONS}
    for name, value in sorted((rows or {}).items()):
        if name == "result.digest":
            continue
        _, run, key = name.split(".", 2)
        values = sorted(int(v) for v in value["candidate"])
        if values != [0]:
            found[run][key] = values
    return found


def metrics(report):
    """The candidate's and the control's CPU, wall and GC of one cell:
    decision, median ratio and 95% interval; the control's interval and
    decision beside, and for a gated metric (CPU, wall) whether the control
    is valid, as acceptance computed it (`control_valid`: its interval lies
    within the equivalence window; None for GC, which has no window)."""
    result, = report["workloads"]
    found = {}
    for key, m in result["candidate"]["metrics"].items():
        control = result["control"]["metrics"][key]
        found[key] = dict(
            decision=m["decision"], reason=m["reason"],
            median=m["median_paired_ratio"],
            interval=m["paired_ratio_bootstrap_95_percent"],
            control_decision=control["decision"],
            control_interval=control["paired_ratio_bootstrap_95_percent"],
            control_valid=m.get("control_valid"))
        a.require(isinstance(found[key]["control_valid"], bool) or
                  key not in a.EQUIVALENCE_POLICY["gated_timing"],
                  "the %s of a cell has no control_valid, which acceptance "
                  "computes for a gated metric (%s)" % (key, ", ".join(
                      a.EQUIVALENCE_POLICY["gated_timing"])))
    return found


def record_of(spec, final, reports, new, evidence, result):
    """The disposition record: `result` is timing_grid.dispose's, the
    per-cell record is the evidence class, the note, the metrics of the
    final report, the work counts and the digest, the number of allocation
    rows and what failed, if anything. `residual` records whether the
    candidate's CPU or wall upper bound exceeds the policy's margin; when it
    does, the note is the spec's with `RESIDUAL` added."""
    cells = {}
    for cell, listed in spec["attributed"].items():
        case, size = split(cell)
        found = row(new, cell) or {}
        work = found.get("work")
        digest = None if not work or "result.digest" not in work else \
            sorted(work["result.digest"]["candidate"])
        found_metrics = metrics(reports[case, size])
        residual = residual_applies(found_metrics)
        cells[cell] = dict(
            listed, residual=residual,
            note=with_residual(listed["note"]) if residual
            else listed["note"],
            decision=("attributed" if cell in
                      result["cells"]["attributed"] else "blocking"),
            failed=evidence.holds(cell), metrics=found_metrics,
            work=None if work is None else counts(work), digest=digest,
            allocation_rows=sum(len(m) for m in
                                found.get("phases", {}).values()))
    return dict(
        schema=spec["schema"], decided=spec["decided"],
        evidence=list(spec["evidence"]), status=result["status"],
        counts=result["counts"], cells=result["cells"],
        blocking=result["blocking"], allocation=result["allocation"],
        attributed=cells,
        pinned=final.get("source_identity", {}).get("reviewed", {}),
        replaced=final["replaced"])


def seals(here=None):
    here = a.HERE if here is None else Path(here)
    return {name: a.seal(here / name) for name in CODE}


# Beside HISTORY, what else a change to a file of CODE asks of the commit
# that makes it, for the records that were made by the old file (PROTOCOL.md,
# "Seal histories"): the constant, and whether its entries are keyed by file
# (`"name": (SEAL,),`) or are seals in a tuple (`SEAL,`).
ALSO = {
    "timing_grid.py": ("task30_followup.ENGINES", False),
    "acceptance.py": ("task30_followup.ACCEPTANCE", False),
    "task30_followup.py": ("task30_followup.DRIVERS", False),
    "task30_grid.py": ("task30_followup.SEALED_HISTORY", True)}


def entries(name, seal):
    """[(constant, literal text)] a changed file of CODE asks for, as the
    entry to paste into the constant: HISTORY maps the file to a tuple of
    seals; ENGINES, ACCEPTANCE and DRIVERS are tuples of seals; the one
    SEALED_HISTORY entry is, like HISTORY's, a tuple of seals under the
    file's name. Each literal is in backticks."""
    text = json.dumps(seal, sort_keys=True)
    keyed = '`%s: (%s,),`' % (json.dumps(name), text)
    found = [("task30_dispose.HISTORY", keyed)]
    if name in ALSO:
        constant, is_keyed = ALSO[name]
        found.append((constant, keyed if is_keyed else "`%s,`" % text))
    return found


def check_code(recorded, here=None):
    """The seals a disposition records are those of the code now or of
    the earlier code HISTORY names. Every file that is not is named in one
    refusal, with the entries the commit pastes into the constants (each
    the literal element of its constant) and the tests that pin them."""
    now = seals(here)
    older = {name for name, (host, before) in ADDED.items()
             if isinstance(recorded, dict) and recorded.get(host) in before}
    names = [name for name in CODE if name not in older]
    a.require(isinstance(recorded, dict) and set(recorded) == set(names),
              "changed TASK30 disposition: the recorded code is not %s"
              % ", ".join(names))
    changed = [name for name in names
               if recorded[name] != now[name] and
               recorded[name] not in HISTORY.get(name, ())]
    if changed:
        lines = []
        for name in changed:
            lines.append("%s: add %s" % (name, " and, where records were "
                                         "made by the old file, ".join(
                "to %s the entry %s" % found
                for found in entries(name, recorded[name]))))
        raise ValueError(
            "changed TASK30 disposition: %d file(s) changed since it was "
            "recorded; in the same commit add each entry below to its "
            "constant and update the tests that pin those constants "
            "(task30_dispose.HISTORY: test_task30_dispose.py; "
            "task30_followup.ENGINES, ACCEPTANCE, DRIVERS and "
            "SEALED_HISTORY: test_task30_grid.py); a change to a history "
            "constant changes its file, which then needs its own entry "
            "(PROTOCOL.md, \"Seal histories\"): %s"
            % (len(changed), "; ".join(lines)))


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


def loaded(path, what, partial=False):
    a.require((path / "inventory.json").exists() and
              (path / "decisions.json").exists(),
              "%s is not a complete grid: %s" % (what, path))
    a.require(not (partial and (path / "decisions-partial.json").exists()),
              "%s has a partial decision (decisions-partial.json) beside "
              "a complete decisions.json: the partial file is stale (an "
              "earlier --only run left it) and may be removed: %s"
              % (what, path))
    return a.load(path / "inventory.json")


def allocation_gate(label, code, decisions):
    """(outcome, reasons) of one allocation grid, from the status code
    `allocation_matrix.replay` returned (0 pass, 1 fail, 2 any other) and
    the decisions it verified: an allocation `fail` is `fail`, anything but
    a pass is `blocked`, and the reasons name the grid and what is not."""
    reasons = []
    if decisions.get("status") != "pass":
        reasons.append("status %s" % decisions.get("status"))
    if not decisions.get("complete"):
        reasons.append("complete false")
    for key in ("acceptance_pairs", "acceptance_baseline"):
        if decisions.get(key) is False:
            reasons.append("%s false" % key)
    for key in ("nondeterminism", "unresolved"):
        if decisions.get(key):
            reasons.append("%s: %d" % (key, len(decisions[key])))
    if code == 1 or decisions.get("status") == "fail":
        return "fail", ["%s: fail (%s)" % (label, ", ".join(reasons))]
    if code != 0 or reasons:
        return "blocked", ["%s: not pass (%s; replay status %d)" % (
            label, ", ".join(reasons) or "no reason found", code)]
    return "pass", []


def cheap(args, old, new):
    """Every comparison that needs no replay, first: the arguments and the
    pairing of each timing grid with the allocation grid of its harness.
    The paths, resolved."""
    grid, followup = args.grid.resolve(), args.followup.resolve()
    allocation = args.allocation.resolve()
    allocz = args.followup_allocation.resolve()
    a.require(allocation != allocz, "one allocation grid cannot serve both "
              "harnesses: --allocation (Y) and --followup-allocation (Z)")
    timing_y, timing_z = loaded(grid, "--grid"), loaded(followup,
                                                        "--followup")
    a.require("replaces" in timing_z, "--followup is not a follow-up grid")
    a.require((followup / timing_z["replaces"]["grid"]).resolve() == grid,
              "--grid is not the grid the follow-up replaced (%s)"
              % (followup / timing_z["replaces"]["grid"]).resolve())
    counted_y = loaded(allocation, "--allocation", partial=True)
    counted_z = loaded(allocz, "--followup-allocation", partial=True)
    pair(timing_y, counted_y, "TASK30 (Y)")
    pair(timing_z, counted_z, "follow-up (Z)")
    a.require(new.t.replaces is not None and new.t.replaces.engine is old,
              "the follow-up does not replace the TASK30 table's grid")
    judged = {timing_z["attempt"]: followup}
    if timing_z["schema"] == new.t.schema("extension"):
        first = (followup / timing_z["grid"]).resolve()
        judged[loaded(first, "the first stage of --followup")[
            "attempt"]] = first
    return dict(grid=grid, followup=followup, allocation=allocation,
                allocz=allocz, attempts=attempts_of(args, new, judged))


def derive(args, old=base.ENGINE, new=follow.ENGINE, spec=DISPOSITION):
    """Replay everything and derive (final, disposition, lines). `old` and
    `new` are the engines of the TASK30 table and of its follow-up."""
    paths = cheap(args, old, new)
    grid, pilot = paths["grid"], args.pilot.resolve()
    followup, allocation, allocz = (paths[k] for k in (
        "followup", "allocation", "allocz"))
    # The follow-up's replay replays the TASK30 grid in full first.
    new.replay(argparse.Namespace(
        output=followup, partial=False, repo=args.repo, ledger=args.ledger,
        pilot=args.followup_pilot.resolve(), replaces_pilot=pilot))
    y, z = old.replayed, new.replayed
    a.require(y is not None and z is not None, "nothing was replayed")
    a.require(new.bound()["grid"] == grid, "--grid is not the grid the "
              "follow-up replaced")
    # The follow-up is the follow-up's final stage, as the grid it replaced
    # is (`bind_replaced`).
    a.require(z["inventory"]["schema"] == new.t.schema("extension") or
              not new.planned(z["stage1"], z["first"]),
              "--followup is not the follow-up's final stage: its second "
              "stage is still to come, name that")
    # A complete grid's decisions.json is what the replay compared with
    # (`loaded` refused a partial file beside them).
    gates, found = {}, {}
    for label, path in (("alloc", allocation), ("alloc-z", allocz)):
        code = am.replay(argparse.Namespace(output=path))
        found[label] = a.load(path / "decisions.json")
        gates[label] = allocation_gate(label, code, found[label])
    decisions_y, decisions_z = found["alloc"], found["alloc-z"]
    reports = {**y["stage1"], **y["stage2"], **z["stage1"], **z["stage2"]}
    final = old.h.with_sources(old.h.summary(reports), y["inventory"])
    if "remeasured" in y["decisions"]:
        final["remeasured"] = y["decisions"]["remeasured"]
    first_y, first_z = y["first"], z["first"]
    final["replaced"] = dict(
        cells=sorted(new.t.names()),
        replaced_seed=first_y.get("layout_seed"),
        followup_seed=first_z.get("layout_seed"),
        followup_second_seed=(
            z["inventory"].get("layout_seed")
            if z["inventory"]["schema"] == new.t.schema("extension")
            else None),
        replaced_counts=first_y["iterations_seal"],
        followup_counts=first_z["iterations_seal"],
        replaced_candidate=first_y["candidate"],
        followup_candidate=first_z["candidate"],
        followup_status=z["decisions"]["status"])
    evidence = Evidence(spec, final, decisions_y, decisions_z)
    result = tg.dispose(final, spec["attributed"], evidence.holds,
                        judged=new.t.names())
    outcomes = {o for o, _ in gates.values()}
    result["allocation"] = {
        label: dict(outcome=o, status=found[label].get("status"),
                    reasons=r) for label, (o, r) in gates.items()}
    result["status"] = ("fail" if "fail" in outcomes or
                        result["status"] == "fail" else
                        "blocked" if "blocked" in outcomes or
                        result["status"] == "blocked" else "pass")
    record = record_of(spec, final, reports, decisions_z, evidence, result)
    record["code"] = seals()
    record["followup_attempts"] = paths["attempts"]
    lines = tg.class_report("%s final" % old.t.label, final)
    lines.append("FOLLOW-UP status %s (cells %s)" % (
        final["replaced"]["followup_status"],
        ", ".join(final["replaced"]["cells"])))
    for found in paths["attempts"]:
        lines.append("FOLLOW-UP-ATTEMPT %s status %s output %s: %s" % (
            found["attempt"], found["status"], found["output"],
            "void (no measurement admitted)" if found["void"] else
            "judged"))
    for label, (outcome, reasons) in gates.items():
        lines.append("ALLOCATION %s: %s" % (label, outcome))
        lines += ["ALLOCATION-%s %s" % (outcome.upper(), r)
                  for r in reasons]
    for cell, entry in record["attributed"].items():
        lines += cell_lines(cell, entry)
    for cell, reason in record["blocking"].items():
        if cell not in record["attributed"]:
            lines.append("BLOCKING %s: %s" % (cell, reason))
    return final, record, lines


def cell_lines(cell, found):
    """What the record says of an attributed cell, printed: all the numbers
    are from it (never from the note)."""
    lines = ["%s %s (%s)%s" % (
        found["decision"].upper(), cell, found["evidence_class"],
        "" if found["failed"] is None else ": " + found["failed"])]
    for run in SECTIONS:
        if found["work"] is not None:
            lines.append("  work %s %s" % (
                run, json.dumps(found["work"][run], sort_keys=True)))
    for key in ("cpu", "wall", "gc"):
        m = found["metrics"][key]
        valid = m["control_valid"]
        lines.append(
            "  %s %s: median %s, interval %s, control interval %s%s" % (
                key, m["decision"], m["median"], m["interval"],
                m["control_interval"], "" if valid is None else
                " (within the window: %s)" % ("yes" if valid else "no")))
    lines.append("  digest %s; allocation rows %d" % (
        json.dumps(found["digest"]), found["allocation_rows"]))
    return lines


def canon(value):
    """What a file holds of a value (JSON keeps no tuple)."""
    return json.loads(json.dumps(value))


def disposition(args, **engines):
    followup = args.followup.resolve()
    # Every refusal that needs no replay comes before any.
    cheap(args, engines.get("old", base.ENGINE),
          engines.get("new", follow.ENGINE))
    names = ("final.json", "disposition.json")
    if args.record:
        for name in names:
            a.require(not (followup / name).exists(), "refusing to replace "
                      "the recorded %s; remove it to record again" % name)
    else:
        for name in names:
            a.require((followup / name).exists(), "no recorded %s: record "
                      "it with --record" % name)
        recorded = a.load(followup / "disposition.json")
        check_code(recorded.get("code"))
    final, record, lines = derive(args, **engines)
    for line in lines:
        print(line)
    files = {"final.json": final, "disposition.json": record}
    if args.record:
        for name, value in files.items():
            a.save(followup / name, value)
    else:
        for name, value in files.items():
            held = a.load(followup / name)
            if name == "disposition.json":
                held = dict(held, code=record["code"])
            a.require(canon(value) == held,
                      "changed TASK30 disposition: %s" % name)
    print("TASK30 disposition: %s %s" % (
        record["status"], json.dumps(dict(record["counts"], allocation={
            label: found["outcome"]
            for label, found in record["allocation"].items()}))))
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
