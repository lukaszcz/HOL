#!/usr/bin/env python3
"""The TASK30 disposition (task30_dispose.py): the spec of the 13 attributed
cells, the evidence for a cell, and the command that replays everything and
records or checks `final.json` and `disposition.json`.

The command runs here on the toy rig of test_timing_followup.py (a replaced
grid and a follow-up of two of its cells, replayed for real), with the
allocation grids written by hand and their replay stood in for: the
allocation matrix has its own tests (test_allocation_*.py), and the real
TASK30 records are probed by hand (PROTOCOL.md).
"""
import argparse
import contextlib
import copy
import io
import json
import os
import re
import shutil
from pathlib import Path
import unittest
from unittest.mock import patch

import acceptance as a
import allocation_analysis as an
import allocation_matrix as am
import allocation_schema as schema
import allocation_testbed as tb
import task30_dispose as td
import test_timing_followup as ttf
import test_timing_grid as ttg
import timing_grid as tg

THIRTEEN = (
    "exclude_missing-10000", "exclude_matching-10000",
    "exclude_batch-10000", "exclude_qualified-10000",
    "exclude_literal_exact-10000", "history_excluded-10000",
    "exclude_literal_namespace-1", "exclude_dproc-10000",
    "exclude_mixed-10000", "exclude_marker-10000",
    "exclude_marker_reuse-10000", "exclude_tactic_reuse-10000",
    "exclude_tactic_complete-10000")


class Spec(unittest.TestCase):
    def test_the_disposition_is_the_13_cells_the_policy_owner_listed(self):
        d = td.DISPOSITION
        self.assertEqual((d["schema"], d["decided"], d["evidence"]),
                         ("task30-disposition-v1", "2026-11-05",
                          ("sources", "allocation", "work", "result")))
        self.assertEqual(sorted(d["attributed"]), sorted(THIRTEEN))
        # ... which are the control-limited cells of the TASK30 grid, and
        # none of the cells the follow-up replaced.
        self.assertNotIn("exclude_partial-1", d["attributed"])
        self.assertNotIn("exclude_tactic_reuse-0", d["attributed"])

    def test_the_class_of_a_cell_is_fixed_by_its_case(self):
        want = {
            "deletion": ("exclude_missing", "exclude_matching",
                         "exclude_batch", "exclude_qualified",
                         "exclude_literal_exact",
                         "exclude_literal_namespace", "history_excluded"),
            "dproc-deletion": ("exclude_dproc", "exclude_mixed"),
            "operation": ("exclude_marker", "exclude_marker_reuse",
                          "exclude_tactic_reuse",
                          "exclude_tactic_complete")}
        found = {}
        for cell, entry in td.DISPOSITION["attributed"].items():
            found.setdefault(entry["evidence_class"], []).append(
                cell.rsplit("-", 1)[0])
        self.assertEqual({k: sorted(v) for k, v in found.items()},
                         {k: sorted(v) for k, v in want.items()})
        self.assertEqual(set(td.CASE_CLASS), {c for v in want.values()
                                              for c in v})

    def test_the_cells_are_cells_of_the_task30_table(self):
        import task30_grid
        self.assertLessEqual(set(td.DISPOSITION["attributed"]),
                             set(task30_grid.TABLE.names()))

    def test_every_note_says_what_no_row_shows(self):
        for cell, entry in td.DISPOSITION["attributed"].items():
            with self.subTest(cell):
                text = entry["note"]
                self.assertIn("Not shown by any row", text)
                self.assertIn("not equal time", text.replace("\n", " "))
                self.assertIn("startup heap is larger", text)
                self.assertIn("TASK_31", text)
                self.assertNotIn("\t", text)

    def test_the_tail_names_all_six_things_no_row_shows(self):
        for item in ("CPU that neither allocates nor traces",
                     "net node visits", "live heap and retention",
                     "work outside Trace and the kernel counter",
                     "the work phase runs inside the allocation process",
                     "not cold and not the timed process",
                     "code-layout and heap effects of the files outside "
                     "the compared sources (the list SOURCES of the cases "
                     "module) that the candidate changes"):
            self.assertIn(item, td.TAIL)
        self.assertNotIn("likeliest", td.TAIL)
        for cell, entry in td.DISPOSITION["attributed"].items():
            self.assertTrue(entry["note"].endswith(td.TAIL), cell)

    def test_the_notes_do_not_present_zeros_by_construction(self):
        notes = td.DISPOSITION["attributed"]
        for cell in ("exclude_missing-10000", "exclude_matching-10000",
                     "exclude_batch-10000", "exclude_qualified-10000",
                     "exclude_literal_exact-10000",
                     "exclude_literal_namespace-1"):
            text = " ".join(notes[cell]["note"].split())
            self.assertIn("empty by construction", text, cell)
            self.assertIn("rebuilds nothing", text, cell)
            self.assertIn("exact allocation words", text, cell)
            self.assertNotIn("The rows show the operation firing", text)
        text = " ".join(notes["history_excluded-10000"]["note"].split())
        self.assertIn("rebuilds the simpset from the filtered history",
                      text)
        self.assertIn("cannot show the rebuild", text)
        self.assertIn("source identity", text)
        self.assertNotIn("no replay", text)
        text = " ".join(notes["exclude_literal_namespace-1"]["note"].split())
        self.assertIn("single lookup", text)
        self.assertIn("its control interval reaches above the margin, "
                      "while the other controls fall only below the "
                      "window", text)
        self.assertNotIn("lies outside", text)
        self.assertIn("exact allocation words", text)
        self.assertNotIn("operation words", text.replace(
            "exact allocation words", ""))
        self.assertNotIn("inconclusive", text)

    def test_the_notes_of_the_dproc_cells_say_what_a_rebuild_would_call(
            self):
        notes = td.DISPOSITION["attributed"]
        text = " ".join(notes["exclude_dproc-10000"]["note"].split())
        self.assertIn("would call every collector; it would call no "
                      "maker, as no data follows, and no rebuild applies "
                      "a dproc", text)
        text = " ".join(notes["exclude_mixed-10000"]["note"].split())
        self.assertIn("a rebuild would call the maker and every "
                      "collector", text)
        text = " ".join(notes["history_excluded-10000"]["note"].split())
        self.assertIn("The filtered history it rebuilds from carries only "
                      "the empty matrix_drop fragment", text)
        self.assertIn("so the work rows cannot show the rebuild", text)

    def metric(self, interval, **more):
        return dict(decision="inconclusive", reason="r",
                    median_paired_ratio=1.0,
                    paired_ratio_bootstrap_95_percent=interval, **more)

    def test_the_control_validity_is_the_one_acceptance_computed(self):
        def report(**valid):
            keys = ("cpu", "wall", "gc")
            return dict(workloads=[dict(
                candidate=dict(metrics={k: self.metric(
                    [1.0, 1.0], **({"control_valid": valid[k]}
                                   if k in valid else {}))
                    for k in keys}),
                control=dict(metrics={k: dict(
                    decision="pass", paired_ratio_bootstrap_95_percent=(
                        None if k == "wall" else [0.9, 1.1]))
                    for k in keys}))])
        found = td.metrics(report(cpu=False, wall=True))
        self.assertIs(found["cpu"]["control_valid"], False)
        self.assertIs(found["wall"]["control_valid"], True)
        self.assertIsNone(found["gc"]["control_valid"])
        self.assertIsNone(found["wall"]["control_interval"])
        # A gated metric without it is an error, not a null.
        with self.assertRaisesRegex(
                ValueError, "the wall of a cell has no control_valid"):
            td.metrics(report(cpu=True))
        lines = td.cell_lines("c", dict(
            decision="attributed", evidence_class="deletion", failed=None,
            work=None, metrics=found, digest=None, allocation_rows=0))
        self.assertTrue(any(x.startswith("  cpu ") and x.endswith(
            "(within the window: no)") for x in lines))
        self.assertTrue(any(x.startswith("  gc ") and
                            "within the window" not in x for x in lines))

    def test_no_note_carries_a_number(self):
        # Every number of a cell comes from disposition.json, derived from
        # the rows; a note states none the rows do not check. The one
        # exception is the name of the follow-up task. The residual
        # sentence, added by the command, names the policy's margin, which
        # is checked against the acceptance policy.
        self.assertEqual(a.EQUIVALENCE_POLICY["margin"], 0.03)
        for cell, entry in td.DISPOSITION["attributed"].items():
            with self.subTest(cell):
                text = entry["note"].replace("TASK_31", "").replace(
                    "3% margin", "")
                self.assertEqual(
                    [c for c in text if c.isdigit()], [], text)

    def test_the_notes_of_the_spec_carry_no_residual(self):
        for cell, entry in td.DISPOSITION["attributed"].items():
            with self.subTest(cell):
                self.assertNotIn("Residual", entry["note"])

    def test_the_residual_is_derived_from_the_recorded_interval(self):
        def found(cpu, wall):
            return dict(cpu=dict(interval=[0.99, cpu]),
                        wall=dict(interval=[0.99, wall]))
        margin = 1 + a.EQUIVALENCE_POLICY["margin"]
        self.assertTrue(td.residual_applies(found(margin + 0.001, 1.0)))
        self.assertTrue(td.residual_applies(found(1.0, margin + 0.001)))
        self.assertFalse(td.residual_applies(found(margin, 1.0299)))
        base = td.DISPOSITION["attributed"]["exclude_missing-10000"]["note"]
        text = td.with_residual(base)
        self.assertTrue(text.endswith(td.TAIL))
        self.assertIn(td.RESIDUAL, text)
        self.assertEqual(text.replace(" " + td.RESIDUAL, ""), base)
        for part in (
                "candidate CI upper bound exceeds the 3% margin",
                "structural equality shows identical work, not "
                "identical timing",
                "candidate startup heap is larger, GC reported not "
                "gated, attribution in TASK_31"):
            self.assertIn(part, td.RESIDUAL)
        self.assertEqual(
            [c for c in td.RESIDUAL.replace("TASK_31", "").replace(
                "3% margin", "") if c.isdigit()], [])

    def test_on_the_stage_2_data_it_applies_to_exactly_the_two_cells(self):
        # Read-only; set TASK30_STAGE2_DECISIONS to stage2/decisions.json.
        # It skips by default: the evidence is deliberately not in the repo
        # (the in-suite stand-in is the test of the values below).
        path = Path(os.environ.get("TASK30_STAGE2_DECISIONS", "/nonexistent"))
        if not path.exists():
            self.skipTest("TASK30_STAGE2_DECISIONS names no stage-2 record")
        decisions = json.loads(path.read_text())
        found = {}
        for row in decisions["workloads"]:
            cell = "%s-%d" % (row["case"], row["size"])
            if cell in td.DISPOSITION["attributed"]:
                found[cell] = td.residual_applies({
                    key: dict(interval=row["metrics"][key][
                        "paired_ratio_bootstrap_95_percent"])
                    for key in ("cpu", "wall")})
        self.assertEqual(sorted(found), sorted(THIRTEEN))
        self.assertEqual(sorted(c for c, v in found.items() if v),
                         ["exclude_dproc-10000",
                          "exclude_literal_exact-10000"])

    def test_the_values_of_the_two_real_cells_and_the_others(self):
        # Stage 2's recorded upper bounds: the two cells are above the 3%
        # margin, the other 11 at most 1.0185. 1.0277 is a near-margin
        # probe (exclude_tactic_reuse-0, not one of the 13 cells).
        for upper, want in ((1.0406385994423937, True),
                            (1.0753660032366656, True),
                            (1.0185, False), (1.0277270613573477, False)):
            self.assertEqual(td.residual_applies(dict(
                cpu=dict(interval=[1.0, upper]),
                wall=dict(interval=[1.0, 1.0]))), want)

    def test_the_notes_of_the_marker_and_tactic_cells_say_where_the_work_is(
            self):
        for case in ("exclude_marker_reuse", "exclude_tactic_reuse"):
            note = td.DISPOSITION["attributed"][case + "-10000"]["note"]
            self.assertIn("in every", note)
            self.assertIn("only the Excl construction is saved", note)
            self.assertNotIn("Residual", note)
        for case in td.CASE_CLASS:
            if td.CASE_CLASS[case] == td.OPERATION:
                note = td.DISPOSITION["attributed"][case + "-10000"]["note"]
                self.assertIn("only by the operation words", note)

    def test_the_seal_histories_name_only_the_code(self):
        # The seals of 40e176538f, before the harness gave its children
        # /dev/null for stdin.
        self.assertEqual(td.HISTORY, {
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
                               "2a0f3c092f6c5be25820537fa3c1a8e6"),)})
        self.assertEqual(set(td.seals()), set(td.CODE))
        for name in td.CODE:
            self.assertTrue((a.HERE / name).is_file(), name)


class Classes(unittest.TestCase):
    """What each class must show of the rows of its cell."""

    def groups(self, first=(), second=(), use=()):
        return dict(first=list(first), second=list(second), use=list(use))

    REDUCE = "work.use.trace.4.REDUCE"

    def test_a_deletion_fires_nothing_and_has_a_use(self):
        td_ = td.DELETION
        self.assertIsNone(td.class_failure(
            td_, self.groups(use=[self.REDUCE])))
        for label, groups, text in (
                ("a use that is empty (a hook left at noUse)",
                 self.groups(), "work.use has no work.use.trace.4.REDUCE"),
                ("a use without the traversal event",
                 self.groups(use=["work.use.kernel.total"]),
                 "work.use has no work.use.trace.4.REDUCE"),
                ("an operation that fires", self.groups(
                    first=["work.first.trace.4.REDUCE"], use=[self.REDUCE]),
                 "work.first/work.second are not empty"),
                ("a second run that fires", self.groups(
                    second=["work.second.maker"], use=[self.REDUCE]),
                 "work.first/work.second are not empty"),
                ("no work rows", None, "no work rows")):
            with self.subTest(label):
                self.assertIn(text, td.class_failure(td_, groups))

    def test_a_dproc_deletion_also_applies_the_dprocs(self):
        both = self.groups(use=[self.REDUCE, "work.use.dproc"])
        self.assertIsNone(td.class_failure(td.DPROC, both))
        self.assertIn("no work.use.dproc", td.class_failure(
            td.DPROC, self.groups(use=[self.REDUCE])))
        self.assertIn("work.use.trace.4.REDUCE", td.class_failure(
            td.DPROC, self.groups(use=["work.use.dproc"])))

    def test_an_operation_fires_in_both_runs_and_has_no_use(self):
        ok = self.groups(first=["work.first.trace.4.REDUCE"],
                         second=["work.second.trace.4.REDUCE"])
        self.assertIsNone(td.class_failure(td.OPERATION, ok))
        for label, groups in (
                ("first empty", dict(ok, first=[])),
                ("second empty", dict(ok, second=[])),
                ("everything empty", self.groups())):
            with self.subTest(label):
                self.assertIn("work.first or work.second is empty",
                              td.class_failure(td.OPERATION, groups))
        self.assertIn("work.use is not empty", td.class_failure(
            td.OPERATION, dict(ok, use=[self.REDUCE])))

    def test_an_unknown_class_fails(self):
        self.assertIn("unknown evidence class", td.class_failure(
            "construct-reuse", self.groups()))


def work_row(count, decision="equal", same=True, baseline=True,
             candidate=True):
    return dict(decision=decision, control_identical=same,
                baseline={str(count): 20}, candidate={str(count): 20},
                control={str(count): 20}, difference={"0": 20},
                deterministic=dict(baseline=baseline, candidate=candidate))


def digest_row(text="abc", decision="equal"):
    return dict(work_row(0, decision), baseline={text: 20},
                candidate={text: 20}, control={text: 20})


DELETION_WORK = {"result.digest": digest_row(),
                 "work.first.maker": work_row(0),
                 "work.use.trace.4.REDUCE": work_row(10)}
OPERATION_WORK = {"result.digest": digest_row(),
                  "work.first.trace.4.REDUCE": work_row(1),
                  "work.second.trace.4.REDUCE": work_row(1),
                  "work.first.kernel.total": work_row(4),
                  "work.second.kernel.total": work_row(4)}
WORDS = {phase: {metric: dict(decision="pass", baseline={"100": 20},
                              candidate={"100": 20})
                 for metric in schema.METRICS}
         for phase in ("setup", "operation_first", "operation_steady",
                       "apply")}


def alloc_decisions(cells, setup=None):
    """The decisions of an allocation grid with the given cells,
    {(case, size): work rows}: the words pass and are the same everywhere;
    `setup` is the setup row's word."""
    out = dict(schema="task29b-decisions-v1", cases={}, complete=True,
               status="pass", work_status="equal", unresolved=[],
               nondeterminism=[])
    names = {}
    for (case, size), work in cells.items():
        phases = copy.deepcopy(WORDS)
        if setup is not None:
            for m in phases["setup"].values():
                m["candidate"] = m["baseline"] = {str(setup): 20}
        out["cases"].setdefault(case, dict(cells={}))["cells"][str(size)] \
            = dict(phases=phases, work=copy.deepcopy(work))
        names[am.name_of(case, size)] = "equal"
    out["work"] = dict(status="equal", cells=names, nondeterminism=[],
                       missing=[], unresolved=[])
    return out


LIMITED = {("exclude_missing", 10): DELETION_WORK,
           ("exclude_empty", 10000): OPERATION_WORK}
SPEC = dict(
    schema="toy-disposition-v1", decided="2026-11-05", evidence=td.EVIDENCE,
    attributed={"exclude_missing-10": dict(evidence_class=td.DELETION,
                                           note="n1"),
                "exclude_empty-10000": dict(evidence_class=td.OPERATION,
                                            note="n2")})
CLEAN = dict(files=["src/one.sml"], differing=[], reviewed={
    "src/two.sml": dict(blob="b" * 40, reason="a reviewed move")})


def make_evidence(new=None, old=None, final=None):
    final = dict(source_identity=CLEAN) if final is None else final
    return td.Evidence(SPEC, final,
                       old or alloc_decisions(LIMITED, setup=7),
                       new or alloc_decisions(LIMITED, setup=9))


class Evidence(unittest.TestCase):
    """`Evidence.holds`: what fails is named."""

    def make(self, new=None, old=None, final=None):
        return make_evidence(new, old, final)

    def test_the_evidence_holds_for_both_classes(self):
        ev = self.make()
        for cell in SPEC["attributed"]:
            self.assertIsNone(ev.holds(cell), cell)

    def test_a_source_that_differs_names_the_file_and_the_pinned_ones(self):
        ev = self.make(final=dict(source_identity=dict(
            CLEAN, differing=["src/one.sml"])))
        failed = ev.holds("exclude_missing-10")
        self.assertRegex(failed, r"^sources: source differs from develop: "
                         r"src/one.sml \(pinned and reviewed: src/two.sml")
        self.assertIn("no source record", self.make(
            final=dict(a=1)).holds("exclude_missing-10"))

    def test_an_allocation_row_of_alloc_z_that_does_not_pass_is_named(self):
        new = alloc_decisions(LIMITED, setup=9)
        new["cases"]["exclude_missing"]["cells"]["10"]["phases"]["apply"][
            "heap"]["decision"] = "fail"
        self.assertEqual(
            self.make(new=new).holds("exclude_missing-10"),
            "allocation: allocation row apply.heap of alloc-z is fail")
        self.assertIsNone(self.make(new=new).holds("exclude_empty-10000"))

    def test_the_operation_rows_of_the_two_grids_must_be_equal(self):
        for phase in td.OPERATION_PHASES:
            for side in ("baseline", "candidate"):
                with self.subTest(phase, side=side):
                    old = alloc_decisions(LIMITED, setup=7)
                    old["cases"]["exclude_missing"]["cells"]["10"][
                        "phases"][phase]["total"][side] = {"101": 20}
                    failed = self.make(old=old).holds("exclude_missing-10")
                    self.assertRegex(
                        failed, r"operation row %s.total differs between "
                        r"alloc and alloc-z \(%s: " % (phase, side))

    def test_the_setup_rows_are_not_compared_across_grids(self):
        # make() gives the two grids other setup words.
        self.assertIsNone(self.make().holds("exclude_missing-10"))

    def test_a_cell_missing_from_either_grid_is_named(self):
        new = alloc_decisions({k: v for k, v in LIMITED.items()
                               if k[0] != "exclude_empty"})
        new["cases"]["exclude_empty"] = dict(cells={})
        self.assertEqual(self.make(new=new).holds("exclude_empty-10000"),
                         "allocation: alloc-z has no row for the cell")
        old = alloc_decisions({k: v for k, v in LIMITED.items()
                               if k[0] != "exclude_empty"})
        old["cases"]["exclude_empty"] = dict(cells={})
        self.assertEqual(self.make(old=old).holds("exclude_empty-10000"),
                         "allocation: alloc has no row for the cell")

    def test_a_work_status_that_is_not_equal_is_named(self):
        new = alloc_decisions(LIMITED)
        new["work"]["cells"]["exclude_missing-10"] = "differs"
        self.assertEqual(self.make(new=new).holds("exclude_missing-10"),
                         "work: the cell's work status is 'differs', "
                         "not 'equal'")
        new["work"]["cells"]["exclude_missing-10"] = "inconclusive"
        self.assertIn("'inconclusive', not 'equal'",
                      self.make(new=new).holds("exclude_missing-10"))

    def test_missing_unresolved_or_absent_work_is_refused(self):
        for key in ("missing", "unresolved"):
            with self.subTest(key):
                new = alloc_decisions(LIMITED)
                new["work"][key] = ["exclude_missing-10"]
                self.assertEqual(
                    self.make(new=new).holds("exclude_missing-10"),
                    "work: work rows are missing or unresolved")
        new = alloc_decisions(LIMITED)
        del new["work"]
        self.assertIn("alloc-z has no work section",
                      self.make(new=new).holds("exclude_missing-10"))

    def test_a_row_that_is_not_reproducible_is_named(self):
        new = alloc_decisions(LIMITED)
        new["work"]["nondeterminism"].append(
            ["exclude_missing", 10, "work.use.trace.4.REDUCE", "candidate"])
        self.assertEqual(
            self.make(new=new).holds("exclude_missing-10"),
            "work: work row work.use.trace.4.REDUCE is not reproducible "
            "(candidate)")
        # Several sides of one row are grouped under it.
        new["work"]["nondeterminism"].append(
            ["exclude_missing", 10, "work.use.trace.4.REDUCE", "baseline"])
        new["work"]["nondeterminism"].append(
            ["exclude_missing", 10, "work.first.maker", "control"])
        self.assertEqual(
            self.make(new=new).holds("exclude_missing-10"),
            "work: work row work.use.trace.4.REDUCE is not reproducible "
            "(candidate, baseline); work row work.first.maker is not "
            "reproducible (control)")
        new["work"]["nondeterminism"][1:] = []
        # Another cell's row is not this cell's.
        self.assertIsNone(self.make(new=new).holds("exclude_empty-10000"))

    def test_a_row_that_is_not_equal_is_named(self):
        for key in ("work.use.trace.4.REDUCE", "work.first.maker"):
            with self.subTest(key):
                work = copy.deepcopy(DELETION_WORK)
                work[key] = work_row(3, decision="differs")
                new = alloc_decisions({("exclude_missing", 10): work,
                                       ("exclude_empty", 10000):
                                       OPERATION_WORK})
                self.assertEqual(
                    self.make(new=new).holds("exclude_missing-10"),
                    'work: work row %s differs from develop (candidate '
                    '["3"], baseline ["3"], control ["3"])' % key)

    def test_the_digest_must_be_there_and_equal(self):
        for label, change, text in (
                ("absent", lambda w: w.pop("result.digest"),
                 "no result.digest row"),
                ("differs", lambda w: w.update(
                    {"result.digest": digest_row(decision="differs")}),
                 "differs")):
            with self.subTest(label):
                work = copy.deepcopy(OPERATION_WORK)
                change(work)
                new = alloc_decisions({("exclude_missing", 10):
                                       DELETION_WORK,
                                       ("exclude_empty", 10000): work})
                self.assertIn(text,
                              self.make(new=new).holds("exclude_empty-10000"))

    def test_a_deletion_cell_whose_use_is_empty_is_refused(self):
        # A hook regressed to noUse: every row is equal and empty.
        work = {"result.digest": digest_row(),
                "work.first.maker": work_row(0),
                "work.use.trace.4.REDUCE": work_row(0)}
        new = alloc_decisions({("exclude_missing", 10): work,
                               ("exclude_empty", 10000): OPERATION_WORK})
        self.assertRegex(
            self.make(new=new).holds("exclude_missing-10"),
            r"^work: class deletion: work.use has no work.use.trace.4"
            r".REDUCE \(an empty use shows nothing\)")

    def test_an_operation_cell_whose_first_run_is_empty_is_refused(self):
        work = {"result.digest": digest_row(),
                "work.first.trace.4.REDUCE": work_row(0),
                "work.second.trace.4.REDUCE": work_row(1)}
        new = alloc_decisions({("exclude_missing", 10): DELETION_WORK,
                               ("exclude_empty", 10000): work})
        self.assertEqual(
            self.make(new=new).holds("exclude_empty-10000"),
            "work: class operation: work.first or work.second is empty")

    def test_the_class_check_is_for_the_attributed_cells_only(self):
        # Other cells of the grid (n = 0, where a deletion has no use) are
        # not looked at: the evidence is asked for the listed cells.
        cells = dict(LIMITED)
        cells["exclude_missing", 0] = {"result.digest": digest_row()}
        ev = self.make(new=alloc_decisions(cells))
        self.assertEqual({k: v for k, v in ev.groups.items()
                          if k[0] == "exclude_missing" and k[1] == 0},
                         {("exclude_missing", 0): dict(
                             first=[], second=[], use=[])})
        for cell in SPEC["attributed"]:
            self.assertIsNone(ev.holds(cell))

    def test_the_evidence_is_checked_in_the_order_it_is_named(self):
        new = alloc_decisions(LIMITED)
        new["work"]["cells"]["exclude_missing-10"] = "differs"
        new["cases"]["exclude_missing"]["cells"]["10"]["phases"]["apply"][
            "heap"]["decision"] = "fail"
        ev = self.make(new=new, final=dict(source_identity=dict(
            CLEAN, differing=["x"])))
        self.assertTrue(ev.holds("exclude_missing-10").startswith(
            "sources:"))
        ev = self.make(new=new)
        self.assertTrue(ev.holds("exclude_missing-10").startswith(
            "allocation:"))


def after_void(test):
    """The test judges follow-ups of its own: setUp's first follow-up is a
    void attempt (every cell a protocol failure, as the rig's
    `protocol_failure` makes them), not the settled one."""
    test.void_first = True
    return test


class Toy(ttf.Rig):
    """The replaced toy grid with two control-limited cells beside its two
    open ones, its follow-up (settled by default; a void attempt for a test
    marked `after_void`) and two hand-written allocation grids."""

    def mid_control(self, case, size, pairs, seed):
        if (case, size) in ((c, s) for c, s in LIMITED):
            return (0.90, 1.12)
        return super().mid_control(case, size, pairs, seed)

    def setUp(self):
        super().setUp()
        self.declare()
        self.committed_counts = True
        self.settled()
        if getattr(getattr(self, self._testMethodName), "void_first",
                   False):
            self.protocol_failure = lambda case, size: True
            self.out, code, text = self.run_followup()
            self.assertEqual(code, 2, text)
            self.protocol_failure = lambda case, size: False
        else:
            self.out, code, text = self.run_followup()
            self.assertEqual(code, 0, text)
        self.work = {"y": alloc_decisions(LIMITED, setup=7),
                     "z": alloc_decisions(LIMITED, setup=9)}
        self.replayed = []
        patcher = patch.object(am, "replay", self.fake_replay)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.alloc = self.allocation("alloc", self.replaced, self.work["y"])
        self.allocz = self.allocation("alloc-z", self.out, self.work["z"])

    def settled(self, ci_a=ttg.GOOD, ci_b=ttg.GOOD):
        self.new_candidate = lambda c, s, pairs, seed: {
            ttf.CELL_A: ci_a, ttf.CELL_B: ci_b}.get((c, s), ttg.GOOD)

    def broken_unpack(self, folder):
        real = tg.bundle.unpack

        def unpack(archive, output):
            if folder in Path(archive).parts[-2:-1]:
                raise ValueError("changed archive")
            return real(archive, output)
        return unpack

    def fake_replay(self, args):
        self.replayed.append(Path(args.output).name)
        # What allocation_matrix.replay returns of the decisions it checked.
        decisions = self.load(Path(args.output) / "decisions.json")
        return {"pass": 0, "fail": 1}.get(decisions["status"], 2)

    def allocation(self, name, grid, decisions):
        """An allocation grid of the harness the timing grid `grid` ran in."""
        timing = self.load(grid / "inventory.json")
        folder = self.root / name
        folder.mkdir()
        (folder / "inventory.json").write_text(json.dumps(dict(
            task="task30", candidate=timing["candidate"],
            baseline=timing["baseline"], harness=dict(
                head=timing["checkout"]["head"], dirty=False,
                tree_outside_performance=timing["checkout"][
                    "tree_outside_performance"]))))
        self.save_decisions(folder, decisions)
        return folder

    def save_decisions(self, folder, decisions):
        (folder / "decisions.json").write_text(json.dumps(decisions))

    def dargv(self, *extra, record=False, **given):
        paths = dict(grid=self.replaced, pilot=self.pilot_dir,
                     allocation=self.alloc, followup=self.out,
                     followup_pilot=self.fpilot,
                     followup_allocation=self.allocz)
        paths.update(given)
        return [x for k, v in paths.items()
                for x in ("--" + k.replace("_", "-"), str(v))] + [
            "--repo", str(self.repo)] + (["--record"] if record else []) \
            + list(extra)

    def dispose(self, *argv, **kw):
        """The command, as the engine's `main` runs it (a refusal is an
        exception); returns (status, standard output)."""
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = td.disposition(td.parser().parse_args(
                self.dargv(*argv, **kw)), old=self.grid, new=self.fgrid,
                spec=SPEC)
        return code, out.getvalue()


class Command(Toy):
    def test_a_settled_follow_up_and_evidence_that_holds_pass(self):
        code, text = self.dispose(record=True)
        self.assertEqual(code, 0, text)
        self.assertIn("TOY final grid: inconclusive (pass 10, fail 0, "
                      "inconclusive 0, control-limited 2, protocol 0)", text)
        self.assertIn("ATTRIBUTED exclude_missing-10 (deletion)", text)
        self.assertIn("ATTRIBUTED exclude_empty-10000 (operation)", text)
        self.assertRegex(text, r"TOY two-stage archives and decisions "
                         "replayed")
        self.assertIn("TOYF archives and decisions replayed: pass", text)
        self.assertTrue(text.rstrip().endswith(
            'TASK30 disposition: pass {"pass": 10, "fail": 0, '
            '"attributed": 2, "blocking": 0, "allocation": {"alloc": '
            '"pass", "alloc-z": "pass"}}'), text)
        self.assertEqual(self.replayed, ["alloc", "alloc-z"])

    def test_the_final_decision_has_the_follow_up_in_place_of_the_cells(
            self):
        self.dispose(record=True)
        final = self.load(self.out / "final.json")
        replaced = self.load(self.replaced / "decisions.json")
        follow = self.load(self.out / "decisions.json")
        rows = {(r["case"], r["size"]): r for r in final["workloads"]}
        old = {(r["case"], r["size"]): r for r in replaced["workloads"]}
        new = {(r["case"], r["size"]): r for r in follow["workloads"]}
        self.assertEqual(len(rows), 12)
        for key, row in rows.items():
            self.assertEqual(row, new.get(key, old[key]), key)
        self.assertEqual(final["status"], "inconclusive")
        self.assertEqual(
            [k for k, r in rows.items() if tg.classify_row(r) ==
             "inconclusive"], [])
        self.assertEqual(final["remeasured"], replaced["remeasured"])
        first = self.load(self.replaced1 / "inventory.json")
        second = self.load(self.out / "inventory.json")
        self.assertEqual(final["replaced"], dict(
            cells=sorted(CELLS), replaced_seed="s0", followup_seed="f0",
            followup_second_seed=None,
            replaced_counts=first["iterations_seal"],
            followup_counts=second["iterations_seal"],
            replaced_candidate=first["candidate"],
            followup_candidate=second["candidate"],
            followup_status="pass"))

    def test_the_disposition_records_each_cell_and_the_code(self):
        self.dispose(record=True)
        record = self.load(self.out / "disposition.json")
        self.assertEqual(record["schema"], "toy-disposition-v1")
        self.assertEqual(record["status"], "pass")
        self.assertEqual(record["code"], td.seals())
        self.assertEqual(record["pinned"], {})
        found = record["attributed"]["exclude_missing-10"]
        self.assertEqual(
            (found["evidence_class"], found["note"], found["decision"],
             found["failed"], found["digest"], found["allocation_rows"]),
            ("deletion", "n1", "attributed", None, ["abc"], 24))
        self.assertEqual(found["work"], dict(
            first={}, second={}, use={"trace.4.REDUCE": [10]}))
        self.assertEqual(record["allocation"], {
            label: dict(outcome="pass", status="pass", reasons=[])
            for label in ("alloc", "alloc-z")})
        self.assertEqual(set(found["metrics"]), {"cpu", "wall", "gc"})
        cpu = found["metrics"]["cpu"]
        self.assertEqual((cpu["decision"], cpu["reason"]),
                         ("inconclusive", tg.CONTROL))
        self.assertEqual(cpu["control_interval"], [0.90, 1.12])
        self.assertIs(cpu["control_valid"], False)
        self.assertEqual(cpu["interval"], list(ttg.GOOD))
        self.assertIsNotNone(cpu["median"])
        self.assertEqual(found["metrics"]["gc"]["decision"], "reported")
        self.assertIsNone(found["metrics"]["gc"]["control_valid"])
        other = record["attributed"]["exclude_empty-10000"]
        self.assertEqual(other["work"], dict(
            first={"trace.4.REDUCE": [1], "kernel.total": [4]},
            second={"trace.4.REDUCE": [1], "kernel.total": [4]}, use={}))

    def test_a_check_without_a_record_is_refused(self):
        with self.assertRaisesRegex(ValueError, "no recorded final.json"):
            self.dispose()
        self.assertFalse((self.out / "final.json").exists())

    def test_a_recorded_disposition_is_checked_again(self):
        self.dispose(record=True)
        before = {n: (self.out / n).read_bytes()
                  for n in ("final.json", "disposition.json")}
        code, text = self.dispose()
        self.assertEqual(code, 0, text)
        self.assertEqual(before, {n: (self.out / n).read_bytes()
                                  for n in before})

    def test_a_record_does_not_replace_a_recorded_file(self):
        self.dispose(record=True)
        with self.assertRaisesRegex(ValueError, "refusing to replace the "
                                    "recorded final.json"):
            self.dispose(record=True)

    def test_a_changed_file_is_refused(self):
        self.dispose(record=True)
        for name, change in (
                ("disposition.json", lambda v: v["attributed"][
                    "exclude_missing-10"].update(note="another")),
                ("disposition.json", lambda v: v.update(status="blocked")),
                ("disposition.json", lambda v: v["cells"]["pass"].pop()),
                ("final.json", lambda v: v.update(status="pass")),
                ("final.json", lambda v: v["workloads"].pop())):
            with self.subTest(name, change=change):
                path = self.out / name
                kept = path.read_text()
                value = json.loads(kept)
                change(value)
                path.write_text(json.dumps(value, indent=2) + "\n")
                with self.assertRaisesRegex(
                        ValueError, "changed TASK30 disposition: " + name):
                    self.dispose()
                path.write_text(kept)
        self.assertEqual(self.dispose()[0], 0)

    def test_the_recorded_seals_are_those_of_the_code_or_its_history(self):
        self.dispose(record=True)
        real = a.seal

        def changed(path):
            found = real(path)
            if Path(path).name == "task30_dispose.py":
                return dict(bytes=found["bytes"] + 1, sha256="e" * 64)
            return found
        with patch.object(a, "seal", changed):
            with self.assertRaisesRegex(
                    ValueError, "changed TASK30 disposition: 1 file.s. "
                    "changed since it was recorded; in the same "
                    "commit add each entry .* task30_dispose.py: add to "
                    "task30_dispose.HISTORY the entry "
                    '`"task30_dispose.py": \\(\\{.*,\\),`$'):
                self.dispose()
            # The history is what a commit appends with the change.
            with patch.dict(td.HISTORY, {"task30_dispose.py": (
                    real(a.HERE / "task30_dispose.py"),)}):
                self.assertEqual(self.dispose()[0], 0)
        value = self.load(self.out / "disposition.json")
        value["code"].pop("timing_grid.py")
        (self.out / "disposition.json").write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "the recorded code is not"):
            self.dispose()

    def test_the_disposition_is_replayed_not_trusted(self):
        self.dispose(record=True)
        # A changed cell of the replaced grid breaks the replay.
        with patch.object(tg.bundle, "unpack", self.broken_unpack(
                "replaced")), self.assertRaises(Exception):
            self.dispose()
        self.assertEqual(self.dispose()[0], 0)

    @after_void
    def test_a_follow_up_fail_stays_a_fail(self):
        # A new follow-up (the toy one is settled in setUp).
        self.settled(ci_b=(1.04, 1.08))
        out, code, text = self.run_followup("failing")
        self.assertEqual(code, 1, text)
        code, text = self.dispose(
            record=True, followup=out, followup_allocation=(
                self.allocation("alloc-z-2", out, self.work["z"])))
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL exclude_missing-1000", text)
        self.assertTrue(text.rstrip().endswith(
            'TASK30 disposition: fail {"pass": 9, "fail": 1, '
            '"attributed": 2, "blocking": 0, "allocation": {"alloc": '
            '"pass", "alloc-z": "pass"}}'), text)

    @after_void
    def test_an_inconclusive_follow_up_blocks(self):
        self.new_candidate = self.old_candidate
        out, code, text = self.run_followup("open")
        self.assertEqual(code, 2, text)
        code, text = self.dispose(
            record=True, followup=out, followup_allocation=(
                self.allocation("alloc-z-2", out, self.work["z"])))
        self.assertEqual(code, 2, text)
        self.assertIn("INCONCLUSIVE exclude_empty-100", text)
        self.assertRegex(text, r'TASK30 disposition: blocked \{"pass": 8, '
                         r'"fail": 0, "attributed": 2, "blocking": 2, '
                         r'"allocation": \{"alloc": "pass", "alloc-z": '
                         r'"pass"\}\}')

    def test_evidence_that_fails_blocks_the_cell_and_is_printed(self):
        z = copy.deepcopy(self.work["z"])
        z["work"]["cells"]["exclude_missing-10"] = "differs"
        self.save_decisions(self.allocz, z)
        code, text = self.dispose(record=True)
        self.assertEqual(code, 2, text)
        self.assertIn("BLOCKING exclude_missing-10 (deletion): work: the "
                      "cell's work status is 'differs', not 'equal'", text)
        self.assertIn("ATTRIBUTED exclude_empty-10000 (operation)", text)
        record = self.load(self.out / "disposition.json")
        self.assertEqual(record["blocking"], {
            "exclude_missing-10": "control-limited, evidence fails: work: "
            "the cell's work status is 'differs', not 'equal'"})
        self.assertEqual(record["status"], "blocked")

    def test_a_stale_list_is_refused_naming_the_cells(self):
        spec = dict(SPEC, attributed=dict(
            SPEC["attributed"], **{"exclude_empty-0": dict(
                evidence_class=td.DELETION, note="n")}))
        out = io.StringIO()
        with contextlib.redirect_stdout(out), self.assertRaisesRegex(
                ValueError, r"stale attribution: listed but not "
                r"control-limited: exclude_empty-0 \(pass\)"):
            td.disposition(td.parser().parse_args(self.dargv(record=True)),
                           old=self.grid, new=self.fgrid, spec=spec)
        spec["attributed"].pop("exclude_missing-10")
        spec["attributed"].pop("exclude_empty-0")
        with contextlib.redirect_stdout(out), self.assertRaisesRegex(
                ValueError, "control-limited but not listed: "
                "exclude_missing-10"):
            td.disposition(td.parser().parse_args(self.dargv(record=True)),
                           old=self.grid, new=self.fgrid, spec=spec)

    def test_a_refusal_is_one_line_and_the_status_3(self):
        err, out = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(
                err):
            code = td.main(self.dargv(), old=self.grid, new=self.fgrid,
                           spec=SPEC)
        self.assertEqual((code, err.getvalue()), (
            tg.REFUSED, "REFUSED: no recorded final.json: record it with "
            "--record\n"))

    def test_the_main_status_is_that_of_the_disposition(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(td.main(self.dargv(record=True), old=self.grid,
                                     new=self.fgrid, spec=SPEC), 0)
            self.assertEqual(td.main(self.dargv(), old=self.grid,
                                     new=self.fgrid, spec=SPEC), 0)

    def test_the_arguments_are_all_required(self):
        for missing in ("grid", "pilot", "allocation", "followup",
                        "followup-pilot", "followup-allocation"):
            with self.subTest(missing):
                argv = self.dargv()
                at = argv.index("--" + missing)
                del argv[at:at + 2]
                with self.assertRaises(SystemExit), \
                        contextlib.redirect_stderr(io.StringIO()):
                    td.parser().parse_args(argv)


class Pairing(Toy):
    """Each timing grid with the allocation grid of its harness, and the
    follow-up with the grid it replaced."""

    def setUp(self):
        super().setUp()
        # Another grid of the harness of Y.
        self.other = self.allocation("alloc-y2", self.replaced,
                                     self.work["y"])

    def refused(self, regex, **given):
        before = list(self.replayed)
        with self.assertRaisesRegex(ValueError, regex):
            self.dispose(**given)
        # The cheap comparisons come before any replay.
        self.assertEqual(self.replayed, before)

    def test_the_y_timing_grid_with_the_allocation_of_z_is_refused(self):
        self.refused(r"TASK30 \(Y\) timing grid measured c+, its allocation "
                     "grid d+", allocation=self.allocz,
                     followup_allocation=self.other)

    def test_the_follow_up_with_the_allocation_of_y_is_refused(self):
        self.refused(r"follow-up \(Z\) timing grid measured d+, its "
                     "allocation grid c+", followup_allocation=self.other)

    def test_one_allocation_grid_cannot_serve_both(self):
        self.refused("one allocation grid cannot serve both harnesses",
                     allocation=self.allocz, followup_allocation=self.allocz)

    def test_a_harness_other_than_the_timing_grids_is_refused(self):
        for name, key in (("alloc", "head"), ("alloc", "tree"),
                          ("alloc-z", "head"), ("alloc-z", "tree")):
            with self.subTest(name, key=key):
                path = self.root / name / "inventory.json"
                kept = path.read_text()
                value = json.loads(kept)
                value["harness"]["head" if key == "head" else
                                 "tree_outside_performance"] = "x" * (
                    40 if key == "head" else 64)
                path.write_text(json.dumps(value))
                try:
                    self.refused("the two grids ran in different "
                                 "harnesses")
                finally:
                    path.write_text(kept)

    def test_a_dirty_harness_is_refused(self):
        path = self.root / "alloc-z" / "inventory.json"
        value = json.loads(path.read_text())
        value["harness"]["dirty"] = True
        path.write_text(json.dumps(value))
        self.refused("the two grids ran in different harnesses")

    def test_baselines_and_tasks_must_agree(self):
        for key, value, regex in (
                ("baseline", "9" * 40, "have different baselines"),
                ("task", "task29b", "is not a TASK30 grid")):
            with self.subTest(key):
                path = self.root / "alloc-z" / "inventory.json"
                kept = path.read_text()
                changed = json.loads(kept)
                changed[key] = value
                path.write_text(json.dumps(changed))
                try:
                    self.refused(regex)
                finally:
                    path.write_text(kept)

    def test_a_partial_allocation_grid_is_refused(self):
        (self.allocz / "decisions.json").unlink()
        self.refused("--followup-allocation is not a complete grid")

    def test_the_grid_must_be_the_one_the_follow_up_replaced(self):
        self.refused("--grid is not the grid the follow-up replaced",
                     grid=self.replaced1)

    def test_a_grid_that_is_not_a_follow_up_is_refused(self):
        self.refused("--followup is not a follow-up grid",
                     followup=self.replaced,
                     followup_allocation=self.alloc,
                     allocation=self.allocation(
                         "alloc-3", self.replaced, self.work["y"]))

    def test_follow_up_cells_other_than_the_open_ones_are_refused(self):
        # The follow-up replays the grid it replaced and compares the cells
        # it holds with the cells that grid left inconclusive.
        self.ftable.cells = (CELLS[0],)
        with self.assertRaisesRegex(ValueError, "follow-up cells differ "
                                    "from the open cells"):
            self.dispose(record=True)

    def test_a_follow_up_with_another_source_record_is_refused(self):
        # (The follow-up's own check; its comparison with the replaced
        # grid's record is tested in test_timing_followup.py.)
        path = self.out / "inventory.json"
        value = json.loads(path.read_text())
        value["sources"]["src/one.sml"]["candidate"] = "e" * 40
        path.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "changed source identity"):
            self.dispose(record=True)


class Seals(Toy):
    """What a commit that changes the code of a recorded disposition must
    append, named in one refusal."""

    def changed(self, *names):
        real = a.seal

        def seal(path):
            found = real(path)
            if Path(path).name in names:
                return dict(bytes=found["bytes"] + 1, sha256="e" * 64)
            return found
        return real, patch.object(a, "seal", seal)

    def test_every_changed_file_is_listed_with_its_recorded_seal(self):
        self.dispose(record=True)
        recorded = self.load(self.out / "disposition.json")["code"]
        names = ("timing_grid.py", "task30_followup.py",
                 "task30_dispose.py", "task30_grid.py", "acceptance.py")
        real, patcher = self.changed(*names)
        with patcher:
            with self.assertRaises(ValueError) as caught:
                td.check_code(recorded)
        text = str(caught.exception)
        self.assertIn("%d file(s) changed" % len(names), text)
        for name in names:
            seal = json.dumps(recorded[name], sort_keys=True)
            self.assertIn('%s: add to task30_dispose.HISTORY the entry '
                          '`"%s": (%s,),`' % (name, name, seal), text)
        # ... and the history constants the records made by the old file
        # need too, and the tests that pin them.
        for constant in ("task30_followup.ENGINES",
                         "task30_followup.ACCEPTANCE",
                         "task30_followup.DRIVERS",
                         "task30_followup.SEALED_HISTORY"):
            self.assertIn(constant, text)
        self.assertIn("test_task30_dispose.py", text)
        self.assertIn("test_task30_grid.py", text)
        # Files that did not change are not named.
        self.assertNotIn("allocation_matrix.py: add", text)
        # The refusal's seals are what makes it pass.
        with patcher, patch.dict(td.HISTORY, {
                n: (recorded[n],) for n in names}):
            td.check_code(recorded)
        # One entry short leaves that file named alone.
        with patcher, patch.dict(td.HISTORY, {
                n: (recorded[n],) for n in names[1:]}):
            with self.assertRaisesRegex(ValueError, "1 file.s. changed"):
                td.check_code(recorded)

    def test_the_printed_entries_are_literals_of_their_constant(self):
        import ast
        seal = dict(bytes=7, sha256="f" * 64)
        for name in td.CODE:
            found = dict(td.entries(name, seal))
            history = ast.literal_eval("{%s}" % found[
                "task30_dispose.HISTORY"][1:-1])
            self.assertEqual(history, {name: (seal,)})
            self.assertEqual(len(found), 1 + (name in td.ALSO))
        for name, (constant, keyed) in td.ALSO.items():
            element = dict(td.entries(name, seal))[constant]
            self.assertTrue(element.startswith("`") and
                            element.endswith("`"), element)
            element = element[1:-1]
            if keyed:
                # Pasted into `{}`: a dict of str to tuple of str-keyed
                # seals, as HISTORY's entry is.
                value = ast.literal_eval("{%s}" % element)
                self.assertEqual(value, {name: (seal,)})
                self.assertIsInstance(value, dict)
                self.assertTrue(all(
                    isinstance(k, str) and isinstance(v, tuple)
                    for k, v in value.items()))
            else:
                # A tuple of seals (a constant's element).
                self.assertEqual(ast.literal_eval("(%s)" % element),
                                 (seal,))
        # The refusal's text carries exactly those literals.
        self.dispose(record=True)
        recorded = self.load(self.out / "disposition.json")["code"]
        real, patcher = self.changed("timing_grid.py")
        with patcher, self.assertRaises(ValueError) as caught:
            td.check_code(recorded)
        for constant, text in td.entries("timing_grid.py",
                                         recorded["timing_grid.py"]):
            self.assertIn("to %s the entry %s" % (constant, text),
                          str(caught.exception))

    def test_the_command_refuses_with_that_text(self):
        self.dispose(record=True)
        real, patcher = self.changed("timing_grid.py", "acceptance.py")
        with patcher, self.assertRaisesRegex(
                ValueError, "2 file.s. changed since it was recorded.*"
                "timing_grid.py: add to .*acceptance.py: add to "):
            self.dispose()


class Gates(Toy):
    """The allocation grids are gated by their own status: a fail is a fail,
    anything else but a pass blocks, with the reason named."""

    def stale(self, label, **change):
        decisions = copy.deepcopy(self.work["z" if label == "alloc-z"
                                            else "y"])
        decisions.update(change)
        self.save_decisions(self.allocz if label == "alloc-z" else
                            self.alloc, decisions)

    def run_once(self):
        code, text = self.dispose(record=True)
        return code, text, self.load(self.out / "disposition.json")

    def test_an_allocation_that_fails_is_a_fail(self):
        for label in ("alloc", "alloc-z"):
            with self.subTest(label):
                self.stale(label, status="fail", acceptance_pairs=False)
                for name in ("final.json", "disposition.json"):
                    if (self.out / name).exists():
                        (self.out / name).unlink()
                code, text, record = self.run_once()
                self.assertEqual(code, 1, text)
                self.assertEqual(record["status"], "fail")
                found = record["allocation"][label]
                self.assertEqual(found["outcome"], "fail")
                self.assertIn(label + ": fail (status fail, "
                              "acceptance_pairs false)", found["reasons"])
                self.assertIn("ALLOCATION-FAIL " + label, text)
                self.assertTrue(text.rstrip().endswith(
                    'TASK30 disposition: fail {"pass": 10, "fail": 0, '
                    '"attributed": 2, "blocking": 0, "allocation": '
                    + json.dumps({"alloc": "pass", "alloc-z": "pass",
                                  label: "fail"}) + "}"), text)
                self.stale(label)

    def test_a_pass_needs_a_complete_grid_with_enough_pairs(self):
        for label, change, reason in (
                ("alloc-z", dict(status="inconclusive",
                                 acceptance_pairs=False),
                 "status inconclusive, acceptance_pairs false"),
                ("alloc-z", dict(status="inconclusive", complete=False),
                 "status inconclusive, complete false"),
                ("alloc", dict(status="inconclusive"),
                 "status inconclusive"),
                # A status that says pass beside the other facts is not
                # taken at its word.
                ("alloc-z", dict(acceptance_pairs=False),
                 "acceptance_pairs false"),
                ("alloc", dict(acceptance_baseline=False),
                 "acceptance_baseline false"),
                ("alloc-z", dict(nondeterminism=[["c", 1, "p", "m", "x"]]),
                 "nondeterminism: 1")):
            with self.subTest(label, change=change):
                for name in ("final.json", "disposition.json"):
                    if (self.out / name).exists():
                        (self.out / name).unlink()
                self.stale(label, **change)
                code, text, record = self.run_once()
                self.assertEqual(code, 2, text)
                self.assertEqual(record["status"], "blocked")
                found = record["allocation"][label]
                self.assertEqual(found["outcome"], "blocked")
                self.assertEqual(len(found["reasons"]), 1)
                self.assertIn(reason, found["reasons"][0])
                self.assertIn("ALLOCATION-BLOCKED " + label, text)
                self.assertIn("ALLOCATION %s: blocked" % label, text)
                # The cells are still attributed: this is about the grid.
                self.assertEqual(record["counts"]["attributed"], 2)
                self.stale(label)

    def test_a_fail_beats_a_block(self):
        self.stale("alloc", status="inconclusive")
        self.stale("alloc-z", status="fail")
        code, text, record = self.run_once()
        self.assertEqual((code, record["status"]), (1, "fail"), text)

    def test_the_two_grids_that_pass_are_recorded_and_printed(self):
        code, text, record = self.run_once()
        self.assertEqual(code, 0, text)
        self.assertIn("ALLOCATION alloc: pass", text)
        self.assertIn("ALLOCATION alloc-z: pass", text)
        self.assertNotIn("ALLOCATION-", text)

    def test_the_refusal_says_the_partial_file_is_stale(self):
        (self.allocz / "decisions-partial.json").write_text("{}")
        with self.assertRaisesRegex(
                ValueError, "beside a complete decisions.json: the partial "
                "file is stale .* and may be removed"):
            self.dispose(record=True)
        self.assertTrue((self.allocz / "decisions-partial.json").exists())

    def test_a_partial_decision_is_refused_before_any_replay(self):
        for label, folder in (("--allocation", self.alloc),
                              ("--followup-allocation", self.allocz)):
            with self.subTest(label):
                before = list(self.replayed)
                partial = folder / "decisions-partial.json"
                partial.write_text("{}")
                with self.assertRaisesRegex(
                        ValueError, "%s has a partial decision" % label):
                    self.dispose(record=True)
                self.assertEqual(self.replayed, before)
                partial.unlink()


class Reproducibility(Toy):
    """A cell whose work rows do not reproduce is blocked, with the row
    named, and a fail stays a fail."""

    def spread(self, row="work.use.trace.4.REDUCE", digest=False):
        z = copy.deepcopy(self.work["z"])
        cell = z["cases"]["exclude_missing"]["cells"]["10"]
        if digest:
            found = digest_row()
            found["candidate"] = {"abc": 10, "abd": 10}
            found["decision"] = "inconclusive"
            found["deterministic"]["candidate"] = False
            cell["work"]["result.digest"] = found
        else:
            cell["work"][row]["candidate"] = {"10": 10, "11": 10}
            cell["work"][row]["decision"] = "inconclusive"
            cell["work"][row]["deterministic"]["candidate"] = False
        z["work"]["cells"]["exclude_missing-10"] = "inconclusive"
        z["work"]["nondeterminism"].append(
            ["exclude_missing", 10, "result.digest" if digest else row,
             "candidate"])
        self.save_decisions(self.allocz, z)

    def test_several_values_block_the_cell_naming_the_row(self):
        self.spread()
        code, text = self.dispose(record=True)
        self.assertEqual(code, 2, text)
        self.assertIn("BLOCKING exclude_missing-10 (deletion): work: work "
                      "row work.use.trace.4.REDUCE is not reproducible "
                      "(candidate)", text)
        self.assertIn("ATTRIBUTED exclude_empty-10000 (operation)", text)
        record = self.load(self.out / "disposition.json")
        self.assertEqual(record["status"], "blocked")
        found = record["attributed"]["exclude_missing-10"]
        # All the values are recorded.
        self.assertEqual(found["work"]["use"], {"trace.4.REDUCE": [10, 11]})
        self.assertEqual(found["decision"], "blocking")

    def test_a_row_that_does_not_reproduce_is_named_when_the_status_is_equal(
            self):
        self.spread()
        z = self.load(self.allocz / "decisions.json")
        z["work"]["cells"]["exclude_missing-10"] = "equal"
        cell = z["cases"]["exclude_missing"]["cells"]["10"]["work"]
        cell["work.use.trace.4.REDUCE"]["decision"] = "equal"
        self.save_decisions(self.allocz, z)
        code, text = self.dispose(record=True)
        self.assertEqual(code, 2, text)
        self.assertIn("work row work.use.trace.4.REDUCE is not "
                      "reproducible (candidate)", text)

    def test_a_digest_of_several_values_blocks(self):
        self.spread(digest=True)
        code, text = self.dispose(record=True)
        self.assertEqual(code, 2, text)
        record = self.load(self.out / "disposition.json")
        found = record["attributed"]["exclude_missing-10"]
        self.assertEqual(found["digest"], ["abc", "abd"])
        self.assertEqual(found["decision"], "blocking")

    def test_a_digest_row_that_is_equal_but_not_one_value_is_named(self):
        ev = make_evidence()
        work = copy.deepcopy(DELETION_WORK)
        work["result.digest"] = dict(
            digest_row(), candidate={"a": 10, "b": 10})
        new = alloc_decisions({("exclude_missing", 10): work,
                               ("exclude_empty", 10000): OPERATION_WORK})
        self.assertEqual(
            make_evidence(new=new).result("exclude_missing-10"),
            "result.digest row is not reproducible (2 candidate and 1 "
            "baseline values)")
        self.assertIsNone(ev.result("exclude_missing-10"))

    def test_counts_keep_every_value(self):
        rows = {"result.digest": digest_row(),
                "work.use.trace.4.REDUCE": dict(
                    work_row(0), candidate={"3": 5, "10": 15}),
                "work.first.maker": work_row(0),
                "work.second.kernel.total": work_row(4)}
        self.assertEqual(td.counts(rows), dict(
            first={}, second={"kernel.total": [4]},
            use={"trace.4.REDUCE": [3, 10]}))
        self.assertEqual(td.counts(None), dict(first={}, second={}, use={}))

    @after_void
    def test_a_fail_stays_a_fail_beside_a_row_that_does_not_reproduce(self):
        self.spread()
        self.settled(ci_b=(1.04, 1.08))
        out, code, text = self.run_followup("failing")
        self.assertEqual(code, 1, text)
        code, text = self.dispose(
            record=True, followup=out, followup_allocation=(
                self.allocation("alloc-z-2", out, self.load(
                    self.allocz / "decisions.json"))))
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL exclude_missing-1000", text)
        self.assertIn("BLOCKING exclude_missing-10 (deletion)", text)


class Printed(Toy):
    """The numbers of an attributed cell are printed from the record."""

    def test_the_numbers_come_from_the_record_and_are_printed(self):
        code, text = self.dispose(record=True)
        record = self.load(self.out / "disposition.json")
        for cell, found in record["attributed"].items():
            for run in td.SECTIONS:
                self.assertIn("  work %s %s" % (
                    run, json.dumps(found["work"][run], sort_keys=True)),
                    text)
            for key in ("cpu", "wall", "gc"):
                m = found["metrics"][key]
                valid = m["control_valid"]
                self.assertEqual(valid is None, key == "gc")
                self.assertIn(
                    "  %s %s: median %s, interval %s, control interval "
                    "%s%s" % (
                        key, m["decision"], m["median"], m["interval"],
                        m["control_interval"], "" if valid is None else
                        " (within the window: %s)" % (
                            "yes" if valid else "no")), text)
            self.assertIn("  digest %s; allocation rows %d" % (
                json.dumps(found["digest"]), found["allocation_rows"]),
                text)
        self.assertIn("FOLLOW-UP status pass (cells %s)" %
                      ", ".join(sorted(CELLS)), text)


class FollowUpOutcomes(Toy):
    """A follow-up cell is judged by the follow-up's own outcome: one that
    stays open after its own second stage blocks (it is not a stale
    attribution), and a follow-up that is not final is refused."""

    def open_follow_up(self, name, control, candidate=ttg.GOOD):
        self.new_control = lambda c, s, pairs, seed: (
            control if (c, s) == ttf.CELL_B else ttg.GOOD)
        self.new_candidate = lambda c, s, pairs, seed: candidate
        out, code, text = self.run_followup(name)
        return out, code, text

    @after_void
    def test_a_cell_that_stays_control_limited_blocks(self):
        out, code, text = self.open_follow_up("first-open", ttg.WIDE)
        self.assertEqual(code, 2, text)
        ext, code, text = self.extend_followup(out)
        self.assertEqual(code, 2, text)
        code, text = self.dispose(
            record=True, followup=ext, followup_allocation=(
                self.allocation("alloc-z-2", ext, self.work["z"])))
        self.assertEqual(code, 2, text)
        self.assertIn("CONTROL-LIMITED exclude_missing-1000", text)
        self.assertIn("BLOCKING exclude_missing-1000: follow-up: "
                      "control-limited", text)
        self.assertIn("FOLLOW-UP status inconclusive", text)
        record = self.load(ext / "disposition.json")
        self.assertEqual(record["blocking"], {
            "exclude_missing-1000": "follow-up: control-limited"})
        self.assertEqual(record["status"], "blocked")
        self.assertEqual(record["counts"]["attributed"], 2)
        self.assertEqual(record["replaced"]["followup_status"],
                         "inconclusive")
        # ... and its own second stage's seed is recorded.
        self.assertEqual(record["replaced"]["followup_second_seed"],
                         "f0-ext")

    @after_void
    def test_a_cell_that_stays_inconclusive_blocks(self):
        out, code, text = self.open_follow_up(
            "first-open", ttg.GOOD, candidate=ttg.WIDE)
        ext, code, text = self.extend_followup(out)
        code, text = self.dispose(
            record=True, followup=ext, followup_allocation=(
                self.allocation("alloc-z-2", ext, self.work["z"])))
        self.assertEqual(code, 2, text)
        self.assertRegex(text, r"BLOCKING exclude_\w+-\d+: follow-up: "
                         "inconclusive")

    @after_void
    def test_a_first_stage_with_a_second_stage_to_come_is_refused(self):
        out, code, text = self.open_follow_up("first-open", ttg.WIDE)
        self.assertEqual(code, 2, text)
        with self.assertRaisesRegex(
                ValueError, "--followup is not the follow-up's final "
                "stage: its second stage is still to come"):
            self.dispose(
                record=True, followup=out, followup_allocation=(
                    self.allocation("alloc-z-2", out, self.work["z"])))
        self.assertFalse((out / "final.json").exists())


class Attempts(Toy):
    """Every attempt of the follow-up's table in the ledger is judged or
    void: a void attempt is shown void from its own output, by the id of
    its attempt. Anything else is refused, before any replay."""

    def rerun(self, name="rerun"):
        """A second attempt of the follow-up, settled, and its dispose
        arguments."""
        out, code, text = self.run_followup(name)
        self.assertEqual(code, 0, text)
        return dict(followup=out, followup_allocation=self.allocation(
            "alloc-z-" + name, out, self.work["z"]))

    def refuses(self, regex, check=False, **kw):
        boom = AssertionError("a replay ran before the refusal")
        with patch.object(self.fgrid, "replay", side_effect=boom), \
                patch.object(self.grid, "replay", side_effect=boom), \
                patch.object(am, "replay", side_effect=boom), \
                self.assertRaisesRegex(ValueError, regex):
            self.dispose(record=not check, **kw)

    def reasons(self, attempt, status, output, why):
        return ("follow-up attempt %s \\(status %s, output %s\\) is not "
                "void: %s; only a void attempt .no admitted measurement in "
                "any cell. may stand beside the judged one; anything else "
                "needs a new policy decision, or --followup does not name "
                "the follow-up's final stage .name the final stage" % (
                    attempt, status, re.escape(str(output)), why))

    def edit(self, out, change):
        """Change the inventory of an output; returns the first attempt's
        id."""
        path = out / "inventory.json"
        found = self.load(path)
        change(found)
        path.write_text(json.dumps(found))
        return found["attempt"]

    def refused_void(self, why, change, status="inconclusive"):
        """The void attempt (setUp's) is changed by `change`, and a judged
        rerun beside it is refused for `why`."""
        given = self.rerun()
        attempt = self.edit(self.out, change)
        self.refuses(self.reasons(attempt, status, self.out, why), **given)
        self.assertFalse((given["followup"] / "disposition.json").exists())
        return given

    @after_void
    def test_a_void_earlier_attempt_passes_and_is_recorded(self):
        first = self.load(self.out / "inventory.json")["attempt"]
        given = self.rerun()
        code, text = self.dispose(record=True, **given)
        self.assertEqual(code, 0, text)
        found = self.load(given["followup"] / "disposition.json")[
            "followup_attempts"]
        second = self.load(given["followup"] / "inventory.json")["attempt"]
        self.assertEqual(found, [
            dict(attempt=first, status="inconclusive",
                 output=str(self.out), judged=False, void=True),
            dict(attempt=second, status="pass",
                 output=str(given["followup"]), judged=True, void=False)])
        self.assertIn("FOLLOW-UP-ATTEMPT %s status inconclusive output %s: "
                      "void" % (first, self.out), text)
        self.assertIn("FOLLOW-UP-ATTEMPT %s status pass output %s: judged"
                      % (second, given["followup"]), text)
        # ... and is checked again, without --record.
        code, text = self.dispose(**given)
        self.assertEqual(code, 0, text)

    @after_void
    def test_a_void_attempt_is_void_in_every_archive(self):
        # The rig's void attempt has a row for every cell, every row a
        # protocol failure, every archive the sealed one with an
        # acceptance that failed (the rig's has no command: the realistic
        # shapes are the tests below), and the ledger's close and the
        # decisions say inconclusive.
        found = self.load(self.out / "inventory.json")
        self.assertEqual(sorted((r["case"], r["size"])
                                for r in found["runs"]),
                         sorted(self.fgrid.t.keys()))
        self.assertEqual({r["protocol"] for r in found["runs"]}, {False})
        for row in found["runs"]:
            archive = self.out / row["archive"]
            self.assertEqual(a.seal(archive), row["seal"])
            folder = self.root / "inspected"
            tg.bundle.unpack(archive, folder)
            self.assertIs(self.load(folder / "acceptance.json")["success"],
                          False)
            shutil.rmtree(folder)
        self.assertEqual(self.load(self.out / "decisions.json")["status"],
                         "inconclusive")

    def test_an_earlier_attempt_with_an_admitted_row_is_refused(self):
        given = self.rerun()
        first = self.load(self.out / "inventory.json")["attempt"]
        self.refuses(self.reasons(
            first, "pass", self.out,
            r"the row of exclude_\w+-\d+ is not a protocol failure "
            r"\(protocol True\)"), **given)
        self.assertFalse((given["followup"] / "disposition.json").exists())

    @after_void
    def test_an_inventory_without_runs_is_refused(self):
        self.refused_void(r"its inventory has rows for 0 cell\(s\), not "
                          r"each of the 2 the follow-up measures",
                          lambda found: found.update(runs=[]))

    @after_void
    def test_an_inventory_without_a_row_for_a_cell_is_refused(self):
        self.refused_void(r"its inventory has rows for 1 cell\(s\), not "
                          r"each of the 2 the follow-up measures",
                          lambda found: found["runs"].pop())

    @after_void
    def test_a_row_without_a_protocol_flag_is_refused(self):
        self.refused_void(
            r"the row of exclude_\w+-\d+ is not a protocol failure "
            r"\(protocol None\)",
            lambda found: found["runs"][0].pop("protocol"))

    @after_void
    def test_a_row_with_a_protocol_flag_that_is_not_false_is_refused(self):
        self.refused_void(
            r"the row of exclude_\w+-\d+ is not a protocol failure "
            r"\(protocol 0\)",
            lambda found: found["runs"][0].update(protocol=0))

    @after_void
    def test_a_missing_archive_is_refused(self):
        def change(found):
            (self.out / found["runs"][0]["archive"]).unlink()
        self.refused_void(r"the archive of exclude_\w+-\d+ is missing",
                          change)

    @after_void
    def test_an_archive_that_is_not_the_sealed_one_is_refused(self):
        self.refused_void(
            r"the archive of exclude_\w+-\d+ is not the sealed one",
            lambda found: found["runs"][0]["seal"].update(bytes=1))

    @after_void
    def test_an_archive_with_an_admitted_runner_manifest_is_refused(self):
        def change(found):
            row = found["runs"][0]
            archive = self.out / row["archive"]
            folder = self.root / "poisoned"
            tg.bundle.unpack(archive, folder)
            (folder / "cell").mkdir()
            (folder / "cell" / "manifest.json").write_text(json.dumps(
                dict(runs=[dict(exit=0)], success=True)))
            archive.unlink()
            row["files"] = tg.bundle.pack(folder, archive)
            row["seal"] = a.seal(archive)
            shutil.rmtree(folder)
        self.refused_void(
            r"the archive of exclude_\w+-\d+ holds a runner manifest that "
            r"records an admitted run \(cell/manifest.json\)", change)

    @after_void
    def test_a_manifest_that_records_no_run_is_void(self):
        found = self.load(self.out / "inventory.json")
        row = found["runs"][0]
        archive = self.out / row["archive"]
        folder = self.root / "clean"
        tg.bundle.unpack(archive, folder)
        (folder / "cell").mkdir()
        (folder / "cell" / "manifest.json").write_text(json.dumps(
            dict(runs=[], success=False)))
        archive.unlink()
        row["files"] = tg.bundle.pack(folder, archive)
        row["seal"] = a.seal(archive)
        shutil.rmtree(folder)
        (self.out / "inventory.json").write_text(json.dumps(found))
        code, text = self.dispose(record=True, **self.rerun())
        self.assertEqual(code, 0, text)

    def test_a_missing_output_directory_is_refused(self):
        given = self.rerun()
        first = self.load(self.out / "inventory.json")["attempt"]
        shutil.rmtree(self.out)
        self.refuses(self.reasons(first, "pass", self.out,
                                  "its output directory is missing"),
                     **given)

    @after_void
    def test_an_output_without_an_inventory_is_refused(self):
        given = self.rerun()
        attempt = self.load(self.out / "inventory.json")["attempt"]
        (self.out / "inventory.json").unlink()
        self.refuses(self.reasons(attempt, "inconclusive", self.out,
                                  "its output has no inventory.json"),
                     **given)

    @after_void
    def test_an_inventory_of_another_attempt_is_refused(self):
        given = self.rerun()
        second = self.load(given["followup"] / "inventory.json")
        first = self.load(self.out / "inventory.json")["attempt"]
        (self.out / "inventory.json").write_text(json.dumps(dict(
            self.load(self.out / "inventory.json"),
            attempt=second["attempt"])))
        self.refuses(self.reasons(
            first, "inconclusive", self.out,
            "the output holds attempt %s" % second["attempt"]), **given)

    def test_an_attempt_that_measured_and_whose_path_was_reused_is_refused(
            self):
        # The measured attempt's directory is moved aside and a rerun
        # reuses the path: the path no longer says which attempt it holds.
        measured = self.load(self.out / "inventory.json")["attempt"]
        self.out.rename(self.root / "moved-aside")
        out, code, text = self.run_followup()
        self.assertEqual((out, code), (self.out, 0), text)
        given = dict(followup=out, followup_allocation=self.allocation(
            "alloc-z-reuse", out, self.work["z"]))
        now = self.load(out / "inventory.json")["attempt"]
        self.assertNotEqual(measured, now)
        self.refuses(self.reasons(
            measured, "pass", out, "the output holds attempt %s" % now),
            **given)
        self.refuses(self.reasons(
            measured, "pass", out, "the output holds attempt %s" % now),
            check=True, **given)

    @after_void
    def test_an_attempt_left_open_without_a_close_is_refused(self):
        # An interrupted attempt may have measured: even one whose output
        # is a clean void inventory with no finished cell is refused.
        given = self.rerun()
        out = self.root / "interrupted"
        out.mkdir()
        inventory = self.load(self.out / "inventory.json")
        (out / "inventory.json").write_text(json.dumps(
            dict(inventory, attempt="open-attempt", runs=[])))
        tg.ledger_append(
            self.attempts, event="open", stage="first",
            table=self.fgrid.t.name, attempt="open-attempt",
            candidate=inventory["candidate"], counts_file="x",
            counts=inventory["iterations_seal"], seed="f0",
            output=str(out), checkout=str(self.repo))
        self.refuses(self.reasons(
            "open-attempt", "interrupted", out,
            r"its inventory has rows for 0 cell\(s\), not each of the 2 "
            r"the follow-up measures"), **given)
        # ... also with no output directory at all.
        shutil.rmtree(out)
        self.refuses(self.reasons("open-attempt", "interrupted", out,
                                  "its output directory is missing"),
                     **given)

    # A void attempt as a real one leaves it (`exclude_partial-1` of the
    # real first attempt): acceptance recorded the runner command, which
    # failed (the harness's `poly --version` hung), and the runner wrote its
    # manifest with no run before it failed.

    def realistic(self, manifest=True, runs=(), timed_out=False,
                  success=False):
        """The archives of the void attempt (setUp's) rewritten to that
        shape; `change` of `refused_void`'s kind, on the inventory."""
        def one(folder, name):
            where = "/scratch/%s/%s-control" % (name, name)
            report = self.load(folder / "acceptance.json")
            report.update(
                success=success, failure="runner failed; see the log",
                commands=[dict(
                    argv=["python3", "run_paired.py", "--output", where,
                          "--layout-seed", "seed"],
                    exit=-9 if timed_out else 1, timed_out=timed_out,
                    log=where + ".log", log_hash=dict(sha256="0", bytes=1))])
            (folder / "acceptance.json").write_text(json.dumps(report))
            if manifest:
                (folder / (name + "-control")).mkdir()
                (folder / (name + "-control") /
                 "manifest.json").write_text(json.dumps(dict(
                     runs=list(runs), success=False,
                     failure="poly --version failed")))

        def change(found):
            for row in found["runs"]:
                archive = self.out / row["archive"]
                folder = self.root / "rebuilt"
                tg.bundle.unpack(archive, folder)
                one(folder, "%s-%d" % (row["case"], row["size"]))
                archive.unlink()
                row["files"] = tg.bundle.pack(folder, archive)
                row["seal"] = a.seal(archive)
                shutil.rmtree(folder)
        return change

    @after_void
    def test_a_void_attempt_with_a_runner_command_and_manifest_is_void(self):
        self.edit(self.out, self.realistic())
        given = self.rerun()
        code, text = self.dispose(record=True, **given)
        self.assertEqual(code, 0, text)
        found = self.load(given["followup"] / "disposition.json")[
            "followup_attempts"]
        self.assertEqual([(x["judged"], x["void"]) for x in found],
                         [(False, True), (True, False)])
        code, text = self.dispose(**given)
        self.assertEqual(code, 0, text)

    @after_void
    def test_a_runner_killed_without_its_manifest_is_refused(self):
        self.refused_void(
            r"the archive of exclude_\w+-\d+ has no runner manifest in "
            r"exclude_\w+-\d+-control \(a runner killed while measuring "
            r"leaves none\)", self.realistic(manifest=False))

    @after_void
    def test_a_runner_manifest_with_runs_is_refused(self):
        self.refused_void(
            r"the archive of exclude_\w+-\d+ holds a runner manifest that "
            r"records an admitted run "
            r"\(exclude_\w+-\d+-control/manifest.json\)",
            self.realistic(runs=[dict(exit=0)]))

    @after_void
    def test_a_command_that_timed_out_is_refused(self):
        self.refused_void(
            r"a command of exclude_\w+-\d+ timed out, or its receipt does "
            r"not say it did not: its runner may have measured",
            self.realistic(timed_out=True))

    @after_void
    def test_an_acceptance_that_did_not_fail_is_refused(self):
        self.refused_void(
            r"the acceptance of exclude_\w+-\d+ did not fail "
            r"\(success True\)", self.realistic(success=True))

    def fork(self, attempt, output, status):
        """The ledger resumes and closes `attempt` in another output."""
        inventory = self.load(self.out / "inventory.json")
        for event, more in (("resume", {}), ("close", dict(status=status))):
            tg.ledger_append(
                self.attempts, event=event, stage="first",
                table=self.fgrid.t.name, attempt=attempt,
                candidate=inventory["candidate"], counts_file="x",
                counts=inventory["iterations_seal"], seed="f0",
                output=str(output), checkout=str(self.repo), **more)

    @after_void
    def test_a_void_attempt_with_a_second_output_is_refused(self):
        given = self.rerun()
        first = self.load(self.out / "inventory.json")["attempt"]
        self.fork(first, self.root / "fork", "inconclusive")
        self.refuses("follow-up attempt %s ran in more than one output: "
                     "%s, %s" % (first, re.escape(str(self.out)),
                                 re.escape(str(self.root / "fork"))),
                     **given)

    @after_void
    def test_a_judged_attempt_with_a_second_output_is_refused(self):
        given = self.rerun()
        second = self.load(given["followup"] / "inventory.json")["attempt"]
        self.fork(second, self.root / "fork", "pass")
        self.refuses("follow-up attempt %s ran in more than one output"
                     % second, **given)

    @after_void
    def test_a_judged_attempt_at_another_output_is_refused(self):
        # The ledger has the judged attempt in `rerun`, and --followup is a
        # copy of that output.
        given = self.rerun()
        second = self.load(given["followup"] / "inventory.json")["attempt"]
        copy = self.root / "copy"
        shutil.copytree(given["followup"], copy)
        self.refuses(
            "follow-up attempt %s is judged, from %s, but the ledger has "
            "it in %s" % (second, re.escape(str(copy)),
                          re.escape(str(given["followup"]))),
            followup=copy, followup_allocation=self.allocation(
                "alloc-z-copy", copy, self.work["z"]))

    def open_void_copy(self, name="unclosed"):
        """A complete void inventory under another attempt id, opened in
        the ledger and not closed; returns (id, output)."""
        out = self.root / name
        shutil.copytree(self.out, out)
        inventory = self.load(self.out / "inventory.json")
        (out / "inventory.json").write_text(json.dumps(
            dict(inventory, attempt=name + "-attempt")))
        tg.ledger_append(
            self.attempts, event="open", stage="first",
            table=self.fgrid.t.name, attempt=name + "-attempt",
            candidate=inventory["candidate"], counts_file="x",
            counts=inventory["iterations_seal"], seed="f0",
            output=str(out), checkout=str(self.repo))
        return name + "-attempt", out

    @after_void
    def test_a_void_inventory_with_no_close_in_the_ledger_is_refused(self):
        given = self.rerun()
        attempt, out = self.open_void_copy()
        self.refuses(self.reasons(
            attempt, "interrupted", out,
            r"its ledger has no close \(it was left open\)"), **given)

    def append_lines(self, out, attempt, *events):
        for event, status in events:
            fields = dict(status=status) if status else {}
            tg.ledger_append(
                self.attempts, event=event, stage="first",
                table=self.fgrid.t.name, attempt=attempt, candidate="c",
                counts_file="x", counts="y", seed="f0", output=str(out),
                checkout=str(self.repo), **fields)

    @after_void
    def test_a_resumed_void_attempt_is_refused(self):
        given = self.rerun()
        attempt, out = self.open_void_copy()
        self.append_lines(out, attempt, ("resume", None),
                          ("close", "inconclusive"))
        self.refuses(self.reasons(
            attempt, "inconclusive", out,
            "it was resumed: a resumed attempt may have drawn samples in "
            "the cell it cleared"), **given)

    @after_void
    def test_a_void_attempt_closed_twice_is_refused(self):
        given = self.rerun()
        attempt, out = self.open_void_copy()
        self.append_lines(out, attempt, ("close", "inconclusive"),
                          ("close", "inconclusive"))
        self.refuses(self.reasons(
            attempt, "inconclusive", out,
            "it closed more than once, as inconclusive, inconclusive: "
            "a repeated attempt may have measured"), **given)

    @after_void
    def test_a_plain_open_and_inconclusive_close_is_void(self):
        given = self.rerun()
        attempt, out = self.open_void_copy()
        self.append_lines(out, attempt, ("close", "inconclusive"))
        found = td.attempts_of(
            argparse.Namespace(ledger=self.attempts), self.fgrid, {
                self.load(given["followup"] / "inventory.json")[
                    "attempt"]: given["followup"].resolve()})
        self.assertIn((attempt, True), [(x["attempt"], x["void"])
                                        for x in found])

    @after_void
    def test_a_close_with_another_status_is_refused(self):
        given = self.rerun()
        held = self.attempts.read_bytes()
        for status in ("pass", "fail", "checkout-changed"):
            with self.subTest(status):
                attempt, out = self.open_void_copy("closed-" + status)
                tg.ledger_append(
                    self.attempts, event="close", stage="first",
                    table=self.fgrid.t.name, attempt=attempt,
                    candidate="c", counts_file="x", counts="y", seed="f0",
                    output=str(out), checkout=str(self.repo), status=status)
                self.refuses(self.reasons(
                    attempt, status, out,
                    "its ledger closes it %s, not inconclusive, the status "
                    "of a grid whose every cell is a protocol failure"
                    % status), **given)
                shutil.rmtree(out)
                self.attempts.write_bytes(held)

    @after_void
    def test_a_ledger_line_without_a_table_is_not_of_the_follow_up(self):
        # A line without `table` is of the family's first table, the
        # replaced grid's, whatever its output.
        tg.ledger_append(
            self.attempts, event="open", stage="first",
            attempt="legacy-attempt", candidate="c", counts_file="x",
            counts="y", seed="s", output=str(self.root / "nowhere"),
            checkout=str(self.repo))
        given = self.rerun()
        code, text = self.dispose(record=True, **given)
        self.assertEqual(code, 0, text)
        found = self.load(given["followup"] / "disposition.json")[
            "followup_attempts"]
        self.assertNotIn("legacy-attempt", [x["attempt"] for x in found])

    def test_the_refusal_comes_before_any_replay_in_check_mode(self):
        given = self.rerun()
        first = self.load(self.out / "inventory.json")["attempt"]
        self.refuses("follow-up attempt %s .*is not void" % first,
                     check=True, **given)

    @after_void
    def test_a_second_stage_and_its_first_stage_are_both_judged(self):
        self.new_control = lambda c, s, pairs, seed: (
            ttg.WIDE if (c, s) == ttf.CELL_B else ttg.GOOD)
        out, code, text = self.run_followup("first-open")
        self.assertEqual(code, 2, text)
        ext, code, text = self.extend_followup(out)
        self.assertEqual(code, 2, text)
        code, text = self.dispose(
            record=True, followup=ext, followup_allocation=(
                self.allocation("alloc-z-2", ext, self.work["z"])))
        self.assertEqual(code, 2, text)
        found = self.load(ext / "disposition.json")["followup_attempts"]
        self.assertEqual([(x["output"], x["judged"], x["void"])
                          for x in found], [
            (str(self.out), False, True), (str(out), True, False),
            (str(ext), True, False)])
        self.assertEqual(len([x for x in text.splitlines()
                              if x.startswith("FOLLOW-UP-ATTEMPT")]), 3)
        # Naming the first stage leaves the second unjudged and measured:
        # refused, before the replay can say a second stage is to come.
        later = self.load(ext / "inventory.json")["attempt"]
        self.refuses(self.reasons(
            later, "inconclusive", ext,
            r"the row of exclude_\w+-\d+ is not a protocol failure "
            r"\(protocol True\)"),
            followup=out, followup_allocation=self.allocz)

    @after_void
    def test_a_void_second_stage_is_checked_against_its_own_plan(self):
        self.new_control = lambda c, s, pairs, seed: (
            ttg.WIDE if (c, s) == ttf.CELL_B else ttg.GOOD)
        out, code, text = self.run_followup("first-open")
        self.assertEqual(code, 2, text)
        self.protocol_failure = lambda case, size: True
        ext, code, text = self.extend_followup(out)
        self.assertEqual(code, 2, text)
        found = self.load(ext / "inventory.json")
        self.assertEqual(len(found["plan"]), 1)
        self.assertEqual({r["protocol"] for r in found["runs"]}, {False})
        # The second stage is void against its own plan (one cell, not each
        # of the cells of the follow-up): the attempts pass, and naming the
        # first stage is refused later, as its second stage is to come.
        out_attempts = td.attempts_of(
            argparse.Namespace(ledger=self.attempts), self.fgrid, {
                self.load(out / "inventory.json")["attempt"]: out.resolve()})
        self.assertEqual([(x["judged"], x["void"]) for x in out_attempts],
                         [(False, True), (True, False), (False, True)])
        with self.assertRaisesRegex(
                ValueError, "--followup is not the follow-up's final "
                "stage: its second stage is still to come"):
            self.dispose(record=True, followup=out,
                         followup_allocation=self.allocz)

    @after_void
    def test_a_void_second_stage_closed_fail_says_why(self):
        self.new_control = lambda c, s, pairs, seed: (
            ttg.WIDE if (c, s) == ttf.CELL_B else ttg.GOOD)
        out, code, text = self.run_followup("first-open")
        self.assertEqual(code, 2, text)
        self.protocol_failure = lambda case, size: True
        ext, code, text = self.extend_followup(out)
        self.assertEqual(code, 2, text)
        later = self.load(ext / "inventory.json")["attempt"]
        lines = self.attempts.read_text().splitlines()
        edited = []
        for line in lines:
            record = json.loads(line)
            if record.get("event") == "close" and \
                    record.get("attempt") == later:
                record["status"] = "fail"
            edited.append(json.dumps(record))
        self.attempts.write_text("\n".join(edited) + "\n")
        with self.assertRaisesRegex(
                ValueError, "its ledger closes it fail: a second stage "
                "closes with the combined status of both stages, so a "
                "fail in its first stage is final"):
            td.attempts_of(
                argparse.Namespace(ledger=self.attempts), self.fgrid, {
                    self.load(out / "inventory.json")["attempt"]:
                        out.resolve()})


class Ordering(Toy):
    """Every cheap refusal comes before any replay."""

    def refuses(self, regex, **kw):
        """The refusal, with every replay made to fail the test."""
        boom = AssertionError("a replay ran before the refusal")
        with patch.object(self.fgrid, "replay", side_effect=boom), \
                patch.object(self.grid, "replay", side_effect=boom), \
                patch.object(am, "replay", side_effect=boom), \
                self.assertRaisesRegex(ValueError, regex):
            self.dispose(**kw)

    def test_the_cheap_refusals_of_check_mode_come_first(self):
        self.refuses("no recorded final.json")
        self.dispose(record=True)
        self.refuses("refusing to replace the recorded final.json",
                     record=True)
        (self.out / "disposition.json").unlink()
        self.refuses("no recorded disposition.json")

    def test_the_code_seal_is_checked_before_any_replay(self):
        self.dispose(record=True)
        real = a.seal

        def seal(path):
            found = real(path)
            if Path(path).name == "timing_grid.py":
                return dict(bytes=found["bytes"] + 1, sha256="e" * 64)
            return found
        with patch.object(a, "seal", seal):
            self.refuses("changed TASK30 disposition: 1 file.s. changed "
                         "since it was recorded.*timing_grid.py: add to")

    def test_the_pairing_is_checked_before_any_replay(self):
        self.refuses("one allocation grid cannot serve both",
                     allocation=self.allocz)
        self.refuses("--grid is not the grid the follow-up replaced",
                     grid=self.replaced1)


class Allocation(unittest.TestCase):
    """`Evidence.allocation` on a record that lacks what it compares."""

    def make(self, new, old):
        return make_evidence(new=new, old=old)

    def test_a_missing_phase_or_metric_is_named(self):
        for side, what in (("old", "alloc"), ("new", "alloc-z")):
            with self.subTest(side, what="phase"):
                new = alloc_decisions(LIMITED, setup=9)
                old = alloc_decisions(LIMITED, setup=7)
                target = old if side == "old" else new
                del target["cases"]["exclude_missing"]["cells"]["10"][
                    "phases"]["apply"]
                self.assertEqual(
                    self.make(new, old).holds("exclude_missing-10"),
                    "allocation: operation phase apply is missing from %s"
                    % what)
            with self.subTest(side, what="metric"):
                new = alloc_decisions(LIMITED, setup=9)
                old = alloc_decisions(LIMITED, setup=7)
                target = old if side == "old" else new
                del target["cases"]["exclude_missing"]["cells"]["10"][
                    "phases"]["operation_first"]["heap"]
                failed = self.make(new, old).holds("exclude_missing-10")
                self.assertRegex(
                    failed, r"^allocation: operation phase operation_first "
                    r"has other metrics in alloc \(.*\) than in alloc-z "
                    r"\(.*\)$")
                self.assertEqual("heap" in failed.split("alloc-z")[0],
                                 side == "new")


class RealShape(unittest.TestCase):
    """Evidence over allocation grids built by the real functions
    (`allocation_analysis.cell`, `allocation_matrix.assemble`, with work
    rows), written to JSON and read back: no stand-in for the data path."""

    EMPTY = "trace=;kernel=;maker=0;collector=0;dproc=0"
    USE = "trace=4.REDUCE=3;kernel=;maker=0;collector=0;dproc=0"
    RUN = ("trace=4.REDUCE=1;kernel=SPEC=2,total=2;maker=0;collector=0;"
           "dproc=0")

    def cell(self, first, second, use, digest="d", other=None):
        work = tb.structural(first, second, use, digest)
        if other is not None:
            work = (work, tb.structural(*other))
        pairs, control = tb.experiment({}, {}, work=work)
        record = an.cell(pairs, control, tb.STEADY)
        return dict(record, steady=tb.STEADY, pairs=len(pairs))

    def grid(self, cells):
        records = {(c, n): record for (c, n), record in cells.items()}
        decisions = am.assemble(set(records), records, {}, a.BASE,
                                am.TASKS["task30"])
        return json.loads(json.dumps(decisions))

    def test_a_pass_of_each_class_and_a_fail(self):
        e, u, r = self.EMPTY, self.USE, self.RUN
        cells = {
            ("exclude_missing", 10): self.cell(e, e, u),
            ("exclude_dproc", 10): self.cell(e, e, u.replace(
                "dproc=0", "dproc=9")),
            ("exclude_marker", 10000): self.cell(r, r, e),
            # The candidate's use differs from develop's.
            ("exclude_matching", 10): self.cell(
                e, e, u, other=(e, e, u.replace("=3", "=4"), "d")),
            # A deletion whose use is empty on both sides.
            ("exclude_batch", 10): self.cell(e, e, e),
            # The digest of the result differs.
            ("exclude_qualified", 10): self.cell(
                e, e, u, other=(e, e, u, "other"))}
        spec = dict(
            td.DISPOSITION,
            attributed={
                "%s-%d" % key: dict(
                    evidence_class=td.CASE_CLASS[key[0]], note="n")
                for key in cells})
        decisions = self.grid(cells)
        self.assertEqual(decisions["work"]["cells"], {
            "exclude_missing-10": "equal", "exclude_dproc-10": "equal",
            "exclude_marker-10000": "equal",
            "exclude_matching-10": "differs", "exclude_batch-10": "equal",
            "exclude_qualified-10": "differs"})
        ev = td.Evidence(spec, dict(source_identity=CLEAN), decisions,
                         decisions)
        for cell in ("exclude_missing-10", "exclude_dproc-10",
                     "exclude_marker-10000"):
            self.assertIsNone(ev.holds(cell), cell)
        self.assertEqual(
            ev.holds("exclude_matching-10"),
            'work: work row work.use.trace.4.REDUCE differs from develop '
            '(candidate ["4"], baseline ["3"], control ["3"])')
        self.assertEqual(
            ev.holds("exclude_batch-10"),
            "work: class deletion: work.use has no work.use.trace.4.REDUCE "
            "(an empty use shows nothing)")
        self.assertRegex(
            ev.holds("exclude_qualified-10"),
            r"^work: work row result.digest differs from develop "
            r"\(candidate ")
        # The records are the real ones.
        found = decisions["cases"]["exclude_missing"]["cells"]["10"]
        self.assertEqual(sorted(found["phases"]), sorted(an.GATED))
        self.assertEqual(td.counts(found["work"]), dict(
            first={}, second={}, use={"trace.4.REDUCE": [3]}))
        self.assertEqual(
            sum(len(m) for m in found["phases"].values()), 24)
        # The digest is a SHA-256 of the fingerprint.
        digest, = found["work"]["result.digest"]["candidate"]
        self.assertRegex(digest, "^[0-9a-f]{64}$")

    def varying_cell(self, side):
        """A deletion cell whose `side` has the use count 4 in odd pairs."""
        e, u = self.EMPTY, self.USE
        work = tb.structural(e, e, u, "d")
        pairs, control = tb.experiment({}, {}, work=work)
        other = tb.observation({}, tb.STEADY, tb.structural(
            e, e, u.replace("=3", "=4"), "d"))
        for i in range(1, len(pairs), 2):
            pairs[i][side] = other
        record = an.cell(pairs, control, tb.STEADY)
        return dict(record, steady=tb.STEADY, pairs=len(pairs))

    def test_a_row_that_varies_is_named_and_called_not_reproducible(self):
        spec = dict(td.DISPOSITION, attributed={
            "exclude_missing-10": dict(evidence_class=td.DELETION,
                                       note="n")})
        for side in ("candidate", "baseline"):
            with self.subTest(side):
                decisions = self.grid({
                    ("exclude_missing", 10): self.varying_cell(side)})
                self.assertIn(
                    ["exclude_missing", 10, "work.use.trace.4.REDUCE",
                     side], decisions["work"]["nondeterminism"])
                ev = td.Evidence(spec, dict(source_identity=CLEAN),
                                 decisions, decisions)
                # The sides of the row are grouped under it (a baseline
                # spread is a control spread too).
                self.assertRegex(
                    ev.holds("exclude_missing-10"),
                    r"work row work\.use\.trace\.4\.REDUCE is not "
                    r"reproducible \((\w+, )*%s(, \w+)*\)" % side)

    def test_the_operation_words_of_the_two_grids_are_compared(self):
        e, u = self.EMPTY, self.USE
        cells = {("exclude_missing", 10): self.cell(e, e, u)}
        spec = dict(td.DISPOSITION, attributed={
            "exclude_missing-10": dict(evidence_class=td.DELETION,
                                       note="n")})
        new = self.grid(cells)
        old = copy.deepcopy(new)
        ev = td.Evidence(spec, dict(source_identity=CLEAN), old, new)
        self.assertIsNone(ev.holds("exclude_missing-10"))
        old["cases"]["exclude_missing"]["cells"]["10"]["phases"][
            "operation_first"]["total"]["candidate"] = {"99": 10}
        self.assertRegex(ev.holds("exclude_missing-10"),
                         r"^allocation: operation row operation_first.total "
                         r"differs between alloc and alloc-z \(candidate")


CELLS = ttf.CELLS


if __name__ == "__main__":
    unittest.main()
