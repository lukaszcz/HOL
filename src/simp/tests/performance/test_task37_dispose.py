#!/usr/bin/env python3
"""The TASK37 disposition (task37_dispose.py, with task37_lineage.py and
task37_gates.py): every rule branch on the loaded tables, the lineage on a
real git repository, the timing replay through a real `Grid.replay` (the
rig of test_timing_grid), the readers on files in the producers' formats,
the pilot and follow-up joins, and the sealed code. The allocation case
shape is compared with the real `allocation_analysis.case_decisions`."""
import ast
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import types
import unittest
from unittest import mock

import acceptance as a
import allocation_analysis as an
import allocation_attempts as aa
import allocation_matrix as am
import task31_dispose as d31
import task32_downstream as d32
import task37_cases as c
import task37_dispose as d
from task37_dispose_testbed import lines_record
import task37_gates as gates
import task37_followup as followup
import task37_grid as grid
import task37_lineage as lin
import test_task37_allocation as t37
import test_timing_grid as ttg
import timing_grid as tg

tearDownModule = ttg.tearDownModule

RECORD = [dict(path="src/simp/src/Cond_rewr.sig", reason="adds a spec")]
D4 = c.D4
HEAVY = c.INFEASIBLE[0]
KEYS = grid.SHARD_KEYS
CAND = "c" * 40
ORIGINAL_REPLAY = d.replay_timing
ORIGINAL_CHECK_DECLARATION = d.check_declaration


def trow(cls="pass", first=None, stage2=False, followup=False,
         control_open=False, earlier=()):
    return dict(cls=cls, first=first or cls, stage2=stage2,
                followup=followup, earlier=list(earlier),
                control_open=control_open)


def ident(status="identical"):
    return dict(status=status, route="run",
                attributed=RECORD if status == "attributed" else [])


def arow(decision="pass", work="equal", pairs=3):
    return dict(decision=decision, work=work, pairs=pairs)


class Rule(unittest.TestCase):
    """`judge`: one cell."""

    NAME = "frag_create-100"

    def judge(self, identity="identical", alloc=None, timed=None,
              name=None, groups=None):
        return d.judge(name or self.NAME, ident(identity),
                       arow() if alloc is None else alloc, timed, set(D4),
                       groups)

    def test_unsampled_passes_on_identity_and_allocation(self):
        r = self.judge()
        self.assertEqual((r["status"], r["policy"]), ("pass", "stratified"))
        r = self.judge("attributed")
        self.assertEqual(r["status"], "pass")
        self.assertEqual(r["attribution"][0]["path"], RECORD[0]["path"])

    def test_identity(self):
        self.assertEqual(self.judge("different")["status"], "fail")
        for status in ("unresolved", "inconclusive"):
            r = self.judge(status)
            self.assertEqual((r["status"], r["owed"]),
                             ("incomplete", ["identity-rerun"]))

    def test_allocation(self):
        self.assertEqual(self.judge(alloc=arow("fail"))["status"], "fail")
        self.assertEqual(self.judge(alloc=arow(work="differs"))["status"],
                         "fail")
        for alloc in (arow("inconclusive", pairs=None),
                      arow(work="inconclusive"), arow(work=None)):
            r = self.judge(alloc=alloc)
            self.assertEqual((r["status"], r["owed"]),
                             ("incomplete", ["allocation-rerun"]))
        r = d.judge(self.NAME, ident(), None, None, set())
        self.assertEqual(r["status"], "incomplete")

    def test_timing_decisions(self):
        self.assertEqual(self.judge(timed=trow())["status"], "pass")
        r = self.judge(timed=trow("fail"))
        self.assertEqual(r["status"], "fail")
        self.assertEqual(r["failed"], ["timing: fail"])

    def test_a_fail_of_any_stage_decides(self):
        name = D4[0]
        # a follow-up that passed does not undo the shard's fail
        r = self.judge(timed=trow("pass", first="pass", followup=True,
                                  earlier=["fail"]))
        self.assertEqual(r["status"], "fail")
        self.assertEqual(r["failed"], ["timing: an earlier stage failed"])
        # nor can D4 dispose a cell whose follow-up is control-limited
        r = self.judge(name=name, timed=trow(
            "control_limited", followup=True, earlier=["fail"]))
        self.assertEqual((r["status"], r["policy"]), ("fail", None))
        # a failed first stage is a fail whatever a later stage says
        r = self.judge(name=name, timed=trow(
            "control_limited", first="fail", stage2=True))
        self.assertEqual((r["status"], r["policy"]), ("fail", None))
        # an earlier class that did not fail changes nothing
        r = self.judge(name=name, timed=trow(
            "control_limited", followup=True, earlier=["inconclusive"]))
        self.assertEqual((r["status"], r["policy"]), ("pass", "D4"))

    def test_inconclusive_never_passes_and_owes_something(self):
        r = self.judge(timed=trow("inconclusive"))
        self.assertEqual((r["status"], r["owed"]), ("incomplete",
                                                    ["followup"]))
        r = self.judge(timed=trow("inconclusive", followup=True))
        self.assertEqual((r["owed"], r["blocked"]), (["attribution"], True))
        r = self.judge(timed=trow("control_limited"))
        self.assertEqual((r["status"], r["owed"]), ("incomplete",
                                                    ["stage2"]))
        r = self.judge(timed=trow("control_limited", stage2=True))
        self.assertEqual((r["owed"], r["blocked"]), (["attribution"], True))
        r = self.judge(timed=trow("protocol"))
        self.assertEqual((r["status"], r["owed"]), ("incomplete",
                                                    ["redraw"]))

    def test_an_unsized_inconclusive_cell_owes_stage2(self):
        """Stage 1 inconclusive with an invalid control: stage 2 (sized by
        the control) is owed before any follow-up."""
        r = self.judge(timed=trow("inconclusive", control_open=True))
        self.assertEqual(r["owed"], ["stage2"])
        r = self.judge(timed=trow("inconclusive", control_open=True,
                                  stage2=True))
        self.assertEqual(r["owed"], ["followup"])
        r = self.judge(timed=trow("inconclusive", control_open=True,
                                  stage2=True, followup=True))
        self.assertEqual(r["owed"], ["attribution"])

    def test_every_incomplete_cell_lists_what_is_owed(self):
        for identity in ("identical", "unresolved"):
            for timed in (None, trow("inconclusive"),
                          trow("control_limited"), trow("protocol")):
                for alloc in (arow(), arow("inconclusive", pairs=None),
                              None):
                    r = self.judge(identity, alloc, timed)
                    if r["status"] == "incomplete":
                        self.assertTrue(r["owed"], r)

    def test_d4_policy_only_where_it_decides(self):
        name = D4[0]
        r = self.judge(name=name, timed=trow("control_limited"))
        self.assertEqual((r["status"], r["policy"]), ("pass", "D4"))
        self.assertIn("no stage 2", r["policy_note"])
        self.assertNotIn("skipped", r["policy_note"])
        # the note states the actual chain, stage 2 and follow-up included
        r = self.judge(name=name, timed=trow(
            "control_limited", first="inconclusive", stage2=True,
            followup=True, earlier=["inconclusive"]))
        self.assertIn("first stage inconclusive; stage 2 ran; follow-up "
                      "ran, replacing inconclusive; final class "
                      "control_limited", r["policy_note"])
        self.assertNotIn("no stage 2", r["policy_note"])
        # a fresh pass or fail decides as for any cell, with no policy
        r = self.judge(name=name, timed=trow())
        self.assertEqual((r["status"], r["policy"]), ("pass", None))
        self.assertEqual(self.judge(name=name, timed=trow("fail"))[
            "status"], "fail")
        # the decisive stage is the chain's final one: control-limited
        # after stage 1 inconclusive with an invalid control and a stage 2
        # is disposed by D4; the same chain of a cell outside D4 owes
        # the attribution
        chain = trow("control_limited", first="inconclusive", stage2=True,
                     control_open=True)
        r = self.judge(name=name, timed=chain)
        self.assertEqual((r["status"], r["policy"]), ("pass", "D4"))
        r = self.judge(timed=chain)
        self.assertEqual((r["status"], r["owed"]), ("incomplete",
                                                    ["attribution"]))
        # a stage 1 that was control-limited, then decided inconclusive by
        # stage 2: not disposed
        r = self.judge(name=name, timed=trow("inconclusive",
                                             first="control_limited",
                                             stage2=True))
        self.assertEqual((r["status"], r["policy"]), ("incomplete", None))
        # D4 needs identity and exact allocation: no D4 on a cell that
        # does not pass by it
        for kw in (dict(alloc=arow(work="differs")),
                   dict(identity="different"),
                   dict(identity="unresolved"),
                   dict(alloc=arow(work="inconclusive"))):
            r = self.judge(name=name, timed=trow("control_limited"), **kw)
            self.assertNotEqual(r["status"], "pass")
            self.assertIsNone(r["policy"])
        # a cell that is not on the list has no such policy
        self.assertEqual(self.judge(timed=trow("control_limited"))[
            "status"], "incomplete")

    def test_d2(self):
        r = d.judge(HEAVY, ident(), None, None, set(), None)
        self.assertEqual((r["status"], r["policy"]), ("pass", "D2"))
        self.assertEqual(d.judge(HEAVY, ident("different"), None, None,
                                 set(), None)["status"], "fail")
        none = dict(allocation=[], timing=[])
        r = d.judge(HEAVY, ident("attributed"), None, None, set(), none)
        self.assertEqual((r["status"], r["owed"]), ("incomplete",
                                                    ["attribution"]))
        some = dict(allocation=["x-1"], timing=["x-100"])
        r = d.judge(HEAVY, ident("attributed"), None, None, set(), some)
        self.assertEqual(r["status"], "pass")

    def test_measured_by(self):
        fam = d31.family_of(HEAVY)
        cells = {n: ident("attributed") for n in c.CLIENT_CELLS
                 if d31.family_of(n) == fam and n not in c.INFEASIBLE}
        alloc = {n: arow() for n in cells}
        timed = {n: trow() for n in cells if n in c.CLIENT_SAMPLE}
        got = d.measured_by(HEAVY, cells, alloc, timed)
        self.assertTrue(got["allocation"] and got["timing"])
        self.assertTrue(all(d31.size_of(n) <= 1000
                            for n in got["allocation"]))
        self.assertEqual(d.measured_by(HEAVY, cells, {}, {}),
                         dict(allocation=[], timing=[]))

    def test_finish_refuses_an_incomplete_record_that_owes_nothing(self):
        with self.assertRaisesRegex(ValueError, "owes nothing"):
            d.finish(dict(failed=[], missing=["x"], owed=[]))
        self.assertEqual(d.finish(dict(failed=[], missing=["x"],
                                       owed=["stage2"]))["status"],
                         "incomplete")


def table(names, status=None):
    status = status or {}
    return dict(cells={n: ident(status.get(n, "identical"))
                       for n in names},
                status="identical", unaccounted=[], attributed=[],
                attempts=[0, 0])


def alloc_table(task, names, rows=None, pairs=3):
    rows = rows or {}
    return dict(rows={n: dict(arow(pairs=pairs), **rows.get(n, {}))
                      for n in names}, pairs=pairs, attempts=[],
                cases={"%s:k" % task: dict(
                    slope="pass", constant="pass", failed=[], missing=[],
                    owed=[])},
                state=dict(status="pass", nondeterminism=0,
                           unresolved=[], work_status="pass"))


class Dispose(unittest.TestCase):
    """The join on loaded tables."""

    def tables(self, classes=None, identity=None, rows=None, scaling=None,
               differing=()):
        identity = identity or {}
        classes = classes or {}
        ids = dict(client=table(c.CLIENT_CELLS, identity),
                   matrix=table(c.MATRIX_CELLS, identity),
                   downstream=table(c.DOWNSTREAM_CELLS, identity))
        al = dict(
            matrix=alloc_table("task37-matrix", c.MATRIX_CELLS, rows),
            client=alloc_table("task37-client", c.CLIENT_ALLOCATED, rows),
            downstream=alloc_table("task37-downstream",
                                   c.DOWNSTREAM_CELLS, rows))
        timing = {}
        for key in KEYS:
            timing[grid.name_of(key)] = dict(
                cells={n: classes.get(n, trow()) for n in grid.PARTS[key]},
                scaling=scaling, scaling_raw=None,
                differing=list(differing),
                attempts=[], counts=[1, 1])
        units = {"u1": dict(unit="u1", failed=[], missing=[], owed=[])}
        return ids, al, timing, units, {}, {}

    def test_all_pass(self):
        r = d.dispose(*self.tables())
        self.assertEqual(r["status"], "pass")
        self.assertEqual(r["counts"]["fail"], 0)
        self.assertEqual(r["owed"], [])

    def test_the_default_d4_is_the_31_cells_of_cases(self):
        seen = []
        real = d.judge

        def spy(name, identity, allocated, timed, d4, groups=None):
            seen.append(set(d4))
            return real(name, identity, allocated, timed, d4, groups)
        with mock.patch.object(d, "judge", spy):
            d.dispose(*self.tables())
        self.assertEqual(seen[0], set(c.D4) | set(d.D4_TASK37))
        self.assertEqual(len(seen[0]), 32)

    def test_the_d4_of_a_disposition_adds_the_user_cells(self):
        self.assertEqual(d.D4_TASK37, ("frag_named-10000",))
        self.assertEqual(d.d4_cells(), set(c.D4) | set(d.D4_TASK37))
        self.assertEqual(len(d.d4_cells()), 32)
        seen = []
        real = d.judge

        def spy(name, identity, allocated, timed, d4, groups=None):
            seen.append(set(d4))
            return real(name, identity, allocated, timed, d4, groups)
        with mock.patch.object(d, "judge", spy):
            d.dispose(*self.tables())
        self.assertEqual(seen[0], d.d4_cells())

    def test_a_d4_task37_cell_passes_by_d4(self):
        name = d.D4_TASK37[0]
        self.assertNotIn(name, c.D4)
        ids = {name: "attributed"}
        r = d.dispose(*self.tables({name: trow("control_limited",
                                               stage2=True)},
                                   identity=ids))
        self.assertEqual((r["cells"][name]["status"],
                          r["cells"][name]["policy"]), ("pass", "D4"))
        self.assertIn(name, r["policies"]["D4"])
        # allocation that differs still fails it
        r = d.dispose(*self.tables({name: trow("control_limited",
                                               stage2=True)},
                                   identity=ids,
                                   rows={name: dict(work="differs")}))
        self.assertEqual(r["cells"][name]["status"], "fail")
        self.assertNotIn(name, r["policies"]["D4"])

    def test_d4_task37_must_be_sample_cells_outside_d4(self):
        for bad in (("frag_create-100",), (c.D4[0],),
                    ("frag_named-10000", "frag_named-10000")):
            with mock.patch.object(d, "D4_TASK37", bad):
                with self.assertRaisesRegex(ValueError, "D4_TASK37"):
                    d.dispose(*self.tables())
                self.assertRaises(ValueError, d.d4_cells)

    def test_d4_flag_set_only_for_a_d4_pass(self):
        name = c.D4[0]
        r = d.dispose(*self.tables({name: trow("control_limited")}))
        self.assertEqual(r["cells"][name]["policy"], "D4")
        self.assertEqual(r["policies"]["D4"], [name])
        r = d.dispose(*self.tables({name: trow("control_limited")},
                                   rows={name: dict(work="differs")}))
        self.assertEqual(r["policies"]["D4"], [])
        self.assertEqual(r["status"], "fail")

    def test_owed_is_collected_and_vocabulary_is_unified(self):
        name = [n for n in c.MATRIX_SAMPLE if n not in c.D4][0]
        r = d.dispose(*self.tables({name: trow("control_limited")}))
        self.assertEqual(r["status"], "incomplete")
        self.assertIn(dict(workload=name, owed="stage2"), r["owed"])
        self.assertEqual(gates.OWED_NAMES["second"], "stage2")

    def test_source_identity_differing_is_incomplete(self):
        r = d.dispose(*self.tables(differing=["src/x.sml"]))
        self.assertEqual(r["status"], "incomplete")
        self.assertTrue(r["timing_grid"]["task37-client-1"]["owed"])

    def test_allocation_case_and_slope_records(self):
        ids, al, timing, units, t33, rec = self.tables()
        al["matrix"]["cases"]["task37-matrix:k"] = dict(
            slope="fail", constant="pass",
            failed=["allocation slope: fail"], missing=[], owed=[])
        r = d.dispose(ids, al, timing, units, t33, rec)
        self.assertEqual(r["status"], "fail")
        self.assertEqual(r["allocation_case"]["task37-matrix:k"]["status"],
                         "fail")

    def part_sizes(self, key):
        return {c.split(n)[1] for n in grid.PARTS[key]
                if c.split(n)[0] == "storage_graph"}

    def blocked(self, key, drop=()):
        absent = sorted(set(a.SIZES) - self.part_sizes(key) | set(drop))
        return dict(status="blocked", missing_sizes=absent)

    def slope_key(self):
        return [k for k in KEYS if self.part_sizes(k)][0]

    def sampled(self, found=None, case=True, raw=None, drop=()):
        """Tables where the shard holding storage_graph has a blocked
        retained slope that is not its own to measure; `found` maps S1
        kinds to a status, `case` is the allocation case's status."""
        key = self.slope_key()
        ids, al, timing, units, t33, rec = self.tables()
        name = grid.name_of(key)
        timing[name]["scaling"] = "inconclusive"
        timing[name]["scaling_raw"] = raw or self.blocked(key, drop)
        for kind, status in (found or {}).items():
            t33["S1:" + kind] = dict(
                key="S1:" + kind, failed=["TASK33: fail"]
                if status == "fail" else [], missing=[
                    "TASK33: " + status] if status == "incomplete" else [],
                owed=["attribution"] if status == "incomplete" else [])
        if case:
            al["matrix"]["cases"]["task37-matrix:storage_graph"] = dict(
                slope="pass", constant="pass", failed=[], missing=[],
                owed=[])
            if case in ("fail", "incomplete"):
                al["matrix"]["cases"]["task37-matrix:storage_graph"].update(
                    failed=["allocation slope: fail"] if case == "fail"
                    else [], missing=["allocation slope: x"]
                    if case == "incomplete" else [],
                    owed=["allocation-rerun"] if case == "incomplete"
                    else [])
        return name, (ids, al, timing, units, t33, rec)

    def test_retained_slope_is_a_record(self):
        # a blocked slope missing a size its part holds is a measurement
        # gap: patch in a part with two storage_graph sizes, one missing
        key = self.slope_key()
        parts = dict(grid.PARTS)
        parts[key] = tuple(parts[key]) + ("storage_graph-10",)
        t = self.tables(scaling="inconclusive")
        t[2][grid.name_of(key)]["scaling_raw"] = dict(
            status="blocked", missing_sizes=sorted(
                set(a.SIZES) - {10, 1000} | {10}))
        with mock.patch.object(grid, "PARTS", parts):
            r = d.dispose(*t)
        self.assertEqual(r["status"], "incomplete")
        self.assertTrue(any(o["owed"] == "retained-slope"
                            for o in r["owed"]))
        self.assertEqual(r["retained_slope"][grid.name_of(key)]["class_"],
                         "inconclusive")
        r = d.dispose(*self.tables(scaling="fail"))
        self.assertEqual(r["status"], "fail")

    def test_not_sampled_slope_passes_on_its_deciders(self):
        S1 = {k: "pass" for k in d.RETAINED_KINDS}
        name, t = self.sampled(S1)
        r = d.dispose(*t)
        rec = r["retained_slope"][name]
        self.assertEqual(rec["class_"], "not-sampled")
        self.assertEqual(rec["status"], "pass")
        self.assertEqual(rec["owed"], [])
        self.assertEqual(rec["decided_by"], sorted(
            ["S1:" + k for k in S1] + ["task37-matrix:storage_graph"]))
        self.assertEqual(r["status"], "pass")
        self.assertTrue(any(
            l.startswith("PASS retained-slope %s: not-sampled, decided by"
                         % name) for l in d.lines(lines_record(
                retained_slope=r["retained_slope"]))))

    def test_not_sampled_slope_with_a_failing_decider_fails(self):
        S1 = {k: "pass" for k in d.RETAINED_KINDS}
        S1["merge"] = "fail"
        name, t = self.sampled(S1)
        rec = d.dispose(*t)["retained_slope"][name]
        self.assertEqual(rec["status"], "fail")
        self.assertTrue(any("S1:merge" in f for f in rec["failed"]))
        name, t = self.sampled({k: "pass" for k in d.RETAINED_KINDS},
                               case="fail")
        rec = d.dispose(*t)["retained_slope"][name]
        self.assertEqual(rec["status"], "fail")
        self.assertTrue(any("storage_graph" in f for f in rec["failed"]))

    def test_a_failing_s1_kind_outside_the_six_is_not_a_decider(self):
        S1 = {k: "pass" for k in d.RETAINED_KINDS}
        S1["cong"] = "fail"
        name, t = self.sampled(S1)
        rec = d.dispose(*t)["retained_slope"][name]
        self.assertEqual(rec["status"], "pass")
        self.assertNotIn("S1:cong", rec["decided_by"])

    def test_not_sampled_slope_with_an_incomplete_decider(self):
        S1 = {k: "pass" for k in d.RETAINED_KINDS}
        S1["fragment"] = "incomplete"
        name, t = self.sampled(S1)
        rec = d.dispose(*t)["retained_slope"][name]
        self.assertEqual(rec["status"], "incomplete")
        self.assertEqual(rec["missing"], [
            "retained slope: decided by S1:fragment, which is incomplete"])
        self.assertEqual(rec["owed"], ["retained-slope"])

    def test_not_sampled_slope_with_absent_deciders_is_never_a_pass(self):
        # none, only a subset of the S1 kinds, only the allocation case
        for found, case in (({}, False), ({"merge": "pass"}, False),
                            ({}, True)):
            name, t = self.sampled(found, case=case)
            rec = d.dispose(*t)["retained_slope"][name]
            self.assertEqual(rec["status"], "incomplete", (found, case))
            self.assertEqual(rec["owed"], ["retained-slope"])
            self.assertEqual(len(rec["decided_by"]),
                             len(d.RETAINED_KINDS) + 1)
            self.assertTrue(all("which is absent" in m
                                for m in rec["missing"]))
        name, t = self.sampled({"merge": "pass"}, case=False)
        rec = d.dispose(*t)["retained_slope"][name]
        self.assertNotIn("S1:merge", " ".join(rec["missing"]))
        self.assertEqual(len(rec["missing"]), len(d.RETAINED_KINDS))

    def test_identity_grid_status(self):
        ids, al, timing, units, t33, rec = self.tables()
        ids["client"]["status"] = "inconclusive"
        r = d.dispose(ids, al, timing, units, t33, rec)
        self.assertEqual(r["identity_grid"]["client"]["status"],
                         "incomplete")
        self.assertEqual(r["identity_grid"]["client"]["owed"],
                         ["identity-rerun"])

    def test_wrong_cell_set_is_refused(self):
        ids, al, timing, units, t33, rec = self.tables()
        ids["client"]["cells"].pop(c.CLIENT_CELLS[0])
        with self.assertRaisesRegex(ValueError, "not the cells"):
            d.dispose(ids, al, timing, units, t33, rec)


def case_record(slope="pass", constant="pass"):
    return dict(
        cells={}, slopes=dict(setup=dict(alloc=[dict(decision=slope)])),
        constants=dict(setup=dict(alloc=dict(decision=constant))))


class AllocationShape(unittest.TestCase):
    def test_case_words(self):
        self.assertEqual(d.case_decisions(case_record()),
                         dict(slope="pass", constant="pass"))
        self.assertEqual(d.case_decisions(case_record("fail"))["slope"],
                         "fail")
        self.assertEqual(d.case_decisions(case_record(
            "inconclusive", "fail")), dict(slope="inconclusive",
                                           constant="fail"))
        self.assertEqual(d.case_decisions(dict(cells={})),
                         dict(slope="missing", constant="missing"))

    def test_the_slope_shape_is_that_of_the_analysis(self):
        # the analysis' own reader finds the slope decisions where this
        # module reads them
        self.assertEqual(an.case_decisions(case_record("fail")), ["fail"])

    def test_case_records(self):
        found = d.case_records("t", dict(cases=dict(
            a=case_record(), b=case_record("fail"), c=dict(cells={}))))
        self.assertEqual(found["t:a"]["failed"], [])
        self.assertEqual(found["t:b"]["failed"], ["allocation slope: fail"])
        self.assertEqual(found["t:c"]["owed"], ["allocation-rerun"])
        self.assertEqual(len(found["t:c"]["missing"]), 2)


class FakeLineage:
    """What the readers need of task37_lineage.Lineage, without git."""
    candidate = CAND

    def __init__(self):
        self.recorded = {}

    def candidate_of(self, label, rev):
        self.recorded[label] = rev
        return rev

    def head(self):
        return "h" * 40

    def compiled_ref(self, rev):
        return rev

    EARLIER = "e" * 40   # a head the checkout is a descendant of

    def recorded_head(self, rev):
        a.require(rev == self.EARLIER, "not an earlier head: %s" % rev)
        return rev

    def harness(self, label, found, clean=False):
        a.require(isinstance(found, dict), "%s: no harness" % label)
        return found["head"]

    def equivalent(self, label, rev):
        return rev


class RefusingLineage(FakeLineage):
    """A lineage to which no other revision is equivalent."""

    def equivalent(self, label, rev):
        raise ValueError("%s names %s, whose tree is not the candidate's" %
                         (label, rev))


def write(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(value))


class Allocation(unittest.TestCase):
    """Allocation readers over the real decisions of allocation_matrix, the
    real attempts ledger of allocation_attempts and the real pairs of the
    task."""
    TASK = "task37-downstream"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "out"
        self.root.mkdir()
        self.ledger = Path(self.tmp.name) / "attempts.jsonl"
        self.make_ledger(self.root)

    def make_ledger(self, output, *events, ledger=None):
        for event, status in events or (("open", None),
                                        ("close", "pass")):
            tg.ledger_append(
                ledger or self.ledger, event=event, stage="first",
                table=self.TASK, attempt=aa.attempt_id(output),
                candidate=CAND, counts_file="c.json", counts="0" * 64,
                output=str(output), checkout=self.tmp.name,
                **(dict(status=status) if status else {}))

    def make(self, status="pass", cases=None, pairs=3, **over):
        task = am.task_named(self.TASK)
        harness = dict(head=CAND, dirty=False,
                       tree_outside_performance="t")
        write(self.root / "inventory.json", dict(
            candidate=CAND, baseline=a.BASE, task=self.TASK, pairs=pairs,
            harness=harness))
        out = am.assemble(*t37.grid_of(task, pairs), task=task,
                          candidate=CAND)
        for row in out["rows"]:
            row["work"] = "equal"  # a work-less row would explain a grid
        out.update(over)
        if cases is not None:
            out["cases"] = cases
        if status != "pass":
            out["status"] = status
        write(self.root / "decisions.json", out)
        return out

    def read(self, ledger=None):
        late = []
        got = d.read_allocation(self.root, self.TASK, c.DOWNSTREAM_CELLS,
                                (), FakeLineage(), ledger or self.ledger,
                                late)
        return got, late

    def test_the_real_decisions_have_the_shape_read(self):
        out = self.make()
        self.assertEqual({k: v["constants"] is None
                          for k, v in out["cases"].items()},
                         {k: 0 not in v["cells"]
                          for k, v in out["cases"].items()})
        self.assertTrue(any(v["constants"] is None
                            for v in out["cases"].values()))
        got, late = self.read()
        self.assertEqual(set(got["cases"]),
                         {self.TASK + ":" + k for k in out["cases"]})
        self.assertEqual(got["pairs"], 3)
        self.assertEqual(got["state"]["status"], "pass")
        self.assertEqual(len(late), 1)

    def test_constants_none_is_not_applicable_and_slopes_are_gated(self):
        out = self.make()
        none = [k for k, v in out["cases"].items()
                if v["constants"] is None]
        self.assertTrue(none)
        got, _ = self.read()
        for case in none:
            r = got["cases"]["%s:%s" % (self.TASK, case)]
            self.assertEqual((r["constant"], r["failed"], r["missing"],
                              r["owed"]), ("n/a", [], [], []))
            self.assertEqual(r["slope"], "pass")
        self.assertEqual(d.case_decisions(dict(
            cells={}, constants=None, slopes=case_record("fail")["slopes"])),
            dict(slope="fail", constant="n/a"))
        broken = copy.deepcopy(out["cases"])
        for case in none:
            for phase in broken[case]["slopes"].values():
                for rows in phase.values():
                    rows[0]["decision"] = "fail"
        self.make(cases=broken, status="fail")
        got, _ = self.read()
        r = got["cases"]["%s:%s" % (self.TASK, none[0])]
        self.assertEqual(r["failed"], ["allocation slope: fail"])

    def test_a_case_of_one_size_has_no_slope_to_gate(self):
        out = self.make()
        got, _ = self.read()
        r = got["cases"][self.TASK + ":downstream_boss"]
        self.assertEqual((r["slope"], r["constant"], r["missing"]),
                         ("n/a", "pass", []))
        self.assertEqual(out["cases"]["downstream_boss"]["slopes"]
                         ["setup"]["total"], [])

    def test_one_record_per_case_and_the_status_recorded(self):
        self.make(cases={"k": case_record(), "m": case_record("fail")},
                  status="fail")
        got, late = self.read()
        self.assertEqual(set(got["cases"]), {self.TASK + ":k",
                                             self.TASK + ":m"})
        self.assertEqual(got["state"]["status"], "fail")
        self.assertEqual(got["state"]["nondeterminism"], 0)

    def test_a_grid_that_is_not_pass_and_explains_nothing_is_refused(self):
        self.make(status="inconclusive")
        with self.assertRaisesRegex(ValueError, "explains it"):
            self.read()
        self.make(status="inconclusive", unresolved=["x"])
        self.read()
        self.make(status="inconclusive",
                  cases={"k": case_record("fail")})
        self.read()

    def test_the_pairs_are_the_tasks_own(self):
        self.assertEqual(d.required_pairs(self.TASK), 3)
        self.assertEqual(d.required_pairs("task31"), 10)
        self.make(pairs=3)
        self.read()
        self.make(pairs=2)
        with self.assertRaisesRegex(ValueError, "not the task's 3"):
            self.read()

    def test_an_inventory_of_the_legacy_pairs_is_refused(self):
        self.make(pairs=10)
        with self.assertRaisesRegex(ValueError, "not the task's 3"):
            self.read()

    def test_the_replay_and_the_ledger_run_late(self):
        self.make()
        calls = []
        with mock.patch.object(d, "replay_allocation",
                               lambda root: calls.append("replay")):
            got, late = self.read()
            self.assertIsNone(got["attempts"])
            late[0][1]()
        self.assertEqual(calls, ["replay"])
        self.assertEqual(got["attempts"], [dict(
            attempt=aa.attempt_id(self.root), status="pass",
            output=str(self.root), judged=True, void=False)])

    def replayed(self, ledger=None):
        self.make()
        with mock.patch.object(d, "replay_allocation", lambda root: None):
            got, late = self.read(ledger)
            late[0][1]()
        return got

    def test_the_output_given_is_the_judged_attempt(self):
        void = Path(self.tmp.name) / "void"
        void.mkdir()
        self.make_ledger(void, ("open", None), ("close", "failed"))
        got = self.replayed()
        self.assertEqual([(x["judged"], x["void"])
                          for x in got["attempts"]],
                         [(True, False), (False, True)])

    def test_an_extra_attempt_that_is_not_void_is_refused(self):
        other = Path(self.tmp.name) / "other"
        other.mkdir()
        (other / "x-1.json.xz").write_bytes(b"x")
        self.make_ledger(other, ("open", None), ("close", "failed"))
        with self.assertRaisesRegex(ValueError, "refused.*not void"):
            self.replayed()

    def test_the_output_must_be_in_the_ledger(self):
        elsewhere = Path(self.tmp.name) / "elsewhere"
        elsewhere.mkdir()
        ledger = Path(self.tmp.name) / "other.jsonl"
        self.make_ledger(elsewhere, ledger=ledger)
        with self.assertRaisesRegex(ValueError, "not in the ledger"):
            self.replayed(ledger)

    def test_an_inventory_of_other_pairs_than_the_task_is_refused(self):
        self.make(pairs=5)
        with self.assertRaisesRegex(ValueError, "not the task's 3"):
            self.read()

    def test_a_ledger_is_required(self):
        self.make()
        with self.assertRaisesRegex(ValueError, "no allocation attempts"):
            d.read_allocation(self.root, self.TASK, c.DOWNSTREAM_CELLS, (),
                              FakeLineage(), None, [])

    def test_the_adapter_is_allocation_attempts(self):
        found = d.allocation_attempts(self.TASK, self.ledger, self.root)
        self.assertEqual(found, aa.attempts_of(
            self.TASK, self.ledger,
            {aa.attempt_id(self.root): self.root}))
        with self.assertRaisesRegex(ValueError, "no attempts ledger"):
            d.allocation_attempts(self.TASK, self.root / "none",
                                  self.root)
        with self.assertRaisesRegex(ValueError, "no attempts ledger"):
            d.allocation_attempts("task31", self.ledger, self.root)

    def test_a_void_attempt_is_listed_with_its_rejections(self):
        void = dict(attempt="k1", status="failed", judged=False, void=True,
                    rejections=[dict(archive="x-1.json.xz",
                                     reason="unresolved cell")])
        judged = dict(attempt="k2", status="pass", judged=True, void=False)
        record = lines_record(attempts=dict(
            allocation={"task37-downstream": [void, judged]}))
        self.assertEqual(d.lines(record), [
            "ALLOCATION-ATTEMPT task37-downstream k1 status failed: void "
            "(every cell archive rejected on replay)",
            "ALLOCATION-ATTEMPT task37-downstream k1 rejected "
            "x-1.json.xz: unresolved cell",
            "ALLOCATION-ATTEMPT task37-downstream k2 status pass: judged"])


class Lineage(unittest.TestCase):
    """The candidate equivalence, on a real repository."""

    def git(self, *args):
        return subprocess.run(
            ["git", "-C", str(self.repo), "-c", "user.name=t", "-c",
             "user.email=t@t", *args], check=True, text=True,
            stdout=subprocess.PIPE).stdout.strip()

    def commit(self, path, text):
        p = self.repo / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        self.git("add", "-A")
        self.git("commit", "-qm", text)
        return self.git("rev-parse", "HEAD")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name).resolve()
        self.git("init", "-q", ".")
        perf = "src/simp/tests/performance/p.txt"
        (self.repo / "src/simp/tests/performance").mkdir(parents=True)
        (self.repo / "src/simp/tests/performance/p.txt").write_text("0")
        self.c1 = self.commit("x.txt", "one")
        self.c2 = self.commit(perf, "perf only")
        self.c3 = self.commit(perf, "perf again")
        self.other = self.commit("x.txt", "source change")
        patch = mock.patch.object(
            a, "HERE", self.repo / "src/simp/tests/performance")
        patch.start()
        self.addCleanup(patch.stop)

    def test_only_the_checkout_that_holds_the_code(self):
        with self.assertRaisesRegex(ValueError, "checkout that holds"):
            lin.Lineage(self.repo / "src", self.c2)

    def test_performance_only_commits_are_equivalent(self):
        got = lin.Lineage(self.repo, self.c3)
        self.assertEqual(got.equivalent("x", self.c2), self.c2)
        self.assertEqual(got.equivalent("x", self.c1), self.c1)
        self.assertEqual(got.candidate_of("t", self.c2), self.c2)
        self.assertEqual(got.recorded["t"], self.c2)

    def test_the_head_is_recorded_and_the_tracked_tree_must_be_clean(self):
        got = lin.Lineage(self.repo, self.c3)
        self.assertEqual(got.head(), self.other)
        # untracked files and .agent-files are not in the way
        (self.repo / "scratch.txt").write_text("u")
        (self.repo / ".agent-files").mkdir()
        (self.repo / ".agent-files/e.txt").write_text("e")
        self.assertEqual(got.head(), self.other)
        (self.repo / "src/simp/tests/performance/p.txt").write_text("edit")
        with self.assertRaisesRegex(ValueError, "uncommitted changes"):
            got.head()

    def test_a_later_performance_only_commit_leaves_the_head_acceptable(
            self):
        perf = "src/simp/tests/performance/p.txt"
        recorded = self.git("rev-parse", "HEAD")
        later = self.commit(perf, "later perf only")
        got = lin.Lineage(self.repo, recorded)
        self.assertEqual(got.head(), later)
        self.assertEqual(got.recorded_head(recorded), recorded)
        self.assertEqual(got.recorded_head(later), later)
        # a head that differs outside the performance area, or that is not
        # an ancestor, or that is unknown, is refused
        with self.assertRaisesRegex(ValueError, "tree outside"):
            got.recorded_head(self.c1)
        side = self.git("commit-tree", "-m", "side", "-p", self.c1,
                        self.c1 + "^{tree}")
        with self.assertRaisesRegex(ValueError, "not an ancestor"):
            got.recorded_head(side)
        with self.assertRaisesRegex(ValueError, "no commit"):
            got.recorded_head("e" * 40)
        with self.assertRaisesRegex(ValueError, "ten hex"):
            got.recorded_head(None)
        # a later commit outside the performance area changes the HEAD's
        # tree: the recorded head is then refused
        self.commit("x.txt", "later source change")
        got = lin.Lineage(self.repo, recorded)
        with self.assertRaisesRegex(ValueError, "tree outside"):
            got.recorded_head(recorded)

    def test_the_compiled_reference_must_be_equivalent_to_the_candidate(
            self):
        got = lin.Lineage(self.repo, self.c3)
        self.assertEqual(got.compiled_ref(self.c2), self.c2)
        with self.assertRaisesRegex(ValueError, "tree outside"):
            got.compiled_ref(self.other)
        with self.assertRaisesRegex(ValueError, "no commit"):
            got.compiled_ref("f" * 40)

    def test_a_different_tree_is_refused(self):
        got = lin.Lineage(self.repo, self.c3)
        with self.assertRaisesRegex(ValueError, "tree outside"):
            got.equivalent("x", self.other)

    def test_a_non_ancestor_is_refused(self):
        self.git("checkout", "-q", "-b", "side", self.c1)
        side = self.commit("src/simp/tests/performance/q.txt", "side")
        self.git("checkout", "-q", "-")
        got = lin.Lineage(self.repo, self.c3)
        with self.assertRaisesRegex(ValueError, "not an ancestor"):
            got.equivalent("x", side)

    def test_an_unknown_or_short_revision_is_refused(self):
        got = lin.Lineage(self.repo, self.c3)
        with self.assertRaisesRegex(ValueError, "no commit"):
            got.equivalent("x", "d" * 40)
        with self.assertRaisesRegex(ValueError, "ten hex"):
            got.equivalent("x", "abc")

    def test_harness(self):
        got = lin.Lineage(self.repo, self.c3)
        good = dict(head=self.c2, tree_outside_performance=got.tree,
                    dirty=False)
        self.assertEqual(got.harness("h", good, clean=True), self.c2)
        with self.assertRaisesRegex(ValueError, "dirty"):
            got.harness("h", dict(good, dirty=True))
        with self.assertRaisesRegex(ValueError, "dirty"):
            got.harness("h", {k: v for k, v in good.items()
                              if k != "dirty"}, clean=True)
        with self.assertRaisesRegex(ValueError, "another tree"):
            got.harness("h", dict(good, tree_outside_performance="z"))
        with self.assertRaisesRegex(ValueError, "no harness"):
            got.harness("h", None)

    def test_tie_records_the_candidate(self):
        got = lin.Lineage(self.repo, self.c3)
        self.assertEqual(d.tie("in", dict(candidate=self.c2), got),
                         self.c2)
        self.assertEqual(got.recorded["in"], self.c2)
        with self.assertRaisesRegex(ValueError, "no candidate"):
            d.tie("in", {}, got)
        with self.assertRaisesRegex(ValueError, "another baseline"):
            d.tie("in", dict(candidate=self.c2, baseline="x"), got)


def fake_follow(table):
    return types.SimpleNamespace(t=types.SimpleNamespace(
        name=table + "-followup", fixed_seconds=True,
        counts=types.SimpleNamespace(name="x"),
        names=lambda: list(grid.PARTS[KEYS[0]][:1])))


class Pilot(unittest.TestCase):
    """The pilot reaches every replay of a fixed-seconds table."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.key = KEYS[0]
        self.table = grid.name_of(self.key)
        self.calls = []
        self.engine = types.SimpleNamespace(
            t=types.SimpleNamespace(
                name=self.table, fixed_seconds=True,
                counts=types.SimpleNamespace(name="x")),
            h=types.SimpleNamespace(
                attempt_counts=lambda ledger, cand: (1, 1)))
        self.ledger = self.root / "ledger"
        self.ledger.touch()
        self.names = list(grid.PARTS[self.key])
        for target, value in (
                (d, ("timing_engine", lambda key: self.engine)),
                (d, ("read_stage", self.stage)),
                (d, ("check_counts", lambda *args: None)),
                (d, ("check_declaration", lambda *args: None)),
                (d, ("pins_binding", lambda *args: {})),
                (d, ("replay_timing", self.spy)),
                (d, ("ledger_attempts", self.attempts)),
                (d31, ("judged_attempts",
                       lambda engine, root: {"a1": root})),
                (tg, ("Ledger", lambda path: None))):
            patch = mock.patch.object(target, *value)
            patch.start()
            self.addCleanup(patch.stop)
        self.stages = {}
        self.document = dict(entries=[])

    def stage(self, root, label, lineage):
        found = self.stages.get(Path(root).name)
        if found is None:
            found = dict(
                root=Path(root), first_root=Path(root),
                inventory=dict(candidate=CAND), first_inventory={},
                scaling=None, scaling_raw=None,
            differing=[], seals={}, plan={},
                final={n: "pass" for n in self.names},
                first={n: "pass" for n in self.names})
        return dict(found)

    def spy(self, engine, root, repo, ledger, pilot=None,
            replaces_pilot=None):
        self.calls.append(("replay", engine.t.name, pilot, replaces_pilot))

    def attempts(self, engine, judged, repo, ledger):
        self.calls.append(("attempts", engine.t.name, dict(judged)))
        return []

    def options(self, **more):
        base = dict(timing={self.key: self.root / "main"},
                    ledger={self.key: self.ledger},
                    pilot={self.key: self.root / "pilot"}, followup={})
        base["followup-pilot"] = {}
        base.update(more)
        return base

    def read(self, options, followup=None):
        late = []
        with mock.patch.object(d, "followup_engines",
                               lambda: followup or {}):
            held = d.read_shard(self.key, options, FakeLineage(), "repo",
                                self.document, late)
        return held, late

    def test_the_pilot_is_required(self):
        with self.assertRaisesRegex(ValueError, "no --pilot"):
            self.read(self.options(pilot={}))

    def test_the_pilot_reaches_the_main_replay_and_runs_late(self):
        held, late = self.read(self.options())
        self.assertEqual(self.calls, [])
        late[0][1]()
        replays = [x for x in self.calls if x[0] == "replay"]
        self.assertEqual(replays, [("replay", self.table,
                                    self.root / "pilot", None)])
        self.assertEqual(held["counts"], [1, 1])

    def test_a_fixed_seconds_replay_without_a_pilot_is_refused(self):
        with mock.patch.object(d, "replay_timing", ORIGINAL_REPLAY):
            with self.assertRaisesRegex(ValueError, "needs its pilot"):
                d.replay_timing(self.engine, self.root, "repo", None)

    def test_a_declared_follow_up_is_judged_whether_or_not_given(self):
        self.read_late = self.read(
            self.options(), {followup.name_of(self.key):
                             fake_follow(self.table)})
        self.read_late[1][0][1]()
        judged = [x for x in self.calls if x[0] == "attempts"]
        self.assertEqual([x[1] for x in judged],
                         [self.table, followup.name_of(self.key)])
        self.assertEqual(judged[1][2], {})

    def test_a_follow_up_needs_a_declaration_and_its_pilot(self):
        options = self.options(followup={self.key: self.root / "f"})
        with self.assertRaisesRegex(ValueError, "no follow-up is declared"):
            self.read(options)
        with self.assertRaisesRegex(ValueError, "needs --followup-pilot"):
            self.read(options, {followup.name_of(self.key):
                                fake_follow(self.table)})

    def test_a_follow_up_pilot_without_a_follow_up_is_refused(self):
        options = self.options()
        options["followup-pilot"] = {self.key: self.root / "fp"}
        with self.assertRaisesRegex(ValueError, "no --followup"):
            self.read(options)

    def test_the_follow_up_must_replace_the_shards_output(self):
        first = self.names[0]
        self.stages["f"] = dict(
            root=self.root / "f", first_root=self.root / "f",
            inventory=dict(candidate=CAND, replaces=dict(
                grid="../elsewhere")),
            first_inventory={}, scaling=None, scaling_raw=None,
            differing=[], seals={},
            plan={}, final={first: "pass"}, first={first: "pass"})
        options = self.options(followup={self.key: self.root / "f"})
        options["followup-pilot"] = {self.key: self.root / "fp"}
        with self.assertRaisesRegex(ValueError, "does not replace"):
            self.read(options, {followup.name_of(self.key):
                                fake_follow(self.table)})

    def test_a_follow_up_that_replaces_the_output_gets_both_pilots(self):
        first = self.names[0]
        self.stages["f"] = dict(
            root=self.root / "f", first_root=self.root / "f",
            inventory=dict(candidate=CAND, replaces=dict(grid="../main")),
            first_inventory={}, scaling=None, scaling_raw=None,
            differing=[], seals={},
            plan={}, final={first: "inconclusive"},
            first={first: "inconclusive"})
        options = self.options(followup={self.key: self.root / "f"})
        options["followup-pilot"] = {self.key: self.root / "fp"}
        # the shard's output is resolved, and so is what the follow-up
        # names
        (self.root / "f").mkdir()
        (self.root / "main").mkdir()
        held, late = self.read(options, {followup.name_of(self.key):
                                         fake_follow(self.table)})
        late[0][1]()
        replays = [x for x in self.calls if x[0] == "replay"]
        self.assertEqual(len(replays), 2)
        self.assertEqual(replays[1][2:], (
            (self.root / "fp").resolve(), (self.root / "pilot").resolve()))
        self.assertEqual(held["cells"][first]["cls"], "inconclusive")
        self.assertTrue(held["cells"][first]["followup"])
        self.assertEqual(held["cells"][first]["earlier"], ["pass"])

    def two_stages(self, main_class, follow_class):
        first = self.names[0]
        self.stages["main"] = dict(
            root=self.root / "main", first_root=self.root / "main",
            inventory=dict(candidate=CAND), first_inventory={},
            scaling=None, scaling_raw=None,
            differing=[], seals={}, plan={},
            final={n: main_class if n == first else "pass"
                   for n in self.names},
            first={n: main_class if n == first else "pass"
                   for n in self.names})
        self.stages["f"] = dict(
            root=self.root / "f", first_root=self.root / "f",
            inventory=dict(candidate=CAND, replaces=dict(grid="../main")),
            first_inventory={}, scaling=None, scaling_raw=None,
            differing=[], seals={},
            plan={}, final={first: follow_class},
            first={first: follow_class})
        (self.root / "f").mkdir(exist_ok=True)
        (self.root / "main").mkdir(exist_ok=True)
        options = self.options(followup={self.key: self.root / "f"})
        options["followup-pilot"] = {self.key: self.root / "fp"}
        return first, options

    def test_a_shard_fail_is_not_undone_by_a_follow_up(self):
        engines = {followup.name_of(self.key): fake_follow(self.table)}
        for later, d4 in (("pass", False), ("control_limited", True)):
            first, options = self.two_stages("fail", later)
            held, _ = self.read(options, engines)
            row = held["cells"][first]
            self.assertEqual((row["cls"], row["earlier"]), (later, ["fail"]))
            name = D4[0] if d4 else first
            record = d.judge(name, ident(), arow(), row, set(D4))
            self.assertEqual(record["status"], "fail", later)
            self.assertIsNone(record["policy"])
            self.assertEqual(record["failed"],
                             ["timing: an earlier stage failed"])

    def test_the_follow_ups_declaration_is_checked_against_its_counts(self):
        seen = []
        first, options = self.two_stages("inconclusive", "pass")
        with mock.patch.object(d, "check_declaration",
                               lambda *args: seen.append(args)):
            self.read(options, {followup.name_of(self.key):
                                fake_follow(self.table)})
        self.assertEqual([x[0] for x in seen], [self.key])
        self.assertEqual(seen[0][2], "repo")

    def test_check_declaration_reads_each_inventorys_counts_commit(self):
        stage = dict(inventory=dict(candidate=CAND, counts_commit="1" * 40),
                     first_inventory=dict(candidate="d" * 40,
                                          counts_commit="2" * 40))
        with mock.patch.object(followup, "check_declaration_order") as run:
            ORIGINAL_CHECK_DECLARATION(self.key, stage, "repo")
        self.assertEqual([x.args for x in run.call_args_list], [
            ("repo", CAND, self.key, "1" * 40),
            ("repo", "d" * 40, self.key, "2" * 40)])
        stage["inventory"].pop("counts_commit")
        with self.assertRaisesRegex(ValueError, "no counts commit"):
            ORIGINAL_CHECK_DECLARATION(self.key, stage, "repo")

    def follow_stage(self, extension, first, replaces_ext=None,
                     replaces_first=None):
        cell = self.names[0]
        self.stages["f"] = dict(
            root=extension, first_root=first,
            inventory=dict(candidate=CAND, replaces=replaces_ext),
            first_inventory=dict(candidate=CAND, replaces=replaces_first),
            scaling=None, scaling_raw=None,
            differing=[], seals={}, plan={},
            final={cell: "pass"}, first={cell: "pass"})
        options = self.options(followup={self.key: self.root / "f"})
        options["followup-pilot"] = {self.key: self.root / "fp"}
        return options

    def test_replaces_is_resolved_against_each_inventorys_own_root(self):
        main = self.root / "main"
        ext = self.root / "elsewhere" / "deep" / "ext"
        first = self.root / "other" / "first"
        for each in (main, ext, first):
            each.mkdir(parents=True)
        engines = {followup.name_of(self.key): fake_follow(self.table)}
        # the extension and its first stage are not siblings, and each
        # names the replaced output relative to itself
        good = self.follow_stage(
            ext, first, dict(grid=os.path.relpath(main, ext)),
            dict(grid=os.path.relpath(main, first)))
        held, _ = self.read(good, engines)
        self.assertTrue(held["cells"][self.names[0]]["followup"])
        # resolving the first stage's name against the extension's root
        # (the old reading) would miss: it is refused when it points
        # elsewhere from its own root
        bad = self.follow_stage(
            ext, first, dict(grid=os.path.relpath(main, ext)),
            dict(grid=os.path.relpath(main, ext)))
        with self.assertRaisesRegex(ValueError, "does not replace"):
            self.read(bad, engines)
        none = self.follow_stage(ext, first)
        with self.assertRaisesRegex(ValueError, "does not replace"):
            self.read(none, engines)


def metric(decision="pass", reason="", **more):
    return dict(decision=decision, median_paired_ratio=1.0,
                paired_ratio_bootstrap_95_percent=[0.99, 1.01],
                reason=reason, **more)


def workload(case, size, protocol=True, **metrics):
    """A row of a grid's decisions.json (task29_gate.summary): a failed
    protocol has no metrics."""
    if not protocol:
        return dict(case=case, size=size, protocol=False, exit=2,
                    unresolved="blocked")
    found = dict(cpu=metric(), wall=metric(), gc=metric("reported"))
    found.update(metrics)
    return dict(case=case, size=size, protocol=True, exit=0,
                metrics=found, control_metrics={})


class ReadStage(unittest.TestCase):
    """`read_stage` over the files of a timing output."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def stage(self, rows):
        write(self.root / "inventory.json", dict(
            candidate=CAND, checkout=dict(head=CAND)))
        write(self.root / "decisions.json", dict(
            workloads=rows, retained_scaling=None,
            source_identity=dict(differing=[])))
        return d.read_stage(self.root, "t", FakeLineage())

    def test_the_unsampled_slope_is_read_and_disposed(self):
        """The slope of a part holding storage_graph at 1000 only is
        blocked by acceptance.retained_scaling; read_stage keeps that and
        dispose records it as not-sampled."""
        row = dict(candidate=dict(case="storage_graph", size=1000))
        raw = a.retained_scaling([row])
        write(self.root / "inventory.json", dict(
            candidate=CAND, checkout=dict(head=CAND)))
        write(self.root / "decisions.json", dict(
            workloads=[workload("storage_graph", 1000)],
            retained_scaling=raw, source_identity=dict(differing=[])))
        found = d.read_stage(self.root, "t", FakeLineage())
        self.assertEqual(found["scaling"], "inconclusive")
        self.assertEqual(found["scaling_raw"]["missing_sizes"],
                         [0, 1, 10, 100, 10000])
        rec = d.retained_record(
            "task37-matrix-3", found["scaling"], found["scaling_raw"],
            {}, {})
        self.assertEqual(rec["class_"], "not-sampled")
        self.assertEqual(rec["status"], "incomplete")

    def test_a_protocol_failed_cell_has_no_metrics_to_inspect(self):
        """A cell with no admitted measurement has no `metrics`: it is
        recorded (class `protocol`, owing a `redraw`) and the others are
        read as before."""
        open_ = workload("a", 1, cpu=metric("inconclusive", tg.CONTROL))
        found = self.stage([
            workload("a", 1, **open_["metrics"]),
            workload("b", 10, protocol=False), workload("c", 100)])
        self.assertEqual(found["control_open"], ["a-1"])
        self.assertEqual(found["final"], {
            "a-1": "control_limited", "b-10": "protocol", "c-100": "pass"})
        row = d.judge("b-10", ident(), arow(), dict(
            cls="protocol", first="protocol", stage2=False,
            followup=False, earlier=[], control_open=False), set())
        self.assertEqual((row["status"], row["owed"]),
                         ("incomplete", ["redraw"]))

    def test_the_owed_stage_is_the_engines_rule(self):
        """`owes_stage2` reads `Grid.extension_pairs`' rule from the row:
        checked against the engine over every combination of the two
        gated metrics' decisions and controls."""
        engine = grid.GRIDS["task37-matrix-1"]
        gated = ("cpu", "wall")
        states = [("pass", True), ("inconclusive", True),
                  ("inconclusive", False), ("fail", True),
                  ("fail", False)]
        count = 0
        for cpu in states:
            for wall in states:
                result = dict(
                    candidate=dict(metrics={}),
                    control=dict(metrics={m: dict(
                        paired_ratio_bootstrap_95_percent=[0.9, 1.1])
                        for m in gated}))
                row = workload("a", 1)
                for m, (decision, valid) in zip(gated, (cpu, wall)):
                    reason = (tg.CONTROL if not valid and
                              decision != "fail" else
                              "other" if decision == "inconclusive" else "")
                    result["candidate"]["metrics"][m] = dict(
                        decision=decision, reason=reason,
                        control_valid=valid)
                    row["metrics"][m] = metric(decision, reason)
                report = dict(success=True, workloads=[result])
                self.assertEqual(
                    d.owes_stage2(row),
                    engine.extension_pairs(report, 20) is not None,
                    (cpu, wall))
                count += 1
        self.assertEqual(count, 25)
        # a failed protocol: the engine plans nothing and nor does the row
        self.assertIsNone(engine.extension_pairs(dict(success=False), 20))
        self.assertFalse(d.owes_stage2(workload("a", 1, protocol=False)))
        # a non-gated metric's control reason does not owe a stage
        row = workload("a", 1, gc=metric("inconclusive", tg.CONTROL))
        self.assertFalse(d.owes_stage2(row))
        self.assertEqual(d.chain_text(trow()), "first stage pass; no "
                         "stage 2; final class pass")


class RealReplay(ttg.Rig):
    """`replay_timing` against a real `Grid.replay` (the rig's toy table,
    with the pilot)."""

    def test_a_real_replay_through_replay_timing(self):
        out, status, _ = self.first()
        self.assertEqual(status, 0)
        seen = []
        real = self.grid.replay

        def spy(args):
            seen.append(args.pilot)
            return real(args)
        self.grid.replay = spy
        with contextlib.redirect_stdout(io.StringIO()):
            d.replay_timing(self.grid, out, self.repo, None,
                            pilot=self.pilot_dir)
        self.assertEqual(seen, [self.pilot_dir])
        self.assertTrue(self.table.fixed_seconds)

    def test_a_fixed_seconds_replay_without_the_pilot_is_refused(self):
        out, status, _ = self.first()
        with self.assertRaisesRegex(ValueError, "needs its pilot"):
            d.replay_timing(self.grid, out, self.repo, None)

    def test_a_tampered_output_does_not_replay(self):
        out, status, _ = self.first()
        text = (out / "decisions.json").read_text()
        (out / "decisions.json").write_text(text.replace(
            '"pass"', '"fail"', 1))
        with self.assertRaises(ValueError):
            with contextlib.redirect_stdout(io.StringIO()):
                d.replay_timing(self.grid, out, self.repo, None,
                                pilot=self.pilot_dir)


class Gates(unittest.TestCase):
    def test_gate_records_by_status(self):
        for status, expect in (("pass", "pass"), ("attributed", "pass"),
                               ("fail", "fail"),
                               ("inconclusive", "incomplete")):
            r = gates.gate_record("g", status, ["why"], [], None)
            self.assertEqual(d.finish(r)["status"], expect, status)
        r = gates.gate_record("g", "attributed", [], [], None)
        self.assertEqual((d.finish(r)["status"], r["owed"]),
                         ("incomplete", ["attribution"]))

    def test_startup_status_is_derived_and_a_null_must_pass(self):
        header = dict(record_sha256=None)
        got = gates.startup_gate(header, dict(decision="pass"),
                                 dict(decision="pass"))
        self.assertEqual(got["source"], "pass")
        got = gates.startup_gate(header, dict(decision="smoke"),
                                 dict(decision="pass"))
        self.assertEqual(got["source"], "inconclusive")
        got = gates.startup_gate(header, dict(decision="pass"),
                                 dict(decision="fail"))
        self.assertEqual(got["source"], "inconclusive")
        got = gates.startup_gate(header, dict(decision="fail"),
                                 dict(decision="fail"))
        self.assertEqual(got["source"], "fail")

    BASE = a.BASE

    class Revs(FakeLineage):
        def commit(self, label, rev):
            return rev

    def startup_archive(self, root, null, record_sha, cand=CAND):
        import startup_gate as sg
        trees = {"b1": dict(rev=self.BASE), "b2": dict(rev=self.BASE),
                 "s1": dict(rev=self.BASE if null else cand),
                 "s2": dict(rev=self.BASE if null else cand)}
        write(root / "header.json", dict(
            schema=sg.SCHEMA, null=null, pairs=sg.PAIRS,
            record_sha256=record_sha, trees=trees,
            sides=dict(base=["b1", "b2"], candidate=["s1", "s2"]
                       if not null else ["s1", "s2"]),
            harness=dict(head=CAND, tree_outside_performance="t",
                         dirty=False)))
        write(root / "decisions.json", dict(decision="pass"))
        return root

    def test_a_startup_gate_is_sealed_to_the_record_made_in_its_run(self):
        import hashlib
        import startup_gate as sg
        harness = gates.Harness("t", CAND, Path("."), "x")
        patch = mock.patch.object(gates, "harness_constants",
                                  lambda h: (sg.SCHEMA, sg.PAIRS))
        patch.start()
        self.addCleanup(patch.stop)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            record = root / "not-client-visible.md"
            record.write_text("Baseline: develop %s\n%s\n" % (
                self.BASE, CAND))
            sha = hashlib.sha256(record.read_bytes()).hexdigest()
            lin_ = self.Revs()
            lin_.tree = "t"
            lin_.equivalent = lambda label, rev: rev
            lin_.harness = lambda label, found, clean=False: None
            header, _ = gates.read_startup(
                self.startup_archive(root / "g", False, sha), False, lin_,
                harness)
            self.assertEqual(gates.check_record(header, record, lin_),
                             a.seal(record))
            # a gate with no record, a null control with one
            with self.assertRaisesRegex(ValueError, "no record"):
                gates.read_startup(self.startup_archive(
                    root / "g2", False, None), False, lin_, harness)
            with self.assertRaisesRegex(ValueError, "never has"):
                gates.read_startup(self.startup_archive(
                    root / "n", True, sha), True, lin_, harness)
            gates.read_startup(self.startup_archive(
                root / "n2", True, None), True, lin_, harness)
            # a gate or null made by another harness than the attempt's
            other_harness = gates.Harness("t", "d" * 40, Path("."), "x")
            for null, name in ((False, "g3"), (True, "n3")):
                with self.assertRaisesRegex(
                        ValueError, "made by harness commit %s, not the "
                        "attempt's %s" % (CAND, "d" * 40)):
                    gates.read_startup(self.startup_archive(
                        root / name, null, None if null else sha), null,
                        lin_, other_harness)
            # no record given, another file, a record naming other revisions
            with self.assertRaisesRegex(ValueError, "pass it"):
                gates.check_record(header, None, lin_)
            other = root / "other.md"
            other.write_text("changed")
            with self.assertRaisesRegex(ValueError, "differs from its seal"):
                gates.check_record(header, other, lin_)
            record.write_text("Baseline: develop %s\n" % self.BASE)
            header["record_sha256"] = hashlib.sha256(
                record.read_bytes()).hexdigest()
            with self.assertRaisesRegex(ValueError, "does not name the"):
                gates.check_record(header, record, lin_)

    def test_the_loading_shards_must_share_the_api_audit_receipt(self):
        one = dict(semantic_gate=dict(seal=dict(sha256="1" * 64, bytes=2)))
        other = dict(semantic_gate=dict(seal=dict(sha256="2" * 64,
                                                  bytes=2)))
        with mock.patch.object(gates, "check_audit_receipt"):
            same = gates.check_one_audit({"loading-congLib": one,
                                          "loading-simpLib": one})
            self.assertEqual(same, one["semantic_gate"]["seal"])
        with mock.patch.object(gates, "check_audit_receipt"), \
                self.assertRaisesRegex(ValueError, "different api-audit"):
            gates.check_one_audit({"loading-congLib": one,
                                   "loading-simpLib": other})
        with self.assertRaisesRegex(ValueError, "no api-audit receipt"):
            gates.check_one_audit({"loading-congLib": one,
                                   "loading-simpLib": dict(
                                       semantic_gate="not admitted")})

    def test_the_task33_declaration_must_be_filled_and_for_the_gate(self):
        import task33_offline as offline
        path = a.HERE / "task37_declared.json"
        declared = json.loads(path.read_text())
        held = dict(candidate=declared["cand"])
        with mock.patch.object(offline, "shape_problems",
                               return_value=[]):
            gates.check_declared(held, path, FakeLineage())
            with self.assertRaisesRegex(ValueError, "candidate"):
                gates.check_declared(dict(candidate="d" * 40), path,
                                     RefusingLineage())
        with mock.patch.object(offline, "shape_problems",
                               return_value=["pending"]), \
                self.assertRaisesRegex(ValueError, "not valid"):
            gates.check_declared(held, path, FakeLineage())

    def test_loading_inconclusive_owes_stage2_then_attribution(self):
        r = gates.loading_gate("loading-simpLib", dict(stage="first"),
                               "inconclusive")
        self.assertEqual(r["owed"], ["stage2"])
        r = gates.loading_gate("loading-simpLib", dict(stage="second"),
                               "inconclusive")
        self.assertEqual(r["owed"], ["attribution"])


class Receipt(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.report = self.root / "report.json"
        self.report.write_text(json.dumps(dict(
            schema="task37-builds-v1", pins=dict(base=a.BASE, cand=CAND))))

    def test_the_shipped_declaration_names_the_baseline_as_parent(self):
        for base, declared in gates.BUILD_BASES.items():
            self.assertEqual(len(base), 40)
            self.assertEqual(declared["parent"], a.BASE)
            self.assertTrue(declared["paths"])

    def test_only_d7_has_a_receipt_and_it_needs_a_report(self):
        with self.assertRaisesRegex(ValueError, "replayed"):
            gates.make_receipt("startup-gate", CAND, "pass", 0,
                               [self.report])
        with self.assertRaisesRegex(ValueError, "at least one"):
            gates.make_receipt(gates.D7, CAND, "pass", 0)
        with self.assertRaisesRegex(ValueError, "not that of"):
            gates.make_receipt(gates.D7, CAND, "inconclusive", 0,
                               [self.report])

    def test_round_trip_and_a_changed_report(self):
        made = gates.make_receipt(gates.D7, CAND, "pass", 0, [self.report])
        path = self.root / "r.json"
        a.save(path, made)
        got = gates.load_receipt(path, FakeLineage())
        self.assertEqual(got["status"], "pass")
        self.report.write_text(self.report.read_text() + " ")
        with self.assertRaisesRegex(ValueError, "changed or is missing"):
            gates.load_receipt(path, FakeLineage())

    def test_the_command(self):
        out = self.root / "o.json"
        code = d.main(["receipt", "--gate", "d7-build", "--candidate",
                       CAND, "--status", "pass", "--exit", "0", "--out",
                       str(out), "--report", str(self.report)])
        self.assertEqual(code, 0)
        self.assertEqual(a.load(out)["gate"], gates.D7)


class BuildBase(unittest.TestCase):
    """The declared build base of D7: a tiny repository stands for the
    baseline's tree (parent), the base (a child that changes exactly the
    declared path) and the candidate."""

    PATH = "src/mk.ML"
    OTHER = "src/other.sml"

    def git(self, *argv):
        env = dict(os.environ, GIT_CONFIG_GLOBAL="/dev/null",
                   GIT_CONFIG_NOSYSTEM="1")
        return subprocess.run(
            ("git", "-c", "commit.gpgsign=false", "-c",
             "core.hooksPath=/dev/null", "-C", str(self.repo)) + argv,
            check=True, text=True, stdin=subprocess.DEVNULL, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL
        ).stdout.strip()

    def commit(self, files):
        """A commit of `files` (path to text) over the work tree as it
        is, its sha."""
        for path, text in files.items():
            target = self.repo / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "c%d" % self.count)
        self.count += 1
        return self.git("rev-parse", "HEAD")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.count = 0
        self.git("init", "-q")
        self.git("config", "user.email", "t@example.com")
        self.git("config", "user.name", "t")
        self.parent = self.commit({self.PATH: "old\n",
                                   self.OTHER: "x\n"})
        self.base = self.commit({self.PATH: "fixed\n"})
        self.cand = self.commit({self.PATH: "fixed\n",
                                 self.OTHER: "y\n"})
        patch = mock.patch.object(a, "BASE", self.parent)
        patch.start()
        self.addCleanup(patch.stop)
        self.declare()

    def declare(self, base=None, **over):
        entry = dict(parent=self.parent, paths=(self.PATH,), why="a test")
        entry.update(over)
        patch = mock.patch.object(gates, "BUILD_BASES",
                                  {base or self.base: entry})
        patch.start()
        self.addCleanup(patch.stop)

    def report(self, name, base=None, schema="task37-builds-v1",
               repo=None, folder=None, pinrepo=True):
        path = (folder or self.root) / name
        path.parent.mkdir(parents=True, exist_ok=True)
        pins = dict(base=base or self.base, cand=self.cand)
        if pinrepo:
            pins["repo"] = str(repo or self.repo)
        path.write_text(json.dumps(dict(schema=schema, pins=pins)))
        return path

    def check(self, *reports, **kw):
        return gates.check_builds_reports(self.cand, reports, **kw)

    def test_declared_base_is_accepted_and_recorded(self):
        got = self.check(self.report("r.json"),
                         self.report("at.json", schema="task37-builds-v1-"
                                     "attribution"))
        self.assertEqual(got["commit"], self.base)
        self.assertEqual(got["parent"], self.parent)
        self.assertEqual(got["paths"], [self.PATH])
        made = gates.make_receipt(gates.D7, self.cand, "pass", 0,
                                  [self.report("r.json")])
        self.assertEqual(made["baseline"], a.BASE)
        self.assertEqual(made["build_base"], got)
        out = self.root / "d7.json"
        a.save(out, made)
        loaded = gates.load_receipt(out, FakeLineage())
        self.assertEqual(loaded["build_base"], got)
        other = self.root / "d7-prose.json"
        a.save(other, dict(made, build_base=dict(got, why="else")))
        gates.load_receipt(other, FakeLineage())
        for bad in (None, dict(got, commit=self.cand),
                    dict(got, paths=[self.OTHER])):
            out = self.root / ("d7-%s.json" % self.count)
            self.count += 1
            a.save(out, dict(made, build_base=bad))
            with self.assertRaisesRegex(ValueError, "records build base"):
                gates.load_receipt(out, FakeLineage())

    def test_the_baseline_itself_records_no_build_base(self):
        report = self.root / "b.json"
        report.write_text(json.dumps(dict(
            schema="task37-builds-v1", pins=dict(base=a.BASE,
                                                 cand=self.cand))))
        self.assertIsNone(self.check(report))
        made = gates.make_receipt(gates.D7, self.cand, "pass", 0, [report])
        self.assertNotIn("build_base", made)

    def test_the_summary_line_shows_the_build_base(self):
        build = self.check(self.report("r.json"))
        record = dict(scope="s", reported=dict(d7_build=dict(
            status="pass", exit=0, note="n", gate=False,
            build_base=build)))
        with mock.patch.object(d, "lines", lambda r: []), \
                mock.patch.object(d, "verdict", lambda r: "v"):
            shown = d.summary(record)
        self.assertIn("timed base " + self.base, shown)
        self.assertIn(self.PATH, shown)

    def test_a_second_changed_path_is_refused(self):
        self.git("checkout", "-q", self.parent)
        base = self.commit({self.PATH: "fixed\n", self.OTHER: "z\n"})
        self.declare(base=base)
        with self.assertRaisesRegex(ValueError, "not exactly"):
            self.check(self.report("r.json", base=base))

    def test_a_wrong_parent_is_refused(self):
        self.declare(parent=self.cand)
        with mock.patch.object(a, "BASE", self.cand):
            with self.assertRaisesRegex(ValueError, "has parents"):
                self.check(self.report("r.json"))

    def test_a_declared_parent_other_than_the_baseline_is_refused(self):
        self.declare(parent=self.cand)
        with self.assertRaisesRegex(ValueError, "not the baseline"):
            self.check(self.report("r.json"))

    def test_an_extra_parent_is_refused(self):
        self.git("checkout", "-q", "-b", "side", self.parent)
        self.commit({"side.txt": "s\n"})
        self.git("checkout", "-q", "-")
        self.git("merge", "-q", "--no-ff", "-m", "m", "side")
        merged = self.git("rev-parse", "HEAD")
        self.declare(base=merged, parent=self.cand, paths=("side.txt",))
        with mock.patch.object(a, "BASE", self.cand):
            with self.assertRaisesRegex(ValueError, "has parents"):
                self.check(self.report("r.json", base=merged))

    def test_content_unlike_the_candidates_is_refused(self):
        self.git("checkout", "-q", self.parent)
        base = self.commit({self.PATH: "other fix\n"})
        self.declare(base=base)
        with self.assertRaisesRegex(ValueError, "not the candidate's"):
            self.check(self.report("r.json", base=base))

    def test_a_path_the_candidate_lacks_is_refused(self):
        self.declare(paths=(self.PATH,))
        self.git("checkout", "-q", self.parent)
        self.git("rm", "-q", self.PATH)
        self.git("commit", "-q", "-m", "rm")
        cand = self.git("rev-parse", "HEAD")
        report = self.report("r.json")
        doc = json.loads(report.read_text())
        doc["pins"]["cand"] = cand
        report.write_text(json.dumps(doc))
        with self.assertRaisesRegex(ValueError, "not the candidate's"):
            gates.check_builds_reports(cand, [report])

    def test_a_rename_is_two_changed_paths(self):
        self.git("checkout", "-q", self.parent)
        self.git("mv", self.PATH, "src/moved.ML")
        self.git("commit", "-q", "-m", "mv")
        base = self.git("rev-parse", "HEAD")
        self.declare(base=base, paths=("src/moved.ML",))
        with self.assertRaisesRegex(ValueError, "not exactly"):
            self.check(self.report("r.json", base=base))

    def test_an_undeclared_base_is_refused(self):
        with self.assertRaisesRegex(ValueError, "measured baseline"):
            self.check(self.report("r.json", base=self.cand))

    def test_two_reports_of_different_bases_are_refused(self):
        plain = self.root / "b.json"
        plain.write_text(json.dumps(dict(
            schema="task37-builds-v1-attribution",
            pins=dict(base=a.BASE, cand=self.cand))))
        with self.assertRaisesRegex(ValueError, "different baselines"):
            self.check(self.report("r.json"), plain)

    def test_same_named_reports_of_different_bases_are_refused(self):
        plain = self.root / "one" / "receipt.json"
        plain.parent.mkdir()
        plain.write_text(json.dumps(dict(
            schema="task37-builds-v1",
            pins=dict(base=a.BASE, cand=self.cand))))
        mine = self.report("receipt.json", folder=self.root / "two")
        for order in ((plain, mine), (mine, plain)):
            with self.assertRaisesRegex(ValueError,
                                        "different baselines.*one/rec"):
                self.check(*order)

    def test_an_unreadable_repository_is_refused(self):
        with self.assertRaisesRegex(ValueError, "not readable"):
            self.check(self.report("r.json", repo=self.root / "none"))
        with self.assertRaisesRegex(ValueError, "not a commit.*PROTOCOL"):
            self.check(self.report("r.json", repo=self.root))

    def test_a_report_without_a_repository_needs_the_fallback(self):
        report = self.report("r.json", pinrepo=False)
        with self.assertRaisesRegex(ValueError, "not readable"):
            self.check(report)
        got = self.check(report, fallback=self.repo)
        self.assertEqual(got["commit"], self.base)

    def test_the_lineage_repository_is_a_fallback(self):
        made = gates.make_receipt(gates.D7, self.cand, "pass", 0,
                                  [self.report("r.json")])
        out = self.root / "d7.json"
        a.save(out, made)
        gone = self.report("g.json", repo=self.root / "none")
        a.save(self.root / "d7g.json", dict(
            made, reports=[dict(path=str(gone), seal=a.seal(gone))]))
        lineage = FakeLineage()
        with self.assertRaisesRegex(ValueError, "not readable"):
            gates.load_receipt(self.root / "d7g.json", lineage)
        lineage.repo = self.repo
        got = gates.load_receipt(self.root / "d7g.json", lineage)
        self.assertEqual(got["build_base"]["commit"], self.base)


class Derive(unittest.TestCase):
    """`derive` and the record/check round trip with the readers stood in
    for: the order (replays last) and the record's assembly."""

    tables = Dispose.tables

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.events = []
        quiet = contextlib.redirect_stdout(io.StringIO())
        quiet.__enter__()
        self.addCleanup(quiet.__exit__, None, None, None)
        ids, al, timing, units, t33, rec = self.tables()
        self.timing = timing
        kinds = dict(client=c.CLIENT_CELLS, matrix=c.MATRIX_CELLS,
                     downstream=c.DOWNSTREAM_CELLS)

        def late(label):
            return lambda: self.events.append("replay " + label)

        def read_identity(root, label, names, lineage, kind, ledger, repo,
                          lates):
            self.events.append("read " + label)
            lates.append((label, late(label)))
            return dict(ids[kind], seals={}, candidate=CAND)

        def read_allocation(root, task, names, infeasible, lineage, ledger,
                            lates):
            self.events.append("read " + task)
            lates.append((task, late(task)))
            kind = task.split("-")[1]
            return dict(al[kind], seals={})

        def read_timing(kind, sample, options, lineage, repo, document,
                        lates):
            self.events.append("read timing " + kind)
            lates.append((kind, late("timing " + kind)))
            return {t: dict(v, seals={}, pins={}) for t, v in
                    timing.items() if grid.KIND[t[len("task37-"):]] == kind}
        def read_gates(args, lineage, inputs, lates, extra):
            extra.update(startup_attempts=[], startup_declared={})
            return receipts, None
        self.fake = FakeLineage()
        self.fake.repo, self.fake.tree = Path("."), "tree"
        self.fake.candidate = CAND
        receipts = {g: gates.gate_record(g, "pass", [], [], None)
                    for g in gates.GATES}
        patches = [
            mock.patch.object(d.lineage_of, "Lineage",
                              lambda repo, cand: self.fake),
            mock.patch.object(d, "read_identity", read_identity),
            mock.patch.object(d, "read_allocation", read_allocation),
            mock.patch.object(d, "read_timing", read_timing),
            mock.patch.object(d, "read_gates", read_gates),
            mock.patch.object(gates, "read_task32", lambda p, l: (
                units, {}, CAND)),
            mock.patch.object(gates, "read_task33", lambda p, l: (
                {}, [], {}, {}, CAND)),
            mock.patch.object(gates, "replay_task32",
                              lambda *args: self.events.append(
                                  "replay task32")),
            mock.patch.object(gates, "replay_task33",
                              lambda *args: self.events.append(
                                  "replay task33")),
            mock.patch.object(d, "load_loads", lambda paths: ({}, {}))]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

    def args(self, *extra):
        return d.parser().parse_args([
            "--candidate", CAND, "--identity-client", "i",
            "--identity-matrix", "i", "--identity-downstream", "i",
            "--alloc-client", "a", "--alloc-matrix", "a",
            "--alloc-downstream", "a", "--task32", "t",
            "--task32-replay", "x", "--task33", "t",
            "--task33-replay", "x", *extra])

    def test_replays_come_after_every_read(self):
        record = d.derive(self.args("--record", "o"))
        first_replay = min(i for i, e in enumerate(self.events)
                           if e.startswith("replay"))
        self.assertTrue(all(e.startswith("read")
                            for e in self.events[:first_replay]))
        self.assertTrue(all(e.startswith("replay")
                            for e in self.events[first_replay:]))
        self.assertEqual(len([e for e in self.events
                              if e.startswith("replay")]), 10)
        self.assertEqual(record["status"], "pass")
        self.assertEqual(record["candidates"], {})
        self.assertEqual(record["tree_outside_performance"], "tree")
        self.assertEqual(set(record["attempts"]),
                         {"identity", "allocation", "timing_ledger"})

    def test_record_then_check(self):
        out = self.root / "out"
        self.assertEqual(d.disposition(self.args("--record", str(out))), 0)
        self.assertTrue((out / "SUMMARY.txt").is_file())
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(d.disposition(
                self.args("--check", str(out))), 0)
        held = json.loads((out / "disposition.json").read_text())
        held["status"] = "fail"
        (out / "disposition.json").write_text(json.dumps(held))
        with self.assertRaisesRegex(ValueError, "changed TASK37"):
            d.disposition(self.args("--check", str(out)))
        with self.assertRaisesRegex(ValueError, "refusing to replace"):
            d.disposition(self.args("--record", str(out)))


    def test_a_later_commit_keeps_a_recorded_disposition_checkable(self):
        out = self.root / "out"
        self.assertEqual(d.disposition(self.args("--record", str(out))), 0)
        path = out / "disposition.json"
        held = json.loads(path.read_text())
        self.assertEqual(held["head"], "h" * 40)
        # recorded at an earlier head of the same tree outside the
        # performance area (a later performance-only commit followed)
        held["head"] = FakeLineage.EARLIER
        path.write_text(json.dumps(held))
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(d.disposition(
                self.args("--check", str(out))), 0)
        # a head the checkout does not descend from with that tree (a
        # later commit outside the performance area, or another branch)
        held["head"] = "f" * 40
        path.write_text(json.dumps(held))
        with self.assertRaisesRegex(ValueError, "not an earlier head"):
            d.disposition(self.args("--check", str(out)))
        # the head is no way to alter anything else
        held["head"] = FakeLineage.EARLIER
        held["status"] = "fail"
        path.write_text(json.dumps(held))
        with self.assertRaisesRegex(ValueError, "changed TASK37"):
            d.disposition(self.args("--check", str(out)))

    # Decision 45: an attempt void by an environment refusal needs an event
    # file, an event needs such an attempt, the record holds its seal and
    # `--check` derives it again.
    TABLE = "task37-client-1"
    REFUSAL = "runtime/tool changed during pair"

    def void(self, environment=True):
        x = dict(attempt="V", status="inconclusive", output="o",
                 judged=False, void=True)
        if environment:
            x["environment"] = [self.REFUSAL]
        self.timing[self.TABLE]["attempts"] = [x]

    def event(self):
        path = self.root / "dpkg.log"
        path.write_text("upgrade libc6\n")
        return path

    def test_an_environment_void_attempt_needs_an_event(self):
        self.void()
        with self.assertRaisesRegex(
                ValueError, "no --environment-event.*%s V" % self.TABLE):
            d.derive(self.args("--record", "o"))
        self.events.clear()
        record = d.derive(self.args(
            "--record", "o", "--environment-event", str(self.event())))
        (found,) = record["environment_events"]
        self.assertEqual(found["seal"], a.seal(self.event()))
        self.assertEqual(found["path"], str(self.event()))
        self.assertEqual(found["attempts"], [dict(
            table=self.TABLE, attempt="V", refusals=[self.REFUSAL])])
        self.assertIn("void (environment: %s)" % self.REFUSAL,
                      "\n".join(d.lines(record)))

    def test_an_event_with_no_attempt_it_voids_is_refused(self):
        self.void(environment=False)
        with self.assertRaisesRegex(
                ValueError, "an environment event with no attempt it "
                "voids"):
            d.derive(self.args("--record", "o", "--environment-event",
                               str(self.event())))
        with self.assertRaisesRegex(ValueError, "event is missing"):
            d.derive(self.args("--record", "o", "--environment-event",
                               str(self.root / "none")))

    def test_no_event_and_no_void_attempt_records_none(self):
        self.void(environment=False)
        self.assertEqual(d.derive(self.args(
            "--record", "o"))["environment_events"], [])
        self.assertIn("void (no measurement admitted)",
                      "\n".join(d.lines(d.derive(self.args(
                          "--record", "o")))))

    def test_the_event_is_replayed_by_check(self):
        self.void()
        event = self.event()
        out = self.root / "out"
        more = ("--environment-event", str(event))
        self.assertEqual(d.disposition(
            self.args("--record", str(out), *more)), 0)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(d.disposition(
                self.args("--check", str(out), *more)), 0)
        event.write_text("another\n")
        with self.assertRaisesRegex(ValueError, "changed TASK37"):
            d.disposition(self.args("--check", str(out), *more))
        event.write_text("upgrade libc6\n")
        with self.assertRaisesRegex(ValueError, "no --environment-event"):
            d.disposition(self.args("--check", str(out)))

    def test_the_timing_ledger_passes_the_refusals(self):
        seen = []

        def spy(args, engine, judged, refusals=frozenset()):
            seen.append(refusals)
            return []
        with mock.patch.object(d, "attempts_of", spy):
            d.ledger_attempts("engine", {}, "repo", "ledger")
        self.assertEqual(seen, [d.ENVIRONMENT_REFUSALS])


class Command(unittest.TestCase):
    def test_keyed(self):
        self.assertEqual(d.keyed(["a=/x"], "o"), dict(a=Path("/x")))
        with self.assertRaisesRegex(ValueError, "twice"):
            d.keyed(["a=/x", "a=/y"], "o")
        with self.assertRaisesRegex(ValueError, "needs KEY=PATH"):
            d.keyed(["b=/x"], "o", ("a",))
        with self.assertRaisesRegex(ValueError, "needs KEY=PATH"):
            d.keyed(["nonsense"], "o")

    def test_the_parser_has_the_pilot_and_ledger_options(self):
        args = d.parser().parse_args(
            ["--candidate", "c" * 10, "--pilot", "client-1=p",
             "--alloc-ledger", "task37-client=l", "--record", "o",
             "--identity-ledger", "client=i"])
        self.assertEqual(args.pilot, ["client-1=p"])
        self.assertEqual(args.alloc_ledger, ["task37-client=l"])
        self.assertEqual(args.identity_ledger, ["client=i"])

    def test_the_followup_accessor(self):
        self.assertEqual(d.followup_engines(), dict(followup.GRIDS))
        self.assertFalse(set(grid.GRIDS) & set(followup.GRIDS))
        engines = {followup.name_of("client-1"): "E"}
        with mock.patch.object(d, "followup_engines", lambda: engines):
            self.assertEqual(d.followup_of("client-1"), "E")
            self.assertIsNone(d.followup_of("client-2"))

    def test_main_refuses_with_three(self):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            code = d.main(["--candidate", "x", "--record",
                           "/nonexistent/out"])
        self.assertEqual(code, tg.REFUSED)
        self.assertIn("REFUSED", err.getvalue())


def local_imports(path):
    """Every module name imported anywhere in a file, function-local
    imports included (by `ast`)."""
    found = set()
    for node in ast.walk(ast.parse(Path(path).read_text())):
        if isinstance(node, ast.Import):
            found |= {n.name.split(".")[0] for n in node.names}
        elif isinstance(node, ast.ImportFrom) and node.module:
            found.add(node.module.split(".")[0])
    return found


class Code(unittest.TestCase):
    def test_code_files_exist(self):
        for name in d.CODE:
            self.assertTrue((a.HERE / name).is_file(), name)
        self.assertEqual(len(set(d.CODE)), len(d.CODE))

    def test_every_imported_module_is_sealed_function_local_too(self):
        todo = ["task37_dispose", "task37_gates", "task37_lineage",
                "task37_cases", "task37_identity", "task37_grid",
                "task37_followup", "task37_sources"]
        seen = set()
        while todo:
            name = todo.pop()
            if name in seen or not (a.HERE / (name + ".py")).is_file():
                continue
            seen.add(name)
            todo += sorted(local_imports(a.HERE / (name + ".py")))
        missing = sorted(n for n in seen if n + ".py" not in d.CODE)
        self.assertEqual(missing, [])

    def test_the_ast_finds_a_function_local_import(self):
        with tempfile.TemporaryDirectory() as tmp:
            f = Path(tmp) / "m.py"
            f.write_text("def f():\n    import hidden_module\n")
            self.assertIn("hidden_module", local_imports(f))

    def test_note_second_is_imported_not_copied(self):
        self.assertIs(gates.NOTE_SECOND, d32.NOTE_SECOND)
        text = (a.HERE / "task37_gates.py").read_text()
        self.assertNotIn('NOTE_SECOND = "', text)

    def test_no_stale_claims(self):
        text = (a.HERE / "task37_dispose.py").read_text()
        self.assertNotIn("nothing is looked up in the repository", text)
        self.assertNotIn("same_rev", text)

    def test_check_code_refusals(self):
        with self.assertRaisesRegex(ValueError, "recorded code"):
            d.check_code({})
        now = d.seals()
        d.check_code(now)
        bad = dict(now, **{d.CODE[0]: dict(sha256="0")})
        with self.assertRaisesRegex(ValueError, "changed"):
            d.check_code(bad)
        with mock.patch.object(d, "HISTORY",
                               {d.CODE[0]: [bad[d.CODE[0]]]}):
            d.check_code(bad)


if __name__ == "__main__":
    unittest.main()
