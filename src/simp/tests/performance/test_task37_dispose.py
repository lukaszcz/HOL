#!/usr/bin/env python3
"""The TASK37 disposition (task37_dispose.py, with task37_lineage.py and
task37_gates.py): every rule branch on the loaded tables, the lineage on a
real git repository, the timing replay through a real `Grid.replay` (the
rig of test_timing_grid), the readers on files in the producers' formats,
the pilot and follow-up joins, and the sealed code. The allocation case
shape is compared with the real `allocation_analysis.case_decisions`."""
import ast
import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import types
import unittest
from unittest import mock

import acceptance as a
import allocation_analysis as an
import task31_dispose as d31
import task32_downstream as d32
import task37_cases as c
import task37_dispose as d
import task37_gates as gates
import task37_grid as grid
import task37_lineage as lin
import test_timing_grid as ttg
import timing_grid as tg

tearDownModule = ttg.tearDownModule

RECORD = [dict(path="src/simp/src/Cond_rewr.sig", reason="adds a spec")]
D4 = c.D4
HEAVY = c.INFEASIBLE[0]
KEYS = grid.SHARD_KEYS
CAND = "c" * 40
ORIGINAL_REPLAY = d.replay_timing


def trow(cls="pass", first=None, stage2=False, followup=False):
    return dict(cls=cls, first=first or cls, stage2=stage2,
                followup=followup, earlier=[])


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
        self.assertIn("stage 2 skipped", r["policy_note"])
        # a fresh pass or fail decides as for any cell, with no policy
        r = self.judge(name=name, timed=trow())
        self.assertEqual((r["status"], r["policy"]), ("pass", None))
        self.assertEqual(self.judge(name=name, timed=trow("fail"))[
            "status"], "fail")
        # the decisive first stage was not control-limited
        r = self.judge(name=name, timed=trow("control_limited",
                                             first="inconclusive"))
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
                scaling=scaling, differing=list(differing),
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
        self.assertEqual(seen[0], set(c.D4))
        self.assertEqual(len(seen[0]), 31)

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

    def test_retained_slope_is_a_record(self):
        r = d.dispose(*self.tables(scaling="inconclusive"))
        self.assertEqual(r["status"], "incomplete")
        self.assertTrue(any(o["owed"] == "retained-slope"
                            for o in r["owed"]))
        r = d.dispose(*self.tables(scaling="fail"))
        self.assertEqual(r["status"], "fail")

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

    def harness(self, label, found, clean=False):
        a.require(isinstance(found, dict), "%s: no harness" % label)
        return found["head"]


def write(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(value))


class Allocation(unittest.TestCase):
    TASK = "task37-downstream"

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.ledger = self.root / "ledger"
        self.ledger.touch()
        patch = mock.patch.object(d, "required_pairs", lambda task: 3)
        patch.start()
        self.addCleanup(patch.stop)

    def make(self, status="pass", cases=None, **over):
        harness = dict(head=CAND, dirty=False,
                       tree_outside_performance="t")
        write(self.root / "inventory.json", dict(
            candidate=CAND, baseline=a.BASE, task=self.TASK, pairs=3,
            harness=harness))
        rows = [dict(case=n.rsplit("-", 1)[0],
                     size=int(n.rsplit("-", 1)[1]), pairs=3,
                     decision="pass", work="equal")
                for n in c.DOWNSTREAM_CELLS]
        write(self.root / "decisions.json", dict(dict(
            candidate=CAND, baseline=a.BASE, complete=True,
            infeasible=[], status=status, nondeterminism=[],
            unresolved=[], work_status="pass", rows=rows,
            cases=cases if cases is not None else {"k": case_record()}),
            **over))

    def read(self):
        late = []
        got = d.read_allocation(self.root, self.TASK, c.DOWNSTREAM_CELLS,
                                (), FakeLineage(), self.ledger, late)
        return got, late

    def test_one_record_per_case_and_the_status_recorded(self):
        self.make(cases={"k": case_record(), "m": case_record("fail")},
                  status="fail")
        got, late = self.read()
        self.assertEqual(set(got["cases"]), {self.TASK + ":k",
                                             self.TASK + ":m"})
        self.assertEqual(got["state"]["status"], "fail")
        self.assertEqual(got["state"]["nondeterminism"], 0)
        self.assertEqual(len(late), 1)

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
        self.make()
        with mock.patch.object(d, "required_pairs", lambda task: 5):
            with self.assertRaisesRegex(ValueError, "not the task's 5"):
                self.read()

    def test_the_replay_and_the_ledger_run_late(self):
        self.make()
        calls = []
        with mock.patch.object(d, "replay_allocation",
                               lambda root: calls.append("replay")), \
                mock.patch.object(d, "allocation_attempts",
                                  lambda task, ledger: calls.append(
                                      "ledger") or []):
            got, late = self.read()
            self.assertEqual(calls, [])
            late[0][1]()
        self.assertEqual(calls, ["replay", "ledger"])

    def test_a_ledger_is_required(self):
        self.make()
        with self.assertRaisesRegex(ValueError, "no allocation attempts"):
            d.read_allocation(self.root, self.TASK, c.DOWNSTREAM_CELLS, (),
                              FakeLineage(), None, [])

    def test_the_adapter_names_the_part_c_function(self):
        import allocation_matrix as am
        seen = []
        with mock.patch.object(am, "attempts_of", create=True,
                               new=lambda t, l: seen.append((t, l)) or []):
            d.allocation_attempts("T", "L")
        self.assertEqual(seen, [("T", "L")])


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
                scaling=None, differing=[], seals={}, plan={},
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
            self.options(), {self.table + "-followup":
                             fake_follow(self.table)})
        self.read_late[1][0][1]()
        judged = [x for x in self.calls if x[0] == "attempts"]
        self.assertEqual([x[1] for x in judged],
                         [self.table, self.table + "-followup"])
        self.assertEqual(judged[1][2], {})

    def test_a_follow_up_needs_a_declaration_and_its_pilot(self):
        options = self.options(followup={self.key: self.root / "f"})
        with self.assertRaisesRegex(ValueError, "no follow-up is declared"):
            self.read(options)
        with self.assertRaisesRegex(ValueError, "needs --followup-pilot"):
            self.read(options, {self.table + "-followup":
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
            first_inventory={}, scaling=None, differing=[], seals={},
            plan={}, final={first: "pass"}, first={first: "pass"})
        options = self.options(followup={self.key: self.root / "f"})
        options["followup-pilot"] = {self.key: self.root / "fp"}
        with self.assertRaisesRegex(ValueError, "does not replace"):
            self.read(options, {self.table + "-followup":
                                fake_follow(self.table)})

    def test_a_follow_up_that_replaces_the_output_gets_both_pilots(self):
        first = self.names[0]
        self.stages["f"] = dict(
            root=self.root / "f", first_root=self.root / "f",
            inventory=dict(candidate=CAND, replaces=dict(grid="../main")),
            first_inventory={}, scaling=None, differing=[], seals={},
            plan={}, final={first: "inconclusive"},
            first={first: "inconclusive"})
        options = self.options(followup={self.key: self.root / "f"})
        options["followup-pilot"] = {self.key: self.root / "fp"}
        # the shard's output is resolved, and so is what the follow-up
        # names
        (self.root / "f").mkdir()
        (self.root / "main").mkdir()
        held, late = self.read(options, {self.table + "-followup":
                                         fake_follow(self.table)})
        late[0][1]()
        replays = [x for x in self.calls if x[0] == "replay"]
        self.assertEqual(len(replays), 2)
        self.assertEqual(replays[1][2:], (
            (self.root / "fp").resolve(), (self.root / "pilot").resolve()))
        self.assertEqual(held["cells"][first]["cls"], "inconclusive")
        self.assertTrue(held["cells"][first]["followup"])
        self.assertEqual(held["cells"][first]["earlier"], ["pass"])


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
        self.report = self.root / "report.txt"
        self.report.write_text("report")

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
        self.report.write_text("changed")
        with self.assertRaisesRegex(ValueError, "changed or is missing"):
            gates.load_receipt(path, FakeLineage())

    def test_the_command(self):
        out = self.root / "o.json"
        code = d.main(["receipt", "--gate", "d7-build", "--candidate",
                       CAND, "--status", "pass", "--exit", "0", "--out",
                       str(out), "--report", str(self.report)])
        self.assertEqual(code, 0)
        self.assertEqual(a.load(out)["gate"], gates.D7)


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
            mock.patch.object(d, "read_gates", lambda *args: (
                receipts, None)),
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
        self.assertEqual(d.followup_engines(), {
            n: e for n, e in grid.GRIDS.items()
            if n.endswith("-followup")})
        engines = {grid.name_of("client-1") + "-followup": "E"}
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
                "task37_cases", "task37_identity", "task37_grid"]
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
