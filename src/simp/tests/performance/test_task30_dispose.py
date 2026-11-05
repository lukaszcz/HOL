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
import contextlib
import copy
import io
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import acceptance as a
import allocation_analysis as an
import allocation_matrix as am
import allocation_schema as schema
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
                self.assertIn("1.01M words", text)
                self.assertIn("TASK_31", text)
                self.assertNotIn("\t", text)

    def test_the_two_residuals_are_named(self):
        notes = {c: e["note"] for c, e in
                 td.DISPOSITION["attributed"].items()}
        self.assertIn("Residual", notes["exclude_literal_exact-10000"])
        self.assertIn("1.041", notes["exclude_literal_exact-10000"])
        self.assertIn("Residual", notes["exclude_dproc-10000"])
        self.assertIn("1.075", notes["exclude_dproc-10000"])
        self.assertEqual(
            [c for c, n in notes.items() if "Residual" in n],
            ["exclude_literal_exact-10000", "exclude_dproc-10000"])

    def test_the_notes_of_the_marker_and_tactic_cells_say_where_the_work_is(
            self):
        for case in ("exclude_marker_reuse", "exclude_tactic_reuse"):
            note = td.DISPOSITION["attributed"][case + "-10000"]["note"]
            self.assertIn("in every", note)
            self.assertIn("only the Excl construction is saved", note)
        for case in td.CASE_CLASS:
            if td.CASE_CLASS[case] == td.OPERATION:
                note = td.DISPOSITION["attributed"][case + "-10000"]["note"]
                self.assertIn("only by the operation words", note)

    def test_the_seal_histories_start_empty_and_name_only_the_code(self):
        self.assertEqual(td.HISTORY, {})
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


class Evidence(unittest.TestCase):
    """`Evidence.holds`: what fails is named."""

    def make(self, new=None, old=None, final=None):
        final = dict(source_identity=CLEAN) if final is None else final
        return td.Evidence(SPEC, final,
                           old or alloc_decisions(LIMITED, setup=7),
                           new or alloc_decisions(LIMITED, setup=9))

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
                         "work: work status is differs, not equal")
        new["work"]["cells"]["exclude_missing-10"] = "inconclusive"
        self.assertIn("inconclusive, not equal",
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
                    "work: work row %s is differs" % key)

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


class Toy(ttf.Rig):
    """The replaced toy grid with two control-limited cells beside its two
    open ones, its follow-up (settled by default) and two hand-written
    allocation grids."""

    def mid_control(self, case, size, pairs, seed):
        if (case, size) in ((c, s) for c, s in LIMITED):
            return (0.90, 1.12)
        return super().mid_control(case, size, pairs, seed)

    def setUp(self):
        super().setUp()
        self.declare()
        self.committed_counts = True
        self.settled()
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
        return 0

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
            '"attributed": 2, "blocking": 0}'), text)
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
            ("deletion", "n1", "attributed", None, "abc", 24))
        self.assertEqual(found["work"], dict(
            first={}, second={}, use={"trace.4.REDUCE": 10}))
        self.assertEqual(set(found["metrics"]), {"cpu", "wall", "gc"})
        cpu = found["metrics"]["cpu"]
        self.assertEqual((cpu["decision"], cpu["reason"]),
                         ("inconclusive", tg.CONTROL))
        self.assertEqual(cpu["control_interval"], [0.90, 1.12])
        self.assertEqual(cpu["interval"], list(ttg.GOOD))
        self.assertIsNotNone(cpu["median"])
        self.assertEqual(found["metrics"]["gc"]["decision"], "reported")
        other = record["attributed"]["exclude_empty-10000"]
        self.assertEqual(other["work"], dict(
            first={"trace.4.REDUCE": 1, "kernel.total": 4},
            second={"trace.4.REDUCE": 1, "kernel.total": 4}, use={}))

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
                    ValueError, "changed TASK30 disposition: "
                    "task30_dispose.py changed since it was recorded; "
                    "append the old seal to HISTORY"):
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
            '"attributed": 2, "blocking": 0}'), text)

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
                         r'"fail": 0, "attributed": 2, "blocking": 2\}')

    def test_evidence_that_fails_blocks_the_cell_and_is_printed(self):
        z = copy.deepcopy(self.work["z"])
        z["work"]["cells"]["exclude_missing-10"] = "differs"
        self.save_decisions(self.allocz, z)
        code, text = self.dispose(record=True)
        self.assertEqual(code, 2, text)
        self.assertIn("BLOCKING exclude_missing-10 (deletion): work: work "
                      "status is differs, not equal", text)
        self.assertIn("ATTRIBUTED exclude_empty-10000 (operation)", text)
        record = self.load(self.out / "disposition.json")
        self.assertEqual(record["blocking"], {
            "exclude_missing-10": "control-limited, evidence fails: work: "
            "work status is differs, not equal"})
        self.assertEqual(record["status"], "blocked")

    def test_a_stale_list_is_refused_naming_the_cells(self):
        spec = dict(SPEC, attributed=dict(
            SPEC["attributed"], **{"exclude_empty-0": dict(
                evidence_class=td.DELETION, note="n")}))
        out = io.StringIO()
        with contextlib.redirect_stdout(out), self.assertRaisesRegex(
                ValueError, r"stale attribution: listed but not "
                r"control-limited: exclude_empty-0 \(pass\)"):
            td.disposition(td.parser().parse_args(self.dargv()),
                           old=self.grid, new=self.fgrid, spec=spec)
        spec["attributed"].pop("exclude_missing-10")
        spec["attributed"].pop("exclude_empty-0")
        with contextlib.redirect_stdout(out), self.assertRaisesRegex(
                ValueError, "control-limited but not listed: "
                "exclude_missing-10"):
            td.disposition(td.parser().parse_args(self.dargv()),
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
            self.dispose()

    def test_a_follow_up_with_another_source_record_is_refused(self):
        # (The follow-up's own check; its comparison with the replaced
        # grid's record is tested in test_timing_followup.py.)
        path = self.out / "inventory.json"
        value = json.loads(path.read_text())
        value["sources"]["src/one.sml"]["candidate"] = "e" * 40
        path.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "changed source identity"):
            self.dispose()


CELLS = ttf.CELLS


if __name__ == "__main__":
    unittest.main()
