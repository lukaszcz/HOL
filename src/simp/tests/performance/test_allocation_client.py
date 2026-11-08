#!/usr/bin/env python3
"""TASK31 in the allocation matrix: the client fixture family, the cells of
`task31`, its predeclared counts and the rows of its decisions.

Synthetic receipts and files only, as test_allocation_task.py: no runtime,
toolchain or HOL process.
"""
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest import mock

import acceptance as a
import allocation_analysis as an
import allocation_matrix as m
import allocation_schema as sc
import allocation_testbed as tb
import matrix_schema as ms
import task31_cases as cases
import task31_iterations as it

TASK31 = m.TASKS["task31"]
HERE = m.HERE
# The driver of MatrixAllocation.sml, which ClientAllocation.sml repeats.
DRIVER = "(* Build every foreign closure"


def declarations(text):
    """Top-level declarations by their first line: up to the next line that
    starts another one at column 0 (a comment line starts none)."""
    found, current = {}, None
    for line in text.split("\n"):
        if re.match(r"(fun|val|type|exception|\(\*) ", line):
            current = found.setdefault(line, [])
        if current is not None:
            current.append(line)
    return {k: [l for l in v if l.strip()] for k, v in found.items()}


def client_lines(text):
    return [l for l in text.split("\n") if not l.rstrip().endswith(
        "(*alloc*)")]


class Scope(unittest.TestCase):
    def test_the_cases_are_the_client_traversal_and_tactic_cases(self):
        clients = [c for c, v in ms.EXPECTED_CASES.items()
                   if v["fixture"] == "ClientPerformance.sml" and
                   c.startswith(("traversal_", "tactic_"))]
        self.assertEqual(sorted(cases.CASES), sorted(clients))
        self.assertEqual(len(cases.CASES), 11 + 42)
        self.assertEqual(TASK31.cases, cases.CASES)
        self.assertEqual(len(set(cases.CASES)), len(cases.CASES))
        self.assertFalse(any(c.startswith("downstream_")
                             for c in cases.CASES))

    def test_every_size_is_up_to_1000_but_the_light_families(self):
        found = m.keys(TASK31)
        self.assertEqual(len(found), 245)
        light = tuple("tactic_%s_" % f for f in cases.LIGHT_FAMILIES)
        big = [k for k in found if k[1] > 1000]
        self.assertEqual(sorted(big), sorted(
            (c, 10000) for c in cases.CASES if c.startswith(light)))
        self.assertEqual(len(big), 9)
        for case in cases.CASES:
            sizes = TASK31.sizes(case)
            if case.startswith("traversal_"):
                self.assertIn(sizes, ((0,), (0, 1, 10, 100)), case)
            else:
                self.assertEqual(sizes[:5], (0, 1, 10, 100, 1000), case)

    def test_the_infeasible_cells_are_the_33_heavy_ones_and_not_run(self):
        self.assertEqual(len(cases.INFEASIBLE_CELLS), 33)
        self.assertFalse(set(cases.INFEASIBLE_CELLS) & set(m.keys(TASK31)))
        every = {(c, n) for c in cases.CASES
                 for n in TASK31.every_size(c)}
        self.assertEqual(every, set(m.keys(TASK31)) |
                         set(cases.INFEASIBLE_CELLS))
        self.assertEqual({n for _, n in cases.INFEASIBLE_CELLS}, {10000})
        light = tuple("tactic_%s_" % f for f in cases.LIGHT_FAMILIES)
        self.assertFalse([c for c, _ in cases.INFEASIBLE_CELLS
                          if c.startswith(light)])

    def test_the_infeasible_cells_must_be_cells_of_the_task(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "no cell"):
            m.Task("x", "X", cases.CASES, "c.json",
                   [("tactic_full_reuse", 7)])
        with self.assertRaisesRegex(sc.InvalidAllocation, "no cell"):
            m.Task("x", "X", cases.CASES, "c.json",
                   [("traversal_deep", 10000)])

    def test_the_task_is_named_and_asks_for_rows(self):
        self.assertIs(m.task_named("task31"), TASK31)
        self.assertIs(m.task_of(dict(task="task31")), TASK31)
        self.assertEqual(TASK31.label, "TASK31")
        self.assertTrue(TASK31.rows)
        self.assertFalse(m.TASKS["task29b"].rows or m.TASKS["task30"].rows)

    def test_the_other_tasks_keep_every_size(self):
        for name in ("task29b", "task30"):
            task = m.TASKS[name]
            self.assertEqual(task.infeasible, frozenset())
            self.assertTrue(all(task.sizes(c) == m.SIZES
                                for c in task.cases))


class Families(unittest.TestCase):
    def test_the_fixture_of_the_cases_chooses_the_family(self):
        self.assertEqual(set(m.FAMILIES), {"MatrixPerformance.sml",
                                           "ClientPerformance.sml"})
        for name in ("task29b", "task30"):
            self.assertIs(m.TASKS[name].family,
                          m.FAMILIES["MatrixPerformance.sml"])
        self.assertIs(TASK31.family, m.FAMILIES["ClientPerformance.sml"])
        self.assertEqual(TASK31.family.sources,
                         ("ClientAllocation.sml", "MatrixSupport.sml"))
        self.assertEqual(m.FAMILIES["MatrixPerformance.sml"].sources,
                         m.FIXTURES)

    def test_both_families_install_the_names_the_protocol_checks(self):
        for family in m.FAMILIES.values():
            self.assertEqual(tuple(t for _, t in family.files), m.INSTALLED)
            for source in family.sources:
                self.assertTrue((HERE / source).is_file(), source)

    def test_a_task_of_two_families_is_refused(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "one fixture"):
            m.Task("x", "X", ("traversal_deep", "exclude_empty"), "c.json")

    def test_the_harness_binds_the_family_and_its_case_lists(self):
        def names(task):
            inputs, fixtures = m.harness_files(task)
            return ({p.name for p in inputs}, {p.name for p in fixtures})
        inputs, fixtures = names(TASK31)
        self.assertIn("allocation_iterations_task31.json", inputs)
        self.assertIn("ClientAllocation.sml", inputs | fixtures)
        self.assertNotIn("MatrixAllocation.sml", inputs | fixtures)
        self.assertLessEqual({"task31_cases.py", "MatrixSupport.sml"},
                             inputs)
        self.assertNotIn("client_dependencies.py", inputs)
        inputs, fixtures = names(m.TASKS["task30"])
        self.assertIn("MatrixAllocation.sml", inputs)
        self.assertNotIn("ClientAllocation.sml", inputs | fixtures)
        self.assertNotIn("task31_cases.py", inputs)


class Fixture(unittest.TestCase):
    """ClientAllocation.sml is the client workloads inside the driver of
    MatrixAllocation.sml, and nothing else."""

    @classmethod
    def setUpClass(cls):
        cls.alloc = (HERE / "ClientAllocation.sml").read_text()
        cls.matrix = (HERE / "MatrixAllocation.sml").read_text()
        cls.timing = (HERE / "ClientPerformance.sml").read_text()

    def test_the_driver_is_that_of_the_matrix_fixture_word_for_word(self):
        self.assertEqual(self.alloc[self.alloc.index(DRIVER):],
                         self.matrix[self.matrix.index(DRIVER):])

    def test_the_workloads_are_those_of_the_timing_fixture(self):
        ours = declarations("\n".join(client_lines(self.alloc)))
        theirs = declarations(self.timing)
        for first in ("val sink = ref 0", "fun consume () = sink := !sink + 1",
                      "fun same expected actual =",
                      "fun verify expected actual =",
                      "type workload = {run:unit -> unit, "
                      "verify:unit -> unit}",
                      "fun conversion stage make input expected : workload"
                      " = let"):
            self.assertIn(first, theirs, first)
            self.assertEqual(ours[first], theirs[first], first)
        for name in ("traversal", "tacticWork", "dependencyWork"):
            found = [k for k in theirs if k.startswith("fun %s " % name)]
            self.assertEqual(len(found), 1, name)
            self.assertEqual(ours[found[0]], theirs[found[0]], name)
        choose = [l for l in theirs["fun choose () ="] if "downstream"
                  not in l]
        self.assertEqual(ours["fun choose () ="], choose)

    def test_only_the_marked_lines_are_added_to_the_workloads(self):
        marked = [l for l in self.alloc.split("\n")
                  if l.rstrip().endswith("(*alloc*)")]
        self.assertEqual(len(marked), 2 + 4 + 4)
        retaining = [l for l in marked if "retaining" in l]
        self.assertEqual(len(retaining), 3)
        # the result and a use of it for each of conversion, tactic and
        # dependency work
        self.assertEqual(sum("thmText (!proof)" in l for l in marked), 3)
        self.assertEqual(sum("ignore ((!slot) input)" in l
                             for l in marked), 1)
        self.assertEqual(sum("apply ()" in l for l in marked), 2)

    def test_the_timing_driver_and_downstream_are_not_copied(self):
        for word in ("downstream", "RuntimeMetrics", "calibrate",
                     "PERF_SAMPLES", "PERF_SECONDS", "measure"):
            self.assertNotIn(word, self.alloc.replace(
                "`downstream`", "").replace("RuntimeMetrics)", ""), word)

    def test_the_fixture_makes_one_workload_of_the_case_and_size(self):
        self.assertIn('val label = Paired.env "PERF_CASE"', self.alloc)
        self.assertIn("val selected = label", self.alloc)
        self.assertIn("val workloadSize = size", self.alloc)
        self.assertIn("fun workload _ _ = let", self.alloc)
        self.assertIn("MatrixSupport.basic run check", self.alloc)

    def test_the_sources_follow_the_style(self):
        for name in ("ClientAllocation.sml", "task31_cases.py",
                     "task31_iterations.py", "test_allocation_client.py"):
            for number, line in enumerate(
                    (HERE / name).read_text().split("\n")):
                self.assertNotIn("\t", line, (name, number))
                self.assertEqual(line, line.rstrip(), (name, number))
                self.assertLess(len(line), 80, (name, number))


class Counts(unittest.TestCase):
    def test_the_committed_counts_are_those_of_the_rule(self):
        counts = m.load_iterations(task=TASK31)
        self.assertEqual(counts, json.loads(json.dumps(
            it.document(m.keys(TASK31)))))
        self.assertEqual(len(counts["steady"]), 245)
        self.assertEqual(counts["repeats"], 4)
        self.assertEqual(counts["schema"], "task29b-iterations-v1")
        self.assertEqual(TASK31.iterations, it.OUTPUT)

    def test_the_rule_cuts_only_the_declared_cells_at_1000(self):
        steady = m.load_iterations(task=TASK31)["steady"]
        small = {k: v for k, v in steady.items() if v in (4, 8) and
                 k.endswith("-1000")}
        want = {}
        for f in it.CUT_8:
            for stage in ("reuse", "complete"):
                want["tactic_%s_%s-1000" % (f, stage)] = 8
        for f in it.CUT_4:
            for stage in ("reuse", "complete"):
                want["tactic_%s_%s-1000" % (f, stage)] = 4
        self.assertEqual(len(want), 22)
        self.assertEqual({k: v for k, v in small.items() if k in want},
                         want)
        for key, value in steady.items():
            size = int(key.rsplit("-", 1)[1])
            if key in want:
                continue
            self.assertEqual(
                value, 32 if size <= 100 else 16 if size == 1000 else 8,
                key)

    def test_the_cut_families_are_heavy_ones(self):
        self.assertEqual(set(it.CUT_8) | set(it.CUT_4),
                         set(cases.HEAVY_FAMILIES))
        self.assertFalse(set(it.CUT_8) & set(it.CUT_4))

    def test_the_task_has_its_own_counts_and_they_are_not_the_others(self):
        self.assertFalse(set(m.load_iterations(task=TASK31)["steady"]) &
                         set(m.load_iterations(task=m.TASKS["task30"])[
                             "steady"]))
        with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
            m.load_iterations(TASK31.iterations)
        with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
            m.load_iterations(m.TASKS["task30"].iterations, TASK31)

    def test_the_generator_writes_the_committed_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "counts.json"
            self.assertEqual(it.main(["--output", str(out)]), 0)
            self.assertEqual(out.read_bytes(), it.OUTPUT.read_bytes())


def record(base, cand, work=None, pairs=10, ctrl=None):
    data = tb.experiment(base, cand, ctrl, pairs=pairs, work=work)
    return (dict(an.cell(*data, tb.STEADY), steady=tb.STEADY, pairs=pairs),
            data)


def grid_of(task, change=None, pairs=10):
    """Identical sides in every cell of the task; change(key) may give a
    cell its own (base, cand, work)."""
    cells, records, observed = set(), {}, {}
    for key in m.keys(task):
        base, cand, work = (change(key) if change else None) or (
            {"setup": 10}, {"setup": 10}, None)
        records[key], observed[key] = record(base, cand, work, pairs)
        cells.add(key)
    return cells, records, observed


CAND = "c" * 40


def assembled(cells, records, observed, **more):
    return m.assemble(cells, records, observed, task=TASK31,
                      candidate=CAND, **more)


def rows_of(out):
    return {m.name_of(r["case"], r["size"]): r for r in out["rows"]}


class Decisions(unittest.TestCase):
    def test_the_whole_grid_of_identical_sides_passes_row_by_row(self):
        out = assembled(*grid_of(TASK31))
        self.assertEqual((out["status"], out["complete"],
                          out["acceptance_pairs"]), ("pass", True, True))
        self.assertEqual((out["candidate"], out["baseline"]),
                         (CAND, a.BASE))
        self.assertEqual(m.status_code(out), 0)
        self.assertIsInstance(out["rows"], list)
        self.assertEqual([m.name_of(r["case"], r["size"])
                          for r in out["rows"]],
                         [m.name_of(*k) for k in m.keys(TASK31)])
        for row in out["rows"]:
            self.assertEqual(row, dict(
                case=row["case"], size=row["size"], pairs=10,
                decision="pass", work=None), row)
        self.assertEqual(len(out["cases"]), 53)
        self.assertEqual(out["unresolved"], [])
        self.assertEqual(out["infeasible"], sorted(cases.INFEASIBLE))
        self.assertEqual(len(out["infeasible"]), 33)

    def test_the_slopes_follow_the_sizes_of_each_case(self):
        out = assembled(*grid_of(TASK31))
        for case, record in out["cases"].items():
            sizes = TASK31.sizes(case)
            self.assertEqual(sorted(map(int, record["cells"])),
                             sorted(sizes), case)
            rows = record["slopes"]["setup"]["total"]
            self.assertEqual([r["sizes"] for r in rows],
                             [[lo, hi] for lo, hi in zip(sizes, sizes[1:])],
                             case)
        self.assertEqual(
            out["cases"]["traversal_construct"]["slopes"]["setup"]["total"],
            [])

    def test_a_failing_cell_is_a_failing_row_and_fails_the_grid(self):
        bad = ("tactic_asm_complete", 1000)
        out = assembled(*grid_of(TASK31, lambda k: (
            {"setup": 10}, {"setup": 11}, None) if k == bad else None))
        self.assertEqual(out["status"], "fail")
        self.assertEqual(m.status_code(out), 1)
        rows = rows_of(out)
        self.assertEqual(rows[m.name_of(*bad)]["decision"], "fail")
        self.assertEqual({r["decision"] for n, r in rows.items()
                          if n != m.name_of(*bad)}, {"pass"})

    def test_a_cell_whose_control_varies_is_inconclusive(self):
        base, cand = {"setup": 10}, {"setup": 10}
        data = tb.experiment(base, cand, lambda i: tb.observation(
            {"setup": 10 + (i == 0)}))
        key = ("traversal_deep", 100)
        cells, records, observed = grid_of(TASK31)
        records[key] = dict(an.cell(*data, tb.STEADY), steady=tb.STEADY,
                            pairs=10)
        out = assembled(cells, records, observed)
        self.assertEqual(rows_of(out)[m.name_of(*key)]["decision"],
                         "inconclusive")
        self.assertEqual(out["status"], "inconclusive")
        self.assertFalse(out["complete"] and out["status"] == "pass")

    def test_the_work_row_is_beside_the_words(self):
        work, other = tb.structural(), tb.structural(
            first=tb.WORK_TEXT.replace("=1", "=2", 1))
        key = ("tactic_full_reuse", 100)
        out = assembled(*grid_of(TASK31, lambda k: (
            {"setup": 10}, {"setup": 10}, work if k != key else (
                work, other))))
        rows = rows_of(out)
        self.assertEqual(rows[m.name_of(*key)]["work"], "differs")
        self.assertEqual(rows[m.name_of(*key)]["decision"], "pass")
        self.assertEqual({r["work"] for n, r in rows.items()
                          if n != m.name_of(*key)}, {"equal"})
        self.assertEqual(out["status"], "pass")
        self.assertEqual(out["work_status"], "differs")

    def test_a_difference_in_a_stage_a_count_or_the_digest_is_seen(self):
        key = ("tactic_full_reuse", 100)
        other = tb.WORK_TEXT.replace("=1", "=2", 1)
        for label, changed in (
                ("first stage", dict(first=other)),
                ("second stage", dict(second=other)),
                ("use stage", dict(use=other)),
                ("result digest", dict(digest="names=-,+other;dprocs=;")),
                ("a count", dict(second=tb.WORK_TEXT.replace(
                    "REWRITING=3", "REWRITING=4")))):
            with self.subTest(label):
                out = assembled(*grid_of(TASK31, lambda k: (
                    {"setup": 10}, {"setup": 10}, tb.structural() if
                    k != key else (tb.structural(),
                                   tb.structural(**changed)))))
                self.assertEqual(rows_of(out)[m.name_of(*key)]["work"],
                                 "differs")

    def test_a_partial_run_has_rows_for_its_cells_only(self):
        cells, records, observed = grid_of(TASK31)
        keep = {("traversal_deep", 0), ("tactic_asm_complete", 10000)}
        out = assembled(keep, {k: records[k] for k in keep},
                        {k: observed[k] for k in keep})
        self.assertEqual(sorted(rows_of(out)), sorted(
            m.name_of(*k) for k in keep))
        self.assertFalse(out["complete"])
        self.assertEqual(out["status"], "inconclusive")
        self.assertEqual(len(out["infeasible"]), 33)

    def test_a_cell_without_an_analysis_is_an_inconclusive_row(self):
        keep = {("traversal_deep", 0), ("traversal_deep", 1)}
        cells, records, observed = grid_of(TASK31)
        out = assembled(keep, {("traversal_deep", 0):
                               records["traversal_deep", 0]}, {})
        self.assertEqual(out["unresolved"], ["traversal_deep-1"])
        rows = rows_of(out)
        self.assertEqual(rows["traversal_deep-1"], dict(
            case="traversal_deep", size=1, pairs=None,
            decision="inconclusive", work=None))
        self.assertEqual(rows["traversal_deep-0"]["decision"], "pass")

    def test_a_smoke_is_never_complete_and_has_no_passable_row(self):
        out = assembled(*grid_of(TASK31, pairs=2))
        self.assertFalse(out["acceptance_pairs"])
        self.assertFalse(out["complete"])
        self.assertEqual(out["status"], "inconclusive")
        self.assertEqual({r["pairs"] for r in out["rows"]}, {2})
        self.assertEqual({r["decision"] for r in out["rows"]},
                         {"inconclusive"})

    def test_a_row_of_ten_pairs_passes_and_of_fewer_does_not(self):
        key = ("traversal_deep", 100)
        short, data = record({"setup": 10}, {"setup": 10}, None, pairs=8)
        rows = rows_of(assembled({key}, {key: short}, {key: data}))
        self.assertEqual(rows[m.name_of(*key)]["decision"], "inconclusive")
        self.assertEqual(rows[m.name_of(*key)]["pairs"], 8)

    def test_a_grid_against_another_baseline_is_not_complete(self):
        out = assembled(*grid_of(TASK31), baseline="d" * 40)
        self.assertEqual(out["baseline"], "d" * 40)
        self.assertFalse(out["acceptance_baseline"])
        self.assertFalse(out["complete"])
        self.assertEqual({r["decision"] for r in out["rows"]},
                         {"inconclusive"})

    def test_a_failure_stays_a_failure_in_a_smoke(self):
        bad = ("tactic_asm_complete", 1000)
        out = assembled(*grid_of(TASK31, lambda k: (
            {"setup": 10}, {"setup": 11}, None) if k == bad else None,
            pairs=2))
        self.assertEqual(rows_of(out)[m.name_of(*bad)]["decision"], "fail")

    def test_the_other_tasks_have_no_rows(self):
        cell = ("exclude_empty", 0)
        data = record({"setup": 10}, {"setup": 10})
        out = m.assemble({cell}, {cell: data[0]}, {},
                         task=m.TASKS["task30"])
        for key in ("rows", "infeasible", "candidate", "baseline"):
            self.assertNotIn(key, out)
        self.assertNotIn("rows", m.assemble({("frag_create", 0)}, {
            ("frag_create", 0): data[0]}, {}))

    def test_the_results_name_the_rows_and_the_cells_not_run(self):
        out = assembled(*grid_of(TASK31))
        text = m.results_markdown(out, "TASK31")
        self.assertTrue(text.startswith("# TASK31 allocation matrix"))
        self.assertIn("pass x245", text)
        self.assertIn("33 cells infeasible and not run", text)
        plain = m.results_markdown(m.assemble(
            {("exclude_empty", 0)}, {("exclude_empty", 0): record(
                {"setup": 10}, {"setup": 10})[0]}, {},
            task=m.TASKS["task30"]), "TASK30")
        self.assertNotIn("infeasible", plain)


class Installation(unittest.TestCase):
    """Grid.install_private for the client family: its two fixtures and no
    shared closure."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name) / "d"
        self.directory.mkdir()
        self.grid = m.Grid.__new__(m.Grid)

    def install(self, task):
        self.grid.task = task
        with mock.patch.object(m.rp, "install_fixtures") as fixtures:
            self.grid.install_private(self.directory)
        fixtures.assert_called_once_with(self.directory)

    def test_the_client_family_installs_its_fixture_and_support(self):
        self.install(TASK31)
        self.assertEqual(
            (self.directory / "Performance.sml").read_bytes(),
            (HERE / "ClientAllocation.sml").read_bytes())
        self.assertEqual(
            (self.directory / "MatrixSupport.sml").read_bytes(),
            (HERE / "MatrixSupport.sml").read_bytes())
        self.assertFalse((self.directory / "MatrixAllocation.sml").exists())
        self.assertIn("paired.exe: Performance.uo",
                      (self.directory / "Holmakefile").read_text())

    def test_a_matrix_task_installs_the_matrix_fixture(self):
        self.install(m.TASKS["task30"])
        self.assertEqual(
            (self.directory / "Performance.sml").read_bytes(),
            (HERE / "MatrixAllocation.sml").read_bytes())

    def test_no_family_installs_a_shared_closure(self):
        # A process loads the selected sources, the installed files and the
        # shared heap; a module outside them is refused as shared input.
        self.assertFalse(hasattr(m.Family, "dependencies"))
        self.assertFalse(hasattr(m, "deps"))
        self.assertFalse(hasattr(m.Grid, "probe_dependencies"))


if __name__ == "__main__":
    unittest.main()
