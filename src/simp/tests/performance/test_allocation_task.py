#!/usr/bin/env python3
"""Allocation matrix task selection: TASK29B by default, TASK30 by name.

The same synthetic fixtures as test_allocation_matrix.py and
test_allocation_grid.py; no runtime, toolchain or committed receipt.
"""
import argparse
import contextlib
import io
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest import mock

import acceptance as a
import allocation_matrix as m
import allocation_schema as sc
import allocation_testbed as tb
import matrix_schema as ms
import task29_gate as gate
import task30_cases as cases
import test_allocation_grid as grid_tests

TASK30 = m.TASKS["task30"]


class Selection(unittest.TestCase):
    def test_the_default_is_task29b_and_unchanged(self):
        self.assertEqual(m.DEFAULT_TASK, "task29b")
        self.assertEqual(m.keys(), m.keys(m.TASKS["task29b"]))
        self.assertEqual(len(m.keys()), 162)
        self.assertEqual(m.TASKS["task29b"].cases, tuple(gate.CASES))
        self.assertEqual(m.TASKS["task29b"].iterations, m.ITERATIONS)

    def test_task30_is_every_task30_case_but_the_named_exclusion(self):
        self.assertEqual(len(cases.CASES), 24)
        self.assertEqual(len(TASK30.cases), 23)
        self.assertEqual(set(TASK30.cases) | set(TASK30.excluded),
                         set(cases.CASES))
        self.assertFalse(set(TASK30.cases) & set(TASK30.excluded))
        self.assertEqual(sorted(TASK30.excluded), ["history_theory_change"])
        self.assertTrue(all(len(reason) > 40 for reason in
                            TASK30.excluded.values()))
        self.assertEqual(len(m.keys(TASK30)), 138)
        self.assertFalse(set(TASK30.cases) & set(gate.CASES))

    def test_the_cases_are_the_matrix_exclusion_and_history_cases(self):
        matrix = [c for c in ms.EXPECTED_CASES
                  if c.startswith(("exclude_", "history_"))]
        self.assertEqual(sorted(cases.CASES), sorted(matrix))
        text = (m.HERE / "MatrixSupport.sml").read_text()
        listed = re.search(r"val cases =\s*\[(.*?)\]", text, re.S)
        found = set(re.findall(r'"(exclude_\w+|history_\w+)"',
                               listed.group(1)))
        self.assertLessEqual(set(cases.CASES), found)
        for case in cases.CASES:
            self.assertEqual(ms.EXPECTED_CASES[case]["sizes"], "rules")

    def test_sizes_are_the_gate_sizes(self):
        for case in cases.CASES:
            self.assertEqual(tuple(ms.SIZE_SETS["rules"]), m.SIZES)

    def test_unknown_tasks_are_refused(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown task"):
            m.task_named("task31")
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown task"):
            m.task_of(dict(task="nope"))
        self.assertIs(m.task_of({}), m.TASKS["task29b"])
        self.assertIs(m.task_of(dict(task="task30")), TASK30)

    def test_the_excluded_case_stays_unmeasurable_by_name(self):
        for name in ("history_theory_change-0", "history_theory_change-10"):
            self.assertNotIn(name, {m.name_of(*k) for k in m.keys(TASK30)})


class Counts(unittest.TestCase):
    def test_the_committed_counts_follow_the_fixed_rule(self):
        counts = m.load_iterations(task=TASK30)
        self.assertEqual(len(counts["steady"]), 138)
        self.assertEqual(counts["repeats"], 4)
        base = a.load(m.ITERATIONS)
        self.assertEqual((counts["schema"], counts["rule"]),
                         (base["schema"], base["rule"]))
        for key, value in counts["steady"].items():
            size = int(key.rsplit("-", 1)[1])
            self.assertEqual(value, 32 if size <= 100 else
                             16 if size == 1000 else 8, key)

    def test_the_rule_is_the_one_of_the_other_counts(self):
        base = a.load(m.ITERATIONS)["steady"]
        other = m.load_iterations(task=TASK30)["steady"]
        for key in set(base) & set(other):
            self.assertEqual(base[key], other[key])
        self.assertFalse(set(base) & set(other))

    def test_counts_of_another_task_are_refused(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
            m.load_iterations(TASK30.iterations)
        with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
            m.load_iterations(m.ITERATIONS, TASK30)

    def test_a_missing_or_extra_cell_is_refused(self):
        good = a.load(TASK30.iterations)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "c.json"
            for steady in (
                    {k: v for k, v in good["steady"].items()
                     if k != "history_makers-10"},
                    dict(good["steady"], **{"history_theory_change-0": 32})):
                path.write_text(json.dumps(dict(good, steady=steady)))
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "incomplete"):
                    m.load_iterations(path, TASK30)


class Binding(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.sb = tb.Sandbox(Path(self.tmp.name) / "sb", pairs=2)

    def test_the_task_is_part_of_the_grid_digest_only_when_named(self):
        header = self.sb.header()
        base = m.grid_digest(header)
        self.assertEqual(m.grid_digest(dict(header, task="task29b")), base)
        other = m.grid_digest(dict(header, task="task30"))
        self.assertNotEqual(other, base)
        self.assertEqual(m.grid_digest(dict(header, task="task30")), other)

    def test_a_resume_under_another_task_is_a_different_grid(self):
        header = self.sb.header()
        self.assertEqual(m.changed_settings(header, header), [])
        self.assertEqual(m.changed_settings(header, dict(
            header, task="task30")), ["task"])
        self.assertEqual(m.changed_settings(
            dict(header, task="task30"), header), ["task"])
        self.assertEqual(m.changed_settings(
            dict(header, task="task29b"), header), [])

    def test_the_header_names_a_non_default_task_only(self):
        for task, expected in (("task29b", {}), ("task30", dict(
                task="task30"))):
            with self.subTest(task):
                made = self.sb.real_grid()
                made.task = m.task_named(task)
                with made.make():
                    header = made.make_header(
                        tb.CAND_PIN, self.sb.header()["toolchain_products"])
                self.assertEqual({k: v for k, v in header.items()
                                  if k == "task"}, expected)

    def test_the_bound_counts_are_those_of_the_selected_task(self):
        sizes = m.load_iterations(task=TASK30)["steady"]
        header = dict(self.sb.header(), task="task30",
                      iterations=m.load_iterations(task=TASK30))
        found = m.binding(header, "exclude_empty", 10)
        self.assertEqual(found["steady"], sizes["exclude_empty-10"])
        self.assertEqual(found["grid"], m.grid_digest(header))

    def test_the_grid_takes_its_task_from_the_arguments(self):
        repo = a.HERE.parents[3]
        for name in ("task29b", "task30"):
            args = argparse.Namespace(pairs=2, repo=repo, task=name)
            self.assertEqual(m.Grid(args).task.name, name)
        args = argparse.Namespace(pairs=2, repo=repo)
        self.assertEqual(m.Grid(args).task.name, "task29b")

    def test_the_prepared_grid_binds_the_harness_of_its_task(self):
        source = Path(m.__file__).read_text()
        self.assertEqual(source.count("harness_files(self.task)"), 1)

    def test_assembly_takes_the_cases_of_the_task(self):
        cell = {("exclude_empty", 0)}
        name = m.name_of("exclude_empty", 0)
        self.assertEqual(m.assemble(cell, {}, {}, task=TASK30)[
            "unresolved"], [name])
        self.assertEqual(m.assemble(cell, {}, {})["unresolved"], [])

    def test_the_harness_binds_the_selected_counts_and_the_case_list(self):
        def names(task):
            inputs, _ = m.harness_files(task)
            return {p.name for p in inputs}
        self.assertIn("allocation_iterations.json",
                      names(m.TASKS["task29b"]))
        self.assertNotIn("allocation_iterations_task30.json",
                         names(m.TASKS["task29b"]))
        self.assertIn("allocation_iterations_task30.json", names(TASK30))
        self.assertNotIn("allocation_iterations.json", names(TASK30))
        for task in m.TASKS.values():
            self.assertIn("task30_cases.py", names(task))
        self.assertEqual({p.name for p in m.harness_files()[0]},
                         names(m.TASKS["task29b"]))


class Run(grid_tests.Bed):
    """A stub run of TASK30 cells: header, inventory, replay and labels."""

    def patched30(self):
        stub, log = grid_tests.make_stub(self.sb)

        class Task(stub):
            def __init__(self, args):
                super().__init__(args)
                task = getattr(args, "task", m.DEFAULT_TASK)
                if task != m.DEFAULT_TASK:
                    self.header = dict(self.header, task=task)
        patcher = mock.patch.object(m, "Grid", Task)
        patcher.start()
        self.addCleanup(patcher.stop)
        return log

    def test_a_task30_cell_runs_replays_and_is_labelled(self):
        self.patched30()
        code = self.quiet(m.run, grid_tests.arguments(
            self.out, ["exclude_empty-0", "history_makers-10"],
            task="task30"))
        self.assertEqual(code, 2)
        inventory = a.load(self.out / "inventory.json")
        self.assertEqual(inventory["task"], "task30")
        self.assertEqual(sorted(r["case"] for r in inventory["runs"]),
                         ["exclude_empty", "history_makers"])
        steady = m.load_iterations(task=TASK30)["steady"]
        self.assertEqual({r["case"]: r["steady"]
                          for r in inventory["runs"]},
                         {"exclude_empty": steady["exclude_empty-0"],
                          "history_makers": steady["history_makers-10"]})
        self.assertTrue((self.out / "RESULTS-partial.md").read_text(
            ).startswith("# TASK30 allocation matrix"))
        args = type("Args", (), {"output": self.out})
        self.assertEqual(self.quiet(m.replay, args), 2)

    def test_the_excluded_case_cannot_be_measured(self):
        self.patched30()
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
            self.quiet(m.run, grid_tests.arguments(
                self.out, ["history_theory_change-0"], task="task30"))

    def test_task29b_cells_are_not_task30_cells(self):
        self.patched30()
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
            self.quiet(m.run, grid_tests.arguments(
                self.out, ["frag_create-0"], task="task30"))
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
            self.quiet(m.run, grid_tests.arguments(
                self.root / "other", ["exclude_empty-0"]))

    def test_resume_under_another_task_is_refused(self):
        self.patched30()
        self.quiet(m.run, grid_tests.arguments(
            self.out, ["exclude_empty-0"], task="task30"))
        with self.assertRaisesRegex(
                sc.InvalidAllocation, "resume with different settings.*task"):
            self.quiet(m.run, grid_tests.arguments(
                self.out, ["frag_create-0"], resume=True))

    def test_the_task_option_is_on_the_command_line(self):
        with mock.patch.object(m, "run", lambda args: args.task):
            argv = ["run", "--output", "o", "--candidate", "c" * 40,
                    "--toolchain", "t", "--controls-receipt", "r"]
            self.assertEqual(m.main(argv), "task29b")
            self.assertEqual(m.main(argv + ["--task", "task30"]), "task30")
            with contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit):
                m.main(argv + ["--task", "task31"])


class Fixture(unittest.TestCase):
    """The allocation fixture brackets any MatrixSupport case, whole."""

    @classmethod
    def setUpClass(cls):
        cls.text = (m.HERE / "MatrixAllocation.sml").read_text()

    def test_every_phase_of_a_case_is_inside_a_bracket(self):
        self.assertIn('bracket "setup" (fn () => cell := SOME '
                      '(workload label size))', self.text)
        self.assertIn('batch "operation_first" 1 run', self.text)
        self.assertIn('batch "operation_steady" steady (fn () => '
                      'repeat steady run)', self.text)
        self.assertIn('bracket "apply" verify', self.text)

    def test_callbacks_run_outside_the_brackets(self):
        start = self.text.index("fun batch name count work")
        end = self.text.index("val _ = batch \"operation_first\"")
        body = self.text[start:end]
        self.assertLess(body.index("beforeBatch ()"),
                        body.index("bracket name work"))
        self.assertLess(body.index("bracket name work"),
                        body.index("afterBatch count"))

    def test_every_phase_is_gated(self):
        import allocation_analysis as an
        self.assertEqual(set(an.GATED), {
            "setup", "operation_first", "operation_steady", "apply"})

    def test_the_case_label_is_not_restricted_to_task29b(self):
        self.assertIn("Lib.mem label cases", self.text)
        support = (m.HERE / "MatrixSupport.sml").read_text()
        for case in cases.CASES:
            self.assertIn('"%s"' % case, support)


class PathSensitivity(unittest.TestCase):
    """Why history_theory_change is outside the allocation gate."""

    def test_the_only_path_sensitive_case_is_the_excluded_one(self):
        text = (m.HERE / "MatrixSupport.sml").read_text()
        start = text.index('| "history_theory_change" =>')
        end = text.index('| _ => raise Fail "unknown history case"', start)
        self.assertIn("new_theory", text[start:end])
        outside = text[:start] + text[end:]
        for token in ("new_theory", "export_theory", "getEnv", "OS.FileSys",
                      "FileSys.", "OS.Process", "Posix.", "TextIO.openIn",
                      "TextIO.openOut", "BinIO.open", "Portable.pwd"):
            with self.subTest(token):
                self.assertNotIn(token, outside)

    def test_the_gate_never_contains_it(self):
        self.assertNotIn("history_theory_change", gate.CASES)
        self.assertNotIn("history_theory_change", TASK30.cases)
        self.assertIn("history_theory_change", cases.CASES)


if __name__ == "__main__":
    unittest.main()
