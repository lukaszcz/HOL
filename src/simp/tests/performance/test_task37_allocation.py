#!/usr/bin/env python3
"""TASK37 in the allocation matrix: the pair count of a task, the tasks
`task37-matrix` and `task37-client`, and the refusals around them.

Synthetic receipts and files only: no runtime, toolchain or HOL process.
"""
import argparse
import json
from pathlib import Path
import tempfile
import unittest

import allocation_analysis as an
import allocation_matrix as m
import allocation_schema as sc
import allocation_testbed as tb
import matrix_schema as ms
import task29_gate as gate
import task30_cases
import task31_cases
import task37_cases as cases

MATRIX = m.TASKS["task37-matrix"]
CLIENT = m.TASKS["task37-client"]
CAND = "c" * 40


class Pairs(unittest.TestCase):
    def test_legacy_tasks_keep_ten_pairs_and_task37_uses_three(self):
        self.assertEqual(m.PAIRS, 10)
        for name in ("task29b", "task30", "task31"):
            self.assertEqual(m.TASKS[name].pairs, 10, name)
        for task in (MATRIX, CLIENT):
            self.assertEqual(task.pairs, 3)
        self.assertEqual(m.TASK37_PAIRS, 3)

    def test_a_task_needs_an_ab_and_a_ba_pair(self):
        for pairs in (1, 0, True, 2.5):
            with self.assertRaisesRegex(sc.InvalidAllocation, "pair"):
                m.Task("x", "X", gate.CASES, "c.json", pairs=pairs)
        self.assertEqual(m.Task("x", "X", gate.CASES, "c.json",
                                pairs=2).pairs, 2)

    def test_the_grid_takes_the_pairs_of_its_task(self):
        def grid(task, pairs=None):
            return m.Grid(argparse.Namespace(
                task=task, pairs=pairs, repo=m.HERE.parents[3]))
        self.assertEqual(grid("task37-matrix").pairs, 3)
        self.assertEqual(grid("task37-client").pairs, 3)
        self.assertEqual(grid("task30").pairs, 10)
        self.assertEqual(grid("task31").pairs, 10)
        self.assertEqual(grid("task29b").pairs, 10)
        self.assertEqual(grid("task37-client", 2).pairs, 2)
        self.assertEqual(grid("task30", 4).pairs, 4)

    def test_the_command_line_defaults_to_the_pairs_of_the_task(self):
        seen = {}

        def stop(args):
            seen["pairs"] = args.pairs
            return 0
        saved = m.run
        m.run = stop
        try:
            base = ["run", "--output", "o", "--candidate", CAND,
                    "--toolchain", "t", "--controls-receipt", "c"]
            self.assertEqual(m.main(base + ["--task", "task37-matrix"]), 0)
            self.assertIsNone(seen["pairs"])
            m.main(base + ["--task", "task37-matrix", "--pairs", "4"])
            self.assertEqual(seen["pairs"], 4)
            with self.assertRaisesRegex(sc.InvalidAllocation, "pair"):
                m.main(base + ["--pairs", "1"])
        finally:
            m.run = saved

    def test_an_unknown_task_is_refused(self):
        for name in ("task37-downstream", "task37", "task38"):
            with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
                m.task_named(name)
            with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
                m.task_of(dict(task=name))
            self.assertNotIn(name, m.TASKS)


class Cells(unittest.TestCase):
    def test_the_matrix_is_every_task29_and_task30_cell(self):
        self.assertEqual(MATRIX.cases, tuple(gate.CASES) +
                         tuple(task30_cases.CASES))
        keys = m.keys(MATRIX)
        self.assertEqual(len(keys), 306)
        self.assertEqual(len(keys), len(set(keys)))
        self.assertEqual(len(m.keys(m.TASKS["task29b"])) +
                         len(m.keys(m.TASKS["task30"])), 306)
        self.assertEqual(sum(n == 10000 for _, n in keys), 51)
        self.assertEqual(MATRIX.infeasible, frozenset())
        for case in MATRIX.cases:
            self.assertEqual(MATRIX.sizes(case), m.SIZES, case)
        self.assertIs(MATRIX.family, m.FAMILIES["MatrixPerformance.sml"])

    def test_the_client_cells_are_exactly_those_task31_allocates(self):
        self.assertEqual(m.keys(CLIENT), m.keys(m.TASKS["task31"]))
        self.assertEqual(len(m.keys(CLIENT)), 245)
        self.assertEqual(CLIENT.infeasible,
                         frozenset(task31_cases.INFEASIBLE_CELLS))
        self.assertIs(CLIENT.family, m.FAMILIES["ClientPerformance.sml"])
        self.assertFalse(any(c.startswith("downstream_")
                             for c in CLIENT.cases))

    def test_the_tasks_have_their_own_counts_files(self):
        self.assertEqual(MATRIX.iterations.name,
                         "allocation_iterations_task37_matrix.json")
        self.assertEqual(CLIENT.iterations.name,
                         "allocation_iterations_task37_client.json")
        self.assertEqual(len({t.iterations for t in (
            MATRIX, CLIENT, *(m.TASKS[n] for n in (
                "task29b", "task30", "task31")))}), 5)

    def test_the_counts_cover_the_cells_of_the_task_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            for task in (MATRIX, CLIENT):
                path = Path(tmp) / (task.name + ".json")
                counts = {"schema": "task29b-iterations-v1", "repeats": 4,
                          "steady": {m.name_of(*k): 8
                                     for k in m.keys(task)}}
                path.write_text(json.dumps(counts))
                self.assertEqual(m.load_iterations(path, task), counts)
                counts["steady"].popitem()
                path.write_text(json.dumps(counts))
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "incomplete"):
                    m.load_iterations(path, task)
        # the client's counts are not the matrix's
        counts = {"schema": "task29b-iterations-v1", "repeats": 4,
                  "steady": {m.name_of(*k): 8 for k in m.keys(CLIENT)}}
        path = Path(tempfile.mkdtemp()) / "c.json"
        try:
            path.write_text(json.dumps(counts))
            with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
                m.load_iterations(path, MATRIX)
        finally:
            path.unlink()
            path.parent.rmdir()

    def test_every_case_is_a_case_of_one_fixture_family(self):
        for task in (MATRIX, CLIENT):
            fixtures = {ms.EXPECTED_CASES[c]["fixture"] for c in task.cases}
            self.assertEqual(len(fixtures), 1)

    def test_the_case_views_are_the_task_modules_lists(self):
        self.assertEqual(cases.MATRIX_CASES, MATRIX.cases)
        self.assertEqual(cases.CLIENT_CASES, CLIENT.cases)
        self.assertEqual(len(gate.CASES), 27)
        self.assertEqual(len(task30_cases.CASES), 24)

    def test_the_task_is_in_the_grid_digest_and_the_header(self):
        with tempfile.TemporaryDirectory() as tmp:
            sandbox = tb.Sandbox(Path(tmp), 3)
            for task in (MATRIX, CLIENT):
                header = dict(sandbox.header(), task=task.name)
                self.assertEqual(m.task_of(header), task)
                self.assertNotEqual(
                    m.grid_digest(header),
                    m.grid_digest(dict(header, task="task30")))

    def test_the_harness_binds_the_case_modules_and_counts(self):
        for task in (MATRIX, CLIENT):
            inputs, fixtures = m.harness_files(task)
            names = {p.name for p in inputs}
            self.assertLessEqual({"task37_cases.py", "task31_cases.py",
                                  "task29_gate.py", "task30_cases.py",
                                  task.iterations.name}, names)
            self.assertEqual({p.name for p in fixtures if p.suffix ==
                              ".sml" and p.name.endswith("Allocation.sml")},
                             set(task.family.sources) & {
                                 "ClientAllocation.sml",
                                 "MatrixAllocation.sml"})
        legacy = {n: {p.name for p in m.harness_files(m.TASKS[n])[0]}
                  for n in ("task29b", "task30", "task31")}
        for names in legacy.values():
            self.assertNotIn("task37_cases.py", names)
        self.assertNotIn("task31_cases.py", legacy["task29b"])
        self.assertNotIn("task31_cases.py", legacy["task30"])
        self.assertIn("task31_cases.py", legacy["task31"])


def grid_of(task, pairs, change=None):
    cells, records, observed = set(), {}, {}
    for key in m.keys(task):
        base, cand, work = (change(key) if change else None) or (
            {"setup": 10}, {"setup": 10}, None)
        data = tb.experiment(base, cand, pairs=pairs, work=work)
        records[key] = dict(an.cell(*data, tb.STEADY), steady=tb.STEADY,
                            pairs=pairs)
        observed[key] = data
        cells.add(key)
    return cells, records, observed


class Decisions(unittest.TestCase):
    def test_three_pairs_pass_a_task37_task_row_by_row(self):
        for task in (MATRIX, CLIENT):
            out = m.assemble(*grid_of(task, 3), task=task, candidate=CAND)
            self.assertEqual((out["status"], out["complete"],
                              out["acceptance_pairs"]),
                             ("pass", True, True), task.name)
            self.assertEqual(len(out["rows"]), len(m.keys(task)))
            self.assertTrue(all(r["pairs"] == 3 and
                                r["decision"] == "pass"
                                for r in out["rows"]), task.name)

    def test_the_rule_of_another_task_does_not_accept_the_pairs(self):
        out = m.assemble(*grid_of(m.TASKS["task31"], 3),
                         task=m.TASKS["task31"], candidate=CAND)
        self.assertFalse(out["acceptance_pairs"])
        self.assertFalse(out["complete"])
        self.assertEqual(out["status"], "inconclusive")
        self.assertTrue(all(r["decision"] == "inconclusive"
                            for r in out["rows"]))
        out = m.assemble(*grid_of(MATRIX, 2), task=MATRIX, candidate=CAND)
        self.assertFalse(out["acceptance_pairs"])
        self.assertEqual(out["status"], "inconclusive")

    def test_legacy_tasks_still_need_ten_pairs(self):
        for name in ("task29b", "task30"):
            task = m.TASKS[name]
            ten = m.assemble(*grid_of(task, 10), task=task)
            self.assertTrue(ten["acceptance_pairs"], name)
            self.assertEqual(ten["status"], "pass", name)
            three = m.assemble(*grid_of(task, 3), task=task)
            self.assertFalse(three["acceptance_pairs"], name)
            self.assertEqual(three["status"], "inconclusive", name)

    def test_a_nondeterministic_cell_is_found_with_three_pairs(self):
        data = tb.experiment({"setup": 10}, {"setup": 10}, pairs=3)
        data[0][2]["candidate"] = tb.observation({"setup": 12})
        key = m.keys(CLIENT)[0]
        cells, records, observed = grid_of(CLIENT, 3)
        records[key] = dict(an.cell(*data, tb.STEADY), steady=tb.STEADY,
                            pairs=3)
        out = m.assemble(cells, records, observed, task=CLIENT,
                         candidate=CAND)
        self.assertTrue(any(r[0] == key[0] and r[1] == key[1] and
                            r[4] == "candidate"
                            for r in out["nondeterminism"]))
        self.assertNotEqual(out["status"], "pass")
        row = [r for r in out["rows"] if (r["case"], r["size"]) == key][0]
        self.assertNotEqual(row["decision"], "pass")
        # a control that differs from the baseline is found as well
        data = tb.experiment({"setup": 10}, {"setup": 10}, pairs=3,
                             ctrl=lambda i: tb.observation(
                                 {"setup": 10 + (i == 1)}))
        records[key] = dict(an.cell(*data, tb.STEADY), steady=tb.STEADY,
                            pairs=3)
        out = m.assemble(cells, records, observed, task=CLIENT,
                         candidate=CAND)
        self.assertTrue(any(r[4] == "control"
                            for r in out["nondeterminism"]))
        self.assertNotEqual(out["status"], "pass")


class Records(unittest.TestCase):
    def test_a_pairs_claim_that_is_not_the_rule_of_the_task_is_refused(self):
        def inventory(pairs, flag):
            return dict(pairs=pairs, acceptance_pairs=flag)
        m.check_pairs(inventory(3, True), MATRIX)
        m.check_pairs(inventory(2, False), MATRIX)
        m.check_pairs(inventory(10, True), m.TASKS["task30"])
        m.check_pairs(inventory(3, False), m.TASKS["task30"])
        for task, pairs, flag in ((MATRIX, 2, True), (CLIENT, 3, False),
                                  (m.TASKS["task30"], 3, True),
                                  (m.TASKS["task31"], 9, True)):
            with self.assertRaisesRegex(sc.InvalidAllocation, "acceptance"):
                m.check_pairs(inventory(pairs, flag), task)
        for bad in (None, 1, True, "3"):
            with self.assertRaisesRegex(sc.InvalidAllocation, "pair count"):
                m.check_pairs(dict(pairs=bad), MATRIX)
        # an older inventory without the flag is judged by its cells only
        m.check_pairs(dict(pairs=10), m.TASKS["task30"])

    def test_a_cell_of_other_pairs_than_the_header_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            sb = tb.Sandbox(Path(tmp) / "s", pairs=3)
            folder = Path(tmp) / "cell"
            sb.write_cell(folder)
            self.assertEqual(m.cell_data(folder, sb.bind())[0]["pairs"], 3)
            for pairs in (10, 4, 2):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "different inputs"):
                    m.cell_data(folder, sb.bind(pairs=pairs))

    def test_finish_refuses_an_inventory_that_misstates_its_pairs(self):
        with tempfile.TemporaryDirectory() as tmp:
            for name, pairs, flag in (("task37-client", 3, False),
                                      ("task37-matrix", 2, True),
                                      ("task30", 3, True)):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "acceptance"):
                    m.finish(Path(tmp), dict(
                        task=name, pairs=pairs, acceptance_pairs=flag,
                        runs=[]))


if __name__ == "__main__":
    unittest.main()
