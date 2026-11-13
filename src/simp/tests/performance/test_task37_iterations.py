#!/usr/bin/env python3
"""The TASK37 allocation counts (task37_iterations.py): the rule's output
for each table, against allocation_matrix's naming and loader, the cells
each task allocates, and the refusals."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import acceptance as a
import allocation_matrix as m
import task37_cases as cases
import task37_iterations as it

TASKS = {"matrix": "task37-matrix", "client": "task37-client",
         "downstream": "task37-downstream"}


def counts(name):
    return a.load(a.HERE / name)["steady"]


class Rule(unittest.TestCase):
    def test_the_files_are_those_the_allocation_tasks_name(self):
        for table, task in TASKS.items():
            self.assertEqual(it.path_of(table), m.TASKS[task].iterations)
            self.assertEqual(it.path_of(table, "/x").parent, Path("/x"))
        self.assertEqual(
            sorted(p.name for p in map(it.path_of, TASKS)),
            ["allocation_iterations_task37_client.json",
             "allocation_iterations_task37_downstream.json",
             "allocation_iterations_task37_matrix.json"])

    def test_the_cells_are_the_cells_of_each_task(self):
        for table, task in TASKS.items():
            want = {m.name_of(*k) for k in m.keys(m.TASKS[task])}
            self.assertEqual(set(it.document(table)["steady"]), want)
        self.assertEqual([len(it.document(t)["steady"]) for t in TASKS],
                         [306, 245, 11])

    def test_the_matrix_takes_the_counts_of_its_originating_tasks(self):
        steady = it.document("matrix")["steady"]
        first = counts("allocation_iterations.json")
        second = counts("allocation_iterations_task30.json")
        self.assertEqual(len(first) + len(second), 306)
        for name, count in first.items():
            self.assertEqual(steady[name], count, name)
        for name, count in second.items():
            self.assertEqual(steady[name], count, name)

    def test_the_client_takes_the_counts_of_task31(self):
        steady = it.document("client")["steady"]
        self.assertEqual(steady, counts("allocation_iterations_task31.json"))
        # the cut stages are kept, not reset by the size rule
        self.assertIn(4, steady.values())
        self.assertIn(8, steady.values())

    def test_the_downstream_cells_take_the_task30_size_rule(self):
        steady = it.document("downstream")["steady"]
        self.assertEqual(
            steady,
            {"downstream_arithmetic-1": 32, "downstream_arithmetic-10": 32,
             "downstream_arithmetic-100": 32,
             "downstream_arithmetic-1000": 16,
             "downstream_arithmetic-10000": 8,
             "downstream_reduce-1": 32, "downstream_reduce-10": 32,
             "downstream_reduce-100": 32, "downstream_reduce-1000": 16,
             "downstream_reduce-10000": 8, "downstream_boss-0": 32})
        self.assertEqual(
            [it.size_rule(n) for n in (0, 1, 100, 1000, 10000)],
            [32, 32, 32, 16, 8])

    def test_the_document_has_the_format_of_the_other_counts_files(self):
        old = a.load(a.HERE / "allocation_iterations_task31.json")
        for table in TASKS:
            doc = it.document(table)
            self.assertEqual(list(doc), list(old))
            self.assertEqual(doc["schema"], old["schema"])
            self.assertEqual(doc["repeats"], old["repeats"])
            self.assertTrue(doc["rule"])
            self.assertEqual(
                it.text(table),
                json.dumps(doc, indent=1, allow_nan=False) + "\n")

    def test_each_file_loads_with_the_allocation_loader(self):
        with tempfile.TemporaryDirectory() as tmp:
            for table, task in TASKS.items():
                path = it.write(table, tmp)
                got = m.load_iterations(path, m.TASKS[task])
                self.assertEqual(got, it.document(table))

    def test_the_rule_covers_the_cases_of_the_task_sets(self):
        self.assertEqual(set(cases.MATRIX_CASES),
                         set(m.TASKS["task29b"].cases) |
                         set(m.TASKS["task30"].cases))
        self.assertEqual(set(cases.CLIENT_CASES), set(m.TASKS["task31"].cases))
        self.assertEqual(
            {m.name_of(*k) for k in m.keys(m.TASKS["task37-downstream"])},
            set(cases.DOWNSTREAM_CELLS))


class Refusals(unittest.TestCase):
    def test_a_cell_without_a_predecessor_count_is_refused(self):
        real = it.predecessor

        def cut(task):
            found, doc = real(task)
            if task == "task30":
                steady = dict(doc["steady"])
                steady.pop(next(iter(steady)))
                doc = dict(doc, steady=steady)
            return found, doc
        with mock.patch.object(it, "predecessor", cut):
            with self.assertRaisesRegex(ValueError,
                                        "no predecessor count"):
                it.document("matrix")
            it.document("client")       # the other tables are unaffected

    def test_a_cell_no_predecessor_owns_is_refused(self):
        real = it.predecessor

        def foreign(task):
            found, doc = real(task)
            if task == "task31":
                found = mock.Mock(cases=("no_such_case",))
            return found, doc
        with mock.patch.object(it, "predecessor", foreign):
            with self.assertRaisesRegex(ValueError,
                                        "no predecessor count"):
                it.document("client")

    def test_predecessors_with_other_repeats_are_refused(self):
        real = it.predecessor

        def other(task):
            found, doc = real(task)
            return found, dict(doc, repeats=doc["repeats"] + 1) \
                if task == "task30" else doc
        with mock.patch.object(it, "predecessor", other):
            with self.assertRaisesRegex(ValueError, "different repeats"):
                it.document("matrix")


class Files(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def run_main(self, *argv):
        err = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(err):
            code = it.main(list(argv) + ["--directory", self.tmp.name])
        return code, err.getvalue()

    def test_all_writes_the_three_files_and_check_accepts_them(self):
        self.assertEqual(self.run_main("all")[0], 0)
        self.assertEqual(len(list(Path(self.tmp.name).iterdir())), 3)
        self.assertEqual(self.run_main("all", "--check"), (0, ""))
        self.assertEqual(self.run_main("all")[0], 0)   # again: unchanged

    def test_check_writes_nothing_and_fails_on_a_missing_file(self):
        code, err = self.run_main("matrix", "--check")
        self.assertEqual(code, 1)
        self.assertIn("is missing", err)
        self.assertEqual(list(Path(self.tmp.name).iterdir()), [])

    def test_check_fails_on_a_different_file(self):
        self.run_main("client")
        path = it.path_of("client", self.tmp.name)
        doc = json.loads(path.read_text())
        name = next(iter(doc["steady"]))
        doc["steady"][name] += 1
        path.write_text(json.dumps(doc, indent=1) + "\n")
        code, err = self.run_main("client", "--check")
        self.assertEqual(code, 1)
        self.assertIn("not the output of the rule", err)
        self.assertEqual(self.run_main("downstream", "--check")[0], 1)

    def test_a_different_file_is_never_overwritten(self):
        path = it.path_of("downstream", self.tmp.name)
        path.write_text("{}\n")
        code, err = self.run_main("downstream")
        self.assertEqual(code, 1)
        self.assertIn("never overwritten", err)
        self.assertEqual(path.read_text(), "{}\n")

    def test_the_committed_files_are_the_rules_output_when_they_exist(self):
        for table in TASKS:
            path = it.path_of(table)
            if path.exists():
                self.assertEqual(it.check(table), [])


if __name__ == "__main__":
    unittest.main()
