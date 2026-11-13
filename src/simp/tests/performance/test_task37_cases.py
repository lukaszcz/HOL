#!/usr/bin/env python3
"""The TASK37 cell sets (task37_cases.py): exact counts, derivation and the
presence of every cell the design names."""
import subprocess
import unittest

import acceptance as a
import task30_dispose
import task30_cases
import task31_cases
import task31_followup
import task37_cases as c

FINAL = "7e202dfbaa"


class Counts(unittest.TestCase):
    def test_the_matrix_is_the_task29_and_task30_cases_at_six_sizes(self):
        self.assertEqual(len(c.MATRIX_CASES), 27 + 24)
        self.assertEqual(len(c.MATRIX_CELLS), 306)
        self.assertEqual(len(set(c.MATRIX_CELLS)), 306)
        self.assertEqual(sum(1 for x in c.MATRIX_CELLS
                             if c.split(x)[0] in task30_cases.CASES), 144)

    def test_the_client_cells_are_those_of_task31(self):
        self.assertEqual(len(c.CLIENT_CELLS), 278)

    def test_the_downstream_cells_are_eleven(self):
        self.assertEqual(len(c.DOWNSTREAM_CELLS), 11)
        self.assertEqual(
            [x for x in c.DOWNSTREAM_CELLS if x.endswith("-0")],
            ["downstream_boss-0"])
        self.assertEqual(sum(x.startswith("downstream_arithmetic-")
                             for x in c.DOWNSTREAM_CELLS), 5)

    def test_the_samples(self):
        self.assertEqual(len(c.MATRIX_SAMPLE_BASE), 51)
        self.assertEqual(len(c.D4), 31)
        self.assertEqual(len(c.MATRIX_SAMPLE), 87)
        self.assertEqual(len(c.CLIENT_SAMPLE), 28 + 11)
        self.assertEqual(len(c.CLIENT_SAMPLE_CASES), 26 + 3)


class Derivation(unittest.TestCase):
    def test_every_matrix_case_is_sampled_at_1000(self):
        for case in c.MATRIX_CASES:
            self.assertIn("%s-1000" % case, c.MATRIX_SAMPLE)

    def test_the_nearest_size_at_or_below(self):
        self.assertEqual(c.at_or_below("frag_create"), 1000)
        self.assertEqual(c.at_or_below("frag_create", 50), 10)
        self.assertEqual(c.at_or_below("traversal_deep"), 100)
        self.assertEqual(c.at_or_below("traversal_construct"), 0)
        self.assertEqual(c.at_or_below("downstream_arithmetic", 0), 1)

    def test_every_flagged_and_d4_cell_is_sampled_and_in_the_matrix(self):
        self.assertEqual(len(c.FLAGGED), 11)
        self.assertEqual(len(c.CONTROL_LIMITED), 13)
        self.assertEqual(len(c.ATTRIBUTED), 13)
        self.assertEqual(len(c.ATTRIBUTED_29A), 5)
        for cell in c.FLAGGED + c.D4:
            self.assertIn(cell, c.MATRIX_CELLS)
            self.assertIn(cell, c.MATRIX_SAMPLE)

    def test_the_sample_is_in_matrix_order_without_repeats(self):
        order = {x: i for i, x in enumerate(c.MATRIX_CELLS)}
        self.assertEqual(list(c.MATRIX_SAMPLE),
                         sorted(set(c.MATRIX_SAMPLE), key=order.get))

    def test_the_task30_list_is_the_disposition_of_task30(self):
        self.assertEqual(sorted(c.ATTRIBUTED),
                         sorted(task30_dispose.DISPOSITION["attributed"]))

    def test_the_client_sample_is_the_task31_sample_and_downstream(self):
        self.assertEqual(set(c.CLIENT_SAMPLE),
                         set(task31_cases.SAMPLE) | set(c.DOWNSTREAM_CELLS))
        self.assertTrue(set(task31_followup.CELLS) <=
                        set(task31_cases.SAMPLE))
        self.assertTrue(set(c.CLIENT_SAMPLE) <= set(c.CLIENT_CELLS) |
                        set(c.DOWNSTREAM_CELLS))

    def test_every_cell_name_splits_to_a_known_cell(self):
        for cell in c.MATRIX_SAMPLE + c.CLIENT_SAMPLE:
            case, size = c.split(cell)
            self.assertIn(size, c.sizes(case))

    def test_the_fixtures(self):
        for case in c.MATRIX_CASES:
            self.assertEqual(c.ms.EXPECTED_CASES[case]["fixture"],
                             "MatrixPerformance.sml")
        for case in c.CLIENT_CASES + c.DOWNSTREAM_CASES:
            self.assertEqual(c.ms.EXPECTED_CASES[case]["fixture"],
                             "ClientPerformance.sml")

    def test_an_unknown_case_is_refused(self):
        with self.assertRaises(KeyError):
            c.sizes("no_such_case")


class Sources(unittest.TestCase):
    def test_the_deleted_files_are_not_sources(self):
        for path in c.DELETED_SOURCES:
            self.assertIn(path, task30_cases.SOURCES)
            self.assertNotIn(path, c.MATRIX_SOURCES)
        self.assertEqual(len(c.MATRIX_SOURCES),
                         len(task30_cases.SOURCES) - 2)

    def test_the_sources_exist_at_the_final_candidate(self):
        root = a.HERE.parents[3]
        found = subprocess.run(
            ["git", "-C", str(root), "cat-file", "-t", FINAL],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        if found.returncode:
            self.skipTest("the final candidate is not in this clone")
        for path in c.MATRIX_SOURCES + c.CLIENT_SOURCES:
            kind = subprocess.run(
                ["git", "-C", str(root), "cat-file", "-t",
                 "%s:%s" % (FINAL, path)], stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, text=True).stdout.strip()
            self.assertEqual(kind, "blob", path)


class Style(unittest.TestCase):
    def test_no_tabs_trailing_blanks_or_80_columns(self):
        for name in ("task37_cases.py", "task37_grid.py", "task37_load.py"):
            for i, line in enumerate((a.HERE / name).read_text()
                                     .split("\n"), 1):
                where = "%s:%d" % (name, i)
                self.assertNotIn("\t", line, where)
                self.assertEqual(line, line.rstrip(), where)
                self.assertLess(len(line), 80, where)


if __name__ == "__main__":
    unittest.main()
