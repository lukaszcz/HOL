#!/usr/bin/env python3
"""TASK31 case data (task31_cases.py) and the timing table built on it."""
import subprocess
import unittest

import acceptance as a
import matrix_schema as ms
import task31_cases as c
import task31_grid as g
import timing_grid as tg

REPO = a.HERE.parents[3]


def every():
    return [(case, size) for case in c.CASES for size in
            ms.SIZE_SETS[ms.EXPECTED_CASES[case]["sizes"]]]


class Cases(unittest.TestCase):
    def test_the_cases_are_the_traversal_and_tactic_cases(self):
        self.assertEqual(len(c.TRAVERSAL), 11)
        self.assertEqual(len(c.TACTICS), 42)
        self.assertEqual(len(c.CASES), 53)
        self.assertTrue(all(x.startswith(("traversal_", "tactic_"))
                            for x in c.CASES))
        self.assertFalse([x for x in ms.EXPECTED_CASES
                          if x.startswith(("traversal_", "tactic_"))
                          and x not in c.CASES])
        self.assertEqual(len(every()), 278)

    def test_the_sample_is_28_cells_of_the_cases(self):
        names = {g.name_of(*k) for k in every()}
        self.assertEqual(len(c.SAMPLE), 28)
        self.assertEqual(len(set(c.SAMPLE)), 28)
        self.assertLessEqual(set(c.SAMPLE), names)
        got = {tuple(x.rsplit("-", 1)) for x in c.SAMPLE}
        self.assertEqual({s for k, s in got if k in c.TRAVERSAL_SINGLETON},
                         {"0"})
        self.assertEqual({s for k, s in got if k in c.TRAVERSAL_DEPTH},
                         {"100"})
        self.assertEqual(sum(k.endswith("_complete") and s == "100"
                             for k, s in got), 14)
        self.assertIn("tactic_installed_reuse-1000", c.SAMPLE)

    def test_the_infeasible_cells_are_the_heavy_size_10000_ones(self):
        names = {g.name_of(*k) for k in every()}
        self.assertEqual(len(c.INFEASIBLE), 33)
        self.assertLessEqual(set(c.INFEASIBLE), names)
        self.assertTrue(all(x.endswith("-10000") for x in c.INFEASIBLE))
        self.assertFalse(set(c.INFEASIBLE) & set(c.SAMPLE))
        self.assertEqual(set(c.INFEASIBLE_COST), set(c.INFEASIBLE))
        for x in c.INFEASIBLE:
            self.assertIn(x.rsplit("-", 1)[0] + "-0", names)
            self.assertNotIn(g.anchor(x), c.INFEASIBLE)
        self.assertEqual(len(c.FEASIBLE_10000), 9)

    def test_no_sampled_operation_is_long_against_the_batch(self):
        self.assertEqual(set(c.SURVEY_SAMPLE), set(c.SAMPLE))
        for name, (op, setup, check) in c.SURVEY_SAMPLE.items():
            self.assertLess(op, g.SECONDS / 2, name)
            self.assertLess(setup + check, c.PROCESS_TIMEOUT, name)

    def test_the_infeasible_costs_are_nonnegative_and_grow_with_size(self):
        for name, cost in c.INFEASIBLE_COST.items():
            self.assertEqual(len(cost), 6, name)
            self.assertTrue(all(x >= 0 for x in cost), name)
            self.assertGreaterEqual(cost[4], cost[1], name)

    def test_the_sources_are_tracked_files_present_at_the_baseline(self):
        self.assertEqual(list(c.SOURCES), sorted(set(c.SOURCES)))
        for path in c.SOURCES:
            self.assertIsNotNone(tg.git_blob(REPO, a.BASE, path), path)

    def test_the_heap_sources_are_among_the_sources(self):
        self.assertLessEqual(set(c.HEAP), set(c.SOURCES))
        self.assertEqual(len(c.HEAP), 16)


class Table(unittest.TestCase):
    def test_the_table_is_the_sample_under_the_warmup_schedule(self):
        t = g.TABLE
        self.assertEqual(sorted(t.names()), sorted(c.SAMPLE))
        self.assertEqual((t.schedule, t.headroom, t.pairs, t.samples),
                         ("warmup", 1, 20, 5))
        self.assertTrue(t.fixed_seconds)
        self.assertEqual(t.baseline, a.BASE)
        self.assertEqual(t.seconds_map(), {n: 0.3 for n in c.SAMPLE})
        self.assertEqual(t.seed, "task31-layout-1")
        self.assertEqual(t.family, "task31")
        self.assertIsNone(t.replaces)

    def test_the_equivalence_policy_and_second_stage_are_task30s(self):
        import task30_grid
        t = g.TABLE
        self.assertEqual((t.target, t.max_pairs),
                         (task30_grid.TABLE.target,
                          task30_grid.TABLE.max_pairs))

    def test_every_sealed_file_exists(self):
        for name in g.SEALED:
            self.assertTrue((a.HERE / name).is_file(), name)

    def test_the_installed_files_are_what_the_runner_installs(self):
        paired = {p.name for p in g.PAIRED.iterdir()
                  if p.suffix == ".sml" or p.name == "Holmakefile"}
        listed = {n.rsplit("/", 1)[1] for n in g.INSTALLED
                  if "/paired/" in n}
        self.assertEqual(paired, listed)

    def test_no_source_files_are_demanded_identical_for_timing(self):
        self.assertEqual(g.TABLE.sources, ())
        self.assertEqual(g.TABLE.tree, "src")

    def test_no_line_has_tabs_trailing_blanks_or_80_columns(self):
        for name in ("task31_cases.py", "task31_grid.py",
                     "task31_identity.py", "task31_snapshot.py",
                     "task31_dispose.py"):
            for i, line in enumerate((a.HERE / name).read_text()
                                     .split("\n"), 1):
                where = "%s:%d" % (name, i)
                self.assertNotIn("\t", line, where)
                self.assertEqual(line, line.rstrip(), where)
                self.assertLess(len(line), 80, where)


if __name__ == "__main__":
    unittest.main()
