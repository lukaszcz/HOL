#!/usr/bin/env python3
"""TASK31 case data (task31_cases.py) and the timing table built on it."""
import subprocess
import unittest

import acceptance as a
import matrix_schema as ms
import task31_cases as c
import task31_grid as g
import task31_identity_grid as ig
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
        names = {ig.name_of(*k) for k in every()}
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
        names = {ig.name_of(*k) for k in every()}
        self.assertEqual(len(c.INFEASIBLE), 33)
        self.assertLessEqual(set(c.INFEASIBLE), names)
        self.assertTrue(all(x.endswith("-10000") for x in c.INFEASIBLE))
        self.assertFalse(set(c.INFEASIBLE) & set(c.SAMPLE))
        for x in c.INFEASIBLE:
            self.assertIn(x.rsplit("-", 1)[0] + "-0", names)
            self.assertNotIn(ig.anchor(x), c.INFEASIBLE)

    def test_the_sources_are_tracked_files_present_at_the_baseline(self):
        self.assertEqual(list(c.SOURCES), sorted(set(c.SOURCES)))
        for path in c.SOURCES:
            self.assertIsNotNone(tg.git_blob(REPO, a.BASE, path), path)


class Table(unittest.TestCase):
    def test_the_table_is_the_sample_under_the_warmup_schedule(self):
        t = g.TABLE
        self.assertEqual(sorted(t.names()), sorted(c.SAMPLE))
        self.assertEqual((t.schedule, t.headroom, t.pairs, t.samples),
                         ("warmup", 1, 20, 5))
        self.assertTrue(t.fixed_seconds)
        self.assertEqual(t.baseline, a.BASE)
        self.assertEqual(t.seconds_map(), {
            n: g.LONG_SECONDS if n.endswith("-0") and
            n.startswith("traversal_") else g.SECONDS for n in c.SAMPLE})
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

    def test_the_elaborated_sources_are_the_timing_tables_sources(self):
        self.assertEqual(g.TABLE.sources, tuple(sorted(c.SOURCES)))
        self.assertEqual(g.TABLE.tree, "src")

    def test_the_cases_hold_no_cost_numbers_or_narrative(self):
        for word in ("COST", "SURVEY", "HEAP ="):
            self.assertNotIn(word, (a.HERE / "task31_cases.py").read_text())

    def test_no_line_has_tabs_trailing_blanks_or_80_columns(self):
        for name in ("task31_cases.py", "task31_grid.py",
                     "task31_identity_grid.py", "void_attempts.py",
                     "task31_identity.py", "task31_snapshot.py",
                     "task31_dispose.py", "task31_attribution.py",
                     "task31_followup.py"):
            for i, line in enumerate((a.HERE / name).read_text()
                                     .split("\n"), 1):
                where = "%s:%d" % (name, i)
                self.assertNotIn("\t", line, where)
                self.assertEqual(line, line.rstrip(), where)
                self.assertLess(len(line), 80, where)


if __name__ == "__main__":
    unittest.main()
