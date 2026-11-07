#!/usr/bin/env python3
"""The TASK31 follow-up table (task31_followup.py)."""
import contextlib
import io
import unittest

import task31_cases as c
import task31_followup as f
import task31_grid as g
import timing_grid as tg

CELLS = ["traversal_construct-0", "tactic_full_complete-100"]


class Follow(unittest.TestCase):
    def test_no_follow_up_is_declared_and_every_command_is_refused(self):
        self.assertEqual(f.CELLS, ())
        self.assertIsNone(f.ENGINE)
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            self.assertEqual(f.main(["replay"]), tg.REFUSED)
        self.assertIn("REFUSED", err.getvalue())

    def test_a_follow_up_table_replaces_cells_of_the_first_grid(self):
        t = f.table(CELLS)
        self.assertEqual(sorted(t.names()), sorted(CELLS))
        self.assertEqual(t.pairs, 2 * g.PAIRS)
        self.assertEqual((t.family, t.baseline, t.samples, t.schedule),
                         ("task31", g.TABLE.baseline, g.SAMPLES, "warmup"))
        self.assertNotEqual(t.seed, g.TABLE.seed)
        self.assertEqual(t.sources, g.TABLE.sources)
        self.assertEqual(t.pinned, g.TABLE.pinned)
        self.assertEqual(t.pin_file, g.TABLE.pin_file)
        self.assertIsNotNone(t.replaces)
        self.assertEqual(t.seconds_map(), {
            "traversal_construct-0": g.LONG_SECONDS,
            "tactic_full_complete-100": g.SECONDS})
        self.assertTrue(set(CELLS) <= set(c.SAMPLE))

    def test_the_follow_up_seals_the_first_grids_driver(self):
        self.assertIn("task31_grid.py", f.SEALED)
        self.assertEqual(f.SEALED[:len(g.SEALED)], g.SEALED)

    def test_the_counts_file_is_not_the_first_grids(self):
        self.assertNotEqual(f.COUNTS, g.COUNTS)

    def test_the_follow_up_engine_is_constructed_from_a_table(self):
        engine = tg.Grid(f.table(CELLS), doc=f.__doc__)
        self.assertEqual(sorted(engine.t.names()), sorted(CELLS))


if __name__ == "__main__":
    unittest.main()
