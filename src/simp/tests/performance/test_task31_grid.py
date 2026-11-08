#!/usr/bin/env python3
"""The TASK31 timing driver (task31_grid.py): its table, the pins it takes
from the reviewed table, and its independence of the identity gate."""
import ast
import unittest

import acceptance as a
import task31_attribution as attr
import task31_cases as c
import task31_grid as timing
import timing_grid as tg

OLD = "a" * 64


def entry(path, blob="2" * 40, kind="source"):
    return dict(path=path, kind=kind, baseline_blob="1" * 40,
                candidate_blob=blob, reason="why", gate="gate 2")


def document(entries, history=None):
    return dict(entries=entries, history=history or {})


class Table(unittest.TestCase):
    def test_the_sources_are_the_cells_closure(self):
        self.assertEqual(timing.TABLE.sources, tuple(sorted(c.SOURCES)))
        self.assertEqual(timing.SOURCES, c.SOURCES)

    def test_the_pins_are_those_of_the_sources_only(self):
        source = "src/simp/src/Cond_rewr.sig"
        self.assertIn(source, c.SOURCES)
        entries = [entry(source), entry("src/1/ThmAttribute.sig",
                                        kind="heap"),
                   entry("tools/sequences/base-hol", kind="build")]
        table = timing.table(document(entries))
        self.assertEqual(set(table.pinned), {source})

    def test_adding_an_attribution_entry_leaves_a_timing_grid_replayable(self):
        source = "src/simp/src/Cond_rewr.sig"
        before = [entry(source)]
        after = before + [entry("tools/sequences/base-hol", kind="build"),
                          entry("src/1/ThmAttribute.sig", kind="heap")]
        made = timing.table(document(before))
        # The file now has another seal, which the history keeps; a grid
        # made by the earlier file is judged by the pins it had.
        grown = tg.Grid(timing.table(document(after, {OLD: before})))
        code = dict(pins=dict(bytes=1, sha256=OLD))
        self.assertEqual(grown.pins_for(code), made.pinned)
        self.assertEqual(grown.t.pinned, made.pinned)
        self.assertEqual(grown.t.sources, made.sources)

    def test_a_pin_changed_in_the_sources_is_not_the_earlier_one(self):
        source = "src/simp/src/Cond_rewr.sig"
        before = [entry(source)]
        after = [entry(source, blob="3" * 40)]
        grown = tg.Grid(timing.table(document(after, {OLD: before})))
        found = grown.pins_for(dict(pins=dict(bytes=1, sha256=OLD)))
        self.assertNotEqual(found, grown.t.pinned)
        with self.assertRaises(ValueError):
            grown.pins_for(dict(pins=dict(bytes=1, sha256="b" * 64)))


class Driver(unittest.TestCase):
    def test_it_does_not_import_the_identity_gate(self):
        tree = ast.parse((a.HERE / "task31_grid.py").read_text())
        found = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                found.update(n.name for n in node.names)
            elif isinstance(node, ast.ImportFrom):
                found.add(node.module)
        self.assertFalse({n for n in found if "identity" in n}, found)

    def test_no_identity_file_is_sealed_into_a_timing_grid(self):
        sealed = set(timing.SEALED) | {timing.__name__ + ".py"}
        for name in ("task31_identity_grid.py", "task31_identity.py",
                     "task31_attribution.py", "task31_attributed.json"):
            self.assertNotIn(name, sealed)
        self.assertNotIn(timing.attr.FILE.name, timing.SEALED)

    def test_the_driver_history_is_empty_until_a_grid_is_recorded(self):
        self.assertEqual(
            (timing.DRIVERS, timing.ENGINES, timing.ACCEPTANCE,
             timing.SEALED_HISTORY), ((), (), (), {}))
        self.assertEqual(timing.TABLE.drivers, timing.DRIVERS)
        self.assertEqual(timing.TABLE.engines, timing.ENGINES)


if __name__ == "__main__":
    unittest.main()
