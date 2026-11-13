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


def imports(name):
    """The modules a file of the harness imports (top level or not)."""
    tree = ast.parse((a.HERE / name).read_text())
    found = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            found.update(n.name for n in node.names)
        elif isinstance(node, ast.ImportFrom):
            found.add(node.module)
    return found


class Driver(unittest.TestCase):
    def test_it_does_not_import_the_identity_gate(self):
        found = imports("task31_grid.py")
        self.assertFalse({n for n in found if "identity" in n or
                          "attribution" in n}, found)
        self.assertIn("task31_pins", found)

    def test_no_identity_file_is_sealed_into_a_timing_grid(self):
        sealed = set(timing.SEALED) | {timing.__name__ + ".py"}
        for name in ("task31_identity_grid.py", "task31_identity.py",
                     "task31_attribution.py", "task31_attributed.json",
                     "task31_snapshot.py"):
            self.assertNotIn(name, sealed)
        self.assertNotIn(timing.reviewed.FILE.name, timing.SEALED)

    def test_the_code_that_computes_the_pins_is_sealed_in_the_timing_grid(
            self):
        self.assertIn("task31_pins.py", timing.SEALED)
        self.assertIn("task31_pins.py", timing.TABLE.sealed)
        import task31_followup as follow
        self.assertIn("task31_pins.py", follow.SEALED)
        self.assertEqual(timing.TABLE.pinned, timing.reviewed.pins(
            timing.ATTRIBUTED["entries"], timing.SOURCES))
        # ... and it stands on nothing else of the harness but the
        # acceptance module, which the table seals as its own.
        self.assertEqual({m for m in imports("task31_pins.py")
                          if (a.HERE / (m + ".py")).exists()},
                         {"acceptance"})

    def test_the_driver_history_names_the_seals_of_the_kept_grids(self):
        # Only the change that made a private script's theory private
        # (client_dependencies.py) was made after the first record: its old
        # seal and this driver's are the history; nothing else is.
        self.assertEqual((timing.ENGINES, timing.ACCEPTANCE), ((), ()))
        self.assertEqual(len(timing.DRIVERS), 1)
        self.assertEqual(set(timing.SEALED_HISTORY),
                         {"client_dependencies.py"})
        self.assertEqual(
            {k: len(v) for k, v in timing.SEALED_HISTORY.items()},
            {"client_dependencies.py": 1})
        self.assertEqual(timing.TABLE.drivers, timing.DRIVERS)
        self.assertEqual(timing.TABLE.engines, timing.ENGINES)
        self.assertEqual(timing.TABLE.sealed_history,
                         {k: tuple(v)
                          for k, v in timing.SEALED_HISTORY.items()})


if __name__ == "__main__":
    unittest.main()
