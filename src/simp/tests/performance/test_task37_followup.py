#!/usr/bin/env python3
"""The TASK37 follow-up tables (task37_followup.py): the table of a shard's
follow-up, the engines by table name, and that declaring one is apart from
the shard drivers' seals."""
import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import acceptance as a
import import_closure as ic
import task37_followup as f
import task37_grid as g
import timing_grid as tg


class Declaration(unittest.TestCase):
    def test_none_is_declared_yet(self):
        self.assertEqual(f.CELLS, {})
        self.assertEqual((f.TABLES, f.GRIDS), ({}, {}))
        self.assertIsNone(f.declare("matrix-1", ()))
        self.assertEqual(f.commands(), {})

    def test_a_follow_up_is_a_valid_replacing_table(self):
        key = "matrix-2"
        cells = g.PARTS[key][:2]
        replaced = g.GRIDS["task37-" + key]
        t = f.table(key, cells, replaced)
        self.assertEqual(t.name, "task37-matrix-2-followup")
        self.assertEqual(t.family, "task37-matrix-2")
        self.assertEqual(t.pairs, 2 * g.PAIRS)
        self.assertEqual(set(t.names()), set(cells))
        self.assertEqual(t.counts.name,
                         "task37_matrix_2_followup_iterations.json")
        self.assertEqual(t.counts, f.file_of(key))
        self.assertNotIn(t.counts, [x.counts for x in g.TABLES.values()])
        self.assertNotIn(t.seed, [x.seed for x in g.TABLES.values()])
        self.assertIs(t.replaces.engine, replaced)
        first = g.TABLES["task37-" + key]
        self.assertEqual((t.sources, t.pinned, t.pin_file),
                         (first.sources, first.pinned, first.pin_file))
        self.assertEqual((t.samples, t.schedule, t.baseline),
                         (first.samples, first.schedule, first.baseline))
        self.assertEqual(
            t.sealed, f.SEALED[key] + (f.declaration_file(key).name,))
        self.assertIn("task37_grid.py", t.sealed)
        self.assertNotIn("task37_sources.py", t.sealed)

    def test_the_long_batch_cases_keep_their_seconds(self):
        key = "matrix-1"
        cells = [x for x in g.PARTS[key] if g.cases.split(x)[0]
                 in g.LONG["matrix"]][:1] or g.PARTS[key][:1]
        t = f.table(key, cells, g.GRIDS["task37-" + key])
        self.assertEqual(set(t.seconds_by_case),
                         set(t.cases) & set(g.LONG["matrix"]))

    def test_a_follow_up_of_a_cell_outside_its_shard_is_refused(self):
        other = g.PARTS["matrix-3"][0]
        with self.assertRaises(ValueError):
            f.table("matrix-2", (other,), g.GRIDS["task37-matrix-2"])
        with self.assertRaises(ValueError):
            f.table("matrix-2", (), g.GRIDS["task37-matrix-2"])

    def test_declared_cells_give_an_engine_by_table_name(self):
        key = "client-1"
        cells = g.PARTS[key][:1]
        built, engine = f.declare(key, cells)
        self.assertEqual(built.name, "task37-client-1-followup")
        self.assertIsInstance(engine, tg.Grid)
        with mock.patch.dict(f.GRIDS, {built.name: engine}):
            self.assertEqual(f.commands(), {"client-1": engine})
            with mock.patch.object(engine, "main", return_value=5) as run:
                self.assertEqual(f.main(["client-1", "pilot", "--x"]), 5)
            run.assert_called_once_with(["pilot", "--x"])
        self.assertEqual(f.GRIDS, {})

    def test_the_table_name_of_a_shards_follow_up(self):
        built, _ = f.declare("matrix-4", g.PARTS["matrix-4"][:1])
        self.assertEqual(built.name, f.name_of("matrix-4"))
        self.assertEqual(f.name_of("matrix-4"), "task37-matrix-4-followup")

    def test_every_command_is_refused_while_none_is_declared(self):
        for argv in ([], ["matrix-1", "run"], ["matrix-1-followup", "run"]):
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                self.assertEqual(f.main(argv), tg.REFUSED, argv)
            self.assertIn("no such TASK37 follow-up", err.getvalue())

    def test_the_names_do_not_clash_with_the_shards(self):
        for key in g.SHARD_KEYS:
            self.assertNotIn(f.name_of(key), g.GRIDS)
            self.assertNotEqual(f.file_of(key), g.file_of(key))
            self.assertTrue(f.file_of(key).parent == a.HERE)


def declare_in(root, key, cells, more=None):
    path = Path(root) / f.declaration_file(key).name
    doc = dict(schema=f.SCHEMA, shard=key, cells=list(cells))
    doc.update(more or {})
    path.write_text(json.dumps(doc))
    return path


class Declarations(unittest.TestCase):
    def test_a_declaration_file_gives_the_cells(self):
        with tempfile.TemporaryDirectory() as root:
            cells = g.PARTS["matrix-2"][:2]
            path = declare_in(root, "matrix-2", cells)
            self.assertEqual(path.name,
                             "task37_matrix_2_followup_cells.json")
            self.assertEqual(f.load_declaration("matrix-2", path),
                             tuple(cells))

    def test_declaring_another_shard_changes_no_seal_of_an_earlier_one(
            self):
        first = f.table("matrix-1", g.PARTS["matrix-1"][:1],
                        g.GRIDS["task37-matrix-1"])
        before = (first.driver, first.sealed)
        with tempfile.TemporaryDirectory() as root:
            declare_in(root, "matrix-3", g.PARTS["matrix-3"][:1])
            second = f.table("matrix-3", g.PARTS["matrix-3"][:1],
                             g.GRIDS["task37-matrix-3"])
        again = f.table("matrix-1", g.PARTS["matrix-1"][:1],
                        g.GRIDS["task37-matrix-1"])
        self.assertEqual((again.driver, again.sealed), before)
        self.assertEqual(first.driver, second.driver)
        self.assertIn("task37_matrix_1_followup_cells.json", first.sealed)
        self.assertNotIn("task37_matrix_3_followup_cells.json",
                         first.sealed)
        self.assertNotIn("task37_matrix_1_followup_cells.json",
                         second.sealed)

    def test_the_driver_does_not_hold_a_declaration(self):
        text = Path(f.__file__).read_text()
        for key in g.SHARD_KEYS:
            self.assertNotIn(g.PARTS[key][0], text)

    def test_malformed_or_mismatched_files_are_refused(self):
        key, cells = "matrix-2", list(g.PARTS["matrix-2"][:2])
        with tempfile.TemporaryDirectory() as root:
            for bad in (
                    dict(cells=[]), dict(cells=[g.PARTS["matrix-3"][0]]),
                    dict(cells=cells + cells[:1]), dict(cells="x"),
                    dict(shard="matrix-3"), dict(schema="other"),
                    dict(extra=1)):
                path = declare_in(root, key, cells, bad)
                with self.assertRaises(ValueError, msg=bad):
                    f.load_declaration(key, path)
            path = Path(root) / "x.json"
            path.write_text("[]")
            with self.assertRaises(ValueError):
                f.load_declaration(key, path)
            with self.assertRaises(ValueError):
                f.load_declaration("matrix-9", path)

    def test_declared_discovers_the_files_that_exist(self):
        with tempfile.TemporaryDirectory() as root:
            declare_in(root, "client-1", g.PARTS["client-1"][:1])
            with mock.patch.object(f, "declaration_file", lambda k: Path(
                    root) / ("task37_%s_%s_followup_cells.json" % tuple(
                        k.split("-")))):
                self.assertEqual(f.declared(),
                                 {"client-1": (g.PARTS["client-1"][0],)})


class Apart(unittest.TestCase):
    def test_the_shard_drivers_do_not_import_it(self):
        sources = ic.sources()
        for name in ("task37_grid", "task37_cases"):
            self.assertNotIn("task37_followup", {
                e[1] for e in ic.edges(sources, name)}, name)

    def test_the_follow_up_is_not_in_a_shard_seal(self):
        for key, sealed in g.SEALED.items():
            self.assertNotIn("task37_followup.py", sealed, key)


if __name__ == "__main__":
    unittest.main()
