#!/usr/bin/env python3
"""The TASK37 follow-up tables (task37_followup.py): the table of a shard's
follow-up, the engines by table name, and that declaring one is apart from
the shard drivers' seals."""
import contextlib
import io
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import acceptance as a
import import_closure as ic
import task37_followup as f
import task37_grid as g
import test_task37_grid as tgrid
import timing_grid as tg


class Declaration(unittest.TestCase):
    def test_the_engines_are_those_of_the_declaration_files(self):
        self.assertEqual(f.CELLS, f.declared())
        self.assertEqual(set(f.GRIDS),
                         {f.name_of(k) for k in f.CELLS})
        self.assertEqual(set(f.TABLES), set(f.GRIDS))
        for key, cells in f.CELLS.items():
            self.assertEqual(set(f.TABLES[f.name_of(key)].names()),
                             set(cells))
        self.assertEqual(set(f.commands()), set(f.CELLS))
        self.assertIsNone(f.declare("matrix-1", ()))

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
        before = dict(f.GRIDS)
        with mock.patch.dict(f.GRIDS, {built.name: engine}, clear=True):
            self.assertEqual(f.commands(), {"client-1": engine})
            with mock.patch.object(engine, "main", return_value=5) as run:
                self.assertEqual(f.main(["client-1", "pilot", "--x"]), 5)
            run.assert_called_once_with(["pilot", "--x"])
        self.assertEqual(f.GRIDS, before)

    def test_the_table_name_of_a_shards_follow_up(self):
        built, _ = f.declare("matrix-4", g.PARTS["matrix-4"][:1])
        self.assertEqual(built.name, f.name_of("matrix-4"))
        self.assertEqual(f.name_of("matrix-4"), "task37-matrix-4-followup")

    def test_every_command_is_refused_where_none_is_declared(self):
        for argv in ([], ["matrix-1", "run"], ["matrix-1-followup", "run"]):
            err = io.StringIO()
            with mock.patch.dict(f.GRIDS, {}, clear=True), \
                    contextlib.redirect_stderr(err):
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


class Counts(unittest.TestCase):
    """The counts files of a follow-up are checked like a shard's."""

    def test_a_follow_up_counts_file_that_exists_is_a_valid_one(self):
        found = [(t, p) for t in f.TABLES.values() for p in t.files()
                 if p.exists()]
        if not found:
            self.skipTest("no follow-up is declared yet: its counts are "
                          "made and committed by its measurement stage")
        for t, path in found:
            self.assertEqual(tgrid.counts_problems(t, a.load(path)), [],
                             path)

    def test_the_check_finds_what_is_wrong_with_a_follow_up_file(self):
        key = "matrix-2"
        cells = g.PARTS[key][:2]
        t = f.table(key, cells, g.GRIDS["task37-" + key])
        good = dict(iterations={c: 4 for c in cells},
                    seconds=t.seconds_map())
        self.assertEqual(tgrid.counts_problems(t, good), [])
        # the shard's whole part is no follow-up's cell set
        whole = dict(good, iterations={c: 4 for c in g.PARTS[key]})
        self.assertTrue(tgrid.counts_problems(t, whole))
        self.assertTrue(tgrid.counts_problems(
            t, dict(good, iterations={cells[0]: 4})))
        self.assertTrue(tgrid.counts_problems(t, dict(good, seconds={})))
        self.assertTrue(tgrid.counts_problems(
            t, dict(good, iterations={c: 0 for c in cells})))


class Ordering(unittest.TestCase):
    """The declaration precedes the follow-up's counts (a real repository)."""

    KEY = "matrix-2"

    def git(self, *args):
        return subprocess.run(
            ["git", "-C", str(self.repo), "-c", "user.name=t", "-c",
             "user.email=t@t", *args], check=True, text=True,
            stdout=subprocess.PIPE).stdout.strip()

    def commit(self, **files):
        for name, text in files.items():
            (self.repo / name).write_text(text)
        self.git("add", "-A")
        self.git("commit", "-qm", "c")
        return self.git("rev-parse", "HEAD")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name).resolve()
        self.git("init", "-q", ".")
        self.decl = self.repo / "decl.json"
        patch = mock.patch.object(f, "declaration_file",
                                  lambda key: self.decl)
        patch.start()
        self.addCleanup(patch.stop)

    def check(self, candidate, counts):
        f.check_declaration_order(self.repo, candidate, self.KEY, counts)

    def test_a_declaration_committed_alone_before_the_counts_is_accepted(
            self):
        first = self.commit(**{"decl.json": "{}"})
        counts = self.commit(**{"counts.json": "1"})
        later = self.commit(**{"other.txt": "x"})
        self.check(later, counts)
        self.check(counts, counts)

    def test_a_declaration_after_the_counts_is_refused(self):
        counts = self.commit(**{"counts.json": "1"})
        late = self.commit(**{"decl.json": "{}"})
        with self.assertRaisesRegex(ValueError, "not an ancestor"):
            self.check(late, counts)

    def test_a_declaration_in_the_counts_commit_is_refused(self):
        both = self.commit(**{"decl.json": "{}", "counts.json": "1"})
        with self.assertRaisesRegex(ValueError, "change only that file"):
            self.check(both, both)

    def test_a_declaration_committed_with_other_files_is_refused(self):
        self.commit(**{"decl.json": "{}", "other.txt": "x"})
        counts = self.commit(**{"counts.json": "1"})
        with self.assertRaisesRegex(ValueError, "change only that file"):
            self.check(counts, counts)

    def test_an_uncommitted_edited_or_recommitted_file_is_refused(self):
        counts = self.commit(**{"counts.json": "1"})
        self.decl.write_text("{}")
        with self.assertRaises(ValueError):          # not committed
            self.check(counts, counts)
        decl = self.commit(**{"decl.json": "{}"})
        self.decl.write_text('{"edited": 1}')
        with self.assertRaisesRegex(ValueError, "not the committed one"):
            self.check(decl, decl)
        self.decl.write_text("{}")
        again = self.commit(**{"decl.json": '{"cells": []}'})
        with self.assertRaisesRegex(ValueError, "exactly one commit"):
            self.check(again, again)

    def test_the_declaration_precedes_the_pilot_head(self):
        decl = self.commit(**{"decl.json": "{}"})
        head = self.commit(**{"other.txt": "x"})
        f.check_declaration_at_pilot(self.repo, self.KEY, head)
        f.check_declaration_at_pilot(self.repo, self.KEY, decl)

    def test_a_declaration_after_the_pilot_head_is_refused(self):
        head = self.commit(**{"other.txt": "x"})
        self.commit(**{"decl.json": "{}"})
        with self.assertRaisesRegex(ValueError, "not committed in the"):
            f.check_declaration_at_pilot(self.repo, self.KEY, head)

    def test_an_untracked_or_uncommitted_declaration_is_refused_at_pilot(
            self):
        head = self.commit(**{"other.txt": "x"})
        self.decl.write_text("{}")                   # untracked
        with self.assertRaisesRegex(ValueError, "not committed"):
            f.check_declaration_at_pilot(self.repo, self.KEY, head)
        self.git("add", "decl.json")                 # staged only
        with self.assertRaisesRegex(ValueError, "not committed"):
            f.check_declaration_at_pilot(self.repo, self.KEY, head)
        head = self.commit()
        self.decl.write_text('{"edited": 1}')        # edited after commit
        with self.assertRaisesRegex(ValueError, "not the committed one"):
            f.check_declaration_at_pilot(self.repo, self.KEY, head)

    def test_the_engine_pilot_and_inventory_check_the_declaration(self):
        built, engine = f.declare(self.KEY, g.PARTS[self.KEY][:1])
        with mock.patch.object(f, "check_declaration_at_pilot") as check, \
                mock.patch.object(tg.Grid, "pilot",
                                  return_value=0) as pilot:
            self.commit(**{"other.txt": "x"})
            head = self.git("rev-parse", "HEAD")
            args = mock.Mock(repo=self.repo)
            self.assertEqual(engine.pilot(args), 0)
            check.assert_called_once_with(self.repo, self.KEY, head)
            pilot.assert_called_once_with(args)
        with mock.patch.object(f, "check_declaration_at_pilot",
                               side_effect=ValueError("late")), \
                mock.patch.object(tg.Grid, "pilot") as pilot:
            with self.assertRaisesRegex(ValueError, "late"):
                engine.pilot(mock.Mock(repo=self.repo))
            pilot.assert_not_called()
        with mock.patch.object(tg.Grid, "check_pilot_settings"), \
                mock.patch.object(f, "repo_of_code",
                                  return_value=self.repo), \
                mock.patch.object(f, "check_declaration_at_pilot") as check:
            engine.check_pilot_settings({"checkout": {"head": "h" * 40}})
            check.assert_called_once_with(self.repo, self.KEY, "h" * 40)
            with self.assertRaisesRegex(ValueError, "no checkout head"):
                engine.check_pilot_settings({})

    def test_the_engine_checks_every_counts_commit_it_reads(self):
        built, engine = f.declare(
            self.KEY, g.PARTS[self.KEY][:1])
        self.assertIsInstance(engine, f.Followup)
        with mock.patch.object(tg.Grid, "counts_commit",
                               return_value="a" * 40) as base, \
                mock.patch.object(f, "check_declaration_order") as check:
            got = engine.counts_commit("repo", "cand", "path")
        self.assertEqual(got, "a" * 40)
        base.assert_called_once_with("repo", "cand", "path")
        check.assert_called_once_with("repo", "cand", self.KEY, "a" * 40)
        # a refusal of the order refuses the counts commit
        with mock.patch.object(tg.Grid, "counts_commit",
                               return_value="a" * 40), \
                mock.patch.object(f, "check_declaration_order",
                                  side_effect=ValueError("late")):
            with self.assertRaisesRegex(ValueError, "late"):
                engine.counts_commit("repo", "cand", "path")


class RepoOfCode(unittest.TestCase):
    def test_the_repository_of_the_code_is_found_unmocked(self):
        repo = f.repo_of_code()
        self.assertIsInstance(repo, Path)
        self.assertTrue((repo / ".git").exists())
        self.assertTrue(f.declaration_file("matrix-1").resolve()
                        .is_relative_to(repo.resolve()))


class UndefinedGlobals(unittest.TestCase):
    def test_no_task37_module_uses_a_name_it_never_binds(self):
        """A pyflakes-like scan: every global name a `task37_*.py` loads
        is bound in its module or is a builtin (an unimported `Path` is
        found here)."""
        import builtins
        import symtable
        for path in sorted(a.HERE.glob("task37_*.py")):
            top = symtable.symtable(path.read_text(), str(path), "exec")
            bound = {s.get_name() for s in top.get_symbols()
                     if s.is_assigned() or s.is_imported() or
                     s.is_namespace()}
            missing = set()
            module_names = {"__file__", "__name__", "__doc__"}

            def walk(table):
                for s in table.get_symbols():
                    if s.is_global() and s.is_referenced() and \
                            s.get_name() not in bound and \
                            not hasattr(builtins, s.get_name()) and \
                            s.get_name() not in module_names:
                        missing.add(s.get_name())
                for child in table.get_children():
                    walk(child)

            walk(top)
            for s in top.get_symbols():
                if s.is_referenced() and not (
                        s.is_assigned() or s.is_imported() or
                        s.is_namespace() or hasattr(builtins, s.get_name())
                        or s.get_name() in module_names):
                    missing.add(s.get_name())
            self.assertEqual(missing, set(), path.name)


class OtherShardDeclared(unittest.TestCase):
    """Declaring the follow-up of another shard leaves a recorded follow-up
    checkable by the real engine."""

    def test_check_code_of_a_recorded_follow_up_survives_another_one(self):
        mine, other = "matrix-1", "matrix-3"
        paths = [f.declaration_file(k) for k in (mine, other)]
        if any(p.exists() for p in paths):
            self.skipTest("a follow-up is already declared")
        self.addCleanup(lambda: [p.unlink() for p in paths
                                 if p.exists()])
        declare_in(a.HERE, mine, g.PARTS[mine][:1])
        built, engine = f.declare(mine, f.load_declaration(mine))
        recorded = engine.code_now()
        engine.check_code(recorded, True)
        # the other shard's declaration appears: the recorded code of this
        # follow-up is still the code of this table
        declare_in(a.HERE, other, g.PARTS[other][:1])
        self.assertEqual(engine.code_now(), recorded)
        engine.check_code(recorded, True)
        again = f.declare(mine, f.load_declaration(mine))[1]
        again.check_code(recorded, True)
        theirs = f.declare(other, f.load_declaration(other))[1]
        self.assertNotEqual(theirs.code_now(), recorded)
        with self.assertRaises(ValueError):
            engine.check_code(theirs.code_now(), True)


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
