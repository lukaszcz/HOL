#!/usr/bin/env python3
"""The TASK37 timing tables (task37_grid.py): the shards and their
partition, configuration, seals, pins, the independence of concurrent
streams, and the load recorder."""
import copy
import collections
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import acceptance as a
import import_closure as ic
import performance_schema as ps
import task37_cases as c
import task37_dispose as d
import task37_followup as f
import task37_grid as g
import task37_load as load
import task30_cases
import task31_cases
import task31_pins as reviewed
import test_task31_attempts as t31a
import timing_grid as tg


KINDS = ("client", "matrix")
KEYS = ("client-1", "client-2", "matrix-1", "matrix-2", "matrix-3",
        "matrix-4")
NAMES = tuple("task37-" + k for k in KEYS)


def of_kind(kind):
    return [g.TABLES[g.name_of(k)] for k in g.shards(kind)]


class Configuration(unittest.TestCase):
    def test_the_shards(self):
        self.assertEqual(g.SHARDS, dict(client=2, matrix=4))
        self.assertEqual(g.SHARD_KEYS, KEYS)
        self.assertEqual(sorted(g.TABLES), sorted(NAMES))
        self.assertEqual(sorted(g.GRIDS), sorted(NAMES))
        self.assertEqual({k: t.name for k, t in g.TABLES.items()},
                         {n: n for n in NAMES})
        # No un-sharded table.
        self.assertNotIn("task37-client", g.TABLES)
        self.assertNotIn("task37-matrix", g.TABLES)

    def test_the_schedule_pairs_and_policy(self):
        for t in g.TABLES.values():
            self.assertEqual((t.schedule, t.headroom), ("warmup", 1))
            self.assertEqual((t.pairs, t.samples), (20, 5))
            self.assertTrue(t.fixed_seconds and t.require_seed)
            self.assertEqual(t.baseline, a.BASE)
            self.assertEqual(t.tree, "src")
            self.assertTrue(t.seed.startswith("task37-"))
            self.assertEqual((t.target, t.max_pairs),
                             (tg.TARGET, tg.MAX_PAIRS))

    def test_the_shards_measure_exactly_the_samples(self):
        for kind, sample in (("client", c.CLIENT_SAMPLE),
                             ("matrix", c.MATRIX_SAMPLE)):
            found = [n for t in of_kind(kind) for n in t.names()]
            self.assertEqual(len(found), len(set(found)))
            self.assertEqual(set(found), set(sample))
        self.assertEqual(len(c.CLIENT_SAMPLE), 39)
        self.assertEqual(len(c.MATRIX_SAMPLE), 87)
        # A shard's table keeps the cells in the order of its cases.
        for t in g.TABLES.values():
            self.assertEqual(set(t.names()), set(g.PARTS[t.name[7:]]))
            self.assertEqual(sorted(t.cases), sorted(
                {c.split(x)[0] for x in t.names()}))

    def test_the_fixture_family_of_every_cell(self):
        for t in of_kind("matrix"):
            for case in t.cases:
                self.assertEqual(c.ms.EXPECTED_CASES[case]["fixture"],
                                 "MatrixPerformance.sml")
        for t in of_kind("client"):
            for case in t.cases:
                self.assertEqual(c.ms.EXPECTED_CASES[case]["fixture"],
                                 "ClientPerformance.sml")
        self.assertIn("MatrixPerformance.sml", g.INSTALLED["matrix"])
        self.assertNotIn("MatrixPerformance.sml", g.INSTALLED["client"])
        self.assertIn("ClientPerformance.sml", g.INSTALLED["client"])

    def test_the_downstream_cells_are_selectable_by_the_client_fixture(self):
        text = (a.HERE / "ClientPerformance.sml").read_text()
        self.assertIn('String.isPrefix "downstream_" selected', text)
        found = {n for t in of_kind("client") for n in t.names()}
        for case in c.DOWNSTREAM_CASES:
            self.assertIn('"%s" =>' % case, text)
        self.assertLessEqual(set(c.DOWNSTREAM_CELLS), found)

    def test_the_long_batches(self):
        for kind, long in (("matrix", c.LONG_MATRIX),
                           ("client", c.LONG_CLIENT)):
            found = set()
            for t in of_kind(kind):
                self.assertEqual(set(t.seconds_by_case),
                                 set(t.cases) & set(long))
                found |= set(t.seconds_by_case)
            self.assertEqual(found, set(long) & {
                x for t in of_kind(kind) for x in t.cases})

    def test_no_seal_history_and_no_older_code(self):
        self.assertEqual((g.DRIVERS, g.ENGINES, g.ACCEPTANCE,
                          g.SEALED_HISTORY), ((), (), (), {}))

    def test_the_counts_files_are_named_per_shard(self):
        self.assertEqual(
            {k: g.TABLES[g.name_of(k)].counts.name for k in KEYS},
            {k: "task37_%s_%s_iterations.json" % tuple(k.split("-"))
             for k in KEYS})
        self.assertEqual(g.TABLES["task37-matrix-1"].counts.name,
                         "task37_matrix_1_iterations.json")
        self.assertEqual(g.TABLES["task37-client-2"].counts.name,
                         "task37_client_2_iterations.json")
        # No un-sharded counts file is a table's.
        for old in ("task37_client_iterations.json",
                    "task37_matrix_iterations.json"):
            self.assertNotIn(old, [t.counts.name
                                   for t in g.TABLES.values()])

    def test_a_counts_file_that_exists_is_a_valid_one(self):
        """The measurement stages create and commit the counts files (each
        alone); until then there is none to check, and nothing is said
        about its absence (as test_task30_grid.py)."""
        found = [(t, p) for t in g.TABLES.values() for p in t.files()
                 if p.exists()]
        if not found:
            self.skipTest("the counts files are made by each shard's "
                          "measurement stage and committed then")
        for t, path in found:
            self.assertEqual(counts_problems(t, a.load(path)), [], path)

    def test_the_counts_check_finds_what_is_wrong(self):
        t = g.TABLES["task37-matrix-1"]
        cells = t.names()
        good = dict(iterations={c: 3 for c in cells},
                    seconds=t.seconds_map())
        self.assertEqual(counts_problems(t, good), [])
        for bad in (
                dict(good, iterations={c: 3 for c in cells[1:]}),
                dict(good, iterations=dict(good["iterations"], x=1)),
                dict(good, seconds={}),
                dict(good, iterations=dict(good["iterations"],
                                           **{cells[0]: 0})),
                dict(good, iterations=dict(good["iterations"],
                                           **{cells[0]: 1.5})),
                dict(good, iterations=dict(good["iterations"],
                                           **{cells[0]: "3"})),
                dict(seconds=good["seconds"])):
            self.assertTrue(counts_problems(t, bad), bad)

    def test_the_sources_are_the_boundary_lists(self):
        """The rule: matrix shards pin TASK30's list less SimpTracking,
        client shards task31_cases.SOURCES (the identity tables use the
        elaborated lists of task37_sources.py instead)."""
        for t in of_kind("matrix"):
            self.assertEqual(t.sources, c.MATRIX_TIMING_SOURCES)
            self.assertEqual(t.sources, tuple(
                p for p in task30_cases.SOURCES
                if p not in c.DELETED_SOURCES))
        for t in of_kind("client"):
            self.assertEqual(t.sources, c.CLIENT_TIMING_SOURCES)
            self.assertEqual(t.sources, tuple(task31_cases.SOURCES))
        self.assertEqual(g.SOURCES, dict(client=c.CLIENT_TIMING_SOURCES,
                                         matrix=c.MATRIX_TIMING_SOURCES))

    def test_the_pins(self):
        for t in g.TABLES.values():
            self.assertEqual(set(t.pinned), {"src/simp/src/Cond_rewr.sig"})
            self.assertEqual(t.pin_file, "task37_attributed.json")
            self.assertEqual(g.FILE, c.REVIEWED_FILE)


def counts_problems(t, counts):
    """What is wrong with the counts document of table `t`, as a list: its
    cells, its seconds (a per-cell map) and the schema's own rule for every
    batch count (the warmup schedule: any positive integer)."""
    found = []
    if not isinstance(counts.get("iterations"), dict) or \
            set(counts["iterations"]) != set(t.names()):
        found.append("the cells are not the table's")
        return found
    if counts.get("seconds") != t.seconds_map():
        found.append("the seconds are not the table's")
    for cell, value in counts["iterations"].items():
        try:
            same = ps.batch_iterations(value, t.schedule) == value
        except (ValueError, TypeError):
            same = False
        if not same:
            found.append("%s: %r is no batch count" % (cell, value))
    return found


class Shards(unittest.TestCase):
    """The partition of a sample over its shards."""

    def parts(self, kind):
        return [g.PARTS[k] for k in g.shards(kind)]

    def test_the_parts_are_disjoint_and_cover_the_sample(self):
        for kind, sample in (("client", c.CLIENT_SAMPLE),
                             ("matrix", c.MATRIX_SAMPLE)):
            found = [x for part in self.parts(kind) for x in part]
            self.assertEqual(len(found), len(set(found)))
            self.assertEqual(sorted(found), sorted(sample))
            self.assertTrue(all(self.parts(kind)))

    def test_the_parts_are_balanced(self):
        for kind in KINDS:
            sizes = [len(p) for p in self.parts(kind)]
            self.assertLessEqual(max(sizes) - min(sizes), 1, kind)
        self.assertEqual(sorted(len(p) for p in self.parts("matrix")),
                         [21, 22, 22, 22])
        self.assertEqual(sorted(len(p) for p in self.parts("client")),
                         [19, 20])

    def test_the_long_batch_cells_are_spread(self):
        for kind, long in (("client", c.LONG_CLIENT),
                           ("matrix", c.LONG_MATRIX)):
            found = [sum(c.split(x)[0] in long for x in p)
                     for p in self.parts(kind)]
            self.assertGreater(sum(found), 1, kind)
            self.assertLessEqual(max(found) - min(found), 1, kind)

    def test_the_partition_is_the_stated_rule_and_sorted(self):
        """Recomputed here, independently of `partition`: the sample's
        cells sorted, the long-batch cells first, dealt round-robin by one
        running count; each part sorted."""
        for kind, sample, long in (("client", c.CLIENT_SAMPLE, c.LONG_CLIENT),
                                   ("matrix", c.MATRIX_SAMPLE,
                                    c.LONG_MATRIX)):
            order = sorted(sample, key=lambda x: (
                c.split(x)[0] not in long, x))
            dealt = [sorted(order[i::g.SHARDS[kind]])
                     for i in range(g.SHARDS[kind])]
            self.assertEqual([list(p) for p in g.partition(kind)], dealt)
            for part in g.partition(kind):
                self.assertEqual(list(part), sorted(part))
            self.assertEqual(
                [g.PARTS[k] for k in g.shards(kind)],
                list(g.partition(kind)))
        # The order the sample is listed in does not matter.
        reversed_ = dict(g.CELLS, matrix=tuple(reversed(c.MATRIX_SAMPLE)))
        with mock.patch.dict(g.CELLS, reversed_):
            self.assertEqual(g.partition("matrix"), tuple(
                g.PARTS[k] for k in g.shards("matrix")))

    def test_the_round_robin_rule(self):
        small = ("a_long-1", "b-1", "c-1", "d_long-1", "e-1", "f-1", "g-1")
        with mock.patch.dict(g.CELLS, client=small), mock.patch.dict(
                g.LONG, client=("a_long", "d_long")), mock.patch.dict(
                    g.SHARDS, client=3):
            # Long cells first: a_long, d_long to shards 1 and 2; then the
            # rest continue the count: b to 3, c to 1, e to 2, f to 3, g to
            # 1.
            self.assertEqual(g.partition("client"), (
                ("a_long-1", "c-1", "g-1"), ("d_long-1", "e-1"),
                ("b-1", "f-1")))

    def test_names_files_seeds_and_state_are_unique(self):
        tables = list(g.TABLES.values())
        for found in ([t.name for t in tables],
                      [t.counts for t in tables],
                      [t.seed for t in tables],
                      [t.label for t in tables],
                      [t.family for t in tables]):
            self.assertEqual(len(found), len(set(found)), found)
        for t in tables:
            self.assertEqual(t.family, t.name)
        engines = list(g.GRIDS.values())
        for method in ("ledger_path", "stamp_path", "prepare_log_path"):
            paths = {getattr(e, method)(Path("/clone")) for e in engines}
            self.assertEqual(len(paths), len(engines), method)
        self.assertEqual(g.GRIDS["task37-matrix-2"].ledger_path(
            Path("/clone")), Path(
                "/clone/.agent-files/evidence/task37-matrix-2/"
                "attempts.jsonl"))

    def test_an_unknown_shard_is_refused(self):
        for name in ("matrix", "client", "matrix-0", "matrix-5",
                     "client-3", "both", "matrix-1-followup"):
            self.assertEqual(g.main([name, "run"]), tg.REFUSED, name)
        self.assertEqual(g.main([]), tg.REFUSED)
        with self.assertRaises(KeyError):
            g.table("matrix-5")
        self.assertEqual(sorted(g.commands()), sorted(KEYS))

    def test_a_shard_command_reaches_its_own_engine(self):
        for key in KEYS:
            with mock.patch.object(g.GRIDS["task37-" + key], "main",
                                   return_value=7) as engine:
                self.assertEqual(g.main([key, "pilot", "--x"]), 7)
            engine.assert_called_once_with(["pilot", "--x"])


class FollowupsAreApart(unittest.TestCase):
    """Follow-ups are in task37_followup.py (test_task37_followup.py)."""

    def test_the_shard_driver_declares_no_follow_up(self):
        for name in ("FOLLOWUP_CELLS", "declare", "followup_table"):
            self.assertFalse(hasattr(g, name), name)
        self.assertFalse([n for n in g.GRIDS if n.endswith("-followup")])
        self.assertEqual(g.file_of("matrix-2").name,
                         "task37_matrix_2_iterations.json")


class Seals(unittest.TestCase):
    def test_every_sealed_file_exists_and_the_derivation_is_sealed(self):
        for table in g.TABLES.values():
            for name in table.sealed:
                self.assertTrue((a.HERE / name).is_file(), name)
            for name in ("task37_cases.py", "task31_pins.py"):
                self.assertIn(name, table.sealed)
            self.assertIn("task37_attributed.json", [table.pin_file])
            self.assertEqual(table.code(), ("driver", "engine", "acceptance",
                                            "sealed", "pins"))

    def test_a_sealed_file_edit_is_detected(self):
        for name, engine in g.GRIDS.items():
            code = engine.code_now()
            engine.check_code(code, True)
            bad = copy.deepcopy(code)
            bad["sealed"]["task37_cases.py"] = dict(bytes=1,
                                                    sha256="0" * 64)
            with self.assertRaises(ValueError):
                engine.check_code(bad, True)
            bad = copy.deepcopy(code)
            bad["driver"] = dict(bytes=1, sha256="0" * 64)
            with self.assertRaises(ValueError):
                engine.check_code(bad, True)

    def test_no_sealed_list_repeats_a_file(self):
        for kind, sealed in g.SEALED.items():
            self.assertEqual(len(sealed), len(set(sealed)), kind)
        for table in g.TABLES.values():
            self.assertEqual(len(table.sealed), len(set(table.sealed)),
                             table.name)

    def test_the_pin_file_is_not_one_of_the_sealed_files(self):
        for table in g.TABLES.values():
            self.assertNotIn(table.pin_file, table.sealed)

    def test_the_tables_seal_their_own_fixtures_only(self):
        for t in of_kind("matrix"):
            self.assertIn("MatrixPerformance.sml", t.sealed)
            self.assertNotIn("ClientPerformance.sml", t.sealed)
        for t in of_kind("client"):
            self.assertNotIn("MatrixPerformance.sml", t.sealed)
            self.assertIn("ClientPerformance.sml", t.sealed)


class Revisions(unittest.TestCase):
    """Counts revisions are data (`revisions_of`): found by the engine's
    own naming, each bound to the table whose counts file it revises, with
    no edit to the driver."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        # a directory the way a.HERE is deep (the table roots at its
        # fourth parent)
        self.here = self.root / "p" / "q" / "r" / "s"
        self.here.mkdir(parents=True)

    def touch(self, *names):
        for name in names:
            (self.here / name).write_text("{}")

    def test_none_exist_yet(self):
        self.assertTrue(all(t.revisions == () for t in g.TABLES.values()))
        self.assertEqual(g.revisions_of(self.here / "x_iterations.json"),
                         ())

    def test_the_revisions_found_are_in_numeric_order(self):
        self.touch("x_iterations_3.json", "x_iterations_2.json",
                   "x_iterations_10.json", *(
                       "x_iterations_%d.json" % n for n in range(4, 10)),
                   "y_iterations_2.json", "x_other.json")
        got = g.revisions_of(self.here / "x_iterations.json")
        self.assertEqual([p.name for p in got], [
            "x_iterations_%d.json" % n for n in range(2, 11)])
        self.assertEqual(g.revisions_of(self.here / "y_iterations.json"),
                         (self.here / "y_iterations_2.json",))

    def test_a_gap_or_an_odd_name_is_refused(self):
        self.touch("x_iterations_3.json")
        with self.assertRaisesRegex(ValueError, "without a gap") as e:
            g.revisions_of(self.here / "x_iterations.json")
        self.assertIn("x_iterations_3.json", str(e.exception))
        self.touch("x_iterations_2.json")
        g.revisions_of(self.here / "x_iterations.json")
        for odd in ("x_iterations_02.json", "x_iterations_rev1.json",
                    "x_iterations_1.json"):
            self.touch(odd)
            with self.assertRaisesRegex(ValueError, "no revision of") as e:
                g.revisions_of(self.here / "x_iterations.json")
            # the error names the offending file, by its full path
            self.assertIn(str(self.here / odd), str(e.exception))
            (self.here / odd).unlink()

    def table_with(self, key, names):
        self.touch(*names)
        return g.table(key, revisions=g.revisions_of(
            self.here / g.file_of(key).name))

    def test_a_table_takes_its_revisions_with_real_objects(self):
        key = "matrix-1"
        base = g.file_of(key).stem
        t = self.table_with(key, [base + "_2.json", base + "_3.json"])
        self.assertEqual([p.name for p in t.revisions],
                         [base + "_2.json", base + "_3.json"])
        self.assertEqual(t.files()[0], g.file_of(key))
        self.assertEqual(t.latest().name, base + "_3.json")
        self.assertEqual(t.file_named(base + "_2.json").name,
                         base + "_2.json")
        with self.assertRaises(ValueError):
            t.file_named("task37_matrix_2_iterations_2.json")
        self.assertIsInstance(tg.Grid(t, doc=__doc__), tg.Grid)

    def test_discovery_reads_the_directory_of_the_counts_file(self):
        base = g.file_of("matrix-1").stem
        self.touch(base + "_2.json")
        with mock.patch.object(a, "HERE", self.here):
            found = {k: g.table(k).revisions for k in g.SHARD_KEYS}
        self.assertEqual(found.pop("matrix-1"),
                         (self.here / (base + "_2.json"),))
        self.assertTrue(all(v == () for v in found.values()))

    def test_a_revision_of_one_shard_touches_no_other_shard(self):
        base = g.file_of("matrix-1").stem
        revised = self.table_with("matrix-1", [base + "_2.json"])
        plain = g.TABLES["task37-matrix-1"]
        # the revision changes the files of its own table only
        self.assertEqual(len(revised.files()), 2)
        self.assertEqual(len(plain.files()), 1)
        for key in g.SHARD_KEYS:
            if key != "matrix-1":
                other = g.table(key)
                self.assertEqual(other.files(), (g.file_of(key),))
        # and no seal: the sealed files, the driver and the pins of
        # every table are the same, and so are the engines' code seals
        for key in g.SHARD_KEYS:
            engine = g.GRIDS[g.name_of(key)]
            before = engine.code_now()
            if key == "matrix-1":
                other = tg.Grid(revised, doc=__doc__)
                self.assertEqual(other.code_now(), before)
            self.assertEqual(g.table(key).sealed, g.TABLES[
                g.name_of(key)].sealed)
        # a follow-up of another shard is not touched either: its table
        # has its own counts file, whose revisions are its own
        replaced = g.GRIDS["task37-matrix-2"]
        follow = f.table("matrix-2", g.PARTS["matrix-2"][:1], replaced)
        self.assertEqual(follow.files(), (f.file_of("matrix-2"),))

    def test_the_follow_up_of_a_shard_has_its_own_revisions(self):
        shard = g.file_of("matrix-1").stem
        follow = f.file_of("matrix-1").stem
        self.touch(shard + "_2.json", follow + "_2.json",
                   follow + "_3.json")
        with mock.patch.object(a, "HERE", self.here):
            first = g.table("matrix-1")
            other = f.table("matrix-1", g.PARTS["matrix-1"][:1],
                            g.GRIDS["task37-matrix-1"])
        self.assertEqual([p.name for p in first.revisions],
                         [shard + "_2.json"])
        self.assertEqual([p.name for p in other.revisions],
                         [follow + "_2.json", follow + "_3.json"])
        # the follow-up's counts file is still not the shard's
        self.assertNotIn(other.counts, first.files())

    def test_the_disposition_accepts_a_revision_of_its_own_table(self):
        base = g.file_of("matrix-1").stem
        t = self.table_with("matrix-1", [base + "_2.json"])
        other = g.TABLES["task37-matrix-2"]
        (self.root / "task37_matrix_1_iterations.json").write_text("one")
        (self.root / (base + "_2.json")).write_text("two")
        with mock.patch.object(d, "COUNTS_DIR", self.root):
            for name in (base + ".json", base + "_2.json"):
                inventory = dict(counts_file=name, iterations_seal=a.seal(
                    self.root / name))
                stage = dict(inventory=inventory,
                             first_inventory=inventory)
                self.assertEqual(
                    d.check_counts(stage, "t", t),
                    a.seal(self.root / name))
            # a revision of shard 1 is no counts file of shard 2's table
            with self.assertRaisesRegex(ValueError, "not one of"):
                d.check_counts(stage, "t", other)


class Modules(unittest.TestCase):
    """The carried-over invariant of test_task31_attempts.Modules: every
    local module that a timing driver imports, to the transitive closure, is
    sealed by the table's records or reached only by a reviewed exempt
    import edge with a stated reason."""

    OTHER_SAMPLE = (
        "task37_cases.py derives both samples; this table reads the cells "
        "and source list of the other sample from nothing here (only "
        "%s), so a change to that module alters no cell of this table "
        "(and task37_cases.py itself is sealed)")
    CONSTANTS = (
        "task37_grid takes the constants INSTALLED and SEALED[1:5] from "
        "task30_grid and no function. No seal list has task30_grid.py: what "
        "binds the constants is the table's SEALED, whose names the check "
        "compares as a set with the record's and whose files it compares "
        "by seal (test_task31_attempts.Modules.TASK30_CONSTANTS)")
    CLIENT_ONLY = (
        "task37_grid takes the constant INSTALLED of the client tables from "
        "task31_grid; the matrix tables take none of it and seal the "
        "fixtures they install (task37_cases.py is sealed)")

    MATRIX_RUN = (
        "run_paired.main imports it only when the fixture is "
        "ClientPerformance.sml (`matrix_fixture`); the matrix "
        "tables run MatrixPerformance.sml, and run_paired.py itself is "
        "sealed")

    @classmethod
    def exempt(cls, kind):
        found = t31a.Modules.runtime_edges(
            "loading", "path_schema", "prepare_patch", "check_patch")
        found.update(t31a.Modules.edges(
            cls.CONSTANTS, ("task37_grid", "task30_grid", None)))
        if kind == "matrix":
            found.update(t31a.Modules.edges(
                cls.CLIENT_ONLY, ("task37_grid", "task31_grid", None)))
            found.update(t31a.Modules.edges(
                cls.MATRIX_RUN, ("run_paired", "client_dependencies",
                                 "main")))
            found.update(t31a.Modules.edges(
                cls.OTHER_SAMPLE % "the matrix",
                ("task37_cases", "task31_cases", None),
                ("task37_cases", "task31_followup", None)))
        else:
            found.update(t31a.Modules.edges(
                cls.CONSTANTS, ("task31_grid", "task30_grid", None)))
            found.update(t31a.Modules.edges(
                cls.OTHER_SAMPLE % "the client", (
                    "task37_cases", "task29a_grid", None), (
                    "task37_cases", "task30_cases", None)))
        return found

    def covered(self, roots, sealed, exempt):
        sources = ic.sources()
        stems = {Path(n).stem for n in sealed}
        found, used = ic.closure(sources, roots, exempt)
        self.assertEqual(sorted(found - stems), [])
        self.assertEqual(sorted(set(exempt) - used, key=str), [])
        self.assertEqual(sorted(e for e in exempt if e[1] in stems), [])
        for edge, reason in exempt.items():
            self.assertTrue(reason, edge)
        return found

    def test_a_shard_driver_imports_only_sealed_code(self):
        for kind in g.SHARDS:
            with self.subTest(kind=kind):
                found = self.covered(
                    ("task37_grid", "run_paired"),
                    (*g.SEALED[kind], "task37_grid.py", *tg.REPLAY_CODE),
                    self.exempt(kind))
                self.assertIn("task37_cases", found)

    def test_a_follow_up_imports_only_sealed_code(self):
        for key in g.SHARD_KEYS:
            with self.subTest(key=key):
                self.covered(
                    ("task37_followup", "run_paired"),
                    (*f.SEALED[key], "task37_followup.py",
                     *tg.REPLAY_CODE), self.exempt(g.KIND[key]))

    def test_a_new_import_of_driver_code_is_found(self):
        for kind in g.SHARDS:
            sources = ic.sources()
            sources["task37_cases"] += "\nimport allocation_boundary\n"
            stems = {Path(n).stem for n in (
                *g.SEALED[kind], "task37_grid.py", *tg.REPLAY_CODE)}
            found, _ = ic.closure(sources, ("task37_grid",),
                                  self.exempt(kind))
            self.assertIn("allocation_boundary", found - stems)


class Refusals(unittest.TestCase):
    def test_an_unknown_cell_is_refused(self):
        with self.assertRaises(ValueError):
            tg.Table("x", "X", c.MATRIX_CASES[:1], __file__,
                     a.HERE / "x_iterations.json", fixed_seconds=True,
                     seed="s-1", cells=["frag_create-7"])

    def test_a_cell_outside_a_tables_cases_is_refused(self):
        with self.assertRaises(ValueError):
            tg.Table("x", "X", ("frag_create",), __file__,
                     a.HERE / "x_iterations.json", fixed_seconds=True,
                     seed="s-1", cells=["frag_update-1000"])

    def test_the_table_must_be_named(self):
        self.assertEqual(g.main([]), tg.REFUSED)
        self.assertEqual(g.main(["both", "run"]), tg.REFUSED)


class Pins(unittest.TestCase):
    def test_the_attributed_file_is_valid_and_matches_git_blobs(self):
        document = reviewed.load(g.FILE)
        paths = [e["path"] for e in document["entries"]]
        self.assertIn("src/1/ThmAttribute.sig", paths)
        self.assertIn("src/1/ThmAttribute.sml", paths)
        self.assertEqual(document["history"], {})
        for e in document["entries"]:
            self.assertIsNotNone(e["candidate_blob"], e["path"])
        root = a.HERE.parents[3]
        try:
            have = {e["path"]: (tg.git_blob(root, a.BASE, e["path"]),
                                tg.git_blob(root, "7e202dfbaa", e["path"]))
                    for e in document["entries"]}
        except ValueError:
            self.skipTest("the final candidate is not in this clone")
        for e in document["entries"]:
            self.assertEqual(
                have[e["path"]], (e["baseline_blob"], e["candidate_blob"]),
                e["path"])


class Concurrency(unittest.TestCase):
    """Streams from their own clones share no path: the lock, ledger, stamp
    and counts are per table and per checkout."""

    def test_another_clone_has_other_paths(self):
        engine = g.GRIDS["task37-client-1"]
        self.assertNotEqual(engine.ledger_path(Path("/one")),
                            engine.ledger_path(Path("/two")))

    def test_the_lock_is_below_the_checkout(self):
        text = (a.HERE / "acceptance.py").read_text()
        self.assertIn('agent_files = repo / ".agent-files"', text)

    def test_no_fixed_temporary_name_is_used_by_the_task37_modules(self):
        for name in ("task37_cases.py", "task37_grid.py", "task37_load.py",
                     "task37_sources.py", "task37_followup.py"):
            text = (a.HERE / name).read_text()
            self.assertNotIn("/tmp/", text)
            self.assertNotIn("/dev/shm", text)


class LoadRecorder(unittest.TestCase):
    def test_sample_and_summary(self):
        with tempfile.TemporaryDirectory() as tmp:
            proc = Path(tmp) / "loadavg"
            proc.write_text("1.50 2.00 3.25 4/300 1234\n")
            out = Path(tmp) / "load.jsonl"
            import time
            real = time.sleep
            time.sleep = lambda s: None
            try:
                with self.assertRaises(ValueError):
                    load.record(out, 0, "s")
                self.assertEqual(load.record(out, 1, "s", 3, str(proc)), 3)
            finally:
                time.sleep = real
            rows = [json.loads(x) for x in out.read_text().split("\n") if x]
            self.assertEqual(len(rows), 3)
            self.assertEqual(rows[0]["load"], [1.5, 2.0, 3.25])
            self.assertEqual(rows[0]["runnable"], 4)
            self.assertEqual(load.summarize(out)["samples"], 3)

    def test_the_signal_handlers_are_restored(self):
        import signal
        before = {n: signal.getsignal(n)
                  for n in (signal.SIGTERM, signal.SIGINT)}
        with tempfile.TemporaryDirectory() as tmp:
            proc = Path(tmp) / "loadavg"
            proc.write_text("1.50 2.00 3.25 4/300 1234\n")
            out = Path(tmp) / "load.jsonl"
            with mock.patch("time.sleep"):
                load.record(out, 1, "s", 2, str(proc))
                for n, handler in before.items():
                    self.assertIs(signal.getsignal(n), handler)
                # also after a failure while recording
                with mock.patch.object(load, "sample",
                                       side_effect=OSError("gone")):
                    with self.assertRaises(OSError):
                        load.record(out, 1, "s", 2, str(proc))
        for n, handler in before.items():
            self.assertIs(signal.getsignal(n), handler)

    def test_a_signal_stops_the_recording_cleanly(self):
        import signal
        with tempfile.TemporaryDirectory() as tmp:
            proc = Path(tmp) / "loadavg"
            proc.write_text("1.50 2.00 3.25 4/300 1234\n")
            out = Path(tmp) / "load.jsonl"

            def stop(_):
                signal.raise_signal(signal.SIGTERM)
            with mock.patch("time.sleep", stop):
                self.assertEqual(load.record(out, 1, "s", None, str(proc)),
                                 1)

    def test_an_empty_record_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "empty.jsonl"
            out.write_text("")
            with self.assertRaises(ValueError):
                load.summarize(out)
            self.assertEqual(load.main(["summarize", str(out)]), 3)

    def test_the_real_proc_file_parses(self):
        self.assertEqual(len(load.read_loadavg()[0]), 3)


if __name__ == "__main__":
    unittest.main()
