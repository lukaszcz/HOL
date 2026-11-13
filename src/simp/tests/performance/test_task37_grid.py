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
import task37_cases as c
import task37_grid as g
import task37_load as load
import task31_pins as reviewed
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

    def test_the_counts_files_are_named_and_not_created_yet(self):
        self.assertEqual(
            {k: g.TABLES[g.name_of(k)].counts.name for k in KEYS},
            {k: "task37_%s_%s_iterations.json" % tuple(k.split("-"))
             for k in KEYS})
        self.assertEqual(g.TABLES["task37-matrix-1"].counts.name,
                         "task37_matrix_1_iterations.json")
        self.assertEqual(g.TABLES["task37-client-2"].counts.name,
                         "task37_client_2_iterations.json")
        # The measurement stages create them; the old names are gone.
        for t in g.TABLES.values():
            self.assertFalse(t.counts.exists(), t.counts)
        for old in ("task37_client_iterations.json",
                    "task37_matrix_iterations.json"):
            self.assertFalse((a.HERE / old).exists())
            self.assertNotIn(old, [t.counts.name
                                   for t in g.TABLES.values()])

    def test_the_sources_come_from_the_cases_module(self):
        for t in of_kind("matrix"):
            self.assertEqual(t.sources, c.MATRIX_SOURCES)
        for t in of_kind("client"):
            self.assertEqual(t.sources, c.CLIENT_TIMING_SOURCES)

    def test_the_client_timing_sources_cover_the_downstream_cells(self):
        """The client sample holds the downstream cells, so its sources
        are those of the client cells and of the downstream cells."""
        self.assertEqual(set(c.CLIENT_TIMING_SOURCES),
                         set(c.CLIENT_SOURCES) | set(c.DOWNSTREAM_SOURCES))
        for t in of_kind("client"):
            self.assertLessEqual(set(c.CLIENT_SOURCES), set(t.sources))
            self.assertLessEqual(set(c.DOWNSTREAM_SOURCES),
                                 set(t.sources))
        # The rule holds for whatever the downstream list becomes.
        with mock.patch.object(c, "DOWNSTREAM_SOURCES",
                               ("src/simp/src/NewFile.sml",)):
            self.assertEqual(set(c.CLIENT_SOURCES) | {
                "src/simp/src/NewFile.sml"}, set(
                    tuple(sorted(set(c.CLIENT_SOURCES) |
                                 set(c.DOWNSTREAM_SOURCES)))))

    def test_the_pins(self):
        for t in g.TABLES.values():
            self.assertEqual(set(t.pinned), {"src/simp/src/Cond_rewr.sig"})
            self.assertEqual(t.pin_file, "task37_attributed.json")
            self.assertEqual(g.FILE, c.REVIEWED_FILE)


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

    def test_the_partition_is_deterministic_and_sorted(self):
        for kind in KINDS:
            self.assertEqual(g.partition(kind), g.partition(kind))
            for part in g.partition(kind):
                self.assertEqual(list(part), sorted(part))
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


class Followups(unittest.TestCase):
    """The follow-up table of a shard (declared by a policy decision)."""

    def test_none_is_declared_yet(self):
        self.assertEqual(g.FOLLOWUP_CELLS, {})
        self.assertIsNone(g.declare("matrix-1", ()))
        self.assertFalse([n for n in g.GRIDS if n.endswith("-followup")])

    def test_a_follow_up_is_a_valid_replacing_table(self):
        key = "matrix-2"
        cells = g.PARTS[key][:2]
        replaced = g.GRIDS["task37-" + key]
        t = g.followup_table(key, cells, replaced)
        self.assertEqual(t.name, "task37-matrix-2-followup")
        self.assertEqual(t.family, "task37-matrix-2")
        self.assertEqual(t.pairs, 40)
        self.assertEqual(set(t.names()), set(cells))
        self.assertEqual(t.counts.name,
                         "task37_matrix_2_followup_iterations.json")
        self.assertFalse(t.counts.exists())
        self.assertNotIn(t.counts, [x.counts for x in g.TABLES.values()])
        self.assertNotIn(t.seed, [x.seed for x in g.TABLES.values()])
        self.assertIs(t.replaces.engine, replaced)

    def test_a_follow_up_of_a_cell_outside_its_shard_is_refused(self):
        other = g.PARTS["matrix-3"][0]
        with self.assertRaises(ValueError):
            g.followup_table("matrix-2", (other,),
                             g.GRIDS["task37-matrix-2"])
        with self.assertRaises(ValueError):
            g.followup_table("matrix-2", (), g.GRIDS["task37-matrix-2"])

    def test_declared_cells_give_an_engine_by_table_name(self):
        key = "client-1"
        cells = g.PARTS[key][:1]
        with mock.patch.dict(g.GRIDS), mock.patch.dict(g.TABLES):
            engine = g.declare(key, cells)
            self.assertIs(g.GRIDS["task37-client-1-followup"], engine)
            self.assertIn("client-1-followup", g.commands())
        self.assertNotIn("task37-client-1-followup", g.GRIDS)


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
            for e in document["entries"]:
                have = (tg.git_blob(root, a.BASE, e["path"]),
                        tg.git_blob(root, "7e202dfbaa", e["path"]))
                self.assertEqual(
                    have, (e["baseline_blob"], e["candidate_blob"]),
                    e["path"])
        except ValueError:
            self.skipTest("the final candidate is not in this clone")


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
        for name in ("task37_cases.py", "task37_grid.py", "task37_load.py"):
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
