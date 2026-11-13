#!/usr/bin/env python3
"""The TASK37 timing tables (task37_grid.py): configuration, seals, pins,
the independence of two concurrent streams, and the load recorder."""
import copy
import json
import tempfile
import unittest
from pathlib import Path

import acceptance as a
import task37_cases as c
import task37_grid as g
import task37_load as load
import task31_pins as reviewed
import timing_grid as tg


class Configuration(unittest.TestCase):
    def test_the_two_tables(self):
        self.assertEqual({k: t.name for k, t in g.TABLES.items()},
                         dict(client="task37-client",
                              matrix="task37-matrix"))

    def test_the_schedule_pairs_and_policy(self):
        for t in g.TABLES.values():
            self.assertEqual((t.schedule, t.headroom), ("warmup", 1))
            self.assertEqual((t.pairs, t.samples), (20, 5))
            self.assertTrue(t.fixed_seconds and t.require_seed)
            self.assertEqual(t.baseline, a.BASE)
            self.assertEqual(t.tree, "src")
            self.assertEqual(t.seed.startswith("task37-"), True)
            self.assertEqual((t.target, t.max_pairs),
                             (tg.TARGET, tg.MAX_PAIRS))

    def test_the_cells(self):
        self.assertEqual(g.TABLES["client"].names(), sorted_like(
            g.TABLES["client"], c.CLIENT_SAMPLE))
        self.assertEqual(len(g.TABLES["client"].keys()), 39)
        self.assertEqual(len(g.TABLES["matrix"].keys()), 87)
        self.assertEqual(set(g.TABLES["matrix"].names()),
                         set(c.MATRIX_SAMPLE))

    def test_the_fixture_family_of_every_cell(self):
        for case in g.TABLES["matrix"].cases:
            self.assertEqual(
                c.ms.EXPECTED_CASES[case]["fixture"],
                "MatrixPerformance.sml")
        for case in g.TABLES["client"].cases:
            self.assertEqual(
                c.ms.EXPECTED_CASES[case]["fixture"],
                "ClientPerformance.sml")
        self.assertIn("MatrixPerformance.sml", g.INSTALLED["matrix"])
        self.assertNotIn("MatrixPerformance.sml", g.INSTALLED["client"])
        self.assertIn("ClientPerformance.sml", g.INSTALLED["client"])

    def test_the_downstream_cells_are_selectable_by_the_client_fixture(self):
        text = (a.HERE / "ClientPerformance.sml").read_text()
        self.assertIn('String.isPrefix "downstream_" selected', text)
        for case in c.DOWNSTREAM_CASES:
            self.assertIn('"%s" =>' % case, text)
            self.assertIn(case, g.TABLES["client"].cases)

    def test_the_long_batches(self):
        self.assertEqual(set(g.TABLES["matrix"].seconds_by_case),
                         set(c.LONG_MATRIX))
        self.assertEqual(set(g.TABLES["client"].seconds_by_case),
                         set(c.LONG_CLIENT))

    def test_no_seal_history_and_no_older_code(self):
        self.assertEqual((g.DRIVERS, g.ENGINES, g.ACCEPTANCE,
                          g.SEALED_HISTORY), ((), (), (), {}))

    def test_the_counts_are_not_created_yet(self):
        # The measurement stages create them (task37_*_iterations.json).
        self.assertEqual({k: p.name for k, p in g.COUNTS.items()},
                         dict(client="task37_client_iterations.json",
                              matrix="task37_matrix_iterations.json"))

    def test_the_sources_and_pins(self):
        self.assertEqual(g.TABLES["matrix"].sources, c.MATRIX_SOURCES)
        self.assertEqual(g.TABLES["client"].sources, c.CLIENT_SOURCES)
        for t in g.TABLES.values():
            self.assertEqual(set(t.pinned), {"src/simp/src/Cond_rewr.sig"})
            self.assertEqual(t.pin_file, "task37_attributed.json")


def sorted_like(table, cells):
    order = {x: i for i, x in enumerate(table.names())}
    return sorted(cells, key=order.get)


class Seals(unittest.TestCase):
    def test_every_sealed_file_exists_and_the_derivation_is_sealed(self):
        for kind, table in g.TABLES.items():
            for name in table.sealed:
                self.assertTrue((a.HERE / name).is_file(), name)
            for name in ("task37_cases.py", "task31_pins.py"):
                self.assertIn(name, table.sealed)
            self.assertIn("task37_attributed.json", [table.pin_file])
            self.assertEqual(table.code(), ("driver", "engine", "acceptance",
                                            "sealed", "pins"))

    def test_a_sealed_file_edit_is_detected(self):
        for kind, engine in g.ENGINES_BY_KIND.items():
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
        self.assertIn("MatrixPerformance.sml", g.TABLES["matrix"].sealed)
        self.assertNotIn("MatrixPerformance.sml", g.TABLES["client"].sealed)
        self.assertIn("ClientPerformance.sml", g.TABLES["client"].sealed)


class Refusals(unittest.TestCase):
    def test_an_unknown_cell_is_refused(self):
        with self.assertRaises(ValueError):
            tg.Table("x", "X", c.MATRIX_CASES[:1], __file__,
                     g.COUNTS["matrix"], fixed_seconds=True, seed="s-1",
                     cells=["frag_create-7"])

    def test_a_cell_outside_a_tables_cases_is_refused(self):
        with self.assertRaises(ValueError):
            tg.Table("x", "X", ("frag_create",), __file__,
                     g.COUNTS["matrix"], fixed_seconds=True, seed="s-1",
                     cells=["frag_update-1000"])

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
    """Two streams from two clones share no path: the lock, ledger, stamp
    and counts are per table and per checkout."""

    def test_the_two_tables_share_no_file(self):
        client, matrix = g.TABLES["client"], g.TABLES["matrix"]
        self.assertNotEqual(client.counts, matrix.counts)
        self.assertNotEqual(client.family, matrix.family)
        self.assertNotEqual(client.seed, matrix.seed)
        engines = g.ENGINES_BY_KIND
        for method in ("ledger_path", "stamp_path", "prepare_log_path"):
            paths = {getattr(e, method)(Path("/clone"))
                     for e in engines.values()}
            self.assertEqual(len(paths), 2, method)
        # Another clone has other paths: nothing is shared across clones.
        self.assertNotEqual(engines["client"].ledger_path(Path("/one")),
                            engines["client"].ledger_path(Path("/two")))

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
