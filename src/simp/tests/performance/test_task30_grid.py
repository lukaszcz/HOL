#!/usr/bin/env python3
"""TASK30 timing table: its cells, its seconds, and a full synthetic grid.

The engine is tested in test_timing_grid.py; here the TASK30 table itself is
checked, and the engine runs it whole (144 cells) on synthetic stand-ins.
"""
import copy
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

import acceptance as a
import matrix_schema as ms
import task30_cases as cases
import task30_grid as t30
import test_timing_grid as ttg


REPO = a.HERE.parents[3]


def git(*args):
    found = subprocess.run(["git", "-C", str(REPO), *args], text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return found.stdout.strip() if found.returncode == 0 else None


def disk_blob(path):
    """The git blob of the file as it is now in the checkout."""
    return git("hash-object", str(REPO / path))


def base_blob(path):
    """The blob of the file at the baseline, or None when it has none."""
    return git("rev-parse", "%s:%s" % (a.BASE, path))


class Table(unittest.TestCase):
    def test_the_grid_is_24_cases_by_6_sizes(self):
        table = t30.TABLE
        self.assertEqual(len(table.cases), 24)
        self.assertEqual(len(table.keys()), 144)
        self.assertEqual(table.cases, cases.CASES)
        self.assertEqual({s for _, s in table.keys()}, set(a.SIZES))
        self.assertEqual(len(set(table.names())), 144)

    def test_no_case_of_the_matrix_exclusion_family_is_left_out(self):
        family = {c for c in ms.EXPECTED_CASES
                  if c.startswith(("exclude_", "history_"))}
        self.assertEqual(set(t30.TABLE.cases), family)

    def test_the_ten_direct_deletions_have_longer_batches(self):
        table = t30.TABLE
        text = (t30.a.HERE / "MatrixSupport.sml").read_text()
        body = text[text.index("fun exclusions ()"):text.index(
            "fun history ()")]
        branches = re.split(r'\n\s*(?:\|\s*)?(?="exclude_\w+" =>)',
                            body[body.index('in case label of'):])[1:]
        direct = {re.match(r'"(\w+)"', b).group(1) for b in branches
                  if re.search(r"\b(delete|dproc)\b", b)}
        self.assertEqual(direct, set(cases.DELETIONS))
        self.assertEqual(len(direct), 10)
        self.assertGreater(t30.LONG_SECONDS, t30.SECONDS)
        for case in table.cases:
            self.assertEqual(
                table.seconds_for(case),
                t30.LONG_SECONDS if case in direct else t30.SECONDS, case)
        self.assertEqual(set(table.seconds_by_case), direct)

    def test_policy_and_protocol_are_those_of_task29a(self):
        table = t30.TABLE
        self.assertTrue(table.require_seed and table.engine and
                        table.fixed_seconds)
        self.assertEqual((table.target, table.max_pairs, table.headroom),
                         (0.015, 120, 2))
        self.assertEqual((table.pairs, table.samples), (20, 5))
        self.assertEqual(table.seed, "task30-layout-1")
        self.assertEqual(table.tree, "src")
        self.assertEqual(table.revisions, ())
        self.assertEqual(table.latest(), t30.COUNTS)
        self.assertEqual((table.pilot_pairs, table.pilot_samples), (10, 3))
        self.assertEqual(table.drivers, ())
        self.assertEqual(table.schema("grid"), "task30-grid-v1")

    def test_the_counts_file_is_predeclared_from_the_pilot(self):
        self.assertEqual(t30.COUNTS.name, "task30_iterations.json")
        if not t30.COUNTS.exists():
            self.skipTest("produced by the develop-only pilot (see "
                          "PROTOCOL.md), then reviewed and committed")
        counts = a.load(t30.COUNTS)
        self.assertEqual(counts["schema"], "task30-iterations-v1")
        self.assertEqual(set(counts["iterations"]),
                         set(t30.TABLE.names()))
        self.assertEqual(counts["seconds"], t30.TABLE.seconds_map())
        for value in counts["iterations"].values():
            self.assertEqual(value & (value - 1), 0)

    def test_the_baseline_sources_and_sealed_files_are_named(self):
        table = t30.TABLE
        self.assertEqual(table.baseline, a.BASE)
        self.assertEqual(table.engines, ())
        self.assertEqual(table.sources, cases.SOURCES)
        self.assertEqual(len(set(cases.SOURCES)), len(cases.SOURCES))
        for path in cases.SOURCES:
            self.assertFalse(path.startswith("/"), path)
            self.assertTrue(path.endswith((".sml", ".sig")), path)
        for name in table.sealed:
            self.assertTrue((table.home / name).is_file(), name)
        # The driver, the engine and the data of the case list are all
        # sealed, so none of them changes unnoticed.
        self.assertEqual(table.code(), ("driver", "engine", "acceptance",
                                        "sealed"))
        self.assertIn("task30_cases.py", table.sealed)

    def test_the_matrix_fixtures_are_sealed_with_the_driver(self):
        for name in ("MatrixSupport.sml", "MatrixPerformance.sml"):
            self.assertIn(name, t30.TABLE.sealed)

    def test_the_sources_cover_the_modules_the_cases_call_into(self):
        # The simplifier's own modules and what every case calls through
        # them (see the comment on SOURCES for what stays outside).
        for path in (
                "src/simp/src/Trace.sig", "src/simp/src/SimpTracking.sml",
                "src/simp/src/SimpTracking.sig", "src/postkernel/Theory.sml",
                "src/postkernel/Theory.sig", "src/prekernel/Context.sml",
                "src/lite/liteLib.sml", "src/marker/markerSyntax.sml",
                "src/portableML/Uref.sml", "src/1/Drule.sml",
                "src/1/Conv.sml", "src/1/Tactical.sml"):
            self.assertIn(path, cases.SOURCES)
        for path in cases.SOURCES:
            if path.endswith(".sml"):
                self.assertIn(path[:-3] + "sig", cases.SOURCES, path)

    def test_the_pins_are_the_reviewed_simplifier_files(self):
        table = t30.TABLE
        self.assertEqual(table.pinned, cases.PINNED)
        self.assertEqual(sorted(cases.PINNED), [
            "src/simp/src/Cond_rewr.sig", "src/simp/src/Cond_rewr.sml",
            "src/simp/src/SimpTracking.sig", "src/simp/src/SimpTracking.sml"])
        for path, pin in cases.PINNED.items():
            self.assertIn(path, cases.SOURCES)
            self.assertRegex(pin["blob"], "^[0-9a-f]{40}$")
            self.assertTrue(pin["reason"].endswith("."), path)

    def checkout(self):
        if git("rev-parse", "--git-dir") is None or \
                git("cat-file", "-e", a.BASE + "^{commit}") is None:
            self.skipTest("needs a checkout holding the baseline commit")

    def test_each_pin_is_the_blob_of_the_file_in_this_checkout(self):
        self.checkout()
        for path, pin in cases.PINNED.items():
            with self.subTest(path):
                self.assertEqual(disk_blob(path), pin["blob"])
                self.assertNotEqual(base_blob(path), pin["blob"])

    def test_the_files_added_by_the_candidate_are_pinned(self):
        self.checkout()
        for path in cases.SOURCES:
            if base_blob(path) is None:
                self.assertIn(path, cases.PINNED, path)
                self.assertTrue((REPO / path).is_file(), path)
        self.assertIsNone(base_blob("src/simp/src/SimpTracking.sml"))

    def test_every_unpinned_source_is_the_baseline_file_here(self):
        self.checkout()
        for path in cases.SOURCES:
            if path not in cases.PINNED:
                with self.subTest(path):
                    self.assertEqual(disk_blob(path), base_blob(path))

    def test_the_allocation_text_names_the_task_selection(self):
        self.assertIn("--task task30", t30.TABLE.allocation)
        self.assertNotIn("outside", t30.TABLE.allocation)


class Whole(ttg.Rig):
    """The TASK30 table, run end to end on the stand-ins."""
    pairs, samples = 20, 5

    def make_table(self, **kw):
        table = copy.copy(t30.TABLE)
        table.driver, table.counts = self.driver, self.counts
        return table

    def setUp(self):
        super().setUp()
        # The files the candidate adds are absent at the baseline.
        self.absent = {p for p in cases.PINNED if p.endswith(
            ("SimpTracking.sml", "SimpTracking.sig"))}

    def fake_blob(self, repo, rev, path):
        """As the rig's, but the candidate holds each pinned file at its
        pinned blob, as the table requires."""
        if rev == ttg.CANDIDATE and path in cases.PINNED:
            return cases.PINNED[path]["blob"]
        return super().fake_blob(repo, rev, path)

    def test_a_clean_grid_runs_144_cells_and_passes(self):
        out, code, text = self.first()
        self.assertEqual(code, 0)
        self.assertEqual(len(self.runs), 144)
        self.assertIn("TASK30 grid: pass (pass 144, fail 0", text)
        self.assertNotIn("SOURCE-DIFFERS", text)
        identity = json.loads(
            (out / "decisions.json").read_text())["source_identity"]
        self.assertEqual(identity["differing"], [])
        self.assertEqual(identity["reviewed"], cases.PINNED)
        by_case = {}
        for options in self.runs:
            by_case.setdefault(options["case"][0], set()).add(
                options["batch_seconds"])
        self.assertEqual({c: s for c, s in by_case.items()},
                         {c: {t30.TABLE.seconds_for(c)}
                          for c in cases.CASES})
        self.assertEqual({o["layout_seed"] for o in self.runs},
                         {t30.LAYOUT_SEED})
        self.assertEqual({(o["pairs"], o["samples"]) for o in self.runs},
                         {(20, 5)})

    def test_one_open_cell_makes_the_exit_status_nonzero(self):
        for label, interval, code in (("fail", (1.04, 1.08), 1),
                                      ("inconclusive", ttg.WIDE, 2)):
            with self.subTest(label):
                self.candidate = (
                    lambda case, size, pairs, seed, i=interval: i
                    if (case, size) == ("history_makers", 1000)
                    else ttg.GOOD)
                out, status, text = self.first(name="g-" + label)
                self.assertEqual(status, code)
                self.assertIn("%s history_makers-1000" % label.upper(),
                              text)

    def test_a_missing_counts_cell_is_refused_before_any_run(self):
        value = json.loads(self.counts.read_text())
        del value["iterations"]["history_makers-1000"]
        self.counts.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "predeclared counts"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_the_command_line_is_the_shared_one(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError, "exclusive window"):
                t30.main(["run", "--output", tmp + "/x", "--candidate",
                          "c" * 40])
            with self.assertRaisesRegex(ValueError, "exclusive window"):
                t30.main(["pilot", "--output", tmp + "/x"])


tearDownModule = ttg.tearDownModule


if __name__ == "__main__":
    unittest.main()
