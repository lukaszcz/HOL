#!/usr/bin/env python3
"""TASK30 timing table: its cells, its seconds, and a full synthetic grid.

The engine is tested in test_timing_grid.py; here the TASK30 table itself is
checked, and the engine runs it whole (144 cells) on synthetic stand-ins.
"""
import contextlib
import copy
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest
import unittest.mock

import acceptance as a
import matrix_schema as ms
import task30_cases as cases
import task30_grid as t30
import task30_pins as pins
import test_timing_grid as ttg
import timing_grid as tg


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
        self.assertEqual(table.latest(), t30.COUNTS)
        self.assertEqual(table.files()[0], t30.COUNTS)
        self.assertEqual((table.pilot_pairs, table.pilot_samples), (10, 3))
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

    def test_the_seal_histories_hold_only_seals_that_records_carry(self):
        # Every TASK30 record (pilot, grid, stage 2) carries these seals of
        # the driver, the engine, acceptance.py and run_paired.py. The only
        # later entry is task29_gate.py (the Y records), the file before the
        # "exclusive window" wording was dropped; the follow-up's own table
        # (task30_followup.py) holds the seals its records carry.
        def seals(entries):
            return [(d["bytes"], d["sha256"]) for d in entries]
        self.assertEqual(seals(t30.DRIVERS), [(
            9634, "b958adae97df21cbcd5b1b72b5d47fa5455854aec6f45c133f"
            "042fb0e883586f")])
        self.assertEqual(seals(t30.ENGINES), [(
            131311, "b32f98ecee9fd2dbbebf5c21ca2ca0537442b3ba1b070861fe"
            "00a68910cd7d49")])
        self.assertEqual(seals(t30.ACCEPTANCE), [(
            38678, "108a0d0827ec6848a0c1e2e6987f9f8002591ac24498c7119c"
            "f5f58f14725b83")])
        history = t30.SEALED_HISTORY
        self.assertEqual(seals(history["../compatibility/run_paired.py"]), [(
            48705, "81baeb647f95850f267e3f72b333cc2a4921e342070c92a951"
            "a1e34583738dac")])
        self.assertEqual(seals(history["task29_gate.py"]), [(
            9766, "2e7a4f8db0bb4bc98a37b4500b88b2096c979c495bcd3cab4a"
            "63d184f332d16e")])

    def test_the_baseline_sources_and_sealed_files_are_named(self):
        table = t30.TABLE
        self.assertEqual(table.baseline, a.BASE)
        self.assertEqual(table.engines, t30.ENGINES)
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
                                        "sealed", "pins"))
        self.assertIn("task30_cases.py", table.sealed)
        self.assertEqual(table.pin_file, "task30_pins.py")

    def test_the_table_keeps_the_ramp_schedule(self):
        # The warmup schedule is for new tables; this one, its counts, pilot
        # and grid are those of the historical schedule.
        table = t30.TABLE
        # The default being warmup, ramp here means the table names it.
        self.assertEqual((table.schedule, table.headroom), ("ramp", 2))
        if not t30.COUNTS.exists():
            self.skipTest("the counts are not committed")
        counts = a.load(t30.COUNTS)
        self.assertNotIn("schedule", counts)
        self.assertEqual(tg.schedule_of(counts), "ramp")
        self.assertEqual(counts["rule"], tg.RAMP_RULE)
        self.assertEqual(counts["rule"],
                         "HEADROOM * max develop calibration count in B/B")

    def test_the_pins_are_recorded_apart_from_the_sealed_files(self):
        # A pin is bumped after a production fix, and must not change the
        # seal the counts are bound to.
        table = t30.TABLE
        self.assertNotIn("task30_pins.py", table.sealed)
        self.assertEqual(table.pinned, pins.PINNED)
        self.assertEqual(table.pin_history, pins.PIN_HISTORY)
        self.assertTrue((table.home / "task30_pins.py").is_file())

    def test_the_pin_history_is_kept_in_the_pin_file_not_in_the_driver(self):
        # A change of the history is a change of the pin file, whose seal a
        # grid records apart from the driver's: adding to it leaves the
        # driver, and so every earlier grid's driver seal, alone.
        self.assertFalse(hasattr(t30, "PIN_HISTORY"))
        driver = (t30.a.HERE / "task30_grid.py").read_text()
        self.assertNotIn("PIN_HISTORY =", driver)
        self.assertIn("PIN_HISTORY =", (t30.a.HERE / "task30_pins.py"
                                        ).read_text())

    def test_the_matrix_fixtures_are_sealed_with_the_driver(self):
        for name in ("MatrixSupport.sml", "MatrixPerformance.sml"):
            self.assertIn(name, t30.TABLE.sealed)

    def test_the_sealed_files_are_those_the_installer_installs(self):
        import allocation_matrix  # puts compatibility on the path
        import run_paired as rp
        copied = []
        real = rp.shutil.copyfile
        with tempfile.TemporaryDirectory() as tmp, \
                unittest.mock.patch.object(
                    rp.shutil, "copyfile",
                    lambda src, dst: copied.append(Path(src)) or real(
                        src, dst)):
            rp.install_fixtures(Path(tmp), performance=True,
                                matrix_fixture="MatrixPerformance.sml")
        self.assertGreater(len(copied), 5)
        names = {Path(os.path.relpath(p, a.HERE)).as_posix()
                 for p in copied}
        # What the installer reads besides, and the harness's data.
        names |= {"review-20261021/abicheck.sml", "matrix.json",
                  "../compatibility/run_paired.py"}
        self.assertEqual(names, set(t30.INSTALLED))
        self.assertLessEqual(set(t30.INSTALLED), set(t30.TABLE.sealed))
        self.assertEqual(
            sorted(set(t30.TABLE.sealed) - set(t30.INSTALLED)),
            sorted(["task30_cases.py", "task29_gate.py", "matrix_schema.py",
                    "performance_schema.py", "evidence_bundle.py"]))

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
        self.assertEqual(table.pinned, pins.PINNED)
        # Cond_rewr.sml is develop's again (TASK31); the one reviewed
        # difference is the added note_rewrite spec of its signature.
        self.assertEqual(sorted(pins.PINNED), ["src/simp/src/Cond_rewr.sig"])
        for path, pin in pins.PINNED.items():
            self.assertIn(path, cases.SOURCES)
            self.assertRegex(pin["blob"], "^[0-9a-f]{40}$")
            self.assertTrue(pin["reason"].endswith("."), path)

    def checkout(self):
        if git("rev-parse", "--git-dir") is None or \
                git("cat-file", "-e", a.BASE + "^{commit}") is None:
            self.skipTest("needs a checkout holding the baseline commit")

    def test_each_pin_is_the_blob_of_the_file_in_this_checkout(self):
        self.checkout()
        for path, pin in pins.PINNED.items():
            with self.subTest(path):
                self.assertEqual(disk_blob(path), pin["blob"])
                self.assertNotEqual(base_blob(path), pin["blob"])

    def test_the_files_added_by_the_candidate_are_pinned(self):
        self.checkout()
        gone = []
        for path in cases.SOURCES:
            if base_blob(path) is None:
                if (REPO / path).is_file():
                    self.assertIn(path, pins.PINNED, path)
                else:
                    gone.append(path)
        # TASK31 deleted SimpTracking; the sealed list still names it, so
        # the table refuses a new run ("absent at the baseline and not
        # pinned") until its owner revises that list.
        self.assertEqual(gone, ["src/simp/src/SimpTracking.sml",
                                "src/simp/src/SimpTracking.sig"])
        for path in gone:
            self.assertNotIn(path, pins.PINNED)

    def test_every_unpinned_source_is_the_baseline_file_here(self):
        self.checkout()
        for path in cases.SOURCES:
            if path not in pins.PINNED:
                with self.subTest(path):
                    self.assertEqual(disk_blob(path), base_blob(path))

    def test_the_allocation_text_names_the_task_selection(self):
        self.assertIn("--task task30", t30.TABLE.allocation)
        self.assertNotIn("outside", t30.TABLE.allocation)


# The commit the first-stage grid and the pilot were made at (before the
# warmup schedule changed some of the sealed files).
GRID_COMMIT = "63ac28189"


def seal_at(rev, path):
    """The seal of `path` (relative to the performance directory) as of
    commit `rev`, or None when the commit has no such file."""
    relative = os.path.normpath(str(a.HERE.relative_to(REPO) / path))
    found = subprocess.run(["git", "-C", str(REPO), "show",
                            "%s:%s" % (rev, relative)],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if found.returncode != 0:
        return None
    return dict(sha256=hashlib.sha256(found.stdout).hexdigest(),
                bytes=len(found.stdout))


@unittest.skipIf(git("cat-file", "-e", GRID_COMMIT + "^{commit}") is None,
                 "needs a checkout holding the commit of the grid")
class History(unittest.TestCase):
    """The code of the grid made at GRID_COMMIT is still accepted here."""

    def code_then(self):
        table = t30.TABLE
        code = dict(driver=seal_at(GRID_COMMIT, "task30_grid.py"),
                    engine=seal_at(GRID_COMMIT, "timing_grid.py"),
                    acceptance=seal_at(GRID_COMMIT, "acceptance.py"),
                    sealed={n: seal_at(GRID_COMMIT, n)
                            for n in table.sealed},
                    pins=seal_at(GRID_COMMIT, table.pin_file))
        self.assertNotIn(None, list(code["sealed"].values()))
        return code

    def test_the_seals_of_the_files_that_moved_are_in_the_history(self):
        table = t30.TABLE
        moved = {n: seal_at(GRID_COMMIT, n) for n in table.sealed
                 if seal_at(GRID_COMMIT, n) != a.seal(table.home / n)}
        # The files the warmup schedule changed are among them.
        self.assertGreaterEqual(set(moved), {
            "MatrixPerformance.sml", "performance_schema.py",
            "../compatibility/run_paired.py"})
        for name, seal in moved.items():
            self.assertIn(seal, table.sealed_history[name], name)
        for field, seals in (("driver", table.drivers),
                             ("engine", table.engines),
                             ("acceptance", table.layout_acceptance)):
            old = self.code_then()[field]
            self.assertIn(old, seals, field)

    def test_a_record_of_the_code_then_is_accepted_now(self):
        code = self.code_then()
        t30.ENGINE.check_code(code, True)
        t30.ENGINE.check_code(code, False)
        for field in ("driver", "engine", "acceptance"):
            bad = copy.deepcopy(code)
            bad[field] = dict(sha256="0" * 64, bytes=1)
            with self.subTest(field=field), self.assertRaises(ValueError):
                t30.ENGINE.check_code(bad, True)
        bad = copy.deepcopy(code)
        bad["sealed"]["MatrixPerformance.sml"] = dict(sha256="0" * 64,
                                                      bytes=1)
        with self.assertRaisesRegex(ValueError, "changed Matrix"):
            t30.ENGINE.check_code(bad, True)


class Followup(unittest.TestCase):
    """The follow-up table (task30_followup.py): two cells of the TASK30
    grid, measured again under the table's own conditions."""

    def test_it_is_the_two_cells_the_task30_grid_left_inconclusive(self):
        import task30_followup as f
        table = f.TABLE
        self.assertEqual(table.names(),
                         ["exclude_partial-1", "exclude_tactic_reuse-0"])
        self.assertEqual(table.cases, ("exclude_partial",
                                       "exclude_tactic_reuse"))
        self.assertLessEqual(set(table.names()), set(t30.TABLE.names()))
        self.assertIs(table.replaces.engine, t30.ENGINE)
        self.assertIs(table.replaces.table, t30.TABLE)
        self.assertEqual(table.replaces.rule, "inconclusive")
        self.assertEqual(table.family, t30.TABLE.name)
        self.assertEqual((table.name, table.label),
                         ("task30f", "TASK30-FOLLOWUP"))
        self.assertEqual(table.schema("iterations"),
                         "task30f-iterations-v1")

    def test_it_measures_as_task30_does_with_the_warmup_schedule(self):
        import task30_followup as f
        table = f.TABLE
        self.assertEqual((table.schedule, table.headroom), ("warmup", 1))
        self.assertTrue(table.fixed_seconds and table.require_seed and
                        table.engine)
        # Seconds: the TASK30 table's, per case.
        self.assertEqual(
            table.seconds_map(), {
                "exclude_partial-1": 1.0, "exclude_tactic_reuse-0": 0.3})
        for case in table.cases:
            self.assertEqual(table.seconds_for(case),
                             t30.TABLE.seconds_for(case))
        self.assertEqual((table.samples, table.pairs), (5, 40))
        self.assertEqual(table.pairs, 2 * t30.TABLE.pairs)
        self.assertEqual((table.target, table.max_pairs, table.baseline),
                         (0.015, 120, a.BASE))
        # The sealed files are TASK30's and TASK30's driver, which the
        # follow-up imports.
        self.assertEqual((table.sealed, table.sources, table.pinned,
                          table.pin_file, table.tree),
                         (t30.TABLE.sealed + ("task30_grid.py",),
                          t30.TABLE.sources, t30.TABLE.pinned,
                          t30.TABLE.pin_file, t30.TABLE.tree))
        self.assertEqual(table.code(), t30.TABLE.code())
        mine, theirs = f.ENGINE.code_now(), t30.ENGINE.code_now()
        self.assertEqual(mine["sealed"]["task30_grid.py"],
                         theirs["driver"])
        mine["sealed"].pop("task30_grid.py")
        self.assertEqual(
            {k: v for k, v in mine.items() if k != "driver"},
            {k: v for k, v in theirs.items() if k != "driver"})
        self.assertEqual(mine["driver"], a.seal(f.__file__))

    def test_its_seal_histories_are_those_the_module_names(self):
        # Appended when the code changes after the table's first record
        # (PROTOCOL.md): the mechanism is TASK30's. 40e176538f is the code
        # before the harness gave its children /dev/null for stdin.
        import task30_followup as f
        table = f.TABLE
        self.assertEqual(
            (f.DRIVERS, f.ENGINES, f.ACCEPTANCE, f.SEALED_HISTORY),
            ((dict(bytes=6360,
                   sha256="287a3140d4bd12567ca4fcf8510d2c6a"
                          "111b96116db8ebff9461905920fe8ebd"),),
             (dict(bytes=190317,
                   sha256="6fbc62fac47439a5a7ad13dd1f2edf61"
                          "62729a15f7cb7d6c28434f1a4ee06ac3"),),
             (dict(bytes=39557,
                   sha256="1076ad0d8f984a9081eaa2408554a483"
                          "2a0f3c092f6c5be25820537fa3c1a8e6"),),
             {"task30_grid.py": (dict(
                 bytes=11833, sha256="1022124dc9a7f051da45166f1ad254eb"
                                "ca43853d5b5cccf4e0dc34cd38dc9978"),),
              "../compatibility/run_paired.py": (dict(
                  bytes=49616, sha256="52622f55fa6399bd2df1557faeb0d881"
                                 "8358e6c46695487fd70e036f3c1fa4c7"),),
              "task29_gate.py": (dict(
                  bytes=9766, sha256="2e7a4f8db0bb4bc98a37b4500b88b209"
                                 "6c979c495bcd3cab4a63d184f332d16e"),)}))
        self.assertEqual((table.drivers, table.engines,
                          table.layout_acceptance, table.acceptance,
                          table.sealed_history),
                         (f.DRIVERS, f.ENGINES, f.ACCEPTANCE, (),
                          f.SEALED_HISTORY))
        # An older seal of a listed file is accepted by check_code, the
        # mechanism the history appends to.
        code = dict(f.ENGINE.code_now(),
                    engine=dict(bytes=1, sha256="0" * 64))
        with self.assertRaisesRegex(ValueError, "changed engine"):
            f.ENGINE.check_code(code, True)
        older = tg.Table(
            "task30f", "TASK30-FOLLOWUP", f.CASES, f.__file__, f.COUNTS,
            cells=f.CELLS, family="task30", replaces=table.replaces,
            seconds=t30.SECONDS, fixed_seconds=True, pairs=40,
            seed=f.LAYOUT_SEED, baseline=a.BASE, engine=True,
            engines=(dict(bytes=1, sha256="0" * 64),), sealed=f.SEALED,
            sealed_history={"task30_grid.py": (dict(
                bytes=2, sha256="1" * 64),)},
            seconds_by_case={"exclude_partial": t30.LONG_SECONDS},
            sources=table.sources, tree="src",
            layout_acceptance=(dict(bytes=3, sha256="2" * 64),))
        old = dict(f.ENGINE.code_now(),
                   engine=dict(bytes=1, sha256="0" * 64),
                   acceptance=dict(bytes=3, sha256="2" * 64))
        old["sealed"] = dict(old["sealed"], **{"task30_grid.py": dict(
            bytes=2, sha256="1" * 64)})
        tg.Grid(older).check_code(old, True)

    def test_its_layout_seed_is_not_the_task30_grids_nor_its_second_stage(
            self):
        import task30_followup as f
        self.assertEqual(f.TABLE.seed, "task30-followup-1")
        taken = {t30.LAYOUT_SEED, t30.LAYOUT_SEED + "-ext"}
        self.assertFalse({f.TABLE.seed, f.TABLE.seed + "-ext"} & taken)
        with self.assertRaisesRegex(ValueError, "seed of its own"):
            tg.Table(
                "task30f", "TASK30-FOLLOWUP", f.CASES, f.__file__, f.COUNTS,
                cells=f.CELLS, family="task30", seconds=t30.SECONDS,
                replaces=f.TABLE.replaces, fixed_seconds=True,
                pairs=40, seed=t30.LAYOUT_SEED + "-ext", baseline=a.BASE,
                seconds_by_case={"exclude_partial": t30.LONG_SECONDS})

    def test_its_evidence_is_kept_with_the_task30_ledger(self):
        import task30_followup as f
        for repo in (REPO, Path("/nowhere")):
            self.assertEqual(f.ENGINE.ledger_path(repo),
                             t30.ENGINE.ledger_path(repo))
            # The stamp and the prepare log are the table's own, beside the
            # one ledger; TASK30 keeps the names it always had.
            self.assertEqual(f.ENGINE.stamp_path(repo).parent,
                             t30.ENGINE.stamp_path(repo).parent)
            self.assertNotEqual(f.ENGINE.stamp_path(repo),
                                t30.ENGINE.stamp_path(repo))
            self.assertEqual(t30.ENGINE.stamp_path(repo).name,
                             "build-stamp.json")
            self.assertEqual(t30.ENGINE.prepare_log_path(repo).name,
                             "prepare.log")
            self.assertEqual(f.ENGINE.stamp_path(repo).name,
                             "build-stamp-task30f.json")
            self.assertEqual(f.ENGINE.prepare_log_path(repo).name,
                             "prepare-task30f.log")
        self.assertEqual(
            f.ENGINE.ledger_path(REPO).relative_to(REPO).as_posix(),
            ".agent-files/evidence/task30/attempts.jsonl")

    def test_its_sealed_set_is_the_codes_not_the_checkouts(self):
        # Repository names, from the root of the repository the code is in:
        # a replay pointed at another checkout sees the same set.
        import task30_followup as f
        found = f.ENGINE.sealed_paths()
        area = "src/simp/tests/performance/"
        self.assertIn("src/simp/tests/compatibility/run_paired.py", found)
        self.assertIn(area + "task30_followup.py", found)
        self.assertIn(area + "task30_grid.py", found)
        self.assertEqual(found, {
            (area + n if not n.startswith("../") else
             "src/simp/tests/" + n[3:]) for n in f.SEALED} |
            {area + "task30_followup.py"})
        self.assertEqual(t30.ENGINE.sealed_paths(), {
            (area + n if not n.startswith("../") else
             "src/simp/tests/" + n[3:]) for n in t30.SEALED} |
            {area + "task30_grid.py"})

    def test_the_table_loads_before_its_counts_exist(self):
        import task30_followup as f
        self.assertEqual(f.COUNTS.name, "task30_followup_iterations.json")
        self.assertEqual(f.TABLE.latest(), f.COUNTS)
        if f.COUNTS.exists():
            counts = a.load(f.COUNTS)
            self.assertEqual(counts["schema"], "task30f-iterations-v1")
            self.assertEqual(set(counts["iterations"]), set(f.CELLS))
            self.assertEqual(counts["pairs"], 40)
            self.assertEqual(set(counts["pairs_by_cell"]), set(f.CELLS))
            self.assertEqual(counts["seconds"], f.TABLE.seconds_map())
            self.assertEqual(tg.schedule_of(counts), "warmup")

    def test_its_commands_are_the_engines_with_the_replaced_grid(self):
        import task30_followup as f
        parser, sub = f.ENGINE.parser()
        for action, option in (("predeclare", "--replaces"),
                               ("predeclare", "--ledger"),
                               ("verify-counts", "--replaces-pilot"),
                               ("verify-counts", "--ledger"),
                               ("run", "--replaces"),
                               ("extend", "--replaces-pilot"),
                               ("replay", "--replaces-pilot")):
            self.assertIn(option, sub.choices[action].format_help(), action)
        with tempfile.TemporaryDirectory() as tmp:
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                self.assertEqual(f.main(["run", "--output", tmp + "/x",
                                         "--candidate", "c" * 40]),
                                 tg.REFUSED)
            self.assertEqual(err.getvalue(),
                             "REFUSED: measurement authorization required\n")


class Harness(unittest.TestCase):
    """The exact comparison of a timing grid's checkout with the harness of
    an allocation grid, as `close` makes it."""
    HEAD, TREE = "c" * 40, "t" * 64

    def timing(self, **kw):
        return dict(checkout=dict(
            dict(head=self.HEAD, tree_outside_performance=self.TREE), **kw))

    def counted(self, **kw):
        return dict(harness=dict(
            dict(head=self.HEAD, tree_outside_performance=self.TREE,
                 dirty=False), **kw))

    def test_one_head_one_tree_and_a_clean_checkout_match(self):
        counted = self.counted()
        self.assertIs(t30.harness_match(self.timing(), counted),
                      counted["harness"])

    def test_any_difference_is_a_refusal_naming_the_heads(self):
        for label, timing, counted in (
                ("head", self.timing(head="d" * 40), self.counted()),
                ("allocation head", self.timing(),
                 self.counted(head="d" * 40)),
                ("tree", self.timing(), self.counted(
                    tree_outside_performance="u" * 64)),
                ("timing tree", self.timing(
                    tree_outside_performance="u" * 64), self.counted()),
                ("dirty", self.timing(), self.counted(dirty=True)),
                ("not recorded dirty", self.timing(), dict(harness=dict(
                    head=self.HEAD, tree_outside_performance=self.TREE))),
                ("no harness", self.timing(), {})):
            with self.subTest(label), self.assertRaisesRegex(
                    ValueError, r"different harnesses \(head %s and "
                    % (timing["checkout"]["head"],)):
                t30.harness_match(timing, counted)

    def test_close_uses_it(self):
        with unittest.mock.patch.object(
                t30, "harness_match", side_effect=ValueError("seen")) as seen:
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                for name in ("grid", "alloc"):
                    (root / name).mkdir()
                (root / "grid" / "inventory.json").write_text(json.dumps(
                    dict(candidate="c" * 40, baseline=a.BASE)))
                (root / "alloc" / "inventory.json").write_text(json.dumps(
                    dict(task="task30", candidate="c" * 40,
                         baseline=a.BASE)))
                (root / "alloc" / "decisions.json").write_text("{}")
                with self.assertRaisesRegex(ValueError, "seen"):
                    t30.verdict(root / "grid", root / "alloc", REPO,
                                root / "pilot")
        self.assertEqual(seen.call_count, 1)


class Whole(ttg.Rig):
    """The TASK30 table, run end to end on the stand-ins."""
    pairs, samples = 20, 5

    def make_table(self, **kw):
        table = copy.copy(t30.TABLE)
        table.driver, table.counts = self.driver, self.counts
        table.ledger = self.attempts
        return table

    def setUp(self):
        super().setUp()
        # The candidate adds no file here: every pinned file exists at the
        # baseline, so nothing is absent.
        self.absent = set()

    def fake_blob(self, repo, rev, path):
        """As the rig's, but the candidate holds each pinned file at its
        pinned blob, as the table requires."""
        if rev == ttg.CANDIDATE and path in pins.PINNED:
            return pins.PINNED[path]["blob"]
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
        self.assertEqual(identity["reviewed"], pins.PINNED)
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
            for argv in (["run", "--output", tmp + "/x", "--candidate",
                          "c" * 40], ["pilot", "--output", tmp + "/x"]):
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    self.assertEqual(t30.main(argv), tg.REFUSED)
                self.assertEqual(
                    err.getvalue(),
                    "REFUSED: measurement authorization required\n")


class Closing(unittest.TestCase):
    """`close` replays the timing grid and the allocation grid and prints
    one verdict, only for one candidate in one harness."""
    CANDIDATE, HARNESS = "c" * 40, "c" * 40

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="task30-close-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.grid, self.allocation = self.root / "grid", self.root / "alloc"
        self.pilot = self.root / "pilot"
        for folder in (self.grid, self.allocation, self.pilot):
            folder.mkdir()
        self.codes = {"timing": 0, "allocation": 0}
        import allocation_matrix as am
        self.am = am
        for patcher in (
                unittest.mock.patch.object(t30.ENGINE, "replay",
                                           self.fake_timing),
                unittest.mock.patch.object(am, "replay",
                                           self.fake_allocation)):
            patcher.start()
            self.addCleanup(patcher.stop)
        self.replayed = []
        self.timing(), self.counted()
        # The ledger of the checkout the timing grid was made in: three
        # attempts, two of this candidate.
        self.ledger = self.root / "attempts.jsonl"
        for name, candidate, events in (
                ("a" * 32, self.CANDIDATE, ("open", "close")),
                ("b" * 32, "d" * 40, ("open", "close")),
                ("c" * 32, self.CANDIDATE, ("open",))):
            for event in events:
                tg.ledger_append(
                    self.ledger, event=event, stage="first", attempt=name,
                    candidate=candidate, status="pass", checkout="/here")

    def fake_timing(self, args):
        self.replayed.append(("timing", args.output, args.pilot,
                              args.ledger))
        return self.codes["timing"]

    def fake_allocation(self, args):
        self.replayed.append(("allocation", args.output))
        return self.codes["allocation"]

    def timing(self, status="pass", **more):
        head = more.pop("head", self.CANDIDATE)
        found = dict(candidate=self.CANDIDATE, baseline=a.BASE, checkout=dict(
            head=head, tree_outside_performance="t" * 64))
        found.update(more)
        (self.grid / "inventory.json").write_text(json.dumps(found))
        (self.grid / "decisions.json").write_text(json.dumps(dict(
            status=status, workloads=[], retained_scaling=None)))

    def counted(self, status="pass", **more):
        harness = dict(head=self.HARNESS, dirty=False,
                       tree_outside_performance="t" * 64)
        harness.update(more.pop("harness", {}))
        found = dict(task="task30", candidate=self.CANDIDATE,
                     baseline=a.BASE, harness=harness)
        found.update(more)
        (self.allocation / "inventory.json").write_text(json.dumps(found))
        (self.allocation / "decisions.json").write_text(json.dumps(
            dict(status=status)))

    def argv(self):
        return ["close", "--grid", str(self.grid), "--pilot",
                str(self.pilot), "--allocation", str(self.allocation),
                "--repo", str(REPO), "--ledger", str(self.ledger)]

    def close(self):
        """`close` as the engine runs it: a refusal is an exception here."""
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = t30.ENGINE.execute(self.argv(), extra=t30.commands())
        return code, out.getvalue()

    def test_a_refused_close_is_one_line_and_not_the_status_of_a_grid(self):
        self.ledger.unlink()
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = t30.main(self.argv())
        self.assertEqual(code, tg.REFUSED)
        self.assertRegex(err.getvalue(), r"^REFUSED: no attempts ledger: "
                         r".*attempts.jsonl\n$")

    def test_two_passes_of_one_candidate_in_one_harness_are_one_pass(self):
        code, text = self.close()
        self.assertEqual(code, 0)
        self.assertEqual([k for k, *_ in self.replayed],
                         ["timing", "allocation"])
        self.assertEqual(self.replayed[0][1:], (
            self.grid.resolve(), self.pilot.resolve(), self.ledger))
        verdicts = [x for x in text.splitlines() if "closing verdict" in x]
        self.assertEqual(verdicts, [
            "TASK30 closing verdict: pass (timing pass, allocation pass; "
            "candidate %s, harness %s; attempts 3 in the ledger, 2 of the "
            "candidate)" % (self.CANDIDATE, self.HARNESS)])

    def test_either_gate_that_is_not_a_pass_is_not_a_pass(self):
        for timing, allocation, code in ((1, 0, 1), (0, 1, 1), (2, 0, 2),
                                         (1, 2, 2)):
            with self.subTest((timing, allocation)):
                self.codes = {"timing": timing, "allocation": allocation}
                self.timing("fail" if timing == 1 else "inconclusive")
                got, text = self.close()
                self.assertEqual(got, code)
                self.assertIn("closing verdict: not pass (timing", text)

    def test_the_two_grids_must_be_of_one_candidate_and_baseline(self):
        self.counted(candidate="d" * 40)
        with self.assertRaisesRegex(ValueError, "timing grid measured"):
            self.close()
        self.counted(baseline="b" * 40)
        with self.assertRaisesRegex(ValueError, "different baselines"):
            self.close()

    def test_the_cheap_comparisons_come_before_the_replays(self):
        # Neither gate is replayed in full for a pair that cannot close.
        self.counted(candidate="d" * 40)
        with self.assertRaises(ValueError):
            self.close()
        self.counted(harness=dict(head="e" * 40))
        with self.assertRaises(ValueError):
            self.close()
        self.counted(task="task29b")
        with self.assertRaises(ValueError):
            self.close()
        self.counted()
        (self.allocation / "decisions.json").unlink()
        with self.assertRaises(ValueError):
            self.close()
        self.assertEqual(self.replayed, [])

    def test_close_reads_a_ledger_that_exists(self):
        self.ledger.unlink()
        with self.assertRaisesRegex(ValueError, "no attempts ledger"):
            self.close()

    def test_the_two_grids_must_have_run_in_one_harness(self):
        for label, harness in (
                ("head", dict(head="e" * 40)),
                ("tree", dict(tree_outside_performance="u" * 64)),
                ("dirty", dict(dirty=True))):
            with self.subTest(label):
                self.counted(harness=harness)
                with self.assertRaisesRegex(ValueError, "different "
                                            "harnesses"):
                    self.close()
        self.counted()
        self.timing(head="e" * 40)
        with self.assertRaisesRegex(ValueError, "different harnesses"):
            self.close()

    def test_the_allocation_grid_must_be_a_complete_task30_grid(self):
        self.counted(task="task29b")
        with self.assertRaisesRegex(ValueError, "not a TASK30 grid"):
            self.close()
        (self.allocation / "decisions.json").unlink()
        with self.assertRaisesRegex(ValueError, "allocation grid is "
                                    "partial"):
            self.close()

    def test_close_applies_no_disposition(self):
        self.codes = {"timing": 1, "allocation": 0}
        self.timing("fail")
        code, text = self.close()
        self.assertEqual(code, 1)
        self.assertNotIn("disposition", text.lower())
        self.assertEqual(sorted(p.name for p in self.grid.iterdir()),
                         ["decisions.json", "inventory.json"])

    def test_close_needs_the_grid_the_pilot_and_the_allocation(self):
        for missing in ("--grid", "--pilot", "--allocation"):
            argv = {"--grid": str(self.grid), "--pilot": str(self.pilot),
                    "--allocation": str(self.allocation)}
            del argv[missing]
            with self.subTest(missing), self.assertRaises(SystemExit), \
                    contextlib.redirect_stderr(io.StringIO()):
                t30.main(["close", *(x for kv in argv.items()
                                     for x in kv)])


class RealChain(ttg.ChainRig):
    """The operator's sequence on the real TASK30 table: its cells, seals and
    pins, real git and the real checkout binding, the real harness binding of
    the allocation gate and the real `close`. Only the build, the
    measurement and the allocation replay are stand-ins. The repository is a
    sparse shared clone of this one at its HEAD (the baseline and the
    reviewed sources are in its history), with the products a build leaves."""
    pairs, samples = 20, 5

    def setUp(self):
        if git("rev-parse", "--git-dir") is None or \
                git("cat-file", "-e", a.BASE + "^{commit}") is None:
            self.skipTest("needs a checkout holding the baseline commit")
        self.head = git("rev-parse", "HEAD")
        for path, pin in pins.PINNED.items():
            if git("rev-parse", "%s:%s" % (self.head, path)) != pin["blob"]:
                self.skipTest("the pins are not those of HEAD: " + path)
        import allocation_matrix as am
        self.am = am
        inputs, fixtures = am.harness_files(am.task_named("task30"))
        self.harness = [p for p in inputs + fixtures
                        if p.name != "task30_iterations.json"]
        if any(git("rev-parse", "%s:%s" % (
                self.head, p.relative_to(REPO).as_posix())) is None
                for p in self.harness):
            self.skipTest("needs the harness files committed")
        super().setUp()

    def make_table(self, **kw):
        if not hasattr(self, "base"):
            shutil.rmtree(self.repo)
            clone = ["git", "clone", "-q", "--shared", "--no-checkout",
                     str(REPO), str(self.repo)]
            subprocess.run(clone, check=True)
            self.git("sparse-checkout", "set", "--cone", "bin",
                     "src/simp/tests")
            self.git("-c", "advice.detachedHead=false", "checkout", "-q",
                     "--detach", self.head)
            (self.repo / ".git" / "info" / "exclude").write_text(
                ".agent-files\n")
            perf = self.repo / a.HERE.relative_to(REPO)
            self.counts = perf / "task30_iterations.json"
            if self.counts.exists():
                # Counts are committed: this chain starts before them. X
                # is HEAD's tree without the file, on the parent of the
                # commit that introduced it, so that the file has only the
                # commit of Y in the history of the chain (a file added,
                # removed and added again is refused).
                rel = str(self.counts.relative_to(self.repo))
                intro = self.git("log", "--format=%H", "--full-history",
                                 "--simplify-merges", "HEAD", "--",
                                 rel).split()[-1]
                self.git("rm", "-q", "-f", rel)
                x = self.git("commit-tree", self.git("write-tree"), "-p",
                             intro + "^", "-m", "X: without the counts")
                self.git("reset", "-q", "--soft", x)
            self.base = self.git("rev-parse", "HEAD")
            (self.repo / "bin" / "hol").write_text("executable")
            (self.repo / "bin" / "hol.state0").write_text("heap")
            (self.repo / "bin" / "Holmake").write_text("holmake")
            (self.repo / "sigobj").mkdir()
            (self.repo / "sigobj" / "m.uo").write_text("object")
            self.pilot_revision = a.BASE
        table = copy.copy(t30.TABLE)
        table.counts, table.ledger = self.counts, None
        # TASK31 deleted SimpTracking, which the sealed list still names, so
        # the real table refuses a new run (see
        # test_the_files_added_by_the_candidate_are_pinned). The chain
        # runs on the files of the list that exist at HEAD or the baseline.
        table.sources = tuple(
            p for p in cases.SOURCES if base_blob(p) is not None or git(
                "rev-parse", "--verify", "-q",
                "%s:%s" % (self.head, p)) is not None)
        return table

    def allocation_at(self, y):
        """The allocation gate's own harness binding, at Y, in this
        checkout, and a passing allocation grid of it."""
        move = lambda files: [self.repo / p.relative_to(REPO)
                              for p in files]
        inputs, fixtures = self.am.harness_files(self.am.task_named("task30"))
        binding = self.am.harness_binding(
            self.repo, y, move(inputs), move(fixtures))
        self.assertEqual(binding["head"], y)
        counted = self.root / "allocation"
        counted.mkdir()
        (counted / "inventory.json").write_text(json.dumps(dict(
            task="task30", candidate=y, baseline=a.BASE, harness=binding)))
        (counted / "decisions.json").write_text(json.dumps(
            dict(status="pass")))
        return counted

    def test_the_whole_sequence_from_prepare_to_the_closing_verdict(self):
        y = self.commit_counts()
        status, text = self.run_at(y)
        self.assertEqual(status, 0, text)
        self.assertIn("TASK30 grid: pass (pass 144, fail 0", text)
        grid = self.root / "grid"
        first = self.inventory(grid)
        self.assertEqual((first["candidate"], first["counts_commit"],
                          first["checkout"]["head"]), (y, y, y))
        self.assertEqual(len(self.runs), 144)
        decisions = json.loads((grid / "decisions.json").read_text())
        self.assertEqual(decisions["source_identity"]["differing"], [])
        self.assertEqual(decisions["source_identity"]["reviewed"],
                         pins.PINNED)
        self.assertEqual(self.go(self.replay_argv(grid))[0], 0)
        counted = self.allocation_at(y)
        out = io.StringIO()
        with unittest.mock.patch.object(t30, "ENGINE", self.grid), \
                unittest.mock.patch.object(t30, "TABLE", self.table), \
                unittest.mock.patch.object(self.am, "replay",
                                           lambda args: 0), \
                contextlib.redirect_stdout(out):
            code = t30.main(["close", "--grid", str(grid), "--pilot",
                             str(self.pilot_dir), "--allocation",
                             str(counted), "--repo", str(self.repo)])
        self.assertEqual(code, 0, out.getvalue())
        self.assertIn("TASK30 closing verdict: pass (timing pass, allocation "
                      "pass; candidate %s, harness %s; attempts 1 in the "
                      "ledger, 1 of the candidate)" % (y, y), out.getvalue())
        self.assertEqual(self.git("status", "--porcelain"), "")


    def test_a_close_and_a_replay_refuse_a_difference_found_not_marked(self):
        y = self.commit_counts()
        readme = self.repo / a.HERE.relative_to(REPO) / "README.md"

        def edit():
            readme.write_text(readme.read_text() + "edited\n")
        self.found_not_marked(y, "grid", edit)
        self.git("checkout", "--", str(readme))
        self.assertEqual(self.git("status", "--porcelain"), "")
        counted = self.allocation_at(y)
        grid = self.root / "grid"
        self.assertNotIn("checkout_changed", self.inventory(grid))
        with unittest.mock.patch.object(t30, "ENGINE", self.grid), \
                unittest.mock.patch.object(t30, "TABLE", self.table), \
                unittest.mock.patch.object(self.am, "replay",
                                           lambda args: 0):
            for command in (
                    ["close", "--grid", str(grid), "--pilot",
                     str(self.pilot_dir), "--allocation", str(counted),
                     "--repo", str(self.repo)],
                    ["replay", "--output", str(grid), "--repo",
                     str(self.repo), "--pilot", str(self.pilot_dir)]):
                err, out = io.StringIO(), io.StringIO()
                with contextlib.redirect_stderr(err), \
                        contextlib.redirect_stdout(out):
                    code = t30.main(command)
                self.assertEqual(code, tg.REFUSED, out.getvalue())
                self.assertRegex(
                    err.getvalue(), "^REFUSED: the checkout changed while "
                    "attempt .* ran .*the grid is dead")

    def test_a_new_grid_of_the_table_closes_past_the_found_of_a_dead_one(
            self):
        y = self.commit_counts()
        readme = self.repo / a.HERE.relative_to(REPO) / "README.md"

        def edit():
            readme.write_text(readme.read_text() + "edited\n")
        self.found_not_marked(y, "dead", edit)
        self.git("checkout", "--", str(readme))
        dead, = [k[0] for k in tg.Ledger(self.attempts_path()).attempts()]
        self.assertEqual(self.run_at(y, "grid")[0], 0)
        counted = self.allocation_at(y)
        grid = self.root / "grid"
        with unittest.mock.patch.object(t30, "ENGINE", self.grid), \
                unittest.mock.patch.object(t30, "TABLE", self.table), \
                unittest.mock.patch.object(self.am, "replay",
                                           lambda args: 0):
            outputs = []
            for command in (
                    ["replay", "--output", str(grid), "--repo",
                     str(self.repo), "--pilot", str(self.pilot_dir)],
                    ["close", "--grid", str(grid), "--pilot",
                     str(self.pilot_dir), "--allocation", str(counted),
                     "--repo", str(self.repo)]):
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    code = t30.main(command)
                self.assertEqual(code, 0, out.getvalue())
                outputs.append(out.getvalue())
        for text in outputs:
            self.assertRegex(text, "(?m)^CHECKOUT-FOUND-NOT-MARKED %s "
                             "tracked file.*; not marked: " % dead)
        self.assertIn("TASK30 closing verdict: pass", outputs[1])
        self.assertIn("attempts 2 in the ledger, 2 of the candidate",
                      outputs[1])
        self.assertEqual(self.git("status", "--porcelain"), "")


tearDownModule = ttg.tearDownModule


if __name__ == "__main__":
    unittest.main()
