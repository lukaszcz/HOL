#!/usr/bin/env python3
"""Shared timing grid: cells, counts, resume, replay, second stage, pilot.

Synthetic fixtures only. The acceptance runner and the statistics are
replaced by deterministic stand-ins that build a report exactly as
acceptance.run does (real decisions, real control rule), so the engine's own
logic is what these tests exercise. Nothing is measured, and this module (and
test_task30_grid.py) leaves the checkout alone: the lock is taken in a
throwaway git repository. Other modules of this directory run real timing
controls and take the lock in the checkout, so the whole suite does create
`.agent-files/` there.

The counts file of every rig comes from a (stand-in) pilot and `predeclare`,
as a fixed table's must; a pilot is made once for each table and copied.
"""
import argparse
import contextlib
import gzip
import inspect
import io
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
import traceback
import unittest
from unittest.mock import patch

import acceptance as a
import matrix_schema as ms
import timing_grid as tg
from performance_schema import batch_iterations

CASES = ("exclude_empty", "exclude_missing")
LONG = 1.0
SIZES = ms.SIZE_SETS["rules"]
CANDIDATE = "c" * 40
SOURCES = ("src/one.sml", "src/two.sml")
SEALED = ("one.txt", "two.txt")
COMMIT = "1" * 40
PRODUCTS = "p" * 64
GOOD = (0.99, 1.01)
WIDE = (0.95, 1.06)
# The real `run_logged`, before a rig puts a stand-in in its place.
REAL_RUN_LOGGED = a.run_logged


def interval_metric(ci, margin=0.03):
    return dict(decision=a.decision(ci[0], ci[1], margin),
                median_paired_ratio=1.0,
                paired_ratio_bootstrap_95_percent=list(ci),
                reason="paired bootstrap", margin=margin)


PILOTS = {}


def tearDownModule():
    """Pilots are kept for the tests of a module (and of a module that uses
    this one's rig), and removed with it."""
    if "dir" in PILOTS:
        PILOTS["dir"].cleanup()
    PILOTS.clear()


class Rig(unittest.TestCase):
    """A toy table, its files, a private repository and the stand-ins. The
    counts file is made by `predeclare` from a pilot, as a fixed table's must
    be (a pilot is made once per table and copied)."""
    pairs, samples = 10, 3

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="timing-grid-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)
        self.driver = self.root / "toy_grid.py"
        self.driver.write_text("# the toy driver\n")
        self.counts = self.repo / "toy_iterations.json"
        self.attempts = self.root / "attempts.jsonl"
        self.pilot_dir = self.root / "rig-pilot"
        self.committed, self.differ = True, set()
        self.absent, self.gone = set(), set()
        self.pilot_revision = a.BASE
        self.commits = [COMMIT]
        self.changes = [["A", "src/new.sml"], ["M", "src/one.sml"]]
        self.sealed_dir = self.root / "sealed"
        self.sealed_dir.mkdir()
        for name in SEALED:
            (self.sealed_dir / name).write_text("sealed " + name)
        self.table = self.make_table()
        self.grid = tg.Grid(self.table)
        self.runs, self.analyses, self.calls = [], [], 0
        self.launched = []
        self.max_count = lambda case, size: 2 ** len(str(size))
        self.control = lambda case, size, pairs, seed: GOOD
        self.pilot_control = self.control
        self.candidate = lambda case, size, pairs, seed: GOOD
        self.protocol_failure = lambda case, size: False
        self.explode_at = None
        self.kept, self.bound = [], []
        for target, stand_in in ((a, ("run", self.fake_run)),
                                 (a, ("analyze", self.fake_analyze)),
                                 (a, ("run_logged", self.fake_launch)),
                                 *self.git_stand_ins()):
            patcher = patch.object(target, stand_in[0], stand_in[1])
            patcher.start()
            self.addCleanup(patcher.stop)
        self.provision()

    def git_stand_ins(self):
        """What the rig fakes of git and of the checkout (a test with a real
        repository names none)."""
        return ((tg, ("git_blob", self.fake_blob)),
                (tg, ("git_commits", self.fake_commits)),
                (tg, ("git_difference", self.fake_difference)),
                (tg, ("git_keep", self.fake_keep)),
                (tg, ("git_tree_outside", self.fake_tree)),
                (tg, ("checkout_identity", self.fake_checkout)),
                (tg, ("known_difference", self.fake_known)))

    def make_table(self, cases=CASES, **kw):
        options = dict(seconds=0.3, seconds_by_case={CASES[0]: LONG},
                       fixed_seconds=True, schedule="ramp", pairs=self.pairs,
                       samples=self.samples, seed="s0", tree="src",
                       sources=SOURCES, sealed=SEALED, home=self.sealed_dir,
                       ledger=self.attempts)
        options.update(kw)
        return tg.Table("toy", "TOY", cases, self.driver, self.counts,
                        **options)

    def provision(self):
        """A pilot and the counts file `predeclare` makes of it. They are
        made once for each table and copied, because every test needs them."""
        t = self.table
        key = repr((t.keys(), t.seconds_map(), t.pairs, t.samples,
                    t.pilot_pairs, t.pilot_samples, t.seed, t.sealed,
                    t.schedule, t.headroom))
        kept = PILOTS.get(key)
        if kept is None:
            self.make_pilot(self.pilot_dir)
            made = self.root / "rig-counts.json"
            code, _ = self.go(["predeclare", "--grid", str(self.pilot_dir),
                               "--output", str(made)])
            a.require(code == 0, "the rig's counts")
            if "dir" not in PILOTS:
                PILOTS["dir"] = tempfile.TemporaryDirectory(
                    prefix="timing-pilots-")
            where = Path(PILOTS["dir"].name) / ("p%d" % len(PILOTS))
            shutil.copytree(self.pilot_dir, where)
            kept = PILOTS[key] = (where, made.read_text())
        else:
            shutil.copytree(kept[0], self.pilot_dir)
        self.counts.write_text(kept[1])
        self.launched.clear()
        self.analyses.clear()

    def make_pilot(self, out):
        code, _ = self.go(self.argv("pilot", out, "--authorize-measurements"))
        a.require(code == 0, "the rig's pilot")

    # Stand-ins -------------------------------------------------------

    def fake_blob(self, repo, rev, path):
        """Git blobs: the counts files as committed (or not), the sources
        the same at both commits except those in `differ`."""
        if len(rev) != 40:
            raise ValueError("unknown revision: " + rev)
        if (rev == a.BASE and path in self.absent) or (
                rev == CANDIDATE and path in self.gone):
            return None
        if path in [p.name for p in self.table.files()]:
            if isinstance(self.committed, str):
                return self.committed
            found = self.repo / path
            return a.git(repo, "hash-object", str(found)) \
                if self.committed and found.exists() else None
        return ("f" if rev == CANDIDATE and path in self.differ
                else "0") * 40

    def fake_commits(self, repo, rev, path):
        """The commits that changed a counts file: `commits`."""
        return list(self.commits) if self.fake_blob(repo, rev, path) else []

    def fake_difference(self, repo, baseline, candidate, tree):
        return sorted([s, p] for s, p in self.changes)

    def fake_keep(self, repo, table, commit):
        self.kept.append((table, commit))

    def fake_tree(self, repo, rev):
        return "t" * 64

    def fake_known(self, repo, recorded):
        """Nothing is known of a checkout that could not be judged."""
        return None

    def fake_checkout(self, repo, commit=None, stamp=None):
        """The checkout is clean and at the commit measured."""
        self.bound.append(commit)
        return dict(head=commit or COMMIT,
                    tree_outside_performance=self.fake_tree(repo, commit),
                    products=PRODUCTS)

    def analysis(self, case, size, control, pairs, seed, pilot=False):
        ci = (self.pilot_control if pilot else self.control if control
              else self.candidate)(case, size, pairs, seed)
        metrics = {m: interval_metric(ci) for m in ("cpu", "wall")}
        metrics["gc"] = dict(decision="reported", gated=False,
                             median_paired_ratio=1.0,
                             paired_ratio_bootstrap_95_percent=[0.5, 2.0],
                             reason="reported")
        return dict(case=case, size=size, metrics=metrics)

    def fake_analyze(self, folder, *, case, size, baseline, candidate, pairs,
                samples, seconds, iterations=None, policy=a.POLICY,
                layout_seed=None, schedule=None):
        self.analyses.append(dict(
            case=case, size=size, control=candidate == baseline,
            pairs=pairs, samples=samples, seconds=seconds,
            iterations=iterations, seed=layout_seed, policy=policy,
            **({} if schedule is None else dict(schedule=schedule))))
        return self.analysis(case, size, candidate == baseline, pairs,
                             layout_seed, pilot=iterations is None)

    def launch_head(self):
        """The head a pilot process runs at: the one the rig binds."""
        return COMMIT

    def fake_launch(self, command, output, fds, timeout, stdin=None,
                    append=False):
        """A pilot process: both sides the baseline, two develop receipts
        with calibration counts, and one of the loading fixture."""
        self.launched.append(command)
        folder = Path(command[command.index("--output") + 1])
        case = command[command.index("--performance-case") + 1]
        size = int(command[command.index("--performance-size") + 1])
        folder.mkdir(parents=True)
        seconds = self.table.seconds_for(case)
        for pair in range(2):
            # The final batch of the first process took 1.5 times the
            # target, that of the second 1.25 times it (a warmup count
            # reads the wall seconds).
            receipt = dict(fixture="performance", measurements=dict(
                workloads={case: dict(calibration=[
                    dict(iterations=1, wall=round(seconds / 100, 6)),
                    dict(iterations=self.max_count(case, size) // (
                        1 + pair),
                         wall=round(seconds * (1.5 - 0.25 * pair), 6))])}))
            with gzip.open(folder / ("pair-%02d.json.gz" % pair), "wt") as w:
                json.dump(receipt, w)
        with gzip.open(folder / "pair-99.json.gz", "wt") as stream:
            json.dump(dict(fixture="loading"), stream)
        # As run_paired does, the manifest names the head the pilot ran at.
        (folder / "manifest.json").write_text(json.dumps(dict(
            head=self.launch_head(),
            selections={side: dict(revision=self.pilot_revision)
                        for side in ("baseline", "candidate")})))
        Path(output).write_text("log\n")
        return dict(exit=0, timed_out=False)

    def fake_run(self, options):
        self.calls += 1
        if self.explode_at == self.calls:
            raise RuntimeError("infrastructure failure")
        case, size = options.case[0], options.size[0]
        self.runs.append(dict(vars(options)))
        folder = Path(options.output)
        folder.mkdir(parents=True)
        (folder / "evidence.txt").write_text("raw %s %d\n" % (case, size))
        if self.protocol_failure(case, size):
            report = dict(success=False, failure="runner failed",
                          workloads=[], commands=[])
        else:
            results = {}
            for selection in ("control", "candidate"):
                results[selection] = self.analysis(
                    case, size, selection == "control", options.pairs,
                    options.layout_seed)
            for name, value in results["candidate"]["metrics"].items():
                a.apply_control(value, results["control"]["metrics"][name])
            report = dict(success=True, policy=a.EQUIVALENCE_POLICY,
                          workloads=[results], commands=[],
                          retained_scaling=a.retained_scaling([results])
                          if case == "storage_graph" else None)
        a.save(folder / "acceptance.json", report)
        return report

    # Helpers ---------------------------------------------------------

    def argv(self, action, out, *extra):
        more = (["--pilot", str(self.pilot_dir)]
                if action in ("run", "extend") else [])
        return [action, "--output", str(out), "--repo", str(self.repo),
                *more, *extra]

    def replay_argv(self, out, *extra):
        return ["replay", "--output", str(out), "--repo", str(self.repo),
                "--pilot", str(self.pilot_dir), *extra]

    def go(self, argv, **kw):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = self.grid.execute(argv, **kw)
        return code, out.getvalue()

    def rewrite(self, **kw):
        """Change fields of the toy counts file."""
        value = json.loads(self.counts.read_text())
        value.update(kw)
        self.counts.write_text(json.dumps(value))

    def first(self, name="grid", extra=()):
        """A first stage with the settings of the counts file."""
        out = self.root / name
        argv = self.argv("run", out, "--candidate", CANDIDATE,
                         "--authorize-measurements", *extra)
        code, text = self.go(argv)
        return out, code, text

    def inventory(self, out):
        return json.loads((out / "inventory.json").read_text())

    def unrefused(self):
        """A grid recorded before `run` refused a source that cannot pass,
        which must still replay."""
        return patch.object(self.grid, "refuse_unpassable",
                            lambda args, differing: False)

    def grid_only(self, change):
        """`bundle.unpack` altered for the archives of the grid, not for the
        pilot's (which the run's provenance check unpacks too)."""
        real = tg.bundle.unpack

        def unpack(archive, output):
            if "grid" not in Path(archive).parts[-2:-1]:
                return real(archive, output)
            return change(archive, output, real)
        return patch.object(tg.bundle, "unpack", unpack)

    def cells(self):
        """The analyses of grid cells (those of the pilot's, made again by
        the provenance check, have no counts)."""
        return [r for r in self.analyses if r["iterations"] is not None]

    def declare_again(self, **table):
        """The counts file of the table as changed, made again by
        `predeclare` from the rig's pilot."""
        for key, value in table.items():
            setattr(self.table, key, value)
        self.counts.unlink()
        code, _ = self.go(["predeclare", "--grid", str(self.pilot_dir),
                           "--output", str(self.counts)])
        self.assertEqual(code, 0)

    def ledger(self):
        return [json.loads(line)
                for line in self.attempts.read_text().splitlines()]


class FirstStage(Rig):
    def test_every_cell_runs_with_its_count_seconds_and_seed(self):
        out, code, text = self.first()
        self.assertEqual(code, 0)
        keys = self.table.keys()
        self.assertEqual(len(keys), 12)
        self.assertEqual([(r["case"][0], r["size"][0]) for r in self.runs],
                         keys)
        counts = json.loads(self.counts.read_text())["iterations"]
        for options in self.runs:
            case, size = options["case"][0], options["size"][0]
            self.assertEqual(options["batch_iterations"],
                             counts["%s-%d" % (case, size)])
            self.assertEqual(options["batch_seconds"],
                             LONG if case == CASES[0] else 0.3)
            self.assertEqual(options["layout_seed"], "s0")
            self.assertEqual((options["pairs"], options["samples"]),
                             (10, 3))
            self.assertTrue(options["authorize_measurements"])
        header = self.inventory(out)
        self.assertEqual(header["schema"], "toy-experiment-v1")
        self.assertEqual(header["engine"], a.seal(tg.__file__))
        self.assertEqual(header["driver"], a.seal(self.driver))
        self.assertEqual(header["iterations"],
                         json.loads(self.counts.read_text()))
        self.assertEqual(len(header["runs"]), 12)
        self.assertEqual(json.loads((out / "decisions.json").read_text())[
            "schema"], "toy-grid-v1")
        self.assertIn("TOY grid: pass (pass 12, fail 0", text)

    def test_checks_recompute_with_the_cells_own_seconds(self):
        self.first()
        by_case = {(r["case"], r["size"]): r["seconds"]
                   for r in self.analyses}
        for (case, size), seconds in by_case.items():
            self.assertEqual(seconds, LONG if case == CASES[0] else 0.3)

    def test_a_cell_that_is_not_a_pass_fails_the_exit_status(self):
        cases = (
            ("fail", lambda *k: (1.04, 1.08), 1, "FAIL "),
            ("inconclusive", lambda *k: WIDE, 2, "INCONCLUSIVE "))
        for label, candidate, code, word in cases:
            with self.subTest(label):
                self.candidate = (lambda case, size, pairs, seed,
                                  c=candidate: c() if (case, size) ==
                                  (CASES[1], 10) else GOOD)
                out, status, text = self.first(name="g-" + label)
                self.assertEqual(status, code)
                self.assertIn(word + "%s-10" % CASES[1], text)
                self.assertIn("pass 11", text)

    def test_a_control_outside_the_window_is_listed_not_excused(self):
        self.control = (lambda case, size, pairs, seed:
                        WIDE if (case, size) == (CASES[0], 0) else GOOD)
        out, status, text = self.first()
        self.assertEqual(status, 2)
        self.assertIn("CONTROL-LIMITED %s-0" % CASES[0], text)
        self.assertNotIn("INCONCLUSIVE", text)
        self.assertEqual(json.loads((out / "decisions.json").read_text())[
            "status"], "inconclusive")

    def test_a_protocol_failure_is_unresolved_and_not_a_pass(self):
        self.protocol_failure = lambda case, size: (case, size) == (
            CASES[1], 0)
        out, status, text = self.first()
        self.assertEqual(status, 2)
        self.assertIn("PROTOCOL %s-0" % CASES[1], text)
        decisions = json.loads((out / "decisions.json").read_text())
        row, = [r for r in decisions["workloads"]
                if (r["case"], r["size"]) == (CASES[1], 0)]
        self.assertFalse(row["protocol"])

    def test_a_fail_outranks_an_unresolved_cell(self):
        self.protocol_failure = lambda case, size: (case, size) == (
            CASES[1], 0)
        self.candidate = (lambda case, size, pairs, seed:
                          (1.04, 1.08) if size == 1 else GOOD)
        out, status, text = self.first()
        self.assertEqual(status, 1)

    def test_layout_randomization_is_required(self):
        with self.assertRaisesRegex(ValueError, "names its layout seed"):
            self.make_table(seed=None)
        self.rewrite(layout_seed=None)
        with self.assertRaisesRegex(ValueError, "of the counts differs"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_a_table_may_waive_layout_randomization(self):
        self.declare_again(seed=None, require_seed=False)
        out, status, _ = self.first(name="unseeded")
        self.assertEqual(status, 0)
        self.assertNotIn("layout_seed", self.inventory(out))
        self.table.require_seed = True
        with self.assertRaisesRegex(ValueError, "needs layout randomiza"):
            self.first(name="seeded")

    def test_counts_must_match_the_table(self):
        def rewrite(value):
            self.counts.write_text(json.dumps(value))
        good = json.loads(self.counts.read_text())
        broken = (
            ("other schema", dict(good, schema="task29a-iterations-v1")),
            ("missing cell", dict(good, iterations={
                k: v for k, v in good["iterations"].items()
                if k != "exclude_missing-10"})),
            ("extra cell", dict(good, iterations=dict(
                good["iterations"], **{"exclude_missing-7": 64}))),
            ("other seconds", dict(good, seconds=dict(
                good["seconds"], **{"exclude_empty-0": 0.3}))),
            ("no seconds", {k: v for k, v in good.items()
                            if k != "seconds"}))
        for label, value in broken:
            with self.subTest(label):
                rewrite(value)
                with self.assertRaisesRegex(
                        ValueError, "predeclared counts"):
                    self.first(name="g-" + label.replace(" ", "-"))
        rewrite(good)
        self.assertEqual(self.calls, 0)

    def test_batch_seconds_are_the_tables(self):
        with self.assertRaisesRegex(ValueError, "batch seconds differ"):
            self.first(extra=("--batch-seconds", "0.5"))

    def test_a_counts_file_without_per_cell_seconds_is_refused_when_fixed(
            self):
        good = json.loads(self.counts.read_text())
        good["seconds"] = dict(good["seconds"], **{"exclude_empty-1": 5.0})
        self.counts.write_text(json.dumps(good))
        with self.assertRaisesRegex(ValueError, "predeclared counts"):
            self.first()

    def test_a_diagnostic_subset_is_never_a_decision(self):
        out, status, _ = self.first(extra=(
            "--only", "exclude_empty-0", "--only", "exclude_missing-10"))
        self.assertEqual(status, 2)
        self.assertEqual(len(self.runs), 2)
        self.assertFalse((out / "decisions.json").exists())
        with self.assertRaisesRegex(ValueError, "unknown --only cell"):
            self.first(name="other", extra=("--only", "nonexistent-3"))

    def test_measurements_need_authorization_and_exact_pins(self):
        argv = self.argv("run", self.root / "x", "--candidate", CANDIDATE)
        with self.assertRaisesRegex(ValueError, "exclusive window"):
            self.go(argv)
        with self.assertRaisesRegex(ValueError, "exact full git pin"):
            self.go(self.argv("run", self.root / "y", "--candidate",
                              "develop", "--authorize-measurements"))
        self.assertEqual(self.calls, 0)


class Transport(Rig):
    def test_a_transport_that_changes_bytes_is_refused(self):
        def corrupt(archive, output, real):
            count = real(archive, output)
            next(Path(output).rglob("evidence.txt")).write_text("x\n")
            return count
        with self.grid_only(corrupt), \
                self.assertRaisesRegex(ValueError, "transport changed"):
            self.first()

    def test_a_transport_that_loses_a_file_is_refused(self):
        with self.grid_only(lambda archive, output, real:
                            real(archive, output) + 1), \
                self.assertRaisesRegex(ValueError, "transport count"):
            self.first()

    def test_the_archive_is_written_before_the_cell_is_checked(self):
        self.candidate = lambda case, size, pairs, seed: (1.04, 1.08)
        real = self.fake_analyze

        def late(*args, **kw):
            if self.calls == 2 and kw["candidate"] != kw["baseline"]:
                raise ValueError("a replay defect")
            return real(*args, **kw)
        with patch.object(a, "analyze", late), \
                self.assertRaisesRegex(ValueError, "a replay defect"):
            self.first()
        out = self.root / "grid"
        self.assertEqual(sorted(p.name for p in out.glob("*.json.xz")),
                         ["exclude_empty-0.json.xz",
                          "exclude_empty-1.json.xz"])
        self.assertEqual(len(self.inventory(out)["runs"]), 2)


class Slope(Rig):
    """The retained-storage slope is part of the decision."""
    verdict = "pass"

    def make_table(self, **kw):
        return super().make_table(cases=("storage_graph",),
                                  seconds_by_case={}, **kw)

    def setUp(self):
        super().setUp()
        patcher = patch.object(a, "retained_scaling", self.slopes)
        patcher.start()
        self.addCleanup(patcher.stop)

    def slopes(self, workloads):
        return dict(status="measured", adjacent_intervals=[
            dict(selection="candidate",
                 words_per_rule=dict(decision=self.verdict)),
            dict(selection="control",
                 words_per_rule=dict(decision="fail"))])

    def test_a_slope_decides_the_exit_status(self):
        for verdict, code in (("pass", 0), ("fail", 1),
                              ("inconclusive", 2)):
            with self.subTest(verdict):
                self.verdict = verdict
                out, status, text = self.first(name="g-" + verdict)
                self.assertEqual(status, code)
                if verdict != "pass":
                    self.assertIn(verdict.upper() + " retained_scaling",
                                  text)

    def test_replay_recomputes_the_slope(self):
        out, _, _ = self.first()
        self.verdict = "fail"
        with self.assertRaisesRegex(ValueError, "changed slope analysis"):
            self.go(self.replay_argv(out))

    def test_the_grid_status_follows_the_slope_not_only_the_cells(self):
        # Every cell reports exit 0, so only the grid's own reading of the
        # slope can fail it.
        with patch.object(a, "report_exit_status", lambda report: 0):
            for verdict, code in (("pass", 0), ("fail", 1),
                                  ("inconclusive", 2)):
                with self.subTest(verdict):
                    self.verdict = verdict
                    out, status, _ = self.first(name="g-" + verdict)
                    self.assertEqual(status, code)
                    decisions = json.loads(
                        (out / "decisions.json").read_text())
                    self.assertEqual(decisions["status"], {
                        0: "pass", 1: "fail", 2: "inconclusive"}[code])

    def test_a_slope_that_is_not_measured_is_never_a_pass(self):
        blocked = lambda workloads: dict(status="blocked",
                                         adjacent_intervals=[])
        with patch.object(a, "report_exit_status", lambda report: 0), \
                patch.object(a, "retained_scaling", blocked):
            out, status, text = self.first()
        self.assertEqual(status, 2)
        self.assertIn("INCONCLUSIVE retained_scaling", text)


class Resume(Rig):
    def interrupted(self, at=4):
        self.explode_at = at
        with self.assertRaises(RuntimeError):
            self.first()
        self.explode_at = None
        return self.root / "grid"

    def resume(self, out, *extra):
        return self.go(self.argv(
            "run", out, "--candidate", CANDIDATE, "--authorize-measurements",
            "--resume", *extra))

    def test_finished_cells_are_kept_and_the_rest_measured(self):
        out = self.interrupted()
        self.assertEqual(len(self.inventory(out)["runs"]), 3)
        before = self.calls
        self.analyses.clear()
        status, text = self.resume(out)
        self.assertEqual(status, 0)
        self.assertEqual(self.calls - before, 9)
        self.assertEqual(len(self.inventory(out)["runs"]), 12)
        self.assertEqual(text.count("REPLAY "), 3)
        self.assertEqual(text.count("START "), 9)
        # Replayed cells are recomputed, not trusted.
        self.assertGreaterEqual(len(self.analyses), 2 * 12)

    def test_the_resumed_grid_replays_like_an_uninterrupted_one(self):
        out = self.interrupted()
        self.resume(out)
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertIn("TOY archives and decisions replayed: pass", text)

    def test_resume_refuses_other_settings(self):
        out = self.interrupted()
        for option in (("--pairs", "20"), ("--layout-seed", "s1")):
            with self.assertRaisesRegex(
                    ValueError, "differs from the predeclared"):
                self.resume(out, *option)
        with self.assertRaisesRegex(ValueError, "different settings"):
            self.go(self.argv(
                "run", out, "--candidate", "d" * 40,
                "--authorize-measurements", "--resume"))

    def test_resume_refuses_changed_counts_and_a_completed_run(self):
        out = self.interrupted()
        good = self.counts.read_text()
        value = json.loads(good)
        value["iterations"]["exclude_empty-0"] *= 2
        self.counts.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "differ from their pilot"):
            self.resume(out)
        self.counts.write_text(good)
        self.resume(out)
        with self.assertRaisesRegex(ValueError, "already complete"):
            self.resume(out)

    def test_resume_replays_finished_cells_against_their_counts(self):
        out = self.interrupted()
        inventory = self.inventory(out)
        inventory["runs"][0]["iterations"] *= 2
        (out / "inventory.json").write_text(json.dumps(inventory))
        with self.assertRaisesRegex(ValueError, "differs from predecl"):
            self.resume(out)

    def test_a_tampered_archive_is_refused_on_resume(self):
        out = self.interrupted()
        archive = next(out.glob("*.json.xz"))
        archive.write_bytes(archive.read_bytes() + b"x")
        with self.assertRaisesRegex(ValueError, "changed archive"):
            self.resume(out)

    def test_a_fresh_run_never_overwrites(self):
        out, _, _ = self.first()
        with self.assertRaises(FileExistsError):
            self.first()

    def test_a_changed_engine_is_refused_on_resume(self):
        out = self.interrupted()
        inventory = self.inventory(out)
        inventory["engine"] = dict(inventory["engine"], bytes=1)
        (out / "inventory.json").write_text(json.dumps(inventory))
        with self.assertRaisesRegex(ValueError, "changed engine"):
            self.resume(out)

    def test_a_code_change_across_a_resume_is_recorded(self):
        out = self.interrupted()
        known = [a.seal(self.driver)]
        self.driver.write_text("# the toy driver, changed\n")
        self.grid.t.drivers = tuple(known)
        status, _ = self.resume(out)
        self.assertEqual(status, 0)
        header = self.inventory(out)
        self.assertEqual(header["driver"], known[0])
        self.assertEqual(header["resumed"], [dict(
            driver=a.seal(self.driver), engine=a.seal(tg.__file__),
            acceptance=a.seal(a.__file__),
            sealed=self.grid.code_now()["sealed"], after=3)])
        status, _ = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.grid.t.drivers = ()
        with self.assertRaisesRegex(ValueError, "changed driver"):
            self.go(self.replay_argv(out))


class Replay(Rig):
    def test_decisions_and_archives_replay_offline(self):
        out, _, _ = self.first()
        self.analyses.clear()
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertEqual(text.count("REPLAY "), 12)
        # The cells, and the pilot's cells again (they have no counts).
        cells = self.cells()
        self.assertEqual(len(cells), 24)
        self.assertEqual(len(self.analyses) - len(cells), 12)
        self.assertEqual({(r["case"], r["size"]): r["seconds"]
                          for r in cells}[(CASES[0], 0)], LONG)
        self.assertEqual({r["iterations"] for r in cells
                          if r["case"] == CASES[1] and r["size"] == 0},
                         {json.loads(self.counts.read_text())[
                             "iterations"]["exclude_missing-0"]})

    def test_replay_repeats_the_exit_status_and_the_lists(self):
        self.candidate = (lambda case, size, pairs, seed:
                          (1.04, 1.08) if size == 100 else GOOD)
        out, status, _ = self.first()
        self.assertEqual(status, 1)
        again, text = self.go(self.replay_argv(out))
        self.assertEqual(again, 1)
        self.assertIn("FAIL %s-100" % CASES[0], text)

    def test_replay_recomputes_the_analysis(self):
        out, _, _ = self.first()
        self.candidate = lambda case, size, pairs, seed: (1.04, 1.08)
        with self.assertRaisesRegex(ValueError, "changed point analysis"):
            self.go(self.replay_argv(out))

    def test_replay_refuses_tampered_files(self):
        out, _, _ = self.first()
        decisions = (out / "decisions.json").read_text()
        (out / "decisions.json").write_text(decisions.replace(
            '"pass"', '"fail"', 1))
        with self.assertRaisesRegex(ValueError, "changed TOY decisions"):
            self.go(self.replay_argv(out))
        (out / "decisions.json").write_text(decisions)
        archive = out / ("%s-0.json.xz" % CASES[0])
        data = archive.read_bytes()
        archive.write_bytes(data[:-1] + bytes([data[-1] ^ 1]))
        with self.assertRaisesRegex(ValueError, "changed archive"):
            self.go(self.replay_argv(out))

    def test_replay_refuses_a_count_other_than_the_predeclared(self):
        out, _, _ = self.first()
        value = json.loads(self.counts.read_text())
        value["iterations"]["exclude_empty-0"] *= 2
        inventory = self.inventory(out)
        inventory["iterations"] = value
        self.counts.write_text(json.dumps(value))
        (out / "inventory.json").write_text(json.dumps(inventory))
        with self.assertRaisesRegex(ValueError, "changed counts seal"):
            self.go(self.replay_argv(out))

    def test_replay_of_an_interrupted_run_has_no_decision(self):
        self.explode_at = 5
        with self.assertRaises(RuntimeError):
            self.first()
        out = self.root / "grid"
        status, text = self.go(self.replay_argv(out, "--partial"))
        self.assertEqual(status, 2)
        self.assertIn("4 of 12 cells replayed", text)
        self.assertFalse((out / "decisions.json").exists())
        with self.assertRaisesRegex(ValueError, "incomplete TOY grid"):
            self.go(self.replay_argv(out))

    def test_partial_replay_of_a_complete_run_is_refused(self):
        out, _, _ = self.first()
        with self.assertRaisesRegex(ValueError, "complete run replayed"):
            self.go(self.replay_argv(out, "--partial"))

    def write(self, out, inventory):
        (out / "inventory.json").write_text(json.dumps(inventory))

    def test_every_analysis_uses_the_grids_layout_seed(self):
        self.declare_again(seed="abc")
        out, _, _ = self.first()
        seed = self.inventory(out)["layout_seed"]
        self.assertTrue(seed)
        self.assertEqual({r["seed"] for r in self.cells()}, {seed})
        self.analyses.clear()
        self.go(self.replay_argv(out))
        cells = self.cells()
        self.assertEqual(len(cells), 24)
        self.assertEqual({r["seed"] for r in cells}, {seed})

    def test_an_incomplete_experiment_needs_a_recorded_reason(self):
        def check(report):
            return self.grid.check_report(
                self.root, report, a.BASE, CANDIDATE, 0.3, CASES[0], 0, 64)
        with self.assertRaisesRegex(ValueError, "unexplained incomplete"):
            check(dict(success=False, workloads=[]))
        for reason in (dict(failure="runner failed"),
                       dict(blocked="no counter")):
            self.assertIsNone(check(dict(success=False, **reason)))

    def test_replay_refuses_a_changed_recorded_outcome(self):
        out, _, _ = self.first()
        inventory = self.inventory(out)
        for change in (dict(exit=1), dict(protocol=False)):
            with self.subTest(change):
                runs = [dict(inventory["runs"][0], **change)]
                self.write(out, dict(inventory,
                                     runs=runs + inventory["runs"][1:]))
                with self.assertRaisesRegex(ValueError,
                                            "changed experiment outcome"):
                    self.go(self.replay_argv(out))

    def test_replay_refuses_a_repeated_or_foreign_cell(self):
        out, _, _ = self.first()
        inventory = self.inventory(out)
        runs = inventory["runs"]
        for label, changed in (
                ("repeated", runs + [runs[0]]),
                ("foreign", [dict(runs[0], case="exclude_batch")]
                 + runs[1:])):
            with self.subTest(label):
                self.write(out, dict(inventory, runs=changed))
                with self.assertRaisesRegex(ValueError,
                                            "wrong/duplicate case"):
                    self.go(self.replay_argv(out))

    def test_replay_refuses_other_code_and_policy(self):
        out, _, _ = self.first()
        inventory = self.inventory(out)
        other = dict(bytes=1, sha256="0" * 64)
        for change, message in (
                (dict(acceptance=other), "changed acceptance"),
                (dict(driver=other), "changed driver"),
                (dict(engine=other), "changed engine"),
                (dict(policy=dict(inventory["policy"], margin=0.5)),
                 "changed policy")):
            with self.subTest(change):
                self.write(out, dict(inventory, **change))
                with self.assertRaisesRegex(ValueError, message):
                    self.go(self.replay_argv(out))

    def test_a_layout_seed_needs_a_layout_seeded_acceptance(self):
        out, _, _ = self.first()
        old = dict(bytes=1, sha256="0" * 64)
        self.write(out, dict(self.inventory(out), acceptance=old))
        self.table.acceptance = (old,)
        with self.assertRaisesRegex(ValueError, "layout-seeded"):
            self.go(self.replay_argv(out))


class SecondStage(Rig):
    pairs = 20

    def wide_unless_long(self, case, size, pairs, seed):
        if (case, size) == (CASES[1], 100):
            return GOOD if pairs >= 60 else WIDE
        return GOOD

    def stage(self, grid, name="ext", resume=False):
        argv = self.argv("extend", self.root / name, "--grid", str(grid),
                         "--authorize-measurements")
        if resume:
            argv.append("--resume")
        return self.go(argv)

    def test_the_refusals_that_need_no_replay_come_first_in_their_order(
            self):
        # The ledger and the output as at 6b0088ffbb, then the pilot (which
        # that commit refused only after the replay, in the provenance
        # check): each before the first stage is read (the grid named does
        # not exist).
        def replayed(*args, **kw):
            raise AssertionError("the first stage was replayed")
        argv = self.argv("extend", self.root / "ext", "--grid",
                         str(self.root / "nowhere"),
                         "--authorize-measurements")
        without = [x for i, x in enumerate(argv) if x != "--pilot" and
                   argv[i - 1] != "--pilot"]
        with patch.object(tg.Grid, "replay_grid", replayed):
            self.table.ledger = self.repo / "attempts.jsonl"
            with self.assertRaisesRegex(ValueError, "would be tracked"):
                self.go(without)
            self.table.ledger = self.attempts
            inside = [str(self.repo / "ext") if x == str(
                self.root / "ext") else x for x in without]
            with self.assertRaisesRegex(ValueError, "not ignored by git"):
                self.go(inside)
            with self.assertRaisesRegex(ValueError, "needs --pilot DIR"):
                self.go(without)

    def test_open_cells_are_remeasured_from_the_control_alone(self):
        self.control = self.wide_unless_long
        grid, status, _ = self.first()
        self.assertEqual(status, 2)
        self.runs.clear()
        status, text = self.stage(grid)
        self.assertEqual(status, 0)
        self.assertIn("PLAN 1 cells", text)
        self.assertEqual(len(self.runs), 1)
        options, = self.runs
        self.assertEqual((options["case"], options["size"]),
                         ([CASES[1]], [100]))
        self.assertEqual(options["layout_seed"], "s0-ext")
        self.assertGreaterEqual(options["pairs"], 60)
        self.assertEqual(options["batch_seconds"], 0.3)
        extension = self.inventory(self.root / "ext")
        self.assertEqual(extension["schema"], "toy-extension-v1")
        self.assertEqual(extension["engine"], a.seal(tg.__file__))
        decisions = json.loads((self.root / "ext" /
                                "decisions.json").read_text())
        self.assertEqual(decisions["status"], "pass")
        self.assertEqual(decisions["remeasured"]["plan"],
                         [[CASES[1], 100, options["pairs"]]])
        self.assertIn("TOY grid: pass", text)

    def test_the_second_stage_replays_and_is_tied_to_its_first_stage(self):
        self.control = self.wide_unless_long
        grid, _, _ = self.first()
        self.stage(grid)
        ext = self.root / "ext"
        status, text = self.go(self.replay_argv(ext))
        self.assertEqual(status, 0)
        self.assertIn("two-stage archives and decisions replayed: pass",
                      text)
        decisions = (ext / "decisions.json").read_text()
        (ext / "decisions.json").write_text(decisions.replace(
            '"pass"', '"fail"', 1))
        with self.assertRaisesRegex(ValueError, "changed TOY decisions"):
            self.go(self.replay_argv(ext))
        (ext / "decisions.json").write_text(decisions)
        inventory = self.inventory(ext)
        inventory["plan"] = [[CASES[1], 100, 20]]
        (ext / "inventory.json").write_text(json.dumps(inventory))
        with self.assertRaisesRegex(ValueError, "changed extension plan"):
            self.go(self.replay_argv(ext))

    def test_the_second_stage_uses_the_cells_own_seconds(self):
        self.control = (lambda case, size, pairs, seed:
                        GOOD if pairs >= 60 or (case, size) != (CASES[0], 10)
                        else WIDE)
        grid, _, _ = self.first()
        self.runs.clear()
        self.analyses.clear()
        status, _ = self.stage(grid)
        self.assertEqual(status, 0)
        run, = self.runs
        self.assertEqual((run["case"], run["size"]), ([CASES[0]], [10]))
        self.assertEqual(run["batch_seconds"], LONG)
        self.analyses.clear()
        self.go(self.replay_argv(self.root / "ext"))
        self.assertEqual({(r["seconds"], r["pairs"]) for r in self.cells()
                          if r["case"] == CASES[0] and r["size"] == 10},
                         {(LONG, 20), (LONG, tg.MAX_PAIRS)})

    def test_a_changed_first_stage_is_refused(self):
        self.control = self.wide_unless_long
        grid, _, _ = self.first()
        self.stage(grid)
        text = (grid / "decisions.json").read_text()
        (grid / "decisions.json").write_text(text + "\n")
        with self.assertRaisesRegex(ValueError, "changed first-stage"):
            self.go(self.replay_argv(self.root / "ext"))

    def test_a_cell_the_control_leaves_open_stays_open(self):
        self.control = lambda case, size, pairs, seed: (
            WIDE if (case, size) == (CASES[1], 100) else GOOD)
        grid, _, _ = self.first()
        status, text = self.stage(grid)
        self.assertEqual(status, 2)
        self.assertIn("CONTROL-LIMITED %s-100" % CASES[1], text)
        options, = self.runs[-1:]
        self.assertEqual(options["pairs"], tg.MAX_PAIRS)

    def test_a_first_stage_fail_is_final_whatever_its_control(self):
        self.control = lambda case, size, pairs, seed: (
            WIDE if (case, size) == (CASES[1], 100) else GOOD)
        self.candidate = lambda case, size, pairs, seed: (
            (1.04, 1.08) if (case, size) == (CASES[1], 100) else GOOD)
        grid, status, _ = self.first()
        self.assertEqual(status, 1)
        self.runs.clear()
        status, text = self.stage(grid)
        self.assertIn("PLAN 0 cells", text)
        self.assertEqual(self.runs, [])
        self.assertEqual(status, 1)
        self.assertIn("FAIL %s-100" % CASES[1], text)

    def test_the_second_stage_resumes(self):
        self.control = self.wide_unless_long
        self.candidate = lambda case, size, pairs, seed: GOOD
        grid, _, _ = self.first()
        self.explode_at = self.calls + 1
        with self.assertRaises(RuntimeError):
            self.stage(grid)
        self.explode_at = None
        status, _ = self.stage(grid, resume=True)
        self.assertEqual(status, 0)

    def test_the_second_stage_is_in_the_ledger_and_replay_needs_it(self):
        self.control = self.wide_unless_long
        grid, _, _ = self.first()
        status, _ = self.stage(grid)
        self.assertEqual(status, 0)
        lines = self.ledger()
        self.assertEqual([(x["stage"], x["event"]) for x in lines],
                         [("first", "open"), ("first", "close"),
                          ("second", "open"), ("second", "close")])
        first, ext = self.inventory(grid), self.inventory(self.root / "ext")
        # A second stage is an attempt of its own: a retry has another id.
        self.assertEqual(lines[2]["attempt"], ext["attempt"])
        self.assertNotEqual(ext["attempt"], first["attempt"])
        self.assertEqual(lines[3]["status"], "pass")
        keys = ("counts_file", "counts_commit", "source_tree", "checkout")
        self.assertEqual({k: ext[k] for k in keys},
                         {k: first[k] for k in keys})
        ledger = self.attempts.read_text().splitlines()
        for dropped in (2, 0):
            with self.subTest(dropped):
                self.attempts.write_text("\n".join(
                    x for i, x in enumerate(ledger) if i != dropped) + "\n")
                with self.assertRaisesRegex(ValueError, "chain broken"):
                    self.go(self.replay_argv(self.root / "ext"))
        self.attempts.write_text("\n".join(ledger) + "\n")
        self.assertEqual(self.go(self.replay_argv(self.root / "ext"))[0], 0)

    def test_a_second_stage_retried_is_a_new_attempt(self):
        self.control = self.wide_unless_long
        grid, _, _ = self.first()
        self.stage(grid, name="ext")
        self.stage(grid, name="again")
        opened = [x["attempt"] for x in self.ledger()
                  if x["event"] == "open" and x["stage"] == "second"]
        self.assertEqual(len(set(opened)), 2)
        # Replaying one names both, and takes only its own for its opening.
        status, text = self.go(self.replay_argv(self.root / "ext"))
        self.assertEqual(status, 0)
        self.assertEqual(text.count(" second opened "), 2)
        self.assertEqual(text.count("(this grid)"), 1)

    def test_the_second_stage_needs_the_ledger_and_the_first_opening(self):
        self.control = self.wide_unless_long
        grid, _, _ = self.first()
        self.table.ledger = self.root / "other.jsonl"
        with self.assertRaisesRegex(ValueError, "no attempts ledger"):
            self.stage(grid)
        self.table.ledger.write_text("")
        with self.assertRaisesRegex(ValueError, "no opening"):
            self.stage(grid)
        self.assertFalse((self.root / "ext").exists())

    def test_the_second_stage_derives_the_first_stages_commit_again(self):
        self.control = self.wide_unless_long
        grid, _, _ = self.first()
        header = self.inventory(grid)
        (grid / "inventory.json").write_text(
            json.dumps(dict(header, counts_commit="2" * 40)))
        with self.assertRaisesRegex(ValueError, "changed counts commit"):
            self.stage(grid)
        self.assertFalse((self.root / "ext").exists())

    def test_a_second_stage_refuses_a_schedule_switch_before_an_attempt(
            self):
        self.control = self.wide_unless_long
        grid, status, _ = self.first()
        self.assertEqual(status, 2)
        before = self.attempts.read_text()
        self.runs.clear()
        # The table switched to the warmup schedule after the first stage:
        # the grid still replays, but a second stage of it is refused, and
        # no attempt of the ledger records the refusal.
        self.table.schedule, self.table.headroom = "warmup", 1
        self.analyses.clear()
        with self.assertRaisesRegex(ValueError, "schedule of the counts"):
            self.stage(grid)
        self.assertEqual(self.runs, [])
        self.assertEqual(self.attempts.read_text(), before)
        self.assertEqual([(x["stage"], x["event"]) for x in self.ledger()],
                         [("first", "open"), ("first", "close")])
        self.assertFalse((self.root / "ext").exists())

    def test_a_grid_without_a_seed_has_no_second_stage(self):
        self.declare_again(seed=None, require_seed=False)
        grid, _, _ = self.first()
        with self.assertRaisesRegex(ValueError, "layout-randomized"):
            self.stage(grid)

    def two_open(self, case, size, pairs, seed):
        if case == CASES[1] and size in (0, 100):
            return GOOD if pairs >= 60 else WIDE
        return GOOD

    def test_the_second_stage_needs_authorization(self):
        self.control = self.wide_unless_long
        grid, _, _ = self.first()
        self.runs.clear()
        with self.assertRaisesRegex(ValueError, "exclusive window"):
            self.go(self.argv("extend", self.root / "ext", "--grid",
                              str(grid)))
        self.assertEqual(self.runs, [])
        self.assertFalse((self.root / "ext").exists())

    def test_only_a_first_stage_grid_has_a_second_stage(self):
        self.control = self.wide_unless_long
        grid, _, _ = self.first()
        self.stage(grid)
        with self.assertRaisesRegex(ValueError, "not a first-stage grid"):
            self.grid.replay_grid(self.root / "ext")

    def test_a_first_stage_whose_decisions_changed_is_refused(self):
        self.control = self.wide_unless_long
        grid, _, _ = self.first()
        decisions = (grid / "decisions.json").read_text()
        (grid / "decisions.json").write_text(decisions.replace(
            '"pass"', '"fail"', 1))
        with self.assertRaisesRegex(ValueError, "changed TOY decisions"):
            self.stage(grid)

    def test_the_remeasured_cells_follow_the_plan_in_order(self):
        self.control = self.two_open
        grid, _, _ = self.first()
        status, text = self.stage(grid)
        self.assertEqual(status, 0)
        self.assertIn("PLAN 2 cells", text)
        ext = self.root / "ext"
        inventory = self.inventory(ext)
        self.assertEqual(len(inventory["runs"]), 2)
        status, _ = self.go(self.replay_argv(ext))
        self.assertEqual(status, 0)
        (ext / "inventory.json").write_text(json.dumps(
            dict(inventory, runs=inventory["runs"][::-1])))
        with self.assertRaisesRegex(ValueError,
                                    "remeasurement differs from plan"):
            self.go(self.replay_argv(ext))

    def test_partial_replay_of_a_second_stage(self):
        self.control = self.two_open
        grid, _, _ = self.first()
        self.explode_at = self.calls + 2
        with self.assertRaises(RuntimeError):
            self.stage(grid)
        ext = self.root / "ext"
        status, text = self.go(self.replay_argv(ext, "--partial"))
        self.assertEqual(status, 2)
        self.assertIn("1 of 2 cells replayed", text)
        self.explode_at = None
        self.stage(grid, resume=True)
        with self.assertRaisesRegex(ValueError, "complete run replayed"):
            self.go(self.replay_argv(ext, "--partial"))

    def test_pair_count_rule(self):
        def report(control, candidate=GOOD):
            results = {}
            for selection, ci in (("control", control),
                                  ("candidate", candidate)):
                results[selection] = dict(metrics={
                    m: interval_metric(ci) for m in ("cpu", "wall")})
            for name, value in results["candidate"]["metrics"].items():
                a.apply_control(value, results["control"]["metrics"][name])
            return dict(success=True, workloads=[results])
        pairs = self.grid.extension_pairs
        self.assertIsNone(pairs(report(GOOD), 20))
        self.assertEqual(pairs(report((0.965, 1.071)), 20), tg.MAX_PAIRS)
        self.assertEqual(pairs(report((0.975, 1.035)), 20), 80)
        self.assertIsNone(pairs(dict(success=False), 20))
        self.assertIsNone(pairs(report((0.9, 1.1), (1.04, 1.08)), 20))
        # A control without an interval cannot size the remeasurement.
        for missing in (None, []):
            found = report(WIDE)
            for metric in found["workloads"][0]["control"][
                    "metrics"].values():
                metric["paired_ratio_bootstrap_95_percent"] = missing
            self.assertEqual(pairs(found, 20), tg.MAX_PAIRS)


class Classes(unittest.TestCase):
    @staticmethod
    def row(name, *decisions, reason="paired bootstrap", protocol=True):
        case, size = name.rsplit("-", 1)
        metrics = {m: dict(decision=d, reason=reason)
                   for m, d in zip(("cpu", "wall"), decisions)}
        metrics["gc"] = dict(decision="reported", reason="reported")
        return dict(case=case, size=int(size), protocol=protocol,
                    metrics=metrics)

    def decisions(self, *rows, scaling=None):
        return dict(workloads=list(rows), retained_scaling=scaling)

    def test_every_cell_lands_in_one_class(self):
        rows = [self.row("a-0", "pass", "pass"),
                self.row("b-0", "pass", "fail"),
                self.row("c-0", "inconclusive", "pass"),
                self.row("d-0", "inconclusive", "inconclusive",
                         reason=tg.CONTROL),
                self.row("e-0", "pass", "inconclusive", reason=tg.CONTROL),
                self.row("f-0", protocol=False)]
        cells = tg.classify(self.decisions(*rows))
        self.assertEqual(cells["pass"], ["a-0"])
        self.assertEqual(cells["fail"], ["b-0"])
        self.assertEqual(cells["inconclusive"], ["c-0"])
        self.assertEqual(cells["control_limited"], ["d-0", "e-0"])
        self.assertEqual(cells["protocol"], ["f-0"])
        self.assertEqual(sum(map(len, cells.values())), len(rows))

    def test_a_fail_beside_a_control_limited_metric_is_a_fail(self):
        row = self.row("a-0", "fail", "inconclusive", reason=tg.CONTROL)
        row["metrics"]["cpu"]["reason"] = "paired bootstrap"
        self.assertEqual(tg.classify_row(row), "fail")

    def test_mixed_reasons_are_inconclusive_not_control_limited(self):
        row = self.row("a-0", "inconclusive", "inconclusive")
        row["metrics"]["cpu"]["reason"] = tg.CONTROL
        self.assertEqual(tg.classify_row(row), "inconclusive")

    def test_retained_scaling_is_one_more_entry(self):
        def scaling(decision, status="measured"):
            return dict(status=status, adjacent_intervals=[
                dict(selection="candidate",
                     words_per_rule=dict(decision=decision)),
                dict(selection="control",
                     words_per_rule=dict(decision="fail"))])
        ok = self.row("a-0", "pass", "pass")
        self.assertEqual(tg.classify(self.decisions(
            ok, scaling=scaling("pass")))["pass"], ["a-0"])
        for decision, kind in (("fail", "fail"),
                               ("inconclusive", "inconclusive")):
            cells = tg.classify(self.decisions(
                ok, scaling=scaling(decision)))
            self.assertEqual(cells[kind], ["retained_scaling"])
        cells = tg.classify(self.decisions(
            ok, scaling=scaling("pass", "blocked")))
        self.assertEqual(cells["inconclusive"], ["retained_scaling"])

    def test_the_report_lists_every_open_cell_and_the_counts(self):
        rows = [self.row("a-0", "pass", "pass"),
                self.row("b-0", "pass", "fail")]
        lines = tg.class_report("T", dict(self.decisions(*rows),
                                          status="fail"))
        self.assertEqual(lines[0], "T grid: fail (pass 1, fail 1, "
                         "inconclusive 0, control-limited 0, protocol 0)")
        self.assertEqual(lines[1:], ["FAIL b-0"])


class Disposition(unittest.TestCase):
    """The generic disposition (`timing_grid.dispose`): a cell the control
    left open is attributed only when it is listed and its evidence holds."""
    row = staticmethod(Classes.row)
    LIMITED = ("exclude_missing-10", "exclude_empty-10000")

    def decisions(self, *rows, scaling=None):
        return dict(workloads=list(rows), retained_scaling=scaling)

    def grid(self, *extra):
        row = self.row
        return self.decisions(
            row("exclude_empty-0", "pass", "pass"),
            row("exclude_missing-10", "pass", "inconclusive",
                reason=tg.CONTROL),
            row("exclude_empty-10000", "inconclusive", "inconclusive",
                reason=tg.CONTROL), *extra)

    def test_a_listed_control_limited_cell_with_evidence_is_attributed(self):
        seen = []
        result = tg.dispose(self.grid(), self.LIMITED,
                            lambda cell: seen.append(cell))
        self.assertEqual(seen, sorted(self.LIMITED))
        self.assertEqual(result["status"], "pass")
        self.assertEqual(result["cells"], dict(
            fail=[], blocking=[], attributed=sorted(self.LIMITED),
            **{"pass": ["exclude_empty-0"]}))
        self.assertEqual(result["counts"], dict(
            fail=0, blocking=0, attributed=2, **{"pass": 1}))
        self.assertEqual(result["blocking"], {})

    def test_evidence_that_fails_blocks_and_names_what_failed(self):
        result = tg.dispose(
            self.grid(), self.LIMITED, lambda cell: "work row X differs"
            if cell == "exclude_empty-10000" else None)
        self.assertEqual(result["status"], "blocked")
        self.assertEqual(result["cells"]["attributed"],
                         ["exclude_missing-10"])
        self.assertEqual(result["blocking"], {
            "exclude_empty-10000":
            "control-limited, evidence fails: work row X differs"})

    def test_a_list_that_is_not_exactly_the_cells_found_is_stale(self):
        for label, listed, regex in (
                ("extra", (*self.LIMITED, "exclude_empty-0"),
                 r"listed but not control-limited: exclude_empty-0 \(pass\)"
                 "; control-limited but not listed: none"),
                ("missing", self.LIMITED[:1], r"listed but not "
                 r"control-limited: none; control-limited but not listed: "
                 "exclude_empty-10000"),
                ("not a cell", (*self.LIMITED, "no_case-1"),
                 r"listed but not control-limited: no_case-1 \(not a cell\)"
                 )):
            with self.subTest(label), self.assertRaisesRegex(
                    ValueError, "stale attribution: " + regex):
                tg.dispose(self.grid(), listed, lambda cell: None)

    def test_the_evidence_is_not_asked_for_a_list_that_is_stale(self):
        asked = []
        with self.assertRaisesRegex(ValueError, "stale attribution"):
            tg.dispose(self.grid(), self.LIMITED[:1],
                       lambda cell: asked.append(cell))
        self.assertEqual(asked, [])

    def test_a_fail_stays_a_fail_and_is_not_attributed(self):
        row = self.row("exclude_empty-1", "pass", "fail")
        result = tg.dispose(self.grid(row), self.LIMITED,
                            lambda cell: None)
        self.assertEqual(result["status"], "fail")
        self.assertEqual(result["cells"]["fail"], ["exclude_empty-1"])
        # A listed cell that turned into a fail is a stale list, which
        # names the class it is in.
        with self.assertRaisesRegex(
                ValueError, r"exclude_empty-1 \(fail\)"):
            tg.dispose(self.grid(row), (*self.LIMITED, "exclude_empty-1"),
                       lambda cell: None)

    def test_inconclusive_and_protocol_cells_block(self):
        for label, row, reason in (
                ("inconclusive", self.row("exclude_empty-1", "pass",
                                          "inconclusive"), "inconclusive"),
                ("protocol", self.row("exclude_empty-1", protocol=False),
                 "no admitted measurement")):
            with self.subTest(label):
                result = tg.dispose(self.grid(row), self.LIMITED,
                                    lambda cell: None)
                self.assertEqual(result["status"], "blocked")
                self.assertEqual(result["blocking"],
                                 {"exclude_empty-1": reason})
                self.assertEqual(result["cells"]["attributed"],
                                 sorted(self.LIMITED))

    def test_a_fail_wins_over_a_block(self):
        rows = (self.row("exclude_empty-1", "pass", "fail"),
                self.row("exclude_empty-2", "pass", "inconclusive"))
        result = tg.dispose(self.grid(*rows), self.LIMITED,
                            lambda cell: None)
        self.assertEqual(result["status"], "fail")
        self.assertEqual(result["counts"]["blocking"], 1)

    def test_the_retained_slope_is_a_cell_too(self):
        def scaling(decision):
            return dict(status="measured", adjacent_intervals=[dict(
                selection="candidate",
                words_per_rule=dict(decision=decision))])
        for decision, status in (("pass", "pass"), ("fail", "fail"),
                                 ("inconclusive", "blocked")):
            with self.subTest(decision):
                result = tg.dispose(
                    dict(self.grid(), retained_scaling=scaling(decision)),
                    self.LIMITED, lambda cell: None)
                self.assertEqual(result["status"], status)

    def test_nothing_is_attributed_without_a_listed_cell(self):
        # A table with no control-limited cell lists none and passes.
        result = tg.dispose(self.decisions(
            self.row("exclude_empty-0", "pass", "pass")), (),
            lambda cell: self.fail("asked"))
        self.assertEqual(result["status"], "pass")


class Pilot(Rig):
    def pilot(self, name="pilot", extra=()):
        argv = self.argv("pilot", self.root / name, "--authorize-measurements",
                         *extra)
        return self.go(argv)

    def test_the_pilot_is_develop_only_and_archives_every_cell(self):
        status, text = self.pilot()
        self.assertEqual(status, 0)
        self.assertEqual(len(self.launched), 12)
        for command in self.launched:
            self.assertEqual(command[command.index("--baseline") + 1],
                             a.BASE)
            self.assertEqual(command[command.index("--candidate") + 1],
                             a.BASE)
            self.assertNotIn("--batch-iterations", command)
            self.assertNotIn("--layout-seed", command)
            case = command[command.index("--performance-case") + 1]
            self.assertEqual(
                float(command[command.index("--batch-seconds") + 1]),
                LONG if case == CASES[0] else 0.3)
        inventory = self.inventory(self.root / "pilot")
        self.assertEqual(inventory["schema"], "toy-pilot-v1")
        self.assertEqual(len(inventory["runs"]), 12)
        self.assertEqual(inventory["engine"], a.seal(tg.__file__))
        self.assertEqual(self.analyses[0]["control"], True)
        self.assertEqual(self.analyses[0]["pairs"], 10)

    def test_predeclared_counts_come_from_the_pilot_alone(self):
        self.pilot()
        out = self.root / "counts.json"
        status, _ = self.go(["predeclare", "--grid",
                             str(self.root / "pilot"), "--output",
                             str(out)])
        self.assertEqual(status, 0)
        value = json.loads(out.read_text())
        self.assertEqual(value["schema"], "toy-iterations-v1")
        self.assertEqual(set(value["iterations"]),
                         set(self.table.names()))
        for key, count in value["iterations"].items():
            case, size = key.rsplit("-", 1)
            self.assertEqual(count, batch_iterations(
                self.expected(case, int(size))))
        self.assertEqual(value["seconds"], self.table.seconds_map())
        self.assertEqual(value["headroom"], 2)
        # What the pilot predeclares is what a run accepts.
        self.counts.write_text(json.dumps(value))
        out_grid, status, _ = self.first(extra=(
            "--pilot", str(self.root / "pilot")))
        self.assertEqual(status, 0)

    def expected(self, case, size):
        """Twice the largest develop count, itself a power of two."""
        return 2 * self.max_count(case, size)

    def test_predeclare_never_overwrites(self):
        self.pilot()
        out = self.root / "counts.json"
        out.write_text("{}")
        with self.assertRaisesRegex(ValueError, "refusing to overwrite"):
            self.go(["predeclare", "--grid",
                     str(self.root / "pilot"), "--output", str(out)])

    def test_predeclare_refuses_a_pilot_of_other_seconds_or_tasks(self):
        self.pilot()
        path = self.root / "pilot" / "inventory.json"
        good = path.read_text()
        for change, message in (
                (dict(seconds=0.5), "pilot batch seconds differ"),
                (dict(seconds_by_case={}), "pilot batch seconds differ"),
                (dict(schema="other-pilot-v1"), "pilot of another task")):
            with self.subTest(change):
                path.write_text(json.dumps(dict(json.loads(good), **change)))
                with self.assertRaisesRegex(ValueError, message):
                    self.go(["predeclare", "--grid",
                             str(self.root / "pilot"), "--output",
                             str(self.root / "c.json")])

    def test_predeclare_refuses_an_incomplete_or_altered_pilot(self):
        self.pilot()
        path = self.root / "pilot" / "inventory.json"
        good = json.loads(path.read_text())
        path.write_text(json.dumps(dict(good, runs=good["runs"][:-1])))
        with self.assertRaisesRegex(ValueError, "incomplete predeclared"):
            self.declare()
        path.write_text(json.dumps(good))
        archive = self.root / "pilot" / good["runs"][0]["archive"]
        archive.write_bytes(archive.read_bytes() + b"x")
        with self.assertRaisesRegex(ValueError, "changed archive"):
            self.declare()

    def test_a_pilot_needs_the_protocol_minimum_and_an_exact_pin(self):
        with self.assertRaisesRegex(ValueError, "at least ten pairs"):
            self.pilot(extra=("--pairs", "9"))
        with self.assertRaisesRegex(ValueError, "at least ten pairs"):
            self.pilot(extra=("--samples", "2"))
        with self.assertRaisesRegex(ValueError, "exact full git pin"):
            self.pilot(extra=("--baseline", "develop"))
        with self.assertRaisesRegex(ValueError, "exclusive window"):
            self.go(self.argv("pilot", self.root / "p"))
        self.assertEqual(self.launched, [])

    def test_a_failed_runner_records_nothing_for_the_cell(self):
        def failing(command, output, fds, timeout):
            self.fake_launch(command, output, fds, timeout)
            return dict(exit=1, timed_out=False)
        with patch.object(a, "run_logged", failing):
            with self.assertRaisesRegex(ValueError, "pilot runner failed"):
                self.pilot()
        self.assertEqual(self.inventory(self.root / "pilot")["runs"], [])
        self.assertEqual(len(list((self.root / "pilot").glob(
            "*.json.xz.failed-1"))), 1)

    def test_a_pilot_that_fails_the_protocol_check_is_not_kept(self):
        def refuse(*args, **kw):
            raise ValueError("failed experiment")
        with patch.object(a, "analyze", refuse):
            with self.assertRaisesRegex(ValueError, "failed experiment"):
                self.pilot()
        self.assertEqual(self.inventory(self.root / "pilot")["runs"], [])

    def test_the_pilot_resumes_without_repeating_finished_cells(self):
        calls = []

        def interrupting(command, output, fds, timeout):
            calls.append(command)
            if len(calls) == 4:
                raise RuntimeError("infrastructure failure")
            return self.fake_launch(command, output, fds, timeout)
        with patch.object(a, "run_logged", interrupting):
            with self.assertRaises(RuntimeError):
                self.pilot()
        self.assertEqual(len(self.inventory(self.root / "pilot")["runs"]), 3)
        self.launched.clear()
        status, _ = self.pilot(extra=("--resume",))
        self.assertEqual(status, 0)
        self.assertEqual(len(self.launched), 9)
        self.assertEqual(len(self.inventory(self.root / "pilot")["runs"]),
                         12)
        with self.assertRaisesRegex(ValueError, "different settings"):
            self.pilot(extra=("--resume", "--pairs", "12"))

    def interrupted(self):
        calls = []

        def interrupting(command, output, fds, timeout):
            calls.append(command)
            if len(calls) == 4:
                raise RuntimeError("infrastructure failure")
            return self.fake_launch(command, output, fds, timeout)
        with patch.object(a, "run_logged", interrupting):
            with self.assertRaises(RuntimeError):
                self.pilot()
        return self.root / "pilot"

    def test_a_pilot_waits_for_the_lock_before_its_first_checkpoint(self):
        with a.serial_lock(self.repo):
            with self.assertRaises(a.Blocked):
                self.pilot()
        self.assertFalse((self.root / "pilot").exists())
        out = self.interrupted()
        before = (out / "inventory.json").read_bytes()
        (out / "x.json.partial").write_text("half")
        with a.serial_lock(self.repo):
            with self.assertRaises(a.Blocked):
                self.pilot(extra=("--resume",))
        self.assertEqual((out / "inventory.json").read_bytes(), before)
        self.assertEqual((out / "x.json.partial").read_text(), "half")

    def test_a_pilot_is_made_in_the_checkout_of_its_own_commit(self):
        self.pilot()
        # The first binding finds the head; the two later ones compare it
        # with the head the inventory recorded.
        self.assertEqual(self.bound, [None, COMMIT, COMMIT])
        self.assertEqual(self.inventory(self.root / "pilot")["checkout"],
                         dict(head=COMMIT, tree_outside_performance="t" * 64,
                              products=PRODUCTS))

    def test_a_pilot_in_a_checkout_that_is_not_clean_measures_nothing(self):
        def unclean(repo, commit=None, stamp=None):
            raise ValueError("harness checkout is not clean: commit first")
        with patch.object(tg, "checkout_identity", unclean):
            with self.assertRaisesRegex(ValueError, "not clean"):
                self.pilot()
        self.assertEqual(self.launched, [])
        self.assertFalse((self.root / "pilot").exists())

    def test_a_resumed_pilot_is_of_the_same_checkout(self):
        self.interrupted()

        def elsewhere(repo, commit=None, stamp=None):
            return dict(head="e" * 40, tree_outside_performance="t" * 64)
        with patch.object(tg, "checkout_identity", elsewhere):
            with self.assertRaisesRegex(ValueError, "different settings"):
                self.pilot(extra=("--resume",))
        self.assertEqual(self.pilot(extra=("--resume",))[0], 0)

    def test_a_checkout_that_changed_under_the_pilot_makes_it_no_pilot(self):
        seen = []

        def identity(repo, commit=None, stamp=None):
            seen.append(commit)
            return self.fake_checkout(repo, commit, stamp) if len(
                seen) < 3 else dict(head=COMMIT,
                                    tree_outside_performance="u" * 64)
        with patch.object(tg, "checkout_identity", identity):
            with self.assertRaises(tg.CheckoutChanged):
                self.pilot()
        recorded = self.inventory(self.root / "pilot")
        self.assertIn("checkout_changed", recorded)
        self.assertEqual(len(recorded["runs"]), len(self.launched))
        with self.assertRaisesRegex(ValueError, "changed while the pilot "
                                    "ran"):
            self.go(["predeclare", "--grid", str(self.root / "pilot"),
                     "--output", str(self.root / "c.json")])

    def unjudged_at_the_end(self, message="harness checkout is not clean"):
        """A pilot whose last binding finds a checkout it cannot judge."""
        seen = []

        def identity(repo, commit=None, stamp=None):
            seen.append(commit)
            if len(seen) < 3:
                return self.fake_checkout(repo, commit, stamp)
            raise tg.CheckoutUnjudged(message)
        with patch.object(tg, "checkout_identity", identity):
            with self.assertRaises(tg.CheckoutChanged):
                self.pilot()

    def test_a_pilot_that_could_not_judge_its_checkout_at_the_end_resumes(
            self):
        self.unjudged_at_the_end()
        out = self.root / "pilot"
        recorded = self.inventory(out)
        self.assertIn("checkout_unjudged", recorded)
        self.assertNotIn("checkout_changed", recorded)
        self.assertEqual(len(recorded["runs"]), 12)
        # It is no pilot yet, but it is not dead either.
        counts = self.root / "c.json"
        with self.assertRaisesRegex(ValueError, "could not be judged.*"
                                    "resume it"):
            self.go(["predeclare", "--grid", str(out), "--output",
                     str(counts)])
        launched = len(self.launched)
        self.assertEqual(self.pilot(extra=("--resume",))[0], 0)
        self.assertEqual(len(self.launched), launched)
        self.assertNotIn("checkout_unjudged", self.inventory(out))
        self.assertEqual(self.go(["predeclare", "--grid", str(out),
                                  "--output", str(counts)])[0], 0)

    def test_an_unjudged_end_of_a_pilot_stays_listed_after_its_resume(self):
        self.unjudged_at_the_end("first: not clean")
        out = self.root / "pilot"
        first = str(tg.CheckoutUnjudged("first: not clean").resumed())
        second = str(tg.CheckoutUnjudged("second: not clean").resumed())
        self.assertEqual(self.inventory(out)["unjudged_ends"], [first])
        self.assertEqual(self.pilot(extra=("--resume",))[0], 0)
        resumed = self.inventory(out)
        # The mark that gates predeclare is gone, the text is not.
        self.assertNotIn("checkout_unjudged", resumed)
        self.assertEqual(resumed["unjudged_ends"], [first])
        # The resume does not compare the list, and a later unjudged end
        # adds to it.
        seen = []

        def identity(repo, commit=None, stamp=None):
            seen.append(commit)
            if len(seen) < 3:
                return self.fake_checkout(repo, commit, stamp)
            raise tg.CheckoutUnjudged("second: not clean")
        with patch.object(tg, "checkout_identity", identity):
            with self.assertRaises(tg.CheckoutChanged):
                self.pilot(extra=("--resume",))
        again = self.inventory(out)
        self.assertEqual(again["unjudged_ends"], [first, second])
        self.assertEqual(again["checkout_unjudged"], second)

    def test_verify_counts_refuses_an_unjudged_pilot_and_resume_keeps_it(
            self):
        self.unjudged_at_the_end()
        out = self.root / "pilot"
        with self.assertRaisesRegex(ValueError, "could not be judged.*"
                                    "resume it"):
            self.go(["verify-counts", "--grid", str(out)])

        def unclean(repo, commit=None, stamp=None):
            raise tg.CheckoutUnjudged("harness checkout is not clean")
        before = (out / "inventory.json").read_bytes()
        with patch.object(tg, "checkout_identity", unclean):
            with self.assertRaisesRegex(ValueError, "not clean"):
                self.pilot(extra=("--resume",))
        # Still unclean: nothing was resumed and the mark is where it was.
        self.assertEqual((out / "inventory.json").read_bytes(), before)
        self.assertIn("checkout_unjudged", self.inventory(out))
        with self.assertRaisesRegex(ValueError, "could not be judged"):
            self.go(["verify-counts", "--grid", str(out)])
        self.assertEqual(self.pilot(extra=("--resume",))[0], 0)

    def test_a_pilot_whose_checkout_is_known_to_differ_at_the_end_is_dead(
            self):
        # A tracked file that changed, the products or the like, found
        # when the tree could not be judged: the pilot is dead.
        seen = []

        def identity(repo, commit=None, stamp=None):
            seen.append(commit)
            if len(seen) < 3:
                return self.fake_checkout(repo, commit, stamp)
            raise tg.CheckoutUnjudged("harness checkout is not clean")
        with patch.object(tg, "checkout_identity", identity), patch.object(
                tg, "known_difference",
                lambda repo, recorded: "tracked file(s) changed: M x"):
            with self.assertRaisesRegex(tg.CheckoutChanged, "tracked"):
                self.pilot()
        recorded = self.inventory(self.root / "pilot")
        self.assertIn("checkout_changed", recorded)
        self.assertNotIn("checkout_unjudged", recorded)
        self.assertNotIn("unjudged_ends", recorded)
        with self.assertRaisesRegex(ValueError, "changed while the pilot "
                                    "ran"):
            self.go(["predeclare", "--grid", str(self.root / "pilot"),
                     "--output", str(self.root / "c.json")])

    def test_a_pilot_checks_the_checkout_again_under_the_lock(self):
        seen = []

        def identity(repo, commit=None, stamp=None):
            seen.append(commit)
            return self.fake_checkout(repo, commit, stamp) if len(
                seen) < 2 else dict(head=COMMIT,
                                    tree_outside_performance="u" * 64)
        launched = len(self.launched)
        with patch.object(tg, "checkout_identity", identity):
            with self.assertRaises(tg.CheckoutChanged):
                self.pilot()
        self.assertEqual(len(self.launched), launched)
        self.assertFalse((self.root / "pilot").exists())

    def test_a_tampered_pilot_archive_is_refused_on_resume(self):
        out = self.interrupted()
        archive = next(out.glob("*.json.xz"))
        archive.write_bytes(archive.read_bytes() + b"x")
        with self.assertRaisesRegex(ValueError, "changed archive"):
            self.pilot(extra=("--resume",))

    def test_a_fresh_pilot_never_overwrites(self):
        self.pilot()
        with self.assertRaises(FileExistsError):
            self.pilot()

    def test_a_pilot_without_develop_counts_decides_nothing(self):
        def loading_only(command, output, fds, timeout):
            folder = Path(command[command.index("--output") + 1])
            folder.mkdir(parents=True)
            with gzip.open(folder / "pair-99.json.gz", "wt") as stream:
                json.dump(dict(fixture="loading"), stream)
            Path(output).write_text("log\n")
            return dict(exit=0, timed_out=False)
        with patch.object(a, "run_logged", loading_only):
            with self.assertRaisesRegex(ValueError,
                                        "no develop calibration counts"):
                self.pilot()
        self.assertEqual(self.inventory(self.root / "pilot")["runs"], [])

    def test_predeclare_refuses_a_changed_file_count_or_a_repeated_row(self):
        self.pilot()
        path = self.root / "pilot" / "inventory.json"
        good = json.loads(path.read_text())
        runs = good["runs"]
        for label, changed, message in (
                ("count", [dict(runs[0], files=runs[0]["files"] + 1)]
                 + runs[1:], "changed archive file count"),
                ("repeated", runs + [runs[0]], "repeated pilot cell")):
            with self.subTest(label):
                path.write_text(json.dumps(dict(good, runs=changed)))
                with self.assertRaisesRegex(ValueError, message):
                    self.go(["predeclare", "--grid",
                             str(self.root / "pilot"), "--output",
                             str(self.root / "c.json")])

    def test_pilot_settings_default_to_the_tables_and_reach_the_check(self):
        self.table.pilot_pairs, self.table.pilot_samples = 12, 4
        self.pilot()
        inventory = self.inventory(self.root / "pilot")
        self.assertEqual((inventory["pairs"], inventory["samples"]),
                         (12, 4))
        for command in self.launched:
            self.assertEqual(command[command.index("--performance-pairs")
                                     + 1], "12")
            self.assertEqual(command[command.index("--samples") + 1], "4")
        found = self.analyses[0]
        self.assertEqual((found["pairs"], found["samples"]), (12, 4))
        self.assertEqual(found["policy"], a.EQUIVALENCE_POLICY)
        self.pilot(name="again", extra=("--pairs", "13", "--samples", "5"))
        found = self.analyses[-1]
        self.assertEqual((found["pairs"], found["samples"]), (13, 5))

    def declare(self, *extra, grid="pilot", out="c.json"):
        argv = ["predeclare", "--grid", str(self.root / grid), "--output",
                str(self.root / out), *extra]
        return self.go(argv)

    def test_the_counts_file_is_the_predeclaration(self):
        self.pilot()
        self.table.pairs, self.table.samples, self.table.seed = 12, 4, "q1"
        self.declare()
        value = json.loads((self.root / "c.json").read_text())
        pilot = self.root / "pilot"
        inventory = self.inventory(pilot)
        self.assertEqual((value["layout_seed"], value["pairs"],
                          value["samples"], value["baseline"]),
                         ("q1", 12, 4, a.BASE))
        self.assertEqual(value["source"], inventory["driver"])
        self.assertEqual(value["sealed"], inventory["sealed"])
        self.assertEqual(sorted(value["sealed"]), sorted(SEALED))
        self.assertEqual(value["pilot"]["inventory"],
                         a.seal(pilot / "inventory.json"))
        self.assertEqual(
            value["pilot"]["archives"],
            {"%s-%d" % (r["case"], r["size"]): r["seal"]
             for r in inventory["runs"]})

    def test_the_settings_of_the_run_are_checked_when_predeclared(self):
        self.pilot()
        for label, change, message in (
                ("pairs", dict(pairs=9), "protocol minimum"),
                ("samples", dict(samples=2), "protocol minimum"),
                ("no seed", dict(seed=None), "needs layout random"),
                ("long seed", dict(seed="a" * 61), "layout seed")):
            with self.subTest(label):
                saved = {k: getattr(self.table, k) for k in change}
                for key, value in change.items():
                    setattr(self.table, key, value)
                with self.assertRaisesRegex(ValueError, message):
                    self.declare(out="f.json")
                for key, value in saved.items():
                    setattr(self.table, key, value)
        self.assertFalse((self.root / "f.json").exists())

    def test_a_pilot_is_the_only_source_of_a_fixed_table(self):
        self.pilot()
        path = self.root / "pilot" / "inventory.json"
        good = json.loads(path.read_text())
        for label, change, message in (
                ("schema", dict(schema="toy-experiment-v1"),
                 "pilot of another task"),
                ("baseline", dict(baseline="e" * 40),
                 "pilot of another baseline")):
            with self.subTest(label):
                path.write_text(json.dumps(dict(good, **change)))
                with self.assertRaisesRegex(ValueError, message):
                    self.declare()
        path.write_text(json.dumps(good))

    def test_predeclare_checks_the_code_of_the_pilot(self):
        self.pilot()
        self.driver.write_text("# the toy driver, changed\n")
        with self.assertRaisesRegex(ValueError, "changed driver"):
            self.declare()
        (self.sealed_dir / "one.txt").write_text("edited")
        self.driver.write_text("# the toy driver\n")
        with self.assertRaisesRegex(ValueError, "changed one.txt"):
            self.declare()

    def test_predeclare_takes_no_settings_from_the_command_line(self):
        # The layout seed, pairs and samples are the table's; no option can
        # make a counts file that differs.
        self.pilot()
        for option, value in (("--layout-seed", "s0"), ("--pairs", "10"),
                              ("--samples", "3")):
            with self.subTest(option), \
                    contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit):
                self.declare(option, value)

    def test_verify_counts_rederives_the_file_from_its_pilot(self):
        self.pilot()
        self.declare()
        self.counts.write_text((self.root / "c.json").read_text())
        status, text = self.go(["verify-counts", "--grid",
                                str(self.root / "pilot")])
        self.assertEqual((status, text), (0, "TOY counts match their "
                                             "pilot\n"))
        # Later changes to the code do not change what the pilot made.
        self.driver.write_text("# the toy driver, changed\n")
        status, _ = self.go(["verify-counts", "--grid",
                             str(self.root / "pilot"), "--counts",
                             str(self.root / "c.json")])
        self.assertEqual(status, 0)

    def test_verify_counts_refuses_a_file_the_pilot_did_not_make(self):
        self.pilot()
        self.declare()
        value = json.loads((self.root / "c.json").read_text())
        for label, changed in (
                ("count", dict(value, iterations=dict(
                    value["iterations"], **{"exclude_empty-0": 1024}))),
                ("pairs", dict(value, pairs=9)),
                ("baseline", dict(value, baseline="e" * 40)),
                ("seal", dict(value, pilot=dict(
                    value["pilot"], inventory=a.seal(self.driver))))):
            with self.subTest(label):
                (self.root / "d.json").write_text(json.dumps(changed))
                with self.assertRaises(ValueError):
                    self.go(["verify-counts", "--grid",
                             str(self.root / "pilot"), "--counts",
                             str(self.root / "d.json")])
        (self.root / "d.json").write_text(json.dumps(dict(
            value, iterations=dict(value["iterations"],
                                   **{"exclude_empty-0": 1024}))))
        with self.assertRaisesRegex(ValueError, "counts differ from their"):
            self.go(["verify-counts", "--grid", str(self.root / "pilot"),
                     "--counts", str(self.root / "d.json")])

    def test_a_pilot_is_not_replayed_as_a_grid(self):
        self.pilot()
        with self.assertRaisesRegex(ValueError, "verify-counts"):
            self.go(self.replay_argv(self.root / "pilot"))

    def test_the_pilot_baseline_is_the_tables(self):
        with self.assertRaisesRegex(ValueError, "pilot baseline differs"):
            self.pilot(extra=("--baseline", "e" * 40))
        self.assertEqual(self.launched, [])

    def test_the_variability_of_every_cell_is_published(self):
        self.pilot_control = lambda case, size, pairs, seed: (
            WIDE if (case, size) == (CASES[1], 10) else GOOD)
        self.pilot()
        found = json.loads(
            (self.root / "pilot" / "variability.json").read_text())
        self.assertEqual(set(found), set(self.table.names()))
        good, wide = found["%s-0" % CASES[0]], found["%s-10" % CASES[1]]
        self.assertEqual(good["cpu"], dict(
            median=1.0, ci95=list(GOOD), in_window=True))
        self.assertIs(wide["wall"]["in_window"], False)
        self.assertNotIn("in_window", good["gc"])
        inventory = self.inventory(self.root / "pilot")
        self.assertEqual(inventory["runs"][0]["variability"],
                         found[self.table.names()[0]])

    def test_a_failed_cell_keeps_its_archive_aside_and_is_measured_again(
            self):
        real = a.analyze
        calls = []

        def failing(*args, **kw):
            calls.append(1)
            if len(calls) == 3:
                raise ValueError("failed experiment")
            return real(*args, **kw)
        with patch.object(a, "analyze", failing):
            with self.assertRaisesRegex(ValueError, "failed experiment"):
                self.pilot()
        out = self.root / "pilot"
        self.assertEqual(len(self.inventory(out)["runs"]), 2)
        self.assertEqual(len(list(out.glob("*.json.xz.failed-1"))), 1)
        self.assertEqual(len(list(out.glob("*.json.xz"))), 2)
        self.launched.clear()
        status, _ = self.pilot(extra=("--resume",))
        self.assertEqual(status, 0)
        self.assertEqual(len(self.launched), 10)
        self.assertEqual(len(list(out.glob("*.json.xz"))), 12)
        self.assertEqual(len(list(out.glob("*.failed-1"))), 1)

    def test_a_pilot_compares_its_settings_before_clearing_anything(self):
        out = self.interrupted()
        (out / "x.json.xz.partial.xz").write_text("half")
        with self.assertRaisesRegex(ValueError, "different settings"):
            self.pilot(extra=("--resume", "--pairs", "12"))
        self.assertEqual((out / "x.json.xz.partial.xz").read_text(), "half")

    def test_a_pilot_clears_what_a_stop_left_under_the_lock(self):
        out = self.interrupted()
        (out / "x.json.xz.partial.xz").write_text("half")
        held = []
        real = self.grid.sweep

        def sweep(root, kept):
            held.append(os.environ.get("HOL4_PERF_LOCK_FDS") is not None)
            return real(root, kept)
        with patch.dict(os.environ), patch.object(self.grid, "sweep", sweep):
            os.environ.pop("HOL4_PERF_LOCK_FDS", None)
            self.pilot(extra=("--resume",))
        self.assertEqual(held, [True])
        self.assertEqual(list(out.glob("*.partial*")), [])

    def test_a_pilot_resumption_without_an_inventory_says_so(self):
        (self.root / "pilot").mkdir()
        with self.assertRaisesRegex(ValueError, "nothing to resume.*no "
                                    "inventory"):
            self.pilot(extra=("--resume",))

    def test_the_pilot_inventory_exists_before_the_first_cell(self):
        seen = []
        real = self.fake_launch

        def watching(command, output, fds, timeout):
            seen.append((self.root / "pilot" / "inventory.json").exists())
            return real(command, output, fds, timeout)
        with patch.object(a, "run_logged", watching):
            self.pilot()
        self.assertEqual(seen[0], True)

    def test_a_pilot_resume_clears_what_a_stop_left(self):
        out = self.interrupted()
        for name in ("x.json.xz.partial.xz", "y.partial"):
            (out / name).write_text("half")
        stray = out / ("%s-100.json.xz" % CASES[1])
        stray.write_bytes(b"unrecorded")
        status, _ = self.pilot(extra=("--resume",))
        self.assertEqual(status, 0)
        self.assertEqual(list(out.glob("*.partial*")), [])
        self.assertEqual((out / (stray.name + ".unrecorded-1")).read_bytes(),
                         b"unrecorded")
        self.assertEqual(len(self.inventory(out)["runs"]), 12)


class Predeclared(Rig):
    """The counts file is the predeclaration, bound to its baseline."""

    def test_a_run_takes_its_settings_from_the_table_through_the_counts(self):
        self.declare_again(pairs=12, samples=4, seed="q1")
        out, status, _ = self.first()
        self.assertEqual(status, 0)
        self.assertEqual({(o["pairs"], o["samples"], o["layout_seed"])
                          for o in self.runs}, {(12, 4, "q1")})
        header = self.inventory(out)
        self.assertEqual((header["pairs"], header["samples"],
                          header["layout_seed"]), (12, 4, "q1"))
        self.assertEqual(header["counts_commit"], COMMIT)
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)

    def test_other_explicit_settings_are_refused(self):
        for option, value in (("--pairs", "11"), ("--samples", "4"),
                              ("--layout-seed", "s9")):
            with self.subTest(option), self.assertRaisesRegex(
                    ValueError, "%s differs from the predeclared" % option):
                self.first(name="g" + option, extra=(option, value))
        self.assertEqual(self.calls, 0)
        out, status, _ = self.first(extra=(
            "--pairs", "10", "--samples", "3", "--layout-seed", "s0"))
        self.assertEqual(status, 0)

    def test_counts_of_other_settings_than_the_tables_are_refused(self):
        good = json.loads(self.counts.read_text())
        for key, value in (("layout_seed", "s9"), ("layout_seed", None),
                           ("pairs", 11), ("samples", 4)):
            with self.subTest(key, value=value):
                self.rewrite(**{key: value})
                with self.assertRaisesRegex(
                        ValueError, "of the counts differs from the table"):
                    self.first(name="g-%s-%s" % (key, value))
                self.counts.write_text(json.dumps(good))
        self.assertEqual(self.calls, 0)

    def test_a_run_refuses_counts_other_than_the_tables(self):
        other = self.root / "other.json"
        value = json.loads(self.counts.read_text())
        value["iterations"]["exclude_empty-0"] *= 2
        other.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "changed predeclared"):
            self.first(extra=("--iterations", str(other)))
        self.assertEqual(self.calls, 0)

    def test_the_baseline_is_the_tables_and_the_counts(self):
        with self.assertRaisesRegex(ValueError, "baseline differs"):
            self.first(extra=("--baseline", "e" * 40))
        self.rewrite(baseline="e" * 40)
        with self.assertRaisesRegex(ValueError, "baseline differs"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_the_candidate_is_not_the_baseline(self):
        with self.assertRaisesRegex(ValueError, "candidate is the baseline"):
            self.go(self.argv("run", self.root / "x", "--candidate", a.BASE,
                              "--authorize-measurements"))
        self.assertEqual(self.calls, 0)

    def test_replay_refuses_another_baseline(self):
        out, _, _ = self.first()
        header = self.inventory(out)
        for label, changed in (
                ("inventory", dict(header, baseline="e" * 40)),
                ("counts", dict(header, iterations=dict(
                    header["iterations"], baseline="e" * 40)))):
            with self.subTest(label):
                (out / "inventory.json").write_text(json.dumps(changed))
                with self.assertRaisesRegex(
                        ValueError, "changed baseline|changed predeclared"):
                    self.go(self.replay_argv(out))
        self.table.baseline = "e" * 40
        (out / "inventory.json").write_text(json.dumps(header))
        with self.assertRaisesRegex(ValueError, "changed baseline"):
            self.go(self.replay_argv(out))

    def test_the_counts_must_be_committed_where_the_candidate_has_them(self):
        self.committed = False
        with self.assertRaisesRegex(ValueError, "not committed"):
            self.first()
        self.committed = "9" * 40  # another version of the file
        with self.assertRaisesRegex(ValueError, "not committed"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_the_header_keeps_the_commit_and_the_settings(self):
        out, _, _ = self.first()
        header = self.inventory(out)
        for label, changed, message in (
                ("commit", {k: v for k, v in header.items()
                            if k != "counts_commit"}, "no commit"),
                ("pairs", dict(header, pairs=11), "settings differ"),
                ("seed", dict(header, layout_seed="s9"),
                 "settings differ")):
            with self.subTest(label):
                (out / "inventory.json").write_text(json.dumps(changed))
                with self.assertRaisesRegex(ValueError, message):
                    self.go(self.replay_argv(out))

    def test_the_second_stage_seed_must_be_valid_before_the_counts(self):
        # The seed of the first stage and its extension are both checked
        # when the counts are made; the table refuses them as well.
        with self.assertRaisesRegex(ValueError, "layout seed"):
            self.declare_again(seed="a" * 61)
        with self.assertRaisesRegex(ValueError, "layout seed"):
            self.make_table(seed="a" * 61)

    def test_the_second_stage_keeps_the_counts_commit(self):
        self.control = lambda case, size, pairs, seed: (
            WIDE if (case, size) == (CASES[1], 100) else GOOD)
        grid, _, _ = self.first()
        self.go(self.argv("extend", self.root / "ext", "--grid", str(grid),
                          "--authorize-measurements"))
        header = self.inventory(self.root / "ext")
        self.assertEqual(header["counts_commit"], COMMIT)
        self.assertEqual(header["sources"], self.inventory(grid)["sources"])
        self.assertEqual(self.go(self.replay_argv(self.root / "ext"))[0], 2)


class CodeSeals(Rig):
    """Engines, sealed files and the history of their seals."""

    def header(self):
        out, _, _ = self.first()
        return self.inventory(out)

    def test_an_earlier_engine_is_refused_unless_the_table_names_it(self):
        header = self.header()
        old = dict(bytes=1, sha256="0" * 64)
        changed = dict(header, engine=old)
        with self.assertRaisesRegex(ValueError, "changed engine"):
            self.grid.check_header(changed)
        self.table.engines = (old,)
        self.grid.check_header(changed)
        with self.assertRaisesRegex(ValueError, "changed engine"):
            self.grid.check_header(dict(header, resumed=[dict(
                header, engine=dict(bytes=2, sha256="1" * 64), after=1)]))

    def test_sealed_files_are_recorded_and_checked(self):
        header = self.header()
        self.assertEqual(set(header["sealed"]), set(SEALED))
        self.assertEqual(header["sealed"]["one.txt"],
                         a.seal(self.sealed_dir / "one.txt"))
        self.grid.check_header(header)
        (self.sealed_dir / "one.txt").write_text("edited")
        with self.assertRaisesRegex(ValueError, "changed one.txt"):
            self.grid.check_header(header)
        self.table.sealed_history = {"one.txt": (
            header["sealed"]["one.txt"],)}
        self.grid.check_header(header)

    def test_the_sealed_names_are_those_of_the_table(self):
        header = self.header()
        with self.assertRaisesRegex(ValueError, "changed sealed files"):
            self.grid.check_header(dict(header, sealed={
                "one.txt": header["sealed"]["one.txt"]}))
        with self.assertRaisesRegex(ValueError, "changed sealed files"):
            self.grid.check_header({k: v for k, v in header.items()
                                    if k != "sealed"})

    def test_a_sealed_change_across_a_resume_is_recorded(self):
        self.explode_at = 4
        with self.assertRaises(RuntimeError):
            self.first()
        self.explode_at = None
        out = self.root / "grid"
        known = a.seal(self.sealed_dir / "one.txt")
        (self.sealed_dir / "one.txt").write_text("edited")
        self.table.sealed_history = {"one.txt": (known,)}
        status, _ = self.go(self.argv(
            "run", out, "--candidate", CANDIDATE, "--resume",
            "--authorize-measurements"))
        self.assertEqual(status, 0)
        header = self.inventory(out)
        self.assertEqual(header["sealed"]["one.txt"], known)
        self.assertEqual(header["resumed"][0]["sealed"]["one.txt"],
                         a.seal(self.sealed_dir / "one.txt"))
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)

    def test_the_history_belongs_to_sealed_files(self):
        with self.assertRaisesRegex(ValueError, "history of an unsealed"):
            self.make_table(sealed_history={"three.txt": ()})


class SourceIdentity(Rig):
    """A source file that differs from the baseline is never a pass."""

    def test_the_sources_are_recorded_at_both_commits(self):
        out, status, text = self.first()
        self.assertEqual(status, 0)
        record = self.inventory(out)["sources"]
        self.assertEqual(sorted(record), sorted(SOURCES))
        self.assertEqual(record["src/one.sml"],
                         dict(baseline="0" * 40, candidate="0" * 40))
        decisions = json.loads((out / "decisions.json").read_text())
        self.assertEqual(decisions["source_identity"], dict(
            files=sorted(SOURCES), differing=[]))
        self.assertNotIn("SOURCE-DIFFERS", text)

    def test_a_differing_file_is_named_and_the_grid_is_no_pass(self):
        self.differ = {"src/two.sml"}
        with self.unrefused():
            out, status, text = self.first()
        self.assertEqual(status, 2)
        decisions = json.loads((out / "decisions.json").read_text())
        self.assertEqual(decisions["status"], "inconclusive")
        self.assertEqual(decisions["source_identity"]["differing"],
                         ["src/two.sml"])
        # Named when the run starts, and again with the outcome.
        self.assertEqual(text.count("SOURCE-DIFFERS src/two.sml"), 2)
        self.assertLess(text.index("SOURCE-DIFFERS"), text.index("START"))
        self.assertIn("TOY grid: inconclusive (pass 12, fail 0", text)

    def test_a_fail_stays_a_fail_beside_a_differing_file(self):
        self.differ = {"src/one.sml"}
        self.candidate = lambda case, size, pairs, seed: (1.04, 1.08)
        with self.unrefused():
            out, status, _ = self.first()
        self.assertEqual(status, 1)

    def test_replay_verifies_the_recorded_identity_again(self):
        self.differ = {"src/two.sml"}
        with self.unrefused():
            out, _, _ = self.first()
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 2)
        self.assertIn("SOURCE-DIFFERS src/two.sml", text)
        self.differ = set()
        with self.assertRaisesRegex(ValueError, "changed source identity"):
            self.go(self.replay_argv(out))
        self.differ = {"src/two.sml"}
        header = self.inventory(out)
        header["sources"]["src/two.sml"]["candidate"] = "0" * 40
        (out / "inventory.json").write_text(json.dumps(header))
        with self.assertRaisesRegex(ValueError, "changed source identity"):
            self.go(self.replay_argv(out))

    def test_the_decisions_cannot_hide_a_differing_file(self):
        self.differ = {"src/two.sml"}
        with self.unrefused():
            out, _, _ = self.first()
        path = out / "decisions.json"
        decisions = json.loads(path.read_text())
        decisions["status"] = "pass"
        decisions["source_identity"]["differing"] = []
        path.write_text(json.dumps(decisions))
        with self.assertRaisesRegex(ValueError, "changed TOY decisions"):
            self.go(self.replay_argv(out))

    def test_a_source_absent_at_the_baseline_is_an_error(self):
        real = self.fake_blob
        with patch.object(tg, "git_blob", lambda repo, rev, path: None
                          if rev == a.BASE and path == "src/two.sml"
                          else real(repo, rev, path)):
            with self.assertRaisesRegex(ValueError, "absent at the baseline"):
                self.first()
        self.assertEqual(self.calls, 0)

    def test_the_record_belongs_to_the_table(self):
        out, _, _ = self.first()
        header = self.inventory(out)
        no_sources = {k: v for k, v in header.items() if k != "sources"}
        with self.assertRaisesRegex(ValueError, "changed source files"):
            self.grid.check_header(no_sources)
        self.table.sources = ()
        with self.assertRaisesRegex(ValueError, "changed source files"):
            self.grid.check_header(header)
        self.grid.check_header(no_sources)

    def test_a_table_without_sources_records_none(self):
        self.table.sources = ()
        out, status, text = self.first()
        self.assertEqual(status, 0)
        self.assertNotIn("sources", self.inventory(out))
        decisions = json.loads((out / "decisions.json").read_text())
        self.assertNotIn("source_identity", decisions)

    def test_the_second_stage_carries_the_identity(self):
        self.differ = {"src/two.sml"}
        self.control = lambda case, size, pairs, seed: (
            WIDE if (case, size) == (CASES[1], 100) and pairs < 60
            else GOOD)
        with self.unrefused():
            grid, _, _ = self.first()
        status, text = self.go(self.argv(
            "extend", self.root / "ext", "--grid", str(grid),
            "--authorize-measurements"))
        self.assertEqual(status, 2)
        decisions = json.loads((self.root / "ext" /
                                "decisions.json").read_text())
        self.assertEqual(decisions["source_identity"]["differing"],
                         ["src/two.sml"])
        self.assertIn("SOURCE-DIFFERS src/two.sml", text)
        self.assertEqual(self.go(self.replay_argv(self.root / "ext"))[0], 2)


class ReviewedDifferences(Rig):
    """A pinned file that differs is published, not refused."""
    PIN = dict(blob="f" * 40, reason="A reviewed change of two.")

    def make_table(self, **kw):
        kw.setdefault("pinned", {"src/two.sml": self.PIN})
        return super().make_table(**kw)

    def test_a_pinned_blob_is_published_and_no_failure(self):
        self.differ = {"src/two.sml"}
        out, status, text = self.first()
        self.assertEqual(status, 0)
        decisions = json.loads((out / "decisions.json").read_text())
        self.assertEqual(decisions["status"], "pass")
        self.assertEqual(decisions["source_identity"], dict(
            files=sorted(SOURCES), differing=[],
            reviewed={"src/two.sml": self.PIN}))
        self.assertNotIn("SOURCE-DIFFERS", text)
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)

    def test_another_file_beside_a_pinned_one_still_differs(self):
        self.differ = {"src/one.sml", "src/two.sml"}
        with self.unrefused():
            out, status, text = self.first()
        self.assertEqual(status, 2)
        identity = json.loads(
            (out / "decisions.json").read_text())["source_identity"]
        self.assertEqual(identity["differing"], ["src/one.sml"])
        self.assertEqual(sorted(identity["reviewed"]), ["src/two.sml"])
        self.assertIn("SOURCE-DIFFERS src/one.sml", text)
        self.assertNotIn("SOURCE-DIFFERS src/two.sml", text)

    def test_another_blob_of_a_pinned_file_behaves_as_without_a_pin(self):
        self.differ = {"src/two.sml"}
        self.table.pinned = {"src/two.sml": dict(self.PIN, blob="e" * 40)}
        with self.unrefused():
            out, status, text = self.first()
        self.assertEqual(status, 2)
        decisions = json.loads((out / "decisions.json").read_text())
        self.assertEqual(decisions["status"], "inconclusive")
        self.assertEqual(decisions["source_identity"]["differing"],
                         ["src/two.sml"])
        self.assertEqual(decisions["source_identity"]["reviewed"], {})
        self.assertEqual(text.count("SOURCE-DIFFERS src/two.sml"), 2)

    def test_a_pin_on_an_identical_file_is_a_table_error(self):
        with self.assertRaisesRegex(ValueError, "identical to the base"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_a_pin_outside_the_sources_is_a_table_error(self):
        with self.assertRaisesRegex(ValueError, "pin outside the sources"):
            self.make_table(pinned={"src/three.sml": self.PIN})

    def test_a_malformed_pin_is_a_table_error(self):
        for pin in (dict(blob="f" * 40), dict(self.PIN, blob="f" * 39),
                    dict(self.PIN, reason=" ")):
            with self.assertRaisesRegex(ValueError, "malformed pin"):
                self.make_table(pinned={"src/two.sml": pin})

    def test_a_table_without_pins_publishes_none(self):
        self.table.pinned = {}
        self.differ = {"src/two.sml"}
        with self.unrefused():
            out, _, _ = self.first()
        identity = json.loads(
            (out / "decisions.json").read_text())["source_identity"]
        self.assertNotIn("reviewed", identity)

    def test_replay_derives_the_decisions_again(self):
        self.differ = {"src/two.sml"}
        out, _, _ = self.first()
        path = out / "decisions.json"
        recorded = json.loads(path.read_text())
        for tamper in (
                lambda d: d["source_identity"]["reviewed"].clear(),
                lambda d: d["source_identity"]["reviewed"][
                    "src/two.sml"].update(reason="Nothing to see."),
                lambda d: d["source_identity"].update(
                    differing=["src/two.sml"])):
            decisions = json.loads(json.dumps(recorded))
            tamper(decisions)
            path.write_text(json.dumps(decisions))
            with self.assertRaisesRegex(ValueError, "changed TOY decisions"):
                self.go(self.replay_argv(out))
        path.write_text(json.dumps(recorded))
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)
        # The pin is the table's: a replay under another pin differs.
        self.table.pinned = {"src/two.sml": dict(self.PIN, blob="e" * 40)}
        with self.assertRaisesRegex(ValueError, "changed TOY decisions"):
            self.go(self.replay_argv(out))

    def test_the_second_stage_carries_the_reviewed_difference(self):
        self.differ = {"src/two.sml"}
        self.control = lambda case, size, pairs, seed: (
            WIDE if (case, size) == (CASES[1], 100) and pairs < 60
            else GOOD)
        grid, _, _ = self.first()
        status, text = self.go(self.argv(
            "extend", self.root / "ext", "--grid", str(grid),
            "--authorize-measurements"))
        self.assertEqual(status, 0)
        identity = json.loads((self.root / "ext" /
                               "decisions.json").read_text())[
            "source_identity"]
        self.assertEqual(identity["differing"], [])
        self.assertEqual(identity["reviewed"], {"src/two.sml": self.PIN})
        self.assertNotIn("SOURCE-DIFFERS", text)
        self.assertEqual(self.go(self.replay_argv(self.root / "ext"))[0], 0)
        decisions = json.loads((self.root / "ext" /
                                "decisions.json").read_text())
        decisions["source_identity"]["reviewed"].clear()
        (self.root / "ext" / "decisions.json").write_text(
            json.dumps(decisions))
        with self.assertRaisesRegex(ValueError, "changed TOY decisions"):
            self.go(self.replay_argv(self.root / "ext"))


class Attempts(Rig):
    """Every measured grid is recorded in an append-only, hash-chained
    ledger below the checkout (git excludes it), so that a rerun under the
    same settings (a new draw) is visible and an earlier attempt cannot be
    dropped from the middle. It is a discipline and not a proof."""

    def run_argv(self, name="grid"):
        return self.argv("run", self.root / name, "--candidate", CANDIDATE,
                         "--authorize-measurements")

    def lines(self):
        return self.attempts.read_text().split("\n")

    def test_the_ledger_is_at_one_place_below_the_checkout(self):
        self.table.ledger = None
        where = self.repo / ".agent-files" / "evidence" / "toy"
        self.assertEqual(self.grid.ledger_path(self.repo),
                         where.resolve() / "attempts.jsonl")
        with self.assertRaisesRegex(ValueError, "would be tracked by git"):
            self.first()
        self.assertEqual(self.calls, 0)
        self.assertFalse(where.exists() and any(where.iterdir()))
        exclude = self.repo / ".git" / "info" / "exclude"
        exclude.write_text(exclude.read_text() + ".agent-files\n")
        out, status, _ = self.first()
        self.assertEqual(status, 0)
        self.assertEqual(
            [x["event"] for x in map(json.loads, (
                where / "attempts.jsonl").read_text().splitlines())],
            ["open", "close"])

    def test_the_ledger_place_is_checked_at_the_pilot_too(self):
        self.table.ledger = None
        calls = len(self.launched)
        with self.assertRaisesRegex(ValueError, "would be tracked by git"):
            self.go(self.argv("pilot", self.root / "again",
                              "--authorize-measurements"))
        self.assertEqual(len(self.launched), calls)
        self.assertFalse((self.root / "again").exists())

    def test_the_refusal_names_the_exclude_step(self):
        self.table.ledger = None
        with self.assertRaisesRegex(ValueError, "exclude .agent-files.*"
                                    "info/exclude"):
            self.first()

    def test_the_command_line_has_no_ledger_option_but_a_read_only_one(self):
        with self.assertRaises(SystemExit), \
                contextlib.redirect_stderr(io.StringIO()):
            self.go(self.run_argv() + ["--attempts", str(self.attempts)])
        # `run` and `extend` append to their own checkout's ledger and take
        # no other; `replay` (and `close`) may read one.
        parser, sub = self.grid.parser()
        for name in ("run", "extend", "pilot", "prepare"):
            options = {o for action in sub.choices[name]._actions
                       for o in action.option_strings}
            self.assertNotIn("--ledger", options, name)
        options = {o for action in sub.choices["replay"]._actions
                   for o in action.option_strings}
        self.assertIn("--ledger", options)
        with self.assertRaises(SystemExit), \
                contextlib.redirect_stderr(io.StringIO()):
            self.go(self.run_argv() + ["--ledger", str(self.attempts)])

    def test_an_appending_command_refuses_another_ledger(self):
        args = argparse.Namespace(repo=self.repo, ledger=self.attempts)
        with self.assertRaisesRegex(ValueError, "of its own checkout"):
            self.grid.attempts_file(args, True)
        self.assertEqual(self.grid.attempts_file(args, False),
                         self.attempts)

    def test_every_line_names_the_checkout_it_was_made_in(self):
        self.first()
        found = self.ledger()
        self.assertEqual({x["checkout"] for x in found},
                         {str(self.repo.resolve())})
        self.assertEqual(len(found), 2)

    def test_replay_reads_the_ledger_of_another_checkout_without_changing_it(
            self):
        out, _, _ = self.first()
        kept = self.root / "kept-attempts.jsonl"
        shutil.copy(self.attempts, kept)
        self.table.ledger = self.root / "elsewhere" / "none.jsonl"
        with self.assertRaisesRegex(ValueError, "no attempts ledger"):
            self.go(self.replay_argv(out))
        before = kept.read_bytes()
        status, text = self.go(self.replay_argv(out, "--ledger", str(kept)))
        self.assertEqual(status, 0)
        self.assertIn("checkout %s" % self.repo.resolve(), text)
        self.assertEqual(kept.read_bytes(), before)
        self.assertFalse(self.table.ledger.parent.exists())

    def test_a_malformed_ledger_is_refused_before_any_cell(self):
        # A line that is no record, followed by a record that does not
        # acknowledge it, is not a torn tail.
        self.first(name="one")
        good = self.attempts.read_text()
        calls = self.calls
        for i, text in enumerate(("not json\n", "[1]\n",
                                  '{"no": "event"}\n')):
            with self.subTest(text):
                self.attempts.write_text(text + good)
                with self.assertRaisesRegex(ValueError, "malformed attempts"):
                    self.first(name="g%d" % i)
        self.assertEqual(self.calls, calls)

    def test_the_ledger_records_the_grid_it_opens_and_closes(self):
        out, status, _ = self.first()
        header = self.inventory(out)
        opening, closing = self.ledger()
        self.assertEqual((opening["event"], closing["event"]),
                         ("open", "close"))
        for line in (opening, closing):
            self.assertEqual(
                {k: line[k] for k in ("stage", "attempt", "candidate",
                                      "counts_file", "counts", "seed",
                                      "output")},
                dict(stage="first", attempt=header["attempt"],
                     candidate=CANDIDATE, counts_file="toy_iterations.json",
                     counts=a.seal(self.counts),
                     seed=header["layout_seed"], output=str(out)))
            self.assertRegex(line["time"], r"^\d{4}-\d\d-\d\dT[\d:]{8}Z$")
        self.assertEqual(closing["status"], "pass")
        self.assertNotIn("status", opening)

    def test_every_line_names_the_hash_of_the_line_before(self):
        self.first()
        text = self.lines()
        self.assertEqual(text.pop(), "")
        self.assertEqual(json.loads(text[0])["prev"], "0" * 64)
        self.assertEqual(json.loads(text[1])["prev"], tg.ledger_hash(text[0]))

    def test_a_line_removed_or_changed_in_the_middle_breaks_the_chain(self):
        self.first(name="one")
        self.first(name="two")
        calls, text = self.calls, self.lines()
        changed = json.loads(text[1])
        changed["status"] = "pass" if changed["status"] != "pass" else "fail"
        for what, lines in (("removed", text[:1] + text[2:]),
                            ("first removed", text[1:]),
                            ("changed", [text[0], json.dumps(
                                changed, sort_keys=True)] + text[2:])):
            with self.subTest(what):
                self.attempts.write_text("\n".join(lines))
                with self.assertRaisesRegex(ValueError, "chain broken"):
                    self.first(name="again")
                with self.assertRaisesRegex(ValueError, "chain broken"):
                    self.go(self.replay_argv(self.root / "one"))
        self.assertEqual(self.calls, calls)

    def test_the_opening_is_written_before_the_first_cell(self):
        seen = []
        real = self.fake_run

        def watching(options):
            seen.append([line["event"] for line in self.ledger()])
            return real(options)
        with patch.object(a, "run", watching):
            self.first()
        self.assertEqual(seen[0], ["open"])

    def test_an_interrupted_grid_is_closed_and_a_resumption_recorded(self):
        self.explode_at = 4
        with self.assertRaises(RuntimeError):
            self.first()
        self.explode_at = None
        self.assertEqual([(x["event"], x.get("status"))
                          for x in self.ledger()],
                         [("open", None), ("close", "interrupted")])
        status, _ = self.go(self.run_argv() + ["--resume"])
        self.assertEqual(status, 0)
        lines = self.ledger()
        self.assertEqual([(x["event"], x.get("status")) for x in lines],
                         [("open", None), ("close", "interrupted"),
                          ("resume", None), ("close", "pass")])
        self.assertEqual({x["attempt"] for x in lines},
                         {self.inventory(self.root / "grid")["attempt"]})

    def test_a_rerun_is_a_new_draw_and_the_earlier_one_stays(self):
        self.candidate = lambda case, size, pairs, seed: (1.04, 1.08)
        self.first(name="one")
        self.candidate = lambda case, size, pairs, seed: GOOD
        self.first(name="two")
        lines = self.ledger()
        self.assertEqual([x["event"] for x in lines],
                         ["open", "close", "open", "close"])
        self.assertEqual([x["status"] for x in lines if x["event"] == "close"],
                         ["fail", "pass"])
        self.assertNotEqual(lines[0]["attempt"], lines[2]["attempt"])
        self.assertEqual({x["candidate"] for x in lines}, {CANDIDATE})

    def test_replay_prints_every_attempt_of_the_table_marking_the_candidates(
            self):
        self.candidate = lambda case, size, pairs, seed: (1.04, 1.08)
        one, _, _ = self.first(name="one")
        self.candidate = lambda case, size, pairs, seed: GOOD
        two, _, _ = self.first(name="two")
        # A retry at another commit, made in the same checkout.
        other = "d" * 40
        tg.ledger_append(self.attempts, event="open", stage="first",
                         attempt="x" * 32, candidate=other,
                         counts_file="toy_iterations.json", counts="s",
                         seed="s0", output="o", checkout=str(self.repo))
        status, text = self.go(self.replay_argv(two))
        self.assertEqual(status, 0)
        self.assertIn("ATTEMPTS of TOY: 3 in the ledger, 2 of this candidate "
                      "%s (5 records of TOY, 5 records in the family "
                      "ledger, chain intact)" % CANDIDATE, text)
        mine = [x for x in text.splitlines() if x.startswith("ATTEMPT ")]
        self.assertEqual(len(mine), 3)
        self.assertRegex(mine[0], r" first opened \S+ resumed 0 status fail "
                         r"candidate %s checkout \S+ \(this candidate\)$"
                         % CANDIDATE)
        self.assertRegex(mine[1], r" resumed 0 status pass candidate .* "
                         r"\(this grid\)$")
        self.assertIn(self.inventory(two)["attempt"], mine[1])
        self.assertRegex(mine[2], r"status interrupted candidate %s "
                         r"checkout \S+$" % other)

    def test_a_new_ledger_is_synced_in_its_directory_too(self):
        synced = []
        real = os.fsync

        def fsync(fd):
            synced.append(stat.S_ISDIR(os.fstat(fd).st_mode))
            return real(fd)
        where = self.root / "ledger" / "new.jsonl"
        where.parent.mkdir()
        with patch.object(os, "fsync", fsync):
            for _ in range(2):
                tg.ledger_append(where, event="open", stage="first",
                                 attempt="q" * 32)
        # The file, then its directory, once; then the file only.
        self.assertEqual(synced, [False, True, False])

    def test_every_status_of_an_attempt_is_kept(self):
        def append(event, **more):
            tg.ledger_append(self.attempts, event=event, stage="first",
                             attempt="z" * 32, candidate=CANDIDATE,
                             counts_file="toy_iterations.json", counts="s",
                             seed="s0", output="o", checkout="/here", **more)
        found = lambda: tg.Ledger(self.attempts).attempts()
        append("open")
        self.assertEqual(found()[("z" * 32, "first")]["statuses"],
                         ["interrupted"])
        append("close", status="checkout-changed")
        append("resume")
        append("close", status="interrupted")
        append("resume")
        append("close", status="pass")
        row = found()[("z" * 32, "first")]
        self.assertEqual((row["statuses"], row["status"], row["resumed"]),
                         (["checkout-changed", "interrupted", "pass"],
                          "pass", 2))
        append("resume")
        row = found()[("z" * 32, "first")]
        self.assertEqual((row["statuses"], row["status"]), (
            ["checkout-changed", "interrupted", "pass", "interrupted"],
            "interrupted"))

    def test_replay_shows_the_close_of_a_resumed_attempt_and_its_places(self):
        out = self.root / "grid"
        self.explode_at = 4
        with self.assertRaises(RuntimeError):
            self.first()
        self.explode_at = None
        self.assertEqual(self.go(self.argv(
            "run", out, "--candidate", CANDIDATE, "--resume",
            "--authorize-measurements"))[0], 0)
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertRegex(text, r"ATTEMPT \w+ first opened \S+ resumed 1 "
                         r"status interrupted,pass candidate ")
        # A resumption made in another checkout is named: one place for
        # every checkout of a line, not of the opening alone.
        tg.ledger_append(self.attempts, event="open", stage="first",
                         attempt="a" * 32, candidate=CANDIDATE,
                         counts_file="toy_iterations.json", counts="s",
                         seed="s0", output="o", checkout="/A")
        for event in ("resume", "close"):
            tg.ledger_append(self.attempts, event=event, stage="first",
                             attempt="a" * 32, candidate=CANDIDATE,
                             counts_file="toy_iterations.json", counts="s",
                             seed="s0", output="o", checkout="/B",
                             **(dict(status="pass") if event == "close"
                                else {}))
        status, text = self.go(self.replay_argv(out))
        self.assertIn("checkout /A,/B", text)
        self.assertIn("LEDGER-CHECKOUTS: the attempts of this ledger were "
                      "made in 3 different checkouts", text)

    def test_attempts_made_in_several_checkouts_are_named(self):
        out, _, _ = self.first()
        tg.ledger_append(self.attempts, event="open", stage="first",
                         attempt="y" * 32, candidate=CANDIDATE,
                         counts_file="toy_iterations.json", counts="s",
                         seed="s0", output="o", checkout="/elsewhere")
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertIn("LEDGER-CHECKOUTS: the attempts of this ledger were "
                      "made in 2 different checkouts", text)
        self.assertIn("checkout /elsewhere", text)

    def test_replay_needs_the_ledger_and_the_opening_in_it(self):
        out, _, _ = self.first()
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)
        opening = self.ledger()[0]
        self.table.ledger = self.root / "other.jsonl"
        self.attempts = self.table.ledger
        with self.assertRaisesRegex(ValueError, "no attempts ledger"):
            self.go(self.replay_argv(out))
        self.attempts.write_text("")
        with self.assertRaisesRegex(ValueError, "no opening"):
            self.go(self.replay_argv(out))
        # An opening of another grid, or of the same one with other
        # settings, is not its opening.
        for key, value in (("attempt", "0" * 32), ("candidate", "d" * 40),
                           ("counts", "x"), ("stage", "second")):
            with self.subTest(key):
                self.attempts.write_text(json.dumps(
                    dict(opening, **{key: value}, prev="0" * 64)) + "\n")
                with self.assertRaisesRegex(ValueError, "no opening"):
                    self.go(self.replay_argv(out))

    def test_a_line_cut_short_by_a_crash_is_tolerated_and_reported(self):
        out, _, _ = self.first()
        before = self.attempts.read_text()
        self.attempts.write_text(before + '{"event": "op')
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertIn("LEDGER-TORN-LINE 3: 13 bytes", text)
        # The next append ends that line, acknowledges it and goes on.
        self.first(name="two")
        text = self.lines()
        self.assertEqual(text[2], '{"event": "op')
        self.assertEqual(json.loads(text[3])["event"], "torn")
        self.assertEqual(json.loads(text[3])["skipped"],
                         [tg.ledger_hash('{"event": "op')])
        self.assertEqual(json.loads(text[3])["prev"],
                         tg.ledger_hash(text[1]))
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertNotIn("LEDGER-TORN-LINE", text)
        self.assertIn("ATTEMPTS of TOY: 2 in the ledger", text)

    def test_a_run_of_cut_lines_at_the_tail_is_acknowledged_together(self):
        # The acknowledging append was itself cut short (the same full disk),
        # or stopped just after the newline that ends the cut line: lines
        # at the end that are no record, however many, however ended.
        out, _, _ = self.first()
        before = self.attempts.read_text()
        for what, tail in (
                ("after the newline", ['{"event": "op\n']),
                ("acknowledgement cut", ['{"event": "op\n',
                                         '{"event": "torn", "pr']),
                ("three", ['{"event": "op\n', "x\n", '{"ev'])):
            with self.subTest(what):
                self.attempts.write_text(before + "".join(tail))
                status, text = self.go(self.replay_argv(out))
                self.assertEqual(status, 0)
                self.assertEqual(text.count("LEDGER-TORN-LINE"), len(tail))
                self.first(name="again-" + str(len(tail)) + what[:3])
                lines = self.lines()
                torn = [json.loads(x) for x in lines
                        if x.startswith('{"event": "torn", "prev"')]
                self.assertEqual(len(torn), 1)
                self.assertEqual(torn[0]["skipped"], [
                    tg.ledger_hash(x.rstrip("\n")) for x in tail])
                status, text = self.go(self.replay_argv(out))
                self.assertEqual(status, 0)
                self.assertNotIn("LEDGER-TORN-LINE", text)
                self.attempts.write_text(before)

    def test_a_cut_line_is_refused_when_it_is_not_at_the_tail(self):
        out, _, _ = self.first()
        before = self.attempts.read_text()
        for what, text in (
                ("unacknowledged", before + '{"event": "op\n' + before),
                ("acknowledging another run", before + '{"event": "op\n' +
                 json.dumps(dict(event="torn", prev=tg.ledger_hash(
                     before.split("\n")[-2]), skipped=["0" * 64])) + "\n")):
            with self.subTest(what):
                self.attempts.write_text(text)
                with self.assertRaisesRegex(ValueError, "malformed attempts"):
                    self.go(self.replay_argv(out))

    def test_a_complete_last_line_without_its_newline_is_kept(self):
        out, _, _ = self.first()
        self.attempts.write_text(self.attempts.read_text().rstrip("\n"))
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertIn("LEDGER-UNTERMINATED-LAST-LINE 2", text)
        self.first(name="two")
        self.assertEqual([x["event"] for x in self.ledger()],
                         ["open", "close", "open", "close"])
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)

    def test_a_close_that_cannot_be_written_leaves_the_outcome(self):
        real = tg.ledger_append

        def refusing(path, **record):
            if record["event"] == "close":
                raise OSError("disk full")
            return real(path, **record)
        for what in ("returns", "raises"):
            with self.subTest(what), patch.object(tg, "ledger_append",
                                                  refusing):
                self.attempts.unlink(missing_ok=True)
                self.calls = 0
                self.explode_at = 4 if what == "raises" else None
                err = io.StringIO()
                with contextlib.redirect_stderr(err):
                    if what == "raises":
                        with self.assertRaisesRegex(RuntimeError,
                                                    "infrastructure"):
                            self.first(name=what)
                    else:
                        out, status, _ = self.first(name=what)
                        self.assertEqual(status, 0)
                self.assertIn("ATTEMPT-NOT-CLOSED", err.getvalue())
                self.assertEqual([x["event"] for x in self.ledger()],
                                 ["open"])
        self.explode_at = None

    def test_a_resumption_needs_its_opening_before_any_cell(self):
        self.explode_at = 4
        with self.assertRaises(RuntimeError):
            self.first()
        self.explode_at, calls = None, self.calls
        kept = self.attempts.read_text()
        self.attempts.unlink()
        with self.assertRaisesRegex(ValueError, "no attempts ledger"):
            self.go(self.run_argv() + ["--resume"])
        self.attempts.write_text("")
        with self.assertRaisesRegex(ValueError, "no opening"):
            self.go(self.run_argv() + ["--resume"])
        self.assertEqual(self.calls, calls)
        self.attempts.write_text(kept)
        self.assertEqual(self.go(self.run_argv() + ["--resume"])[0], 0)

    def test_a_second_stage_resumption_needs_its_opening_too(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)
        grid, _, _ = self.first()
        argv = self.argv("extend", self.root / "ext", "--grid", str(grid),
                         "--authorize-measurements")
        self.explode_at = self.calls + 1
        with self.assertRaises(RuntimeError):
            self.go(argv)
        self.explode_at, calls = None, self.calls
        kept = self.attempts.read_text()
        self.attempts.write_text("".join(
            x + "\n" for x in kept.split("\n")[:2]))
        with self.assertRaisesRegex(ValueError, "no opening"):
            self.go(argv + ["--resume"])
        self.assertEqual(self.calls, calls)
        self.attempts.write_text(kept)
        self.assertEqual(self.go(argv + ["--resume"])[0], 0)


class Provenance(Rig):
    """A fixed table's counts are derived again from their pilot whenever a
    grid runs, is extended or is replayed."""

    def test_a_run_extension_and_replay_need_the_pilot(self):
        out, _, _ = self.first()
        argv = self.replay_argv(out)
        i = argv.index("--pilot")
        with self.assertRaisesRegex(ValueError, "needs --pilot DIR"):
            self.go(argv[:i] + argv[i + 2:])
        run = self.argv("run", self.root / "x", "--candidate", CANDIDATE,
                        "--authorize-measurements")
        i = run.index("--pilot")
        with self.assertRaisesRegex(ValueError, "needs --pilot DIR"):
            self.go(run[:i] + run[i + 2:])
        ext = self.argv("extend", self.root / "ext", "--grid", str(out),
                        "--authorize-measurements")
        i = ext.index("--pilot")
        with self.assertRaisesRegex(ValueError, "needs --pilot DIR"):
            self.go(ext[:i] + ext[i + 2:])
        self.assertEqual(self.calls, 12)

    def test_a_changed_pilot_archive_is_refused_everywhere(self):
        out, _, _ = self.first()
        archive = next(self.pilot_dir.glob("*.json.xz"))
        archive.write_bytes(archive.read_bytes() + b"x")
        with self.assertRaisesRegex(ValueError, "changed archive"):
            self.go(self.replay_argv(out))
        self.calls = 0
        with self.assertRaisesRegex(ValueError, "changed archive"):
            self.first(name="again")
        self.assertEqual(self.calls, 0)

    def test_a_changed_variability_is_refused(self):
        path = self.pilot_dir / "variability.json"
        value = json.loads(path.read_text())
        value[self.table.names()[0]]["cpu"]["median"] = 2.0
        path.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "changed pilot variability"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_a_changed_variability_in_the_inventory_is_refused(self):
        path = self.pilot_dir / "inventory.json"
        value = json.loads(path.read_text())
        value["runs"][0]["variability"]["cpu"]["median"] = 2.0
        path.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "changed pilot variability"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_a_pilot_process_that_is_not_the_baseline_is_refused(self):
        self.pilot_revision = "e" * 40
        code, _ = self.go(self.argv("pilot", self.root / "bad",
                                    "--authorize-measurements"))
        self.assertEqual(code, 0)
        with self.assertRaisesRegex(ValueError, "not the baseline"):
            self.go(["predeclare", "--grid", str(self.root / "bad"),
                     "--output", str(self.root / "c.json")])
        with self.assertRaisesRegex(ValueError, "not the baseline"):
            self.go(["verify-counts", "--grid", str(self.root / "bad")])
        self.pilot_dir = self.root / "bad"
        with self.assertRaisesRegex(ValueError, "not the baseline"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_one_side_that_is_not_the_baseline_is_refused_too(self):
        for side in ("baseline", "candidate"):
            with self.subTest(side):
                inventory = self.inventory(self.pilot_dir)
                row = inventory["runs"][0]
                with tempfile.TemporaryDirectory() as tmp:
                    case = Path(tmp) / "c"
                    tg.bundle.unpack(self.pilot_dir / row["archive"], case)
                    manifest, = case.rglob("manifest.json")
                    value = json.loads(manifest.read_text())
                    value["selections"][side]["revision"] = "e" * 40
                    manifest.write_text(json.dumps(value))
                    with self.assertRaisesRegex(ValueError, "not the base"):
                        self.grid.check_pilot_cell(
                            manifest.parent.parent, inventory, row,
                            self.grid.calibration_counts(
                                manifest.parent.parent, row["case"],
                                row["size"]))

    def test_a_control_made_at_another_head_than_the_pilot_is_refused(self):
        inventory = dict(self.inventory(self.pilot_dir),
                         checkout={"head": "a" * 40})
        row = inventory["runs"][0]
        for label, head, refused in (
                ("other", "b" * 40, True), ("same", "a" * 40, False),
                ("none", None, True)):
            with self.subTest(label), tempfile.TemporaryDirectory() as tmp:
                case = Path(tmp) / "c"
                tg.bundle.unpack(self.pilot_dir / row["archive"], case)
                manifest, = case.rglob("manifest.json")
                value = json.loads(manifest.read_text())
                value.pop("head", None)
                if head is not None:
                    value["head"] = head
                manifest.write_text(json.dumps(value))
                folder = manifest.parent.parent
                found = self.grid.calibration_counts(
                    folder, row["case"], row["size"])
                if refused:
                    with self.assertRaisesRegex(
                            ValueError, "ran at %s, not at the "
                            "pilot head aaaaaaaaaaaa" % (
                                "bbbbbbbbbbbb" if head else r"\(none\)")):
                        self.grid.check_pilot_cell(
                            folder, inventory, row, found)
                else:
                    self.grid.check_pilot_cell(folder, inventory, row, found)

    def test_counts_that_no_pilot_made_are_refused(self):
        value = json.loads(self.counts.read_text())
        for label, changed in (
                ("no pilot", {k: v for k, v in value.items()
                              if k != "pilot"}),
                ("a count", dict(value, iterations=dict(
                    value["iterations"], **{"exclude_empty-0": 1024}))),
                ("a seal", dict(value, pilot=dict(
                    value["pilot"], inventory="0" * 64)))):
            with self.subTest(label):
                self.counts.write_text(json.dumps(changed))
                with self.assertRaisesRegex(ValueError,
                                            "differ from their pilot"):
                    self.first(name="g" + label.replace(" ", ""))
        self.assertEqual(self.calls, 0)

    def test_a_pilot_of_other_seconds_is_no_provenance(self):
        path = self.pilot_dir / "inventory.json"
        value = json.loads(path.read_text())
        path.write_text(json.dumps(dict(value, seconds=0.5)))
        with self.assertRaisesRegex(ValueError, "pilot batch seconds"):
            self.first()


class Commits(Rig):
    """The counts file is fixed by one commit that git alone dates, and the
    grid names it."""

    def test_the_header_names_the_file_the_commit_and_the_attempt(self):
        out, _, _ = self.first()
        header = self.inventory(out)
        self.assertEqual((header["counts_file"], header["counts_commit"],
                          header["iterations_seal"]),
                         ("toy_iterations.json", COMMIT,
                          a.seal(self.counts)))
        self.assertRegex(header["attempt"], "^[0-9a-f]{32}$")

    def test_a_counts_file_with_two_commits_is_refused(self):
        self.commits = [COMMIT, "2" * 40]
        with self.assertRaisesRegex(ValueError, "exactly one commit.*not 2"):
            self.first()
        self.commits = []
        with self.assertRaisesRegex(ValueError, "exactly one commit.*not 0"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_replay_derives_the_commit_and_the_seal_again(self):
        out, _, _ = self.first()
        header = self.inventory(out)
        for key, value, message in (
                ("counts_commit", "2" * 40, "changed counts commit"),
                ("iterations_seal", "0" * 64, "changed counts seal"),
                ("counts_file", "elsewhere.json", "unknown counts file")):
            with self.subTest(key):
                (out / "inventory.json").write_text(
                    json.dumps(dict(header, **{key: value})))
                with self.assertRaisesRegex(ValueError, message):
                    self.go(self.replay_argv(out))
        (out / "inventory.json").write_text(json.dumps(
            {k: v for k, v in header.items() if k != "attempt"}))
        with self.assertRaisesRegex(ValueError, "no attempt recorded"):
            self.go(self.replay_argv(out))

    def test_replay_sees_a_history_that_gained_a_commit(self):
        out, _, _ = self.first()
        self.commits = [COMMIT, "2" * 40]
        with self.assertRaisesRegex(ValueError, "exactly one commit"):
            self.go(self.replay_argv(out))

    def test_the_settings_at_replay_are_those_of_the_counts_file(self):
        out, _, _ = self.first()
        self.table.pairs, self.table.samples = 12, 4
        self.table.seed = "s1"
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)
        # A run under the changed table is another matter.
        with self.assertRaisesRegex(ValueError, "differs from the table"):
            self.first(name="two")

    def test_the_counts_record_the_limits_of_the_second_stage(self):
        counts = json.loads(self.counts.read_text())
        self.assertEqual((counts["target"], counts["max_pairs"],
                          counts["headroom"]),
                         (tg.TARGET, tg.MAX_PAIRS, 2))
        # A run refuses a file that says other than the table.
        for key, value in (("target", 0.02), ("max_pairs", 60),
                           ("headroom", 3)):
            with self.subTest(key):
                self.rewrite(**{key: value})
                with self.assertRaisesRegex(
                        ValueError, "the %s of the counts differs from the "
                        "table's" % key.replace("_", " ")):
                    self.first(name="g-" + key)
                self.rewrite(**{key: counts[key]})
        self.assertEqual(self.calls, 0)

    def test_the_second_stage_replays_by_the_limits_of_its_counts(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)
        grid, _, _ = self.first()
        ext = self.root / "ext"
        status, _ = self.go(self.argv(
            "extend", ext, "--grid", str(grid), "--authorize-measurements"))
        self.assertEqual(status, 0)
        recorded = self.inventory(ext)
        self.assertEqual((recorded["target"], recorded["max_pairs"]),
                         (tg.TARGET, tg.MAX_PAIRS))
        # Another target and cap in the table change neither the plan nor
        # the replay of grids made under the counts that said otherwise.
        self.table.target, self.table.max_pairs = 0.5, 30
        status, text = self.go(self.replay_argv(ext))
        self.assertEqual(status, 0, text)
        self.assertEqual(self.go(self.replay_argv(grid))[0], 2)

    def test_the_counts_are_derived_again_by_their_own_seconds_and_headroom(
            self):
        pilot = str(self.pilot_dir)
        out, _, _ = self.first()
        # The table is edited after the counts were made: other seconds, no
        # longer cell, another headroom. What the file says is what counts.
        self.table.seconds, self.table.seconds_by_case = 0.6, {}
        self.table.headroom = 5
        self.assertEqual(self.go(["verify-counts", "--grid", pilot])[0], 0)
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)
        # And a pilot made for other seconds than the file's is refused.
        path = self.pilot_dir / "inventory.json"
        recorded = json.loads(path.read_text())
        path.write_text(json.dumps(dict(recorded, seconds_by_case={})))
        with self.assertRaisesRegex(ValueError, "pilot batch seconds "
                                    "differ"):
            self.go(["verify-counts", "--grid", pilot])

    def test_the_counts_are_bound_to_the_sealed_files(self):
        value = json.loads(self.counts.read_text())
        self.assertEqual(sorted(value["sealed"]), sorted(SEALED))
        good = self.counts.read_text()
        self.rewrite(sealed=dict(value["sealed"], **{"one.txt": "0" * 64}))
        with self.assertRaisesRegex(ValueError, "bound to other sealed"):
            self.first()
        self.assertEqual(self.calls, 0)
        self.counts.write_text(good)
        out, _, _ = self.first()
        header = self.inventory(out)
        changed = dict(value, sealed=dict(value["sealed"], **{
            "one.txt": "0" * 64}))
        (out / "inventory.json").write_text(
            json.dumps(dict(header, iterations=changed)))
        self.counts.write_text(json.dumps(changed))
        with self.assertRaisesRegex(ValueError, "bound to other sealed"):
            self.go(self.replay_argv(out))


class PinFile(Rig):
    """The pins are in a file of their own, sealed apart from the sealed
    files the counts are bound to, so that a pin bumped after a production
    fix is a new candidate and not a new pilot."""
    PIN = dict(blob="f" * 40, reason="A reviewed change of two.")

    def setUp(self):
        super().setUp()
        self.differ = {"src/two.sml"}

    def make_table(self, **kw):
        (self.sealed_dir / "pins.py").write_text("PINNED = one\n")
        kw.setdefault("pinned", {"src/two.sml": self.PIN})
        return super().make_table(pin_file="pins.py", **kw)

    def bump(self, pinned, history=True):
        """The pin file as another version, as an operator does when a fix
        changes a reviewed file."""
        old = a.seal(self.sealed_dir / "pins.py")
        (self.sealed_dir / "pins.py").write_text("PINNED = two\n")
        if history:
            self.table.pin_history = {old["sha256"]: {
                "src/two.sml": self.PIN}}
        self.table.pinned = pinned

    def test_the_seal_of_the_pins_is_recorded_beside_the_sealed_files(self):
        out, status, _ = self.first()
        header = self.inventory(out)
        self.assertEqual(header["pins"], a.seal(self.sealed_dir / "pins.py"))
        self.assertNotIn("pins.py", header["sealed"])
        self.assertNotIn("pins.py", json.loads(self.counts.read_text())[
            "sealed"])
        self.assertNotIn("pins", self.inventory(self.pilot_dir))
        self.assertEqual(self.table.code(), (
            "driver", "engine", "acceptance", "sealed", "pins"))

    def test_a_grid_without_the_seal_of_the_pins_is_refused(self):
        header = self.inventory(self.first()[0])
        self.grid.check_header(header)
        with self.assertRaisesRegex(ValueError, "no seal of the pins"):
            self.grid.check_header({k: v for k, v in header.items()
                                    if k != "pins"})

    def test_bumped_pins_leave_the_counts_and_the_sealed_files_alone(self):
        self.bump({"src/two.sml": dict(self.PIN, reason="Seen again.")})
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot_dir)])[0], 0)
        out, status, _ = self.first(name="new")
        self.assertEqual(self.inventory(out)["pins"],
                         a.seal(self.sealed_dir / "pins.py"))
        self.assertEqual(self.inventory(out)["sealed"],
                         json.loads(self.counts.read_text())["sealed"])

    def test_a_grid_replays_by_the_pins_it_was_judged_by(self):
        out, status, _ = self.first()
        self.assertEqual(status, 0)
        # The pin file changed and the table knows the old version.
        self.bump({}, history=True)
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)
        # Without the old version in the table the pins are not known.
        self.table.pin_history = {}
        with self.assertRaisesRegex(ValueError, "changed pins"):
            self.go(self.replay_argv(out))

    def test_a_pin_history_belongs_to_a_table_with_a_pin_file(self):
        with self.assertRaisesRegex(ValueError, "belongs to a table"):
            tg.Table("toy", "TOY", CASES, "d.py", "c.json", sources=SOURCES,
                     schedule="ramp", pin_history={"0" * 64: {}})
        with self.assertRaisesRegex(ValueError, "malformed pin"):
            self.make_table(pin_history={"0" * 64: {"src/two.sml": dict(
                blob="f" * 39, reason="x")}})


class AddedFiles(Rig):
    """A source the candidate adds is accepted only with a pin of its blob;
    the whole difference below the tree is published."""
    PIN = dict(blob="f" * 40, reason="A reviewed new file.")

    def make_table(self, **kw):
        kw.setdefault("pinned", {"src/two.sml": self.PIN})
        return super().make_table(**kw)

    def test_a_pinned_added_file_is_published_and_no_failure(self):
        self.absent, self.differ = {"src/two.sml"}, {"src/two.sml"}
        out, status, text = self.first()
        self.assertEqual(status, 0)
        self.assertEqual(self.inventory(out)["sources"]["src/two.sml"],
                         dict(baseline=None, candidate="f" * 40))
        identity = json.loads(
            (out / "decisions.json").read_text())["source_identity"]
        self.assertEqual(identity["differing"], [])
        self.assertEqual(identity["reviewed"], {"src/two.sml": self.PIN})
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)

    def test_an_added_file_with_another_blob_is_a_difference(self):
        self.absent, self.differ = {"src/two.sml"}, {"src/two.sml"}
        self.table.pinned = {"src/two.sml": dict(self.PIN, blob="e" * 40)}
        with self.unrefused():
            out, status, text = self.first()
        self.assertEqual(status, 2)
        self.assertIn("SOURCE-DIFFERS src/two.sml", text)

    def test_an_added_file_without_a_pin_is_refused(self):
        self.absent = {"src/one.sml"}
        with self.assertRaisesRegex(ValueError, "absent at the baseline "
                                    "and not pinned: src/one.sml"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_a_file_absent_at_both_commits_is_refused(self):
        self.absent, self.gone = {"src/two.sml"}, {"src/two.sml"}
        with self.assertRaisesRegex(ValueError, "absent at both"):
            self.first()
        self.assertEqual(self.calls, 0)


class SourceTree(Rig):
    """The name-status difference of every file below the tree is recorded
    and derived again from git."""

    def test_the_difference_is_recorded(self):
        out, _, _ = self.first()
        self.assertEqual(self.inventory(out)["source_tree"], dict(
            tree="src", changes=[["A", "src/new.sml"], ["M", "src/one.sml"]]))

    def test_replay_derives_it_again(self):
        out, _, _ = self.first()
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)
        self.changes = self.changes + [["M", "src/other.sml"]]
        with self.assertRaisesRegex(ValueError, "changed source difference"):
            self.go(self.replay_argv(out))
        self.changes = self.changes[:-1]
        header = self.inventory(out)
        header["source_tree"]["changes"] = header["source_tree"]["changes"][1:]
        (out / "inventory.json").write_text(json.dumps(header))
        with self.assertRaisesRegex(ValueError, "changed source difference"):
            self.go(self.replay_argv(out))

    def test_the_record_belongs_to_the_table(self):
        out, _, _ = self.first()
        header = self.inventory(out)
        bare = {k: v for k, v in header.items() if k != "source_tree"}
        with self.assertRaisesRegex(ValueError, "changed source tree"):
            self.grid.check_header(bare)
        self.table.tree = None
        with self.assertRaisesRegex(ValueError, "changed source tree"):
            self.grid.check_header(header)

    def test_a_table_without_a_tree_records_none(self):
        self.table.tree = None
        out, status, _ = self.first()
        self.assertEqual(status, 0)
        self.assertNotIn("source_tree", self.inventory(out))


class Revisions(Rig):
    """A counts file is never edited: a cell rejected as too short is
    rescaled in a new file the table lists, and the grid is run again."""

    def revise(self, *cells, previous=None, name="toy_iterations_2.json",
               grid=None):
        out = self.repo / name
        return self.go(["predeclare", "--grid", str(grid or self.pilot_dir),
                        "--output", str(out), "--revises",
                        str(previous or self.counts), "--rescale", *cells])

    def adopt(self, *names):
        self.table.revisions = tuple(self.repo / n for n in names)

    def test_a_revision_is_a_new_file_that_rescales_the_named_cells(self):
        before = self.counts.read_text()
        self.assertEqual(self.revise("exclude_empty-0")[0], 0)
        old = json.loads(before)
        new = json.loads((self.repo / "toy_iterations_2.json").read_text())
        self.assertEqual(self.counts.read_text(), before)
        for name, count in old["iterations"].items():
            self.assertEqual(new["iterations"][name], count * (
                4 if name == "exclude_empty-0" else 1))
        self.assertEqual(new["revises"], dict(
            previous=a.seal(self.counts), cells=["exclude_empty-0"],
            factor=4, reason="fixed calibration too short"))
        for key in ("pilot", "sealed", "layout_seed", "pairs", "samples",
                    "baseline", "seconds"):
            self.assertEqual(new[key], old[key], key)

    def test_the_revision_is_derived_again_from_the_pilot(self):
        self.revise("exclude_empty-0", "exclude_missing-10")
        self.adopt("toy_iterations_2.json")
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot_dir)])[0], 0)
        path = self.repo / "toy_iterations_2.json"
        value = json.loads(path.read_text())
        for label, changed in (
                ("count", dict(value, iterations=dict(
                    value["iterations"], **{"exclude_empty-0": 1024}))),
                ("cells", dict(value, revises=dict(
                    value["revises"], cells=["exclude_empty-0"]))),
                ("factor", dict(value, revises=dict(
                    value["revises"], factor=8))),
                ("link", dict(value, revises=dict(
                    value["revises"], previous="0" * 64)))):
            with self.subTest(label):
                path.write_text(json.dumps(changed))
                with self.assertRaises(ValueError):
                    self.go(["verify-counts", "--grid", str(self.pilot_dir)])

    def test_the_file_a_revision_follows_is_derived_again_too(self):
        changed = json.loads(self.counts.read_text())
        changed["iterations"]["exclude_missing-10"] *= 2
        self.counts.write_text(json.dumps(changed))
        # A revision made, by hand, from a file its pilot did not make.
        value = self.grid.rescaled(self.counts, ["exclude_empty-0"])
        (self.repo / "toy_iterations_2.json").write_text(json.dumps(value))
        self.adopt("toy_iterations_2.json")
        with self.assertRaisesRegex(ValueError, "differ from their pilot"):
            self.go(["verify-counts", "--grid", str(self.pilot_dir)])

    def test_a_revision_is_asked_for_precisely(self):
        before = list(self.repo.glob("*.json"))
        with self.assertRaisesRegex(ValueError, "goes with --rescale or"):
            self.go(["predeclare", "--grid", str(self.pilot_dir), "--output",
                     str(self.repo / "r.json"), "--revises",
                     str(self.counts)])
        with self.assertRaisesRegex(ValueError, "go together|goes with"):
            self.go(["predeclare", "--grid", str(self.pilot_dir), "--output",
                     str(self.repo / "r.json"), "--rescale",
                     "exclude_empty-0"])
        for cells in (["no_such-0"], ["exclude_empty-0", "exclude_empty-0"]):
            with self.assertRaisesRegex(ValueError, "rescales cells"):
                self.revise(*cells)
        self.assertEqual(list(self.repo.glob("*.json")), before)

    def test_a_revision_follows_the_last_file_and_its_pilot(self):
        other = self.root / "other.json"
        other.write_text(self.counts.read_text().replace("64", "32"))
        with self.assertRaisesRegex(ValueError, "follows the table's last"):
            self.revise("exclude_empty-0", previous=other)
        changed = json.loads(self.counts.read_text())
        changed["iterations"]["exclude_empty-0"] *= 2
        self.counts.write_text(json.dumps(changed))
        with self.assertRaisesRegex(ValueError, "differ from their pilot"):
            self.revise("exclude_empty-1")

    def test_a_revision_never_overwrites(self):
        self.revise("exclude_empty-0")
        with self.assertRaisesRegex(ValueError, "refusing to overwrite"):
            self.revise("exclude_empty-1")

    def test_a_run_uses_the_last_file_and_names_it(self):
        self.revise("exclude_empty-0")
        self.adopt("toy_iterations_2.json")
        new = self.repo / "toy_iterations_2.json"
        out, status, _ = self.first()
        self.assertEqual(status, 0)
        header = self.inventory(out)
        self.assertEqual((header["counts_file"], header["iterations_seal"]),
                         ("toy_iterations_2.json", a.seal(new)))
        counts = json.loads(new.read_text())["iterations"]
        self.assertEqual(header["iterations"]["iterations"], counts)
        self.assertEqual({r["iterations"] for r in header["runs"]
                          if r["case"] == "exclude_empty" and r["size"] == 0},
                         {counts["exclude_empty-0"]})
        with self.assertRaisesRegex(ValueError, "changed predeclared"):
            self.first(name="old", extra=("--iterations", str(self.counts)))

    def test_an_older_grid_replays_against_its_own_file(self):
        one, _, _ = self.first(name="one")
        self.revise("exclude_empty-0")
        self.adopt("toy_iterations_2.json")
        self.assertEqual(self.go(self.replay_argv(one))[0], 0)
        two, _, _ = self.first(name="two")
        self.assertEqual(self.go(self.replay_argv(two))[0], 0)
        self.assertEqual(self.inventory(one)["counts_file"],
                         "toy_iterations.json")
        self.assertEqual(self.inventory(two)["counts_file"],
                         "toy_iterations_2.json")

    def test_a_revision_of_a_revision_chains_to_the_pilot(self):
        self.revise("exclude_empty-0")
        self.adopt("toy_iterations_2.json")
        self.revise("exclude_empty-0", "exclude_missing-0",
                    previous=self.repo / "toy_iterations_2.json",
                    name="toy_iterations_3.json")
        self.adopt("toy_iterations_2.json", "toy_iterations_3.json")
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot_dir)])[0], 0)
        old = json.loads(self.counts.read_text())["iterations"]
        new = json.loads((self.repo / "toy_iterations_3.json").read_text())
        self.assertEqual(new["iterations"]["exclude_empty-0"],
                         old["exclude_empty-0"] * 16)
        self.assertEqual(new["iterations"]["exclude_missing-0"],
                         old["exclude_missing-0"] * 4)
        # A table that no longer names the file a revision follows cannot
        # derive it.
        self.adopt("toy_iterations_3.json")
        with self.assertRaisesRegex(ValueError, "does not name"):
            self.go(["verify-counts", "--grid", str(self.pilot_dir)])

    def test_a_file_after_the_first_must_revise_the_one_before_it(self):
        self.revise("exclude_empty-0", name="two.json")
        self.revise("exclude_missing-0", name="three.json")
        two, three = (self.repo / n for n in ("two.json", "three.json"))
        # Not a link to the file before it (it is to the first).
        self.adopt("two.json", "three.json")
        with self.assertRaisesRegex(ValueError, "revises the file before"):
            self.go(["verify-counts", "--grid", str(self.pilot_dir)])
        # No link at all.
        value = json.loads(three.read_text())
        del value["revises"]
        three.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "after the first revises"):
            self.go(["verify-counts", "--grid", str(self.pilot_dir)])
        # And the first file revises no other.
        self.adopt("two.json")
        value = json.loads(self.counts.read_text())
        value["revises"] = json.loads(two.read_text())["revises"]
        self.counts.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "first counts file revises"):
            self.go(["verify-counts", "--grid", str(self.pilot_dir),
                     "--counts", str(self.counts)])

    def repilot(self, reason, previous=None, name="toy_iterations_2.json",
                grid=None):
        return self.go(["predeclare", "--grid", str(grid or self.pilot2),
                        "--output", str(self.repo / name), "--revises",
                        str(previous or self.counts), "--repilot", reason])

    @property
    def pilot2(self):
        """A second pilot, made when it is first asked for, of a fixture
        that calibrates to other counts."""
        folder = self.root / "pilot2"
        if not folder.exists():
            self.max_count = lambda case, size: 8 * 2 ** len(str(size))
            self.make_pilot(folder)
        return folder

    def test_a_revision_may_be_a_fresh_pilot_with_a_reason(self):
        reason = "the fixture measured a different workload"
        self.assertEqual(self.repilot(reason)[0], 0)
        new = json.loads((self.repo / "toy_iterations_2.json").read_text())
        self.assertEqual(new["revises"], dict(
            previous=a.seal(self.counts), repilot=reason))
        self.assertEqual(new["pilot"]["inventory"],
                         a.seal(self.pilot2 / "inventory.json"))
        self.assertNotEqual(new["pilot"], json.loads(
            self.counts.read_text())["pilot"])
        self.adopt("toy_iterations_2.json")
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot2)])[0], 0)
        # The new file is derived from the new pilot, and not from the old.
        with self.assertRaisesRegex(ValueError, "another pilot"):
            self.go(["verify-counts", "--grid", str(self.pilot_dir)])
        value = json.loads((self.repo / "toy_iterations_2.json").read_text())
        # The link is derived again; the reason is the operator's words.
        (self.repo / "toy_iterations_2.json").write_text(json.dumps(
            dict(value, revises=dict(value["revises"], previous="0" * 64))))
        with self.assertRaises(ValueError):
            self.go(["verify-counts", "--grid", str(self.pilot2)])

    def test_a_fresh_pilot_needs_a_reason_and_another_pilot(self):
        for reason in ("", "  "):
            with self.assertRaisesRegex(ValueError, "states its reason"):
                self.repilot(reason)
        with self.assertRaisesRegex(ValueError, "another pilot"):
            self.repilot("a reason", grid=self.pilot_dir)
        self.assertFalse((self.repo / "toy_iterations_2.json").exists())

    def test_the_two_kinds_of_link_chain_in_the_table_order(self):
        self.revise("exclude_empty-0", name="two.json")
        self.adopt("two.json")
        self.assertEqual(self.repilot("a new fixture", name="three.json",
                                      previous=self.repo / "two.json")[0], 0)
        self.adopt("two.json", "three.json")
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot2)])[0], 0)
        self.assertEqual(self.go(["verify-counts", "--counts",
                                  str(self.repo / "two.json"), "--grid",
                                  str(self.pilot_dir)])[0], 0)
        self.revise("exclude_empty-1", name="four.json",
                    previous=self.repo / "three.json", grid=self.pilot2)
        self.adopt("two.json", "three.json", "four.json")
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot2)])[0], 0)

    def test_only_a_fixed_table_has_revisions(self):
        with self.assertRaisesRegex(ValueError, "revisions belong"):
            tg.Table("toy", "TOY", CASES, "d.py", "c.json",
                     schedule="ramp", revisions=("c2.json",))
        with self.assertRaisesRegex(ValueError, "repeated counts file"):
            self.make_table(revisions=(self.counts,))


class WarmupCount(unittest.TestCase):
    """The count rule of the warmup schedule."""

    def test_the_count_is_a_ceiling_of_the_exact_quotient(self):
        # 0.1 * 3 / 0.3 is 1.0000000000000002 in floats, exactly 1 here.
        self.assertEqual(tg.warmup_count(1, 0.1, [(3, 0.3)]), 1)
        self.assertEqual(tg.warmup_count(1, 0.3, [(3, 0.9)]), 1)
        self.assertEqual(tg.warmup_count(1, 0.3, [(3, 0.8999)]), 2)
        self.assertEqual(tg.warmup_count(1, 1.0, [(8, 1.5)]), 6)
        self.assertEqual(tg.warmup_count(1, 1, [(8, 2.0)]), 4)
        self.assertEqual(tg.warmup_count(1, 1.0, [(7, 1.0)]), 7)

    def test_the_count_is_the_largest_over_the_processes(self):
        finals = [(4, 1.0), (8, 1.0), (2, 0.1), (1, 100.0)]
        self.assertEqual(tg.warmup_count(1, 1.0, finals), 20)
        self.assertEqual(tg.warmup_count(1, 1.0, finals[::-1]), 20)
        self.assertEqual(tg.warmup_count(1, 1.0, finals[:2]), 8)

    def test_the_headroom_multiplies_before_the_ceiling(self):
        finals = [(8, 1.5), (4, 1.25)]
        self.assertEqual(tg.warmup_count(1, 1.0, finals), 6)
        self.assertEqual(tg.warmup_count(2, 1.0, finals), 11)
        self.assertEqual(tg.warmup_count(3, 1.0, finals), 16)

    def test_the_count_is_a_batch_count(self):
        self.assertEqual(tg.warmup_count(1, 0.001, [(1, 10.0)]), 1)
        self.assertEqual(tg.warmup_count(1, 1.0, [(2 ** 30, 1.0)]), 2 ** 30)
        with self.assertRaisesRegex(ValueError, "1..1073741824"):
            tg.warmup_count(1, 1.0, [(2 ** 30, 0.5)])

    def test_inputs_that_are_not_a_pilot_are_refused(self):
        for args in ((0, 1.0, [(1, 1.0)]), (True, 1.0, [(1, 1.0)]),
                     (1.0, 1.0, [(1, 1.0)]), (1, 1.0, []),
                     (1, 0.0, [(1, 1.0)]), (1, -1.0, [(1, 1.0)]),
                     (1, float("nan"), [(1, 1.0)]),
                     (1, float("inf"), [(1, 1.0)]), (1, "1", [(1, 1.0)]),
                     (1, 1.0, [(0, 1.0)]), (1, 1.0, [(1.0, 1.0)]),
                     (1, 1.0, [(1, 0.0)]), (1, 1.0, [(1, 1)]),
                     (1, 1.0, [(1, float("nan"))]),
                     (1, 1.0, [(1, float("inf"))])):
            with self.subTest(args=args), self.assertRaisesRegex(
                    ValueError, "invalid warm-up count inputs"):
                tg.warmup_count(*args)

    def test_a_schedule_is_ramp_or_warmup_only(self):
        self.assertEqual(tg.schedule_of({}), "ramp")
        self.assertEqual(tg.schedule_of({"schedule": "warmup"}), "warmup")
        for value in ("ramp", "x", 1, ""):
            with self.assertRaises(ValueError):
                tg.schedule_of({"schedule": value})


class Warmup(Rig):
    """A table of the warmup schedule, whole: the counts a pilot gives, the
    run, the replay and the revision."""
    # The rig's pilot: the final batch of the first process is n iterations
    # in 1.5 times the target, that of the second n / 2 in 1.25 times it, so
    # the count of a cell is ceil(2 * n / 3) for n = 2, 4, ..., 32.
    expected = {0: 2, 1: 2, 10: 3, 100: 6, 1000: 11, 10000: 22}

    def make_table(self, **kw):
        return super().make_table(schedule="warmup", **kw)

    def cell_counts(self, counts=None):
        counts = json.loads(self.counts.read_text()) if counts is None \
            else counts
        return counts, {k: v for k, v in counts["iterations"].items()}

    def test_the_counts_follow_the_rule_and_name_the_schedule(self):
        counts, cells = self.cell_counts()
        self.assertEqual((counts["schedule"], counts["headroom"],
                          counts["rule"]), ("warmup", 1, tg.WARMUP_RULE))
        self.assertEqual(cells, {"%s-%d" % key: self.expected[key[1]]
                                 for key in self.table.keys()})
        self.assertNotEqual(set(cells.values()), {2 ** n for n in range(6)})
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot_dir)])[0], 0)

    def test_the_headroom_is_a_field_of_the_table(self):
        self.assertEqual(tg.Table("t", "T", CASES, self.driver, self.counts,
                                  fixed_seconds=True, seed="s0",
                                  schedule="warmup").headroom, 1)
        self.assertEqual(self.table.headroom, 1)
        self.declare_again(headroom=2)
        counts, cells = self.cell_counts()
        self.assertEqual(counts["headroom"], 2)
        self.assertEqual(cells["exclude_missing-100"], 11)
        self.assertEqual(cells["exclude_missing-10000"], 43)

    def test_a_warmup_table_has_fixed_seconds_and_a_known_schedule(self):
        for kw in (dict(schedule="warmup", fixed_seconds=False),
                   dict(schedule="x", fixed_seconds=True),
                   dict(schedule=None, fixed_seconds=True)):
            with self.subTest(**kw), self.assertRaises(ValueError):
                tg.Table("t", "T", CASES, self.driver, self.counts, **kw)

    def test_the_counts_are_derived_again_from_the_pilot(self):
        good = self.counts.read_text()
        value = json.loads(good)
        for label, changed in (
                ("count", dict(value, iterations=dict(
                    value["iterations"], **{"exclude_empty-0": 4}))),
                ("power of two", dict(value, iterations=dict(
                    value["iterations"], **{"exclude_missing-100": 8}))),
                ("rule", dict(value, rule=tg.RAMP_RULE)),
                ("headroom", dict(value, headroom=2)),
                ("ramp", {k: v for k, v in value.items()
                          if k != "schedule"}),
                ("named ramp", dict(value, schedule="ramp"))):
            with self.subTest(label):
                self.counts.write_text(json.dumps(changed))
                with self.assertRaises(ValueError):
                    self.go(["verify-counts", "--grid", str(self.pilot_dir)])
        self.counts.write_text(good)

    def test_counts_of_the_other_schedule_are_refused_by_a_run(self):
        good = json.loads(self.counts.read_text())
        for label, changed in (
                ("ramp", {k: v for k, v in good.items() if k != "schedule"}),
                ("named ramp", dict(good, schedule="ramp"))):
            with self.subTest(label):
                self.counts.write_text(json.dumps(changed))
                with self.assertRaises(ValueError):
                    self.first(name="g-" + label)
        self.assertEqual(self.calls, 0)

    def test_a_ramp_table_refuses_counts_that_name_a_schedule(self):
        self.table.schedule = "ramp"
        with self.assertRaisesRegex(ValueError, "schedule of the counts"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_a_run_gives_every_process_the_schedule_and_its_count(self):
        out, status, text = self.first()
        self.assertEqual(status, 0)
        counts = json.loads(self.counts.read_text())["iterations"]
        self.assertEqual(len(self.runs), 12)
        for options in self.runs:
            name = "%s-%d" % (options["case"][0], options["size"][0])
            self.assertEqual(options["batch_schedule"], "warmup")
            self.assertEqual(options["batch_iterations"], counts[name])
        self.assertEqual(text.count(" schedule=warmup"), 12)
        self.assertIn("exclude_missing-100 N=6 ", text)
        self.assertEqual(self.inventory(out)["iterations"]["schedule"],
                         "warmup")
        cells = self.cells()
        self.assertEqual(len(cells), 24)
        self.assertEqual({r["schedule"] for r in cells}, {"warmup"})

    def test_a_ramp_run_names_no_schedule(self):
        self.table.schedule = "ramp"
        self.table.headroom = 2
        self.declare_again()
        out, status, text = self.first()
        self.assertEqual(status, 0)
        self.assertTrue(all(o["batch_schedule"] is None for o in self.runs))
        self.assertNotIn("schedule", text)
        self.assertNotIn("schedule", self.inventory(out)["iterations"])
        self.assertTrue(all("schedule" not in r for r in self.cells()))

    def test_replay_derives_the_schedule_again_and_says_it(self):
        out, _, _ = self.first()
        self.analyses.clear()
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertIn("TOY schedule: warmup; counts rule: " + tg.WARMUP_RULE,
                      text)
        self.assertEqual({r["schedule"] for r in self.cells()}, {"warmup"})
        header = self.inventory(out)
        for label, counts in (
                ("ramp", {k: v for k, v in header["iterations"].items()
                          if k != "schedule"}),
                ("named ramp", dict(header["iterations"], schedule="ramp"))):
            with self.subTest(label):
                self.counts.write_text(json.dumps(counts))
                (out / "inventory.json").write_text(json.dumps(
                    dict(header, iterations=counts)))
                with self.assertRaises(ValueError):
                    self.go(self.replay_argv(out))

    def test_replay_of_a_ramp_grid_is_silent_about_a_schedule(self):
        self.table.schedule = "ramp"
        self.table.headroom = 2
        self.declare_again()
        out, _, _ = self.first()
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertNotIn("schedule", text)

    def revise(self, *cells):
        return self.go(["predeclare", "--grid", str(self.pilot_dir),
                        "--output", str(self.repo / "toy_iterations_2.json"),
                        "--revises", str(self.counts), "--rescale", *cells])

    def test_a_revision_rescales_a_count_that_is_not_a_power_of_two(self):
        self.assertEqual(self.revise("exclude_missing-100")[0], 0)
        old = json.loads(self.counts.read_text())
        new = json.loads((self.repo / "toy_iterations_2.json").read_text())
        self.assertEqual(new["iterations"]["exclude_missing-100"], 24)
        self.assertEqual(new["schedule"], "warmup")
        self.assertEqual(new["rule"], tg.WARMUP_RULE)
        self.assertEqual(new["revises"], dict(
            previous=a.seal(self.counts), cells=["exclude_missing-100"],
            factor=4, reason="fixed batch too short"))
        for name, count in old["iterations"].items():
            if name != "exclude_missing-100":
                self.assertEqual(new["iterations"][name], count)
        self.table.revisions = (self.repo / "toy_iterations_2.json",)
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot_dir)])[0], 0)
        out, status, _ = self.first()
        self.assertEqual(status, 0)
        self.assertEqual({o["batch_iterations"] for o in self.runs
                          if (o["case"][0], o["size"][0]) ==
                          ("exclude_missing", 100)}, {24})
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)

    def test_a_revision_keeps_the_batch_count_bound(self):
        value = json.loads(self.counts.read_text())
        value["iterations"]["exclude_empty-0"] = 2 ** 29 + 1
        self.counts.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "1..1073741824"):
            self.grid.rescaled(self.counts, ["exclude_empty-0"])
        value["iterations"]["exclude_empty-0"] = 2 ** 28
        self.counts.write_text(json.dumps(value))
        self.assertEqual(self.grid.rescaled(self.counts, [
            "exclude_empty-0"])["iterations"]["exclude_empty-0"], 2 ** 30)


class WarmupStages(Rig):
    """The second stage of a warmup table: its remeasurement is of the
    schedule and the count of its first stage, and replays."""
    pairs = 20

    def make_table(self, **kw):
        return super().make_table(schedule="warmup", **kw)

    def extend(self, grid, name="ext"):
        return self.go(self.argv("extend", self.root / name, "--grid",
                                 str(grid), "--authorize-measurements"))

    def open_cell(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)

    def test_the_remeasurement_uses_the_schedule_and_count(self):
        self.open_cell()
        grid, status, _ = self.first()
        self.assertEqual(status, 2)
        self.runs.clear()
        self.analyses.clear()
        status, text = self.extend(grid)
        self.assertEqual(status, 0)
        options, = self.runs
        counts = json.loads(self.counts.read_text())["iterations"]
        self.assertEqual(counts["%s-100" % CASES[1]], 6)
        self.assertEqual(
            (options["batch_schedule"], options["batch_iterations"]),
            ("warmup", 6))
        self.assertIn(" schedule=warmup", text)
        self.assertEqual(self.inventory(self.root / "ext")[
            "iterations"]["schedule"], "warmup")
        self.assertEqual({(r["iterations"], r["schedule"])
                          for r in self.cells()
                          if (r["case"], r["size"]) == (CASES[1], 100)},
                         {(6, "warmup")})

    def test_the_second_stage_replays_under_its_schedule(self):
        self.open_cell()
        grid, _, _ = self.first()
        self.assertEqual(self.extend(grid)[0], 0)
        ext = self.root / "ext"
        self.analyses.clear()
        status, text = self.go(self.replay_argv(ext))
        self.assertEqual(status, 0)
        self.assertIn("two-stage archives and decisions replayed: pass",
                      text)
        self.assertIn("TOY schedule: warmup; counts rule: ", text)
        self.assertEqual({r["schedule"] for r in self.cells()}, {"warmup"})
        header = self.inventory(ext)
        for label, counts in (
                ("ramp", {k: v for k, v in header["iterations"].items()
                          if k != "schedule"}),
                ("named ramp", dict(header["iterations"], schedule="ramp"))):
            with self.subTest(label):
                (ext / "inventory.json").write_text(json.dumps(
                    dict(header, iterations=counts)))
                with self.assertRaises(ValueError):
                    self.go(self.replay_argv(ext))


class ScheduleSwitch(Rig):
    """A table that changes its schedule after a grid was measured: the
    counts file of that grid says what it was, and a file that names no
    schedule is `ramp`, not whatever the table declares by now."""

    def test_an_earlier_ramp_grid_replays_under_a_warmup_table(self):
        out, status, _ = self.first()
        self.assertEqual(status, 0)
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)
        self.assertNotIn("schedule", json.loads(self.counts.read_text()))
        # The table is now of the warmup schedule (a decision applied
        # through a revision), headroom 1; the old counts file is as it was.
        self.table.schedule, self.table.headroom = "warmup", 1
        self.analyses.clear()
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertNotIn("schedule", text)
        self.assertEqual({r["iterations"] for r in self.cells()},
                         set(json.loads(self.counts.read_text())[
                             "iterations"].values()))
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot_dir)])[0], 0)

    def test_a_run_refuses_the_old_counts_under_a_warmup_table(self):
        self.table.schedule = "warmup"
        with self.assertRaisesRegex(ValueError, "schedule of the counts"):
            self.first()
        self.assertEqual(self.calls, 0)

    def test_a_file_derives_under_its_own_schedule(self):
        for table, own in (("warmup", "ramp"), ("ramp", "ramp")):
            with self.subTest(table=table):
                self.table.schedule = table
                found = json.loads(self.counts.read_text())
                self.assertEqual(
                    self.grid.file_settings(found)["schedule"], own)
        self.table.schedule = "ramp"
        found = dict(json.loads(self.counts.read_text()), schedule="warmup")
        self.assertEqual(self.grid.file_settings(found)["schedule"],
                         "warmup")


class Sweeping(Rig):
    """What a stopped run left is cleared only once the resumption is known
    to be of the same experiment, and under the lock."""

    def interrupted(self):
        self.explode_at = 4
        with self.assertRaises(RuntimeError):
            self.first()
        self.explode_at = None
        return self.root / "grid"

    def resume(self, out, candidate=CANDIDATE):
        return self.go(self.argv("run", out, "--candidate", candidate,
                                 "--resume", "--authorize-measurements"))

    def test_settings_are_compared_before_anything_is_swept(self):
        out = self.interrupted()
        (out / "x.json.partial").write_text("half")
        stray = out / ("%s-100.json.xz" % CASES[1])
        stray.write_bytes(b"unrecorded")
        with self.assertRaisesRegex(ValueError, "different settings"):
            self.resume(out, candidate="d" * 40)
        self.assertEqual((out / "x.json.partial").read_text(), "half")
        self.assertEqual(stray.read_bytes(), b"unrecorded")

    def test_the_sweep_happens_under_the_lock(self):
        out = self.interrupted()
        (out / "x.json.partial").write_text("half")
        held = []
        real = self.grid.sweep

        def sweep(root, kept):
            held.append(os.environ.get("HOL4_PERF_LOCK_FDS") is not None)
            return real(root, kept)
        with patch.dict(os.environ), patch.object(self.grid, "sweep", sweep):
            os.environ.pop("HOL4_PERF_LOCK_FDS", None)
            self.resume(out)
        self.assertEqual(held, [True])
        self.assertEqual(list(out.glob("*.partial*")), [])

    def test_a_resumption_without_an_inventory_says_so(self):
        (self.root / "grid").mkdir()
        with self.assertRaisesRegex(ValueError, "nothing to resume.*no "
                                    "inventory"):
            self.resume(self.root / "grid")

    def test_the_inventory_exists_before_the_first_cell(self):
        seen = []
        real = self.fake_run

        def watching(options):
            seen.append(Path(self.root / "grid" / "inventory.json").exists())
            return real(options)
        with patch.object(a, "run", watching):
            self.first()
        self.assertEqual(seen[0], True)


class Measuring(Rig):
    """What a run and a second stage check before measuring: the lock, the
    checkout, a source that cannot pass; and what they keep."""

    def widen(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)

    def extend_argv(self, grid, name="ext", *extra):
        return self.argv("extend", self.root / name, "--grid", str(grid),
                         "--authorize-measurements", *extra)

    @staticmethod
    def only(*cases):
        return tuple(x for c in cases
                     for x in ("--only", "%s-%d" % (c, SIZES[0])))

    def nothing_written(self, name="grid"):
        self.assertEqual(self.calls, 0)
        self.assertFalse((self.root / name).exists())
        self.assertFalse(self.attempts.exists())

    # The lock ----------------------------------------------------------

    def test_a_run_waits_for_the_lock_before_its_first_checkpoint(self):
        with a.serial_lock(self.repo):
            with self.assertRaises(a.Blocked):
                self.first()
        self.nothing_written()

    def test_a_resumed_run_waits_for_the_lock_before_touching_anything(self):
        self.explode_at = 4
        with self.assertRaises(RuntimeError):
            self.first()
        self.explode_at = None
        out = self.root / "grid"
        (out / "x.json.partial").write_text("half")
        before = ((out / "inventory.json").read_bytes(),
                  self.attempts.read_bytes())
        with a.serial_lock(self.repo):
            with self.assertRaises(a.Blocked):
                self.go(self.argv("run", out, "--candidate", CANDIDATE,
                                  "--resume", "--authorize-measurements"))
        self.assertEqual(((out / "inventory.json").read_bytes(),
                          self.attempts.read_bytes()), before)
        self.assertEqual((out / "x.json.partial").read_text(), "half")

    def test_a_second_stage_waits_for_the_lock_too(self):
        self.widen()
        grid, _, _ = self.first()
        before = self.attempts.read_bytes()
        calls = self.calls
        with a.serial_lock(self.repo):
            with self.assertRaises(a.Blocked):
                self.go(self.extend_argv(grid))
        self.assertFalse((self.root / "ext").exists())
        self.assertEqual((self.attempts.read_bytes(), self.calls),
                         (before, calls))
        self.explode_at = calls + 1
        with self.assertRaises(RuntimeError):
            self.go(self.extend_argv(grid))
        self.explode_at = None
        ext = self.root / "ext"
        (ext / "x.json.partial").write_text("half")
        before = ((ext / "inventory.json").read_bytes(),
                  self.attempts.read_bytes())
        with a.serial_lock(self.repo):
            with self.assertRaises(a.Blocked):
                self.go(self.extend_argv(grid, "ext", "--resume"))
        self.assertEqual(((ext / "inventory.json").read_bytes(),
                          self.attempts.read_bytes()), before)
        self.assertEqual((ext / "x.json.partial").read_text(), "half")

    # The checkout ------------------------------------------------------

    def test_a_run_is_bound_to_the_checkout_of_its_candidate(self):
        out, status, _ = self.first()
        self.assertEqual(self.bound, [CANDIDATE] * 3)
        self.assertEqual(self.inventory(out)["checkout"], dict(
            head=CANDIDATE, tree_outside_performance="t" * 64,
            products=PRODUCTS))

    def test_a_checkout_that_is_not_the_candidate_measures_nothing(self):
        def elsewhere(repo, commit=None, stamp=None):
            raise ValueError("the checkout is at %s, not at the commit "
                             "measured: %s" % ("e" * 40, commit))
        with patch.object(tg, "checkout_identity", elsewhere):
            with self.assertRaisesRegex(ValueError, "not at the commit"):
                self.first()
        self.nothing_written()

    def test_a_second_stage_is_in_the_checkout_of_the_first(self):
        self.widen()
        grid, _, _ = self.first()
        self.assertEqual(self.go(self.extend_argv(grid))[0], 0)
        self.assertEqual(self.bound, [CANDIDATE] * 6)

        def other_tree(repo, commit=None, stamp=None):
            return dict(head=commit, tree_outside_performance="u" * 64)
        calls = self.calls
        with patch.object(tg, "checkout_identity", other_tree):
            with self.assertRaisesRegex(ValueError, "not the one the first"):
                self.go(self.extend_argv(grid, "again"))
        self.assertEqual(self.calls, calls)
        self.assertFalse((self.root / "again").exists())

    def changing_after(self, calls, tree="u" * 64, refuse=False,
                       unjudged=False):
        """checkout_identity as the rig has it for `calls` calls, then
        another tree (or a refusal; or a checkout that cannot be judged, not
        clean): the checkout changed while the grid was measured."""
        seen = []

        def identity(repo, commit=None, stamp=None):
            seen.append(commit)
            if len(seen) > calls:
                if unjudged:
                    raise tg.CheckoutUnjudged(
                        "harness checkout is not clean: commit first")
                if refuse:
                    raise ValueError("bin/hol differs from the stamped "
                                     "build: run prepare at this commit")
                return dict(head=commit, tree_outside_performance=tree)
            return self.fake_checkout(repo, commit, stamp)
        return patch.object(tg, "checkout_identity", identity)

    def closing(self):
        return [(x["event"], x.get("status")) for x in self.ledger()]

    def test_a_checkout_that_changed_under_the_lock_measures_nothing(self):
        with self.changing_after(1):
            with self.assertRaisesRegex(tg.CheckoutChanged, "not the one "
                                        "recorded"):
                self.first()
        self.nothing_written()

    def test_a_checkout_that_changed_while_measuring_is_no_grid(self):
        out = self.root / "grid"
        for label, change in (("tree", dict()),
                              ("refused", dict(refuse=True))):
            with self.subTest(label):
                self.attempts.unlink(missing_ok=True)
                if out.exists():
                    shutil.rmtree(out)
                with self.changing_after(2, **change):
                    with self.assertRaises(tg.CheckoutChanged):
                        self.first()
                self.assertFalse((out / "decisions.json").exists())
                self.assertEqual(self.closing(), [
                    ("open", None), ("close", "checkout-changed")])

    def test_a_second_stage_whose_checkout_changed_is_no_grid_either(self):
        self.widen()
        grid, _, _ = self.first()
        with self.changing_after(2):
            with self.assertRaises(tg.CheckoutChanged):
                self.go(self.extend_argv(grid))
        self.assertFalse((self.root / "ext" / "decisions.json").exists())
        self.assertEqual(self.closing()[-2:], [
            ("open", None), ("close", "checkout-changed")])
        self.assertEqual(self.ledger()[-1]["stage"], "second")

    def test_a_pilot_is_not_extended_and_the_refusal_says_so(self):
        calls = self.calls
        with self.assertRaisesRegex(ValueError, "a pilot is checked by "
                                    "verify-counts"):
            self.go(self.extend_argv(self.pilot_dir))
        self.assertEqual(self.calls, calls)
        self.assertFalse((self.root / "ext").exists())

    def dead(self, argv):
        """A command on a grid whose checkout changed is refused at once."""
        calls, before = self.calls, self.attempts.read_bytes()
        with self.assertRaisesRegex(ValueError, "checkout changed while "
                                    "this grid ran.*dead"):
            self.go(argv)
        self.assertEqual((self.calls, self.attempts.read_bytes()),
                         (calls, before))

    def test_a_grid_whose_checkout_changed_is_dead_not_resumed_or_replayed(
            self):
        out = self.root / "grid"
        with self.changing_after(2):
            with self.assertRaises(tg.CheckoutChanged):
                self.first()
        self.assertIn("not the one recorded",
                      self.inventory(out)["checkout_changed"])
        self.assertEqual(self.closing(), [
            ("open", None), ("close", "checkout-changed")])
        self.dead(self.argv("run", out, "--candidate", CANDIDATE,
                            "--authorize-measurements", "--resume"))
        self.dead(self.replay_argv(out))
        self.dead(self.replay_argv(out, "--partial"))
        # The route is a new grid, and the ledger keeps both attempts.
        self.assertEqual(self.first("again")[1], 0)
        self.assertEqual(self.closing(), [
            ("open", None), ("close", "checkout-changed"),
            ("open", None), ("close", "pass")])
        self.assertEqual(self.go(self.replay_argv(self.root / "again"))[0],
                         0)

    def test_a_checkout_that_could_not_be_judged_at_the_end_is_not_dead(self):
        out = self.root / "grid"
        with self.changing_after(2, unjudged=True):
            with self.assertRaisesRegex(tg.CheckoutChanged,
                                        "not clean") as caught:
                self.first()
        # The attempt closes as changed, there is no decision and no mark.
        self.assertFalse(caught.exception.dead)
        self.assertFalse((out / "decisions.json").exists())
        self.assertNotIn("checkout_changed", self.inventory(out))
        self.assertEqual(self.closing(), [
            ("open", None), ("close", "checkout-changed")])
        # Neither a replay of the finished cells nor a resume is refused as
        # for a dead grid; the resume compares the record and goes on.
        self.assertEqual(self.go(self.replay_argv(out, "--partial"))[0], 2)
        calls = self.calls
        status, text = self.go(self.argv(
            "run", out, "--candidate", CANDIDATE, "--authorize-measurements",
            "--resume"))
        self.assertEqual((status, self.calls), (0, calls))
        self.assertTrue((out / "decisions.json").exists())
        self.assertEqual(self.closing(), [
            ("open", None), ("close", "checkout-changed"),
            ("resume", None), ("close", "pass")])

    def test_a_resume_after_an_unjudged_end_still_compares_the_record(self):
        out = self.root / "grid"
        with self.changing_after(2, unjudged=True):
            with self.assertRaises(tg.CheckoutChanged):
                self.first()
        # The checkout is clean again but is not the recorded one.
        def elsewhere(repo, commit=None, stamp=None):
            return dict(head=commit, tree_outside_performance="u" * 64,
                        products=PRODUCTS)
        with patch.object(tg, "checkout_identity", elsewhere):
            with self.assertRaisesRegex(ValueError, "different settings"):
                self.go(self.argv("run", out, "--candidate", CANDIDATE,
                                  "--authorize-measurements", "--resume"))
        self.assertFalse((out / "decisions.json").exists())

    def test_a_second_stage_whose_checkout_changed_is_dead_too(self):
        self.widen()
        grid, _, _ = self.first()
        with self.changing_after(2):
            with self.assertRaises(tg.CheckoutChanged):
                self.go(self.extend_argv(grid))
        ext = self.root / "ext"
        self.assertIn("checkout_changed", self.inventory(ext))
        self.dead(self.extend_argv(grid, "ext", "--resume"))
        self.dead(self.replay_argv(ext))
        # The first stage is still a grid (inconclusive: it was widened).
        self.assertEqual(self.go(self.replay_argv(grid))[0], 2)

    def test_an_unjudged_end_that_shows_a_difference_is_dead(self):
        out = self.root / "grid"
        with self.changing_after(2, unjudged=True), patch.object(
                tg, "known_difference",
                lambda repo, recorded: "tracked file(s) changed: M x"):
            with self.assertRaisesRegex(tg.CheckoutChanged,
                                        "tracked file") as caught:
                self.first()
        self.assertTrue(caught.exception.dead)
        self.assertIn("tracked file", self.inventory(out)["checkout_changed"])
        self.dead(self.argv("run", out, "--candidate", CANDIDATE,
                            "--authorize-measurements", "--resume"))

    def test_a_second_stage_with_an_unjudged_end_is_not_marked_and_resumes(
            self):
        self.widen()
        grid, _, _ = self.first()
        with self.changing_after(2, unjudged=True):
            with self.assertRaisesRegex(tg.CheckoutChanged,
                                        "not clean") as caught:
                self.go(self.extend_argv(grid))
        ext = self.root / "ext"
        self.assertFalse(caught.exception.dead)
        self.assertNotIn("checkout_changed", self.inventory(ext))
        self.assertFalse((ext / "decisions.json").exists())
        self.assertEqual(self.closing()[-2:], [
            ("open", None), ("close", "checkout-changed")])
        self.assertEqual(self.ledger()[-1]["stage"], "second")
        # Not dead: the resume measures what is left (here, nothing, for
        # the cells were done) and ends with decisions that replay.
        calls = self.calls
        self.assertEqual(self.go(self.extend_argv(grid, "ext",
                                                  "--resume"))[0], 0)
        self.assertEqual(self.calls, calls)
        self.assertTrue((ext / "decisions.json").exists())
        self.assertEqual(self.closing()[-2:], [
            ("resume", None), ("close", "pass")])
        status, text = self.go(self.replay_argv(ext))
        self.assertEqual(status, 0, text)

    def test_a_second_stage_compares_the_checkout_before_the_first_replay(
            self):
        self.widen()
        grid, _, _ = self.first()

        def other_tree(repo, commit=None, stamp=None):
            return dict(head=commit, tree_outside_performance="u" * 64)

        def replayed(*args, **kw):
            raise AssertionError("the first stage was replayed first")
        with patch.object(tg, "checkout_identity", other_tree), \
                patch.object(self.grid, "replay_grid", replayed):
            with self.assertRaisesRegex(ValueError, "not the one the first"):
                self.go(self.extend_argv(grid, "again"))

    def test_replay_sees_a_checkout_that_is_not_the_recorded_one(self):
        out, _, _ = self.first()
        path = out / "inventory.json"
        recorded = json.loads(path.read_text())
        good = recorded["checkout"]
        for label, value in (
                ("head", dict(good, head="e" * 40)),
                ("tree", dict(good, tree_outside_performance="u" * 64)),
                ("keys", dict(good, extra=1)),
                ("products", dict(good, products="short")),
                ("products type", dict(good, products=1)),
                ("none", None)):
            with self.subTest(label):
                changed = dict(recorded, checkout=value)
                if value is None:
                    del changed["checkout"]
                path.write_text(json.dumps(changed))
                with self.assertRaisesRegex(ValueError, "changed checkout"):
                    self.go(self.replay_argv(out))
        # The tree of the candidate as git gives it now is the record.
        path.write_text(json.dumps(recorded))
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)
        with patch.object(tg, "git_tree_outside",
                          lambda repo, rev: "u" * 64):
            with self.assertRaisesRegex(ValueError, "changed checkout"):
                self.go(self.replay_argv(out))

    def test_a_second_stage_sees_a_checkout_that_is_not_the_recorded_one(
            self):
        self.widen()
        grid, _, _ = self.first()
        path = grid / "inventory.json"
        recorded = json.loads(path.read_text())
        path.write_text(json.dumps(dict(recorded, checkout=dict(
            recorded["checkout"], head="e" * 40))))
        calls = self.calls
        with self.assertRaisesRegex(ValueError, "changed checkout"):
            self.go(self.extend_argv(grid))
        self.assertEqual(self.calls, calls)

    # The commit is kept ------------------------------------------------

    def test_the_measured_commit_is_kept_by_a_ref(self):
        self.widen()
        grid, _, _ = self.first()
        self.assertEqual(self.kept, [("toy", CANDIDATE)])
        self.go(self.extend_argv(grid))
        self.assertEqual(self.kept, [("toy", CANDIDATE)] * 2)

    def test_nothing_is_kept_for_a_run_that_is_refused(self):
        self.differ = {"src/one.sml"}
        with self.assertRaisesRegex(ValueError, "cannot pass"):
            self.first()
        self.assertEqual(self.kept, [])

    # A source that cannot pass -----------------------------------------

    def test_a_differing_source_without_a_pin_is_refused_before_measuring(
            self):
        self.differ = {"src/one.sml"}
        with self.assertRaisesRegex(ValueError, "1 source file.*cannot "
                                    "pass: src/one.sml"):
            self.first()
        self.nothing_written()

    def test_a_stale_pin_is_refused_the_same_way(self):
        self.differ = {"src/two.sml"}
        self.table.pinned = {"src/two.sml": dict(
            blob="e" * 40, reason="Reviewed before the last change.")}
        with self.assertRaisesRegex(ValueError, "cannot pass: src/two.sml"):
            self.first()
        self.nothing_written()

    def test_a_pinned_difference_is_measured(self):
        self.differ = {"src/two.sml"}
        self.table.pinned = {"src/two.sml": dict(
            blob="f" * 40, reason="A reviewed change of two.")}
        out, status, _ = self.first()
        self.assertEqual(status, 0)
        self.assertNotIn("diagnostic", self.inventory(out))

    def test_a_diagnostic_subset_may_measure_it_and_is_never_a_grid(self):
        self.differ = {"src/one.sml"}
        out, status, text = self.first(extra=self.only(CASES[0]))
        self.assertEqual(status, 2)
        self.assertIn("SOURCE-DIFFERS src/one.sml", text)
        self.assertTrue(self.inventory(out)["diagnostic"])
        self.assertFalse((out / "decisions.json").exists())
        self.assertEqual([x.get("status") for x in self.ledger()
                          if x["event"] == "close"], ["partial"])
        # A resumption without --only would be the whole grid: refused.
        with self.assertRaisesRegex(ValueError, "cannot pass"):
            self.go(self.argv("run", out, "--candidate", CANDIDATE,
                              "--resume", "--authorize-measurements"))

    def test_a_cell_named_twice_or_not_in_the_grid_is_refused(self):
        for only, message in (
                (self.only(CASES[0], CASES[0]), "repeated --only cell"),
                (("--only", "no_such-0"), "unknown --only cell")):
            with self.assertRaisesRegex(ValueError, message):
                self.first(extra=only)
        self.nothing_written()


class ChainRig(Rig):
    """A real repository, with git, the checkout, the build stamp and the
    ledger as they are, and only the build and the measurement faked."""

    def git(self, *args):
        return subprocess.run(
            ["git", "-C", str(self.repo), "-c", "user.name=t", "-c",
             "user.email=t@example.org", *args], check=True, text=True,
            stdout=subprocess.PIPE).stdout.strip()

    def git_stand_ins(self):
        return ()

    def make_table(self, **kw):
        """The repository as it is at X: the sources, and the products a
        build leaves, which git ignores."""
        if not hasattr(self, "base"):
            perf = self.repo / "src" / "simp" / "tests" / "performance"
            perf.mkdir(parents=True)
            (perf / "p.sml").write_text("val p = 1\n")
            # As the project's, the counts file is in the performance area.
            self.counts = perf / "toy_iterations.json"
            for name in ("one", "two"):
                (self.repo / "src" / (name + ".sml")).write_text(
                    "val %s = 1\n" % name)
            (self.repo / ".gitignore").write_text(
                "bin/\nsigobj/\ntools/Holmake/Systeml.sml\n.hol\n")
            (self.repo / ".git" / "info" / "exclude").write_text(
                ".agent-files\n")
            self.git("add", "-A")
            self.git("commit", "-q", "-m", "X")
            self.base = self.git("rev-parse", "HEAD")
            (self.repo / "bin").mkdir()
            (self.repo / "bin" / "hol").write_text("executable")
            (self.repo / "bin" / "hol.state0").write_text("heap")
            (self.repo / "bin" / "Holmake").write_text("holmake")
            (self.repo / "sigobj").mkdir()
            (self.repo / "sigobj" / "m.uo").write_text("object")
            (self.repo / "src" / ".hol" / "objs").mkdir(parents=True)
            self.theory = self.repo / "src" / ".hol" / "objs" / "t.dat"
            self.theory.write_text("data")
            self.pilot_revision = self.base
        kw.setdefault("baseline", self.base)
        kw.setdefault("ledger", None)
        return super().make_table(**kw)

    def configure(self, holdir=None):
        """What configure leaves: the HOLDIR of the checkout, in a file git
        ignores."""
        where = self.repo / "tools" / "Holmake"
        where.mkdir(parents=True, exist_ok=True)
        (where / "Systeml.sml").write_text('val HOLDIR = "%s"\n' % (
            self.repo.resolve() if holdir is None else holdir))

    def launch_head(self):
        return self.git("rev-parse", "HEAD")

    def fake_launch(self, command, output, fds, timeout, stdin=None,
                    append=False):
        """Configure, the build, or a pilot process. Configure reads its
        standard input, the file. The build reads its standard input (as
        bin/build does after its stale-executable warning), so that with a
        reader that never answers it is killed at the timeout."""
        if "bin/build" not in command and "poly" not in command:
            return super().fake_launch(command, output, fds, timeout)
        kind = "build" if "bin/build" in command else "configure"
        self.steps.append(dict(
            kind=kind, command=command, output=output, fds=fds,
            timeout=timeout, stdin=stdin, append=append))
        # As run_logged does: a new file, or the end of the one before.
        with Path(output).open("a" if append else "x") as stream:
            stream.write(self.build_log if kind == "build"
                         else self.configure_log)
        if kind == "configure":
            self.configure_actions()
            return dict(exit=self.configure_exit, timed_out=False)
        self.built.append(self.steps[-1])
        if stdin is None:
            return dict(exit=-9, timed_out=True)
        self.build()
        return dict(exit=self.build_exit, timed_out=False)

    def configure_actions(self):
        """What configure does to the checkout: it leaves the HOLDIR, and
        it relinks bin/hol, which is never the same bytes twice (the real
        one gave three digests for three runs at one commit)."""
        self.configure()
        self.configured += 1
        (self.repo / "bin" / "hol").write_text(
            "executable %d" % self.configured)

    def build(self):
        """What the build does to the checkout (nothing)."""

    def provision(self):
        self.steps, self.built, self.build_exit = [], [], 0
        self.configured = 0
        self.configure_exit = 0
        self.configure_log = "configure log\n%s\n" % tg.FINISHED
        self.build_log = "build log\n"
        self.assertEqual(self.go(["prepare", "--repo", str(self.repo)])[0],
                         0)
        self.make_pilot(self.pilot_dir)
        code, _ = self.go(["predeclare", "--grid", str(self.pilot_dir),
                           "--output", str(self.counts)])
        self.assertEqual(code, 0)
        self.launched.clear()
        self.analyses.clear()

    def prepare(self):
        return self.go(["prepare", "--repo", str(self.repo)])

    def attempts_path(self):
        return (self.repo / ".agent-files" / "evidence" / self.table.name /
                "attempts.jsonl")

    def ledger_lines(self):
        return [json.loads(line) for line in
                self.attempts_path().read_text().splitlines()]

    def stamp(self):
        return (self.repo / ".agent-files" / "evidence" / "toy" /
                "build-stamp.json")

    def commit_counts(self):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "Y: the counts")
        self.candidate_commit = self.git("rev-parse", "HEAD")
        return self.candidate_commit

    def commit_file(self, path, text, name="Z"):
        (self.repo / path).write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", name)
        return self.git("rev-parse", "HEAD")

    def run_at(self, commit, name="grid", *extra):
        return self.go(self.argv("run", self.root / name, "--candidate",
                                 commit, "--authorize-measurements",
                                 *extra))

    def acting_at(self, call, action):
        """The measurement of cell number `call` finds the worktree changed
        by `action`."""
        real = self.fake_run

        def run(options):
            report = real(options)
            if self.calls == call:
                action()
            return report
        return patch.object(a, "run", run)

    def resume(self, y, name="grid"):
        return self.run_at(y, name, "--resume")

    def failing_after(self, call, action=lambda: None, error=None):
        """Cell number `call` does `action` and then raises `error`."""
        real = self.fake_run

        def run(options):
            if self.calls + 1 == call:
                action()
                self.calls += 1
                raise error or RuntimeError("infrastructure failure")
            return real(options)
        return patch.object(a, "run", run)

    def edit_one(self):
        (self.repo / "src" / "one.sml").write_text("val one = 7\n")

    def undo_one(self):
        self.git("checkout", "--", "src/one.sml")

    def statuses(self):
        return [(x["event"], x.get("status")) for x in self.ledger_lines()]

    def fail_the_mark(self, error=None):
        """The mark of the end cannot be written."""
        def mark(root, inventory, found):
            raise error or OSError("disk full")
        return patch.object(self.grid, "mark_end", mark)

    def found_not_marked(self, y, name="grid", edit=None):
        """P3: an edit after cell 3, cell 5 raises, and the mark of the
        difference found at the stop cannot be written."""
        self.explode_at = self.calls + 5
        with self.acting_at(self.calls + 3, edit or self.edit_one):
            with self.fail_the_mark():
                with self.assertRaises(RuntimeError) as caught:
                    self.run_at(y, name)
        self.explode_at = None
        self.assertEqual(str(caught.exception), "infrastructure failure")
        return self.ledger_lines()[-1]


class Chain(ChainRig):
    """The operator's whole sequence: prepare and pilot at X, predeclare,
    the counts committed as Y, run, extend and replay of both stages."""

    def test_prepare_pilot_predeclare_commit_run_extend_and_replay(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)
        pilot = self.inventory(self.pilot_dir)
        self.assertEqual(pilot["checkout"]["head"], self.base)
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot_dir)])[0], 0)
        y = self.commit_counts()
        self.assertEqual(self.go(["verify-counts", "--grid",
                                  str(self.pilot_dir)])[0], 0)
        # The control leaves one cell open, which the second stage settles.
        # No second prepare: the commit touched only the performance area.
        status, text = self.run_at(y)
        self.assertEqual(status, 2, text)
        grid, ext = self.root / "grid", self.root / "ext"
        first = self.inventory(grid)
        self.assertEqual((first["candidate"], first["counts_commit"],
                          first["checkout"]["head"]),
                         (y, y, y))
        status, text = self.go(self.argv(
            "extend", ext, "--grid", str(grid), "--authorize-measurements"))
        self.assertEqual(status, 0, text)
        for stage, expected in ((grid, 2), (ext, 0)):
            status, text = self.go(self.replay_argv(stage))
            self.assertEqual(status, expected, text)
        self.assertIn("ATTEMPTS of TOY: 2 in the ledger, 2 of this "
                      "candidate %s" % y, text)
        self.assertEqual(self.git("rev-parse", "refs/performance/toy/" + y),
                         y)
        where = self.repo / ".agent-files" / "evidence" / "toy"
        self.assertEqual(
            [(x["stage"], x["event"]) for x in map(json.loads, (
                where / "attempts.jsonl").read_text().splitlines())],
            [("first", "open"), ("first", "close"), ("second", "open"),
             ("second", "close")])
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_a_checkout_that_is_not_the_candidate_is_refused(self):
        y = self.commit_counts()
        (self.repo / "note.txt").write_text("later\n")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "Z")
        with self.assertRaisesRegex(ValueError, "not at the commit"):
            self.run_at(y)
        self.assertEqual(self.calls, 0)
        self.assertFalse((self.root / "grid").exists())

    def test_an_edited_checkout_is_refused(self):
        y = self.commit_counts()
        (self.repo / "src" / "one.sml").write_text("val one = 2\n")
        with self.assertRaisesRegex(ValueError, "not clean"):
            self.run_at(y)
        self.assertEqual(self.calls, 0)

    def test_an_edited_product_is_refused_until_prepare_is_run(self):
        y = self.commit_counts()
        (self.repo / "bin" / "hol.state0").write_text("another heap")
        with self.assertRaisesRegex(ValueError, "run prepare at this "
                                    "commit"):
            self.run_at(y)
        self.assertEqual(self.calls, 0)
        self.assertEqual(self.prepare()[0], 0)
        self.assertEqual(self.run_at(y)[0], 0)

    def test_a_source_change_outside_the_performance_area_needs_prepare(self):
        self.commit_counts()
        z = self.commit_file("src/three.sml", "val three = 1\n")
        with self.assertRaisesRegex(ValueError, "run prepare at this "
                                    "commit"):
            self.run_at(z)
        self.assertEqual(self.calls, 0)
        self.assertEqual(self.prepare()[0], 0)
        self.assertEqual(self.run_at(z)[0], 0)

    def test_a_touched_heap_and_a_round_trip_pass(self):
        y = self.commit_counts()
        os.utime(self.repo / "bin" / "hol.state0", (4e9, 4e9))
        main = self.git("rev-parse", "--abbrev-ref", "HEAD")
        self.git("checkout", "-q", "-b", "side", self.base)
        self.git("checkout", "-q", main)
        self.assertEqual(self.run_at(y)[0], 0)

    def test_the_counts_commit_needs_no_second_prepare(self):
        # The stamp of X is the stamp of Y: the performance area is left out
        # of the tree it binds.
        before = json.loads(self.stamp().read_text())
        y = self.commit_counts()
        self.assertEqual(self.run_at(y)[0], 0)
        self.assertEqual(json.loads(self.stamp().read_text()), before)

    def test_a_counts_file_committed_twice_is_refused(self):
        self.commit_counts()
        self.counts.write_text(self.counts.read_text() + "\n")
        self.git("commit", "-q", "-a", "-m", "again")
        with self.assertRaisesRegex(ValueError, "exactly one commit"):
            self.run_at(self.git("rev-parse", "HEAD"))
        self.assertEqual(self.calls, 0)

    # prepare ------------------------------------------------------------

    def changing_heap(self, call):
        """The measurement of cell number `call` finds the heap replaced
        (a build made in the window, an edit): the checkout, as git sees it,
        is clean and unchanged."""
        real = self.fake_run

        def run(options):
            report = real(options)
            if self.calls == call:
                (self.repo / "bin" / "hol.state0").write_text("another")
            return report
        return patch.object(a, "run", run)

    def test_an_output_inside_the_repository_must_be_ignored_by_git(self):
        y = self.commit_counts()
        loose = self.repo / "grids" / "grid"
        ignored = self.repo / ".agent-files" / "evidence" / "toy" / "grid"
        for action, extra in (("pilot", ()), ("run", ("--candidate", y))):
            with self.subTest(action):
                with self.assertRaisesRegex(ValueError, "inside the "
                                            "repository and not ignored.*"
                                            "put it below .*evidence.toy"):
                    self.go(self.argv(action, loose,
                                      "--authorize-measurements", *extra))
                self.assertFalse(loose.exists())
        self.assertEqual((self.calls, self.launched), (0, []))
        self.assertEqual(self.run_at(y)[0], 0)
        with self.assertRaisesRegex(ValueError, "not ignored"):
            self.go(self.argv("extend", loose, "--grid",
                              str(self.root / "grid"),
                              "--authorize-measurements"))
        self.assertFalse(loose.exists())
        # Below the ignored directory it is accepted, and leaves the
        # checkout clean for the end of the measurement.
        self.assertEqual(self.go(self.argv(
            "run", ignored, "--candidate", y,
            "--authorize-measurements"))[0], 0)
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_a_restamp_cannot_make_a_dead_grid_pass(self):
        y = self.commit_counts()
        with self.changing_heap(5):
            with self.assertRaises(tg.CheckoutChanged):
                self.run_at(y)
        out = self.root / "grid"
        self.assertFalse((out / "decisions.json").exists())
        self.assertIn("checkout_changed", self.inventory(out))
        self.assertEqual(self.prepare()[0], 0)
        calls = self.calls
        with self.assertRaisesRegex(ValueError, "checkout changed while "
                                    "this grid ran"):
            self.run_at(y, "grid", "--resume")
        with self.assertRaisesRegex(ValueError, "checkout changed while "
                                    "this grid ran"):
            self.go(self.replay_argv(out))
        self.assertEqual(self.calls, calls)
        self.assertEqual(
            [(x["event"], x.get("status")) for x in self.ledger_lines()],
            [("open", None), ("close", "checkout-changed")])
        # The route is a new grid, of the products that are there now.
        self.assertEqual(self.run_at(y, "new")[0], 0)
        self.assertNotEqual(self.inventory(out)["checkout"]["products"],
                            self.inventory(self.root / "new")[
                                "checkout"]["products"])

    def test_a_stray_file_at_the_end_does_not_kill_the_grid(self):
        y = self.commit_counts()
        stray = self.repo / "notes.txt"
        with self.acting_at(5, lambda: stray.write_text("x")):
            with self.assertRaisesRegex(tg.CheckoutChanged, "not clean"):
                self.run_at(y)
        out = self.root / "grid"
        self.assertFalse((out / "decisions.json").exists())
        self.assertNotIn("checkout_changed", self.inventory(out))
        self.assertEqual(
            [(x["event"], x.get("status")) for x in self.ledger_lines()],
            [("open", None), ("close", "checkout-changed")])
        stray.unlink()
        calls = self.calls
        status, text = self.resume(y)
        self.assertEqual((status, self.calls), (0, calls), text)
        self.assertEqual(
            [(x["event"], x.get("status")) for x in self.ledger_lines()],
            [("open", None), ("close", "checkout-changed"),
             ("resume", None), ("close", "pass")])
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0, text)
        self.assertIn("status checkout-changed,pass", text)

    def test_a_stamp_missing_at_the_end_does_not_kill_the_grid(self):
        y = self.commit_counts()
        saved = self.stamp().read_bytes()
        with self.acting_at(5, self.stamp().unlink):
            with self.assertRaisesRegex(tg.CheckoutChanged,
                                        "no build stamp"):
                self.run_at(y)
        out = self.root / "grid"
        self.assertNotIn("checkout_changed", self.inventory(out))
        self.stamp().write_bytes(saved)
        self.assertEqual(self.resume(y)[0], 0)

    def dead_resume(self, y, name="grid"):
        """A resume of a grid whose checkout was found to differ."""
        calls = self.calls
        with self.assertRaisesRegex(ValueError, "checkout changed while "
                                    "this grid ran.*dead"):
            self.resume(y, name)
        self.assertEqual(self.calls, calls)

    def test_an_unclean_end_with_other_products_is_dead(self):
        # The products digest needs neither a clean tree nor the stamp: a
        # stray file does not hide that the products are not the recorded
        # ones, and no prepare undoes it.
        y = self.commit_counts()
        stray = self.repo / "notes.txt"

        def both():
            stray.write_text("x")
            (self.repo / "bin" / "hol.state0").write_text("another")
        with self.acting_at(5, both):
            with self.assertRaisesRegex(tg.CheckoutChanged,
                                        "not the recorded ones"):
                self.run_at(y)
        out = self.root / "grid"
        self.assertIn("checkout_changed", self.inventory(out))
        stray.unlink()
        # The binding refuses first, in the words of a resumption.
        with self.assertRaisesRegex(ValueError, "differ from the stamped "
                                    "build: this grid goes on only"):
            self.resume(y)
        self.assertEqual(self.prepare()[0], 0)
        self.dead_resume(y)
        self.assertFalse((out / "decisions.json").exists())

    def test_a_missing_stamp_does_not_hide_other_products_or_a_tracked_edit(
            self):
        y = self.commit_counts()
        for label, action, undo in (
                ("products",
                 lambda: (self.repo / "bin" / "hol.state0").write_text("x"),
                 lambda: (self.repo / "bin" / "hol.state0").write_text(
                     "heap")),
                ("tracked file",
                 lambda: (self.repo / "src" / "one.sml").write_text("x\n"),
                 lambda: self.git("checkout", "--", "src/one.sml"))):
            with self.subTest(label):
                saved = self.stamp().read_bytes()
                name = "grid-" + label.replace(" ", "-")

                def both():
                    self.stamp().unlink()
                    action()
                with self.acting_at(self.calls + 5, both):
                    with self.assertRaises(tg.CheckoutChanged):
                        self.run_at(y, name)
                self.assertIn("checkout_changed",
                              self.inventory(self.root / name))
                undo()
                self.stamp().write_bytes(saved)
                self.dead_resume(y, name)

    def test_a_tracked_edit_at_the_end_kills_the_grid_though_it_is_undone(
            self):
        # An edit seen at the end, then undone, and then a resume that
        # would find the recorded tree: it is not a stray file, it is a
        # tree other than the recorded one, a documentation file included.
        y = self.commit_counts()
        perf = self.repo / "src" / "simp" / "tests" / "performance"
        for label, path, edit in (
                ("source", self.repo / "src" / "one.sml",
                 lambda path: path.write_text("val one = 7\n")),
                ("performance area", perf / "p.sml",
                 lambda path: path.write_text("val p = 7\n")),
                ("removed", self.repo / "src" / "two.sml",
                 lambda path: path.unlink()),
                ("staged", self.repo / "src" / "one.sml",
                 lambda path: (path.write_text("val one = 8\n"),
                               self.git("add", "src/one.sml")))):
            with self.subTest(label):
                name = "grid-" + label.replace(" ", "-")
                with self.acting_at(self.calls + 5, lambda: edit(path)):
                    with self.assertRaisesRegex(tg.CheckoutChanged,
                                                "tracked file"):
                        self.run_at(y, name)
                out = self.root / name
                self.assertIn("checkout_changed", self.inventory(out))
                self.assertFalse((out / "decisions.json").exists())
                self.git("checkout", "HEAD", "--", str(
                    path.relative_to(self.repo)))
                self.assertEqual(self.git("status", "--porcelain"), "")
                self.dead_resume(y, name)
                calls = self.calls
                with self.assertRaisesRegex(ValueError, "checkout changed "
                                            "while this grid ran"):
                    self.go(self.replay_argv(out))
                self.assertEqual(self.calls, calls)
                self.assertEqual(
                    self.ledger_lines()[-1]["status"], "checkout-changed")

    def test_a_head_that_moved_under_a_stray_file_is_dead(self):
        # The head is judged before the tree is looked at, so a tree that
        # is not clean does not make a moved head merely unjudged.
        y = self.commit_counts()
        stray = self.repo / "notes.txt"

        def moves():
            self.commit_file("src/three.sml", "val three = 1\n", "moved")
            stray.write_text("x")
        with self.acting_at(5, moves):
            with self.assertRaisesRegex(tg.CheckoutChanged,
                                        "not at the commit measured") as c:
                self.run_at(y)
        self.assertTrue(c.exception.dead)
        self.assertIn("checkout_changed", self.inventory(self.root / "grid"))
        stray.unlink()
        self.git("checkout", "-q", y)
        self.dead_resume(y)

    def test_a_pilot_ends_dead_on_a_tracked_edit_and_unjudged_on_a_stray(
            self):
        self.commit_counts()
        real = self.fake_launch
        file = self.repo / "src" / "one.sml"
        stray = self.repo / "notes.txt"
        for label, path in (("tracked", file), ("stray", stray)):
            with self.subTest(label):
                name = "pilot-" + label
                before = len(self.launched)

                def launching(command, output, fds, timeout, stdin=None,
                              append=False, path=path):
                    found = real(command, output, fds, timeout, stdin,
                                 append)
                    if "--performance-case" in command and len(
                            self.launched) == before + 12:
                        path.write_text("changed\n")
                    return found
                argv = self.argv("pilot", self.root / name,
                                 "--authorize-measurements")
                with patch.object(a, "run_logged", launching):
                    with self.assertRaises(tg.CheckoutChanged):
                        self.go(argv)
                recorded = self.inventory(self.root / name)
                if label == "tracked":
                    self.assertIn("checkout_changed", recorded)
                    self.assertNotIn("unjudged_ends", recorded)
                    self.git("checkout", "--", "src/one.sml")
                    with self.assertRaisesRegex(ValueError, "different "
                                                "settings"):
                        self.go(argv + ["--resume"])
                else:
                    self.assertIn("checkout_unjudged", recorded)
                    self.assertEqual(len(recorded["unjudged_ends"]), 1)
                    stray.unlink()
                    self.assertEqual(self.go(argv + ["--resume"])[0], 0)
                    resumed = self.inventory(self.root / name)
                    self.assertNotIn("checkout_unjudged", resumed)
                    self.assertEqual(resumed["unjudged_ends"],
                                     recorded["unjudged_ends"])

    # The end of an attempt that stops early -----------------------------

    def test_an_edit_before_an_early_stop_kills_the_grid(self):
        # P1: the edit is made after cell 3, and cell 5 raises. The end of
        # the attempt is judged though the measuring never finished.
        y = self.commit_counts()
        self.explode_at = 5
        try:
            with self.acting_at(3, self.edit_one):
                self.run_at(y)
        except RuntimeError as error:
            # The error of the stop is the one that propagates, with its
            # own traceback.
            self.assertEqual(str(error), "infrastructure failure")
            self.assertIn("fake_run", [f.name for f in traceback.extract_tb(
                error.__traceback__)])
        else:
            self.fail("the stop was swallowed")
        out = self.root / "grid"
        self.assertIn("tracked file", self.inventory(out)["checkout_changed"])
        self.assertEqual(self.statuses(),
                         [("open", None), ("close", "checkout-changed")])
        self.undo_one()
        self.explode_at = None
        self.dead_resume(y)
        self.assertEqual(self.statuses()[-1], ("close", "checkout-changed"))

    def test_a_second_stage_that_stops_early_is_judged_too(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)
        y = self.commit_counts()
        self.assertEqual(self.run_at(y)[0], 2)
        argv = self.argv("extend", self.root / "ext", "--grid",
                         str(self.root / "grid"), "--authorize-measurements")
        with self.failing_after(self.calls + 1, self.edit_one):
            with self.assertRaises(RuntimeError):
                self.go(argv)
        self.assertIn("checkout_changed", self.inventory(self.root / "ext"))
        self.assertEqual(self.statuses()[-2:],
                         [("open", None), ("close", "checkout-changed")])
        self.undo_one()
        calls = self.calls
        with self.assertRaisesRegex(ValueError, "checkout changed while "
                                    "this grid ran.*dead"):
            self.go(argv + ["--resume"])
        self.assertEqual(self.calls, calls)
        with self.subTest("judgement"):
            real, seen = tg.Grid.recheck, []

            def recheck(this, repo, commit, inventory):
                seen.append(1)
                if len(seen) > 1:
                    raise OSError("git went away")
                return real(this, repo, commit, inventory)
            again = self.argv("extend", self.root / "ext2", "--grid",
                              str(self.root / "grid"),
                              "--authorize-measurements")
            with self.failing_after(self.calls + 1):
                with patch.object(tg.Grid, "recheck", recheck):
                    with self.assertRaises(RuntimeError):
                        self.go(again)
            line = self.ledger_lines()[-1]
            self.assertEqual((line["stage"], line["status"]),
                             ("second", "interrupted"))
            self.assertEqual(line["judgement"],
                             "not made: OSError: git went away")
            self.assertNotIn("checkout_changed",
                             self.inventory(self.root / "ext2"))

    def pilot_stopping(self, name, action, before=4, error=RuntimeError):
        """A pilot whose fifth process does `action` and then raises."""
        real = self.fake_launch
        started = len(self.launched)

        def launching(command, output, fds, timeout, stdin=None,
                      append=False):
            if "--performance-case" in command and len(
                    self.launched) == started + before:
                action()
                raise RuntimeError("infrastructure failure")
            return real(command, output, fds, timeout, stdin, append)
        argv = self.argv("pilot", self.root / name,
                         "--authorize-measurements")
        with patch.object(a, "run_logged", launching):
            with self.assertRaises(error):
                self.go(argv)
        return argv

    def test_a_pilot_keeps_what_its_judgement_could_not_write(self):
        self.commit_counts()
        real, seen = tg.Grid.recheck, []

        def recheck(this, repo, commit, inventory):
            seen.append(1)
            if len(seen) > 1:
                raise OSError("git went away")
            return real(this, repo, commit, inventory)
        # P2: the checkout cannot be asked at the stop. A pilot has no
        # ledger, so its inventory must say that the end was not judged.
        with patch.object(tg.Grid, "recheck", recheck):
            argv = self.pilot_stopping("unjudged", lambda: None)
        recorded = self.inventory(self.root / "unjudged")
        text = "not made: OSError: git went away"
        self.assertEqual(recorded["checkout_unjudged"], text)
        self.assertEqual(recorded["unjudged_ends"], [text])
        self.assertNotIn("checkout_changed", recorded)
        with self.assertRaisesRegex(ValueError, "could not be judged.*"
                                    "resume it"):
            self.go(["predeclare", "--grid", str(self.root / "unjudged"),
                     "--output", str(self.root / "c.json")])
        self.assertEqual(self.go(argv + ["--resume"])[0], 0)
        resumed = self.inventory(self.root / "unjudged")
        self.assertNotIn("checkout_unjudged", resumed)
        self.assertEqual(resumed["unjudged_ends"], [text])
        self.assertEqual(self.go(["predeclare", "--grid",
                                  str(self.root / "unjudged"), "--output",
                                  str(self.root / "c.json")])[0], 0)
        # A difference found and not marked is dead in the inventory.
        with self.fail_the_mark():
            self.pilot_stopping("found", self.edit_one)
        recorded = self.inventory(self.root / "found")
        self.assertRegex(recorded["checkout_changed"], "tracked file.*; not "
                         "marked: OSError: disk full$")
        self.assertNotIn("checkout_unjudged", recorded)
        with self.assertRaisesRegex(ValueError, "changed while the pilot "
                                    "ran"):
            self.go(["predeclare", "--grid", str(self.root / "found"),
                     "--output", str(self.root / "d.json")])
        self.undo_one()
        # Nothing is known to differ (a stray file) and the mark of the
        # unjudged end cannot be written: the judgement was not made.
        stray = self.repo / "notes.txt"
        with self.fail_the_mark():
            self.pilot_stopping("stray", lambda: stray.write_text("x"))
        recorded = self.inventory(self.root / "stray")
        self.assertEqual(recorded["checkout_unjudged"],
                         "not made: OSError: disk full")
        self.assertNotIn("checkout_changed", recorded)
        stray.unlink()

    def test_a_pilot_whose_last_checkpoint_fails_shows_that_error(self):
        self.commit_counts()
        real, seen = tg.Grid.recheck, []

        def recheck(this, repo, commit, inventory):
            seen.append(1)
            if len(seen) > 1:
                raise OSError("git went away")
            return real(this, repo, commit, inventory)
        written = tg.checkpoint

        def checkpoint(path, value):
            if "checkout_unjudged" in value:
                raise OSError("disk full")
            return written(path, value)
        with patch.object(tg.Grid, "recheck", recheck), \
                patch.object(tg, "checkpoint", checkpoint):
            # The error of the checkpoint replaces the stop's.
            self.pilot_stopping("full", lambda: None, error=OSError)
        self.assertNotIn("checkout_unjudged",
                         self.inventory(self.root / "full"))

    def test_a_pilot_that_stops_early_is_judged_too(self):
        self.commit_counts()
        argv = self.pilot_stopping("dead", self.edit_one)
        recorded = self.inventory(self.root / "dead")
        self.assertIn("checkout_changed", recorded)
        self.assertEqual(len(recorded["runs"]), 4)
        self.undo_one()
        with self.assertRaisesRegex(ValueError, "different settings"):
            self.go(argv + ["--resume"])
        # A stray file is not judged: no dead mark, and the pilot resumes.
        stray = self.repo / "notes.txt"
        argv = self.pilot_stopping(
            "stray", lambda: stray.write_text("x"))
        recorded = self.inventory(self.root / "stray")
        self.assertNotIn("checkout_changed", recorded)
        self.assertIn("checkout_unjudged", recorded)
        self.assertEqual(len(recorded["unjudged_ends"]), 1)
        stray.unlink()
        self.assertEqual(self.go(argv + ["--resume"])[0], 0)
        self.assertEqual(len(self.inventory(
            self.root / "stray")["unjudged_ends"]), 1)
        # A clean stop is marked with nothing, and resumes.
        argv = self.pilot_stopping("clean", lambda: None)
        recorded = self.inventory(self.root / "clean")
        for key in ("checkout_changed", "checkout_unjudged",
                    "unjudged_ends"):
            self.assertNotIn(key, recorded)
        self.assertEqual(self.go(argv + ["--resume"])[0], 0)

    def test_a_stray_file_before_an_early_stop_leaves_the_grid_alive(self):
        y = self.commit_counts()
        stray = self.repo / "notes.txt"
        self.explode_at = 5
        with self.acting_at(3, lambda: stray.write_text("x")):
            with self.assertRaises(RuntimeError):
                self.run_at(y)
        out = self.root / "grid"
        self.assertNotIn("checkout_changed", self.inventory(out))
        # The same close as an unjudged end after the last cell.
        self.assertEqual(self.statuses(),
                         [("open", None), ("close", "checkout-changed")])
        stray.unlink()
        self.explode_at = None
        status, text = self.resume(y)
        self.assertEqual(status, 0, text)
        self.assertEqual(self.statuses()[-2:],
                         [("resume", None), ("close", "pass")])

    def test_a_clean_early_stop_stays_interrupted_and_resumes(self):
        y = self.commit_counts()
        self.explode_at = 5
        with self.assertRaises(RuntimeError):
            self.run_at(y)
        self.assertNotIn("checkout_changed",
                         self.inventory(self.root / "grid"))
        line = self.ledger_lines()[-1]
        self.assertEqual((line["event"], line["status"]),
                         ("close", "interrupted"))
        self.assertNotIn("judgement", line)
        self.explode_at = None
        self.assertEqual(self.resume(y)[0], 0)

    def test_an_interrupt_propagates_with_the_checkout_judged(self):
        y = self.commit_counts()
        with self.failing_after(5, self.edit_one, KeyboardInterrupt()):
            with self.assertRaises(KeyboardInterrupt):
                self.run_at(y)
        self.assertIn("checkout_changed", self.inventory(self.root / "grid"))
        self.assertEqual(self.statuses()[-1], ("close", "checkout-changed"))

    def test_a_judgement_that_fails_masks_nothing_and_marks_nothing(self):
        y = self.commit_counts()
        real = tg.Grid.recheck
        for label, error, step in (
                ("recheck", OSError("git went away"), "recheck"),
                ("second interrupt", KeyboardInterrupt(), "recheck")):
            with self.subTest(label):
                name = "grid-" + label.replace(" ", "-")
                seen = []

                def recheck(this, repo, commit, inventory):
                    # The first, under the lock, is the real one.
                    seen.append(1)
                    if len(seen) > 1:
                        raise error
                    return real(this, repo, commit, inventory)

                def mark(root, inventory, found):
                    raise error
                # An edit that the judgement would have found.
                with self.failing_after(self.calls + 5, self.edit_one):
                    with patch.object(tg.Grid, "recheck", recheck):
                        with self.assertRaises(RuntimeError) as caught:
                            self.run_at(y, name)
                self.assertEqual(str(caught.exception),
                                 "infrastructure failure")
                self.assertNotIn("checkout_changed",
                                 self.inventory(self.root / name))
                line = self.ledger_lines()[-1]
                self.assertEqual((line["event"], line["status"]),
                                 ("close", "interrupted"))
                self.assertIn("not made: " + type(error).__name__,
                              line["judgement"])
                self.assertNotIn("found", line)
                self.undo_one()
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_a_difference_found_and_not_marked_is_in_the_close(self):
        # P3: the judgement was made and its answer is "known to differ".
        y = self.commit_counts()
        line = self.found_not_marked(y)
        self.assertEqual((line["event"], line["status"]),
                         ("close", "checkout-changed"))
        self.assertNotIn("judgement", line)
        self.assertRegex(line["found"], "tracked file.*; not marked: "
                         "OSError: disk full$")
        self.assertNotIn("checkout_changed",
                         self.inventory(self.root / "grid"))
        found = tg.Ledger(self.attempts_path()).attempts()
        row, = found.values()
        self.assertEqual((row["found"], row["judgement"]),
                         ([line["found"]], []))
        # The line of the report of the attempts, which a replay that
        # refuses does not reach.
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.grid.report_attempts(
                tg.Ledger(self.attempts_path()),
                self.inventory(self.root / "grid"), "first")
        self.assertRegex(out.getvalue(), "(?m)^CHECKOUT-FOUND-NOT-MARKED "
                         "[0-9a-f]{32} tracked file.*; not marked: "
                         "OSError: disk full$")
        self.assertNotIn("JUDGEMENT-NOT-MADE", out.getvalue())

    def test_a_close_that_fails_too_prints_what_it_would_have_said(self):
        # P1: the mark and the close both fail; the line on standard error
        # is the only record of the difference found.
        y = self.commit_counts()
        real = tg.ledger_append

        def refusing(path, **record):
            if record["event"] == "close":
                raise OSError(28, "No space left on device")
            return real(path, **record)
        err = io.StringIO()
        with patch.object(tg, "ledger_append", refusing), \
                contextlib.redirect_stderr(err):
            line = self.found_not_marked(y)
        self.assertEqual(line["event"], "open")
        self.assertEqual([x["event"] for x in self.ledger_lines()], ["open"])
        attempt = line["attempt"]
        self.assertRegex(err.getvalue(), (
            r"(?m)^ATTEMPT-NOT-CLOSED %s \(outcome checkout-changed\): "
            r"\[Errno 28\] No space left on device; found: tracked file"
            r".*; not marked: OSError: disk full$") % attempt)

    DEAD = ("the checkout changed while attempt %s ran \\(tracked file.*"
            "disk full\\).*the grid is dead.*neither replayed nor closed")

    def refused(self, out, attempt=".*"):
        calls = self.calls
        with self.assertRaisesRegex(ValueError, self.DEAD % attempt):
            self.go(self.replay_argv(out))
        self.assertEqual(self.calls, calls)

    def test_a_replay_refuses_the_grid_with_a_found(self):
        y = self.commit_counts()
        self.found_not_marked(y, "found")
        self.undo_one()
        attempt, = [k[0] for k in tg.Ledger(self.attempts_path()).attempts()]
        # The ledger is the only record; a resume does not read it, and
        # goes on.
        self.assertEqual(self.resume(y, "found")[0], 0)
        self.refused(self.root / "found", attempt)
        # Through main: the exit status and the line of a refusal.
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            code = self.grid.main(self.replay_argv(self.root / "found"))
        self.assertEqual(code, tg.REFUSED)
        self.assertRegex(err.getvalue(), "^REFUSED: the checkout changed "
                         "while attempt " + attempt)

    def test_a_new_grid_of_the_table_passes_and_prints_the_found(self):
        y = self.commit_counts()
        self.found_not_marked(y, "found")
        self.undo_one()
        dead, = [k[0] for k in tg.Ledger(self.attempts_path()).attempts()]
        self.assertEqual(self.run_at(y, "other")[0], 0)
        status, text = self.go(self.replay_argv(self.root / "other"))
        self.assertEqual(status, 0, text)
        self.assertIn("ATTEMPTS of TOY: 2 in the ledger, 2 of this "
                      "candidate %s" % y, text)
        self.assertRegex(text, "(?m)^CHECKOUT-FOUND-NOT-MARKED %s tracked "
                         "file.*; not marked: OSError: disk full$" % dead)
        self.assertEqual(text.count("CHECKOUT-FOUND-NOT-MARKED"), 1)
        # The earlier grid stays dead.
        self.refused(self.root / "found", dead)

    def second_stage_rig(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)
        return self.commit_counts()

    def extend_argv(self, *extra):
        return self.argv("extend", self.root / "ext", "--grid",
                         str(self.root / "grid"), "--authorize-measurements",
                         *extra)

    def test_a_second_stage_is_refused_for_a_found_of_its_first_stage(self):
        y = self.second_stage_rig()
        self.found_not_marked(y)
        self.undo_one()
        first, = [k[0] for k in tg.Ledger(self.attempts_path()).attempts()]
        self.assertEqual(self.resume(y)[0], 2)
        self.assertEqual(self.go(self.extend_argv())[0], 0)
        self.refused(self.root / "grid", first)
        self.refused(self.root / "ext", first)

    def test_a_second_stage_is_refused_for_a_found_of_its_own(self):
        y = self.second_stage_rig()
        self.assertEqual(self.run_at(y)[0], 2)
        with self.failing_after(self.calls + 1, self.edit_one):
            with self.fail_the_mark():
                with self.assertRaises(RuntimeError):
                    self.go(self.extend_argv())
        self.undo_one()
        row, = [k[0] for k, v in tg.Ledger(self.attempts_path())
                .attempts().items() if v["found"]]
        self.assertEqual(self.go(self.extend_argv("--resume"))[0], 0)
        self.refused(self.root / "ext", row)
        # The first stage has no found of its own, and replays.
        self.assertEqual(self.go(self.replay_argv(self.root / "grid"))[0], 2)

    def test_a_judgement_not_made_is_a_killed_process_with_a_line(self):
        # P4: a second interrupt during the judgement, so that nothing was
        # found. No refusal: a resume and a replay go on, and the replay
        # prints the line.
        y = self.commit_counts()
        real = tg.Grid.recheck
        seen = []

        def recheck(this, repo, commit, inventory):
            seen.append(1)
            if len(seen) > 1:
                raise KeyboardInterrupt()
            return real(this, repo, commit, inventory)
        self.explode_at = self.calls + 5
        with self.acting_at(self.calls + 3, self.edit_one):
            with patch.object(tg.Grid, "recheck", recheck):
                with self.assertRaises(RuntimeError):
                    self.run_at(y)
        self.explode_at = None
        line = self.ledger_lines()[-1]
        self.assertEqual((line["status"], line["judgement"]),
                         ("interrupted", "not made: KeyboardInterrupt: "))
        self.assertNotIn("found", line)
        self.undo_one()
        self.assertEqual(self.resume(y)[0], 0)
        status, text = self.go(self.replay_argv(self.root / "grid"))
        self.assertEqual(status, 0, text)
        self.assertIn("status interrupted,pass", text)
        self.assertRegex(
            text, "(?m)^JUDGEMENT-NOT-MADE [0-9a-f]{32} not made: "
            "KeyboardInterrupt: $")
        self.assertNotIn("CHECKOUT-FOUND-NOT-MARKED", text)

    def test_a_second_stage_that_loses_the_mark_is_found_in_its_close(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)
        y = self.commit_counts()
        self.assertEqual(self.run_at(y)[0], 2)
        argv = self.argv("extend", self.root / "ext", "--grid",
                         str(self.root / "grid"), "--authorize-measurements")
        with self.failing_after(self.calls + 1, self.edit_one):
            with self.fail_the_mark():
                with self.assertRaises(RuntimeError):
                    self.go(argv)
        line = self.ledger_lines()[-1]
        self.assertEqual((line["stage"], line["status"]),
                         ("second", "checkout-changed"))
        self.assertRegex(line["found"], "tracked file.*not marked: "
                         "OSError: disk full")

    def test_a_mark_that_cannot_be_written_is_not_kept_in_memory(self):
        inventory = dict(schema=self.table.schema("experiment"), runs=[])
        found = tg.CheckoutChanged("tracked file(s) changed: M x")
        with patch.object(tg, "checkpoint", side_effect=OSError("full")):
            with self.assertRaises(OSError):
                self.grid.mark_end(self.root, inventory, found)
        self.assertNotIn("checkout_changed", inventory)
        pilot = dict(schema=self.table.schema("pilot"), runs=[])
        with patch.object(tg, "checkpoint", side_effect=OSError("full")):
            with self.assertRaises(OSError):
                self.grid.mark_end(self.root, pilot, tg.CheckoutChanged(
                    "unclean", dead=False))
        self.assertEqual(set(pilot), {"schema", "runs"})

    def test_a_tracked_edit_found_only_by_resume_is_refused_not_marked(self):
        # The end of the attempt was judged, so the edit came later and no
        # cell ran under it: undoing it and resuming is honest.
        y = self.commit_counts()
        self.explode_at = 5
        with self.assertRaises(RuntimeError):
            self.run_at(y)
        self.explode_at = None
        self.edit_one()
        calls = self.calls
        with self.assertRaisesRegex(ValueError, "not clean"):
            self.resume(y)
        self.assertNotIn("checkout_changed",
                         self.inventory(self.root / "grid"))
        self.undo_one()
        self.assertEqual(self.resume(y)[0], 0)
        self.assertGreater(self.calls, calls)

    def test_a_stray_end_then_a_tracked_edit_found_by_resume_then_undone(
            self):
        # P2
        y = self.commit_counts()
        stray = self.repo / "notes.txt"
        with self.acting_at(5, lambda: stray.write_text("x")):
            with self.assertRaises(tg.CheckoutChanged):
                self.run_at(y)
        stray.unlink()
        self.edit_one()
        with self.assertRaisesRegex(ValueError, "not clean"):
            self.resume(y)
        self.assertNotIn("checkout_changed",
                         self.inventory(self.root / "grid"))
        self.undo_one()
        self.assertEqual(self.resume(y)[0], 0)
        self.assertEqual(
            self.statuses(),
            [("open", None), ("close", "checkout-changed"),
             ("resume", None), ("close", "pass")])

    # The words of a refusal ---------------------------------------------

    def stopped(self, y):
        self.explode_at = 5
        with self.assertRaises(RuntimeError):
            self.run_at(y)
        self.explode_at = None

    def test_a_resume_that_lost_the_stamp_is_told_what_is_safe(self):
        y = self.commit_counts()
        self.stopped(y)
        saved = self.stamp().read_bytes()
        self.stamp().unlink()
        with self.assertRaises(ValueError) as caught:
            self.resume(y)
        text = str(caught.exception)
        self.assertRegex(text, "^no build stamp \\(.*\\): " + re.escape(
            tg.RESUMING) + "$")
        self.assertNotIn("run prepare", text)
        self.assertIn("restore the stamp from a copy of that same file",
                      text)
        self.assertIn("a prepare ends the grid, and a later commit must be "
                      "left: go back to the recorded commit", text)
        self.assertNotIn("or a commit", text)
        self.stamp().write_bytes(saved)
        self.assertEqual(self.resume(y)[0], 0)

    def test_a_resume_with_a_stray_file_is_told_what_is_safe(self):
        y = self.commit_counts()
        self.stopped(y)
        stray = self.repo / "notes.txt"
        stray.write_text("x")
        with self.assertRaises(ValueError) as caught:
            self.resume(y)
        text = str(caught.exception)
        self.assertRegex(text, "^harness checkout is not clean: " +
                         re.escape(tg.RESUMING) + "$")
        self.assertNotIn("commit first", text)
        stray.unlink()
        self.assertEqual(self.resume(y)[0], 0)

    def test_the_other_refusals_of_a_resume_are_told_it_too(self):
        y = self.commit_counts()
        self.stopped(y)
        self.commit_file("note.txt", "later\n")
        with self.assertRaisesRegex(
                ValueError, "not at the commit measured.*: " +
                re.escape(tg.RESUMING)):
            self.resume(y)
        self.git("checkout", "-q", y)
        heap = self.repo / "bin" / "hol.state0"
        heap.write_text("another")
        with self.assertRaisesRegex(ValueError, "differ from the stamped "
                                    "build: " + re.escape(tg.RESUMING)):
            self.resume(y)
        heap.write_text("heap")
        self.assertEqual(self.resume(y)[0], 0)

    def test_a_second_stage_and_a_pilot_resume_are_told_the_same(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)
        y = self.commit_counts()
        self.assertEqual(self.run_at(y)[0], 2)
        argv = self.argv("extend", self.root / "ext", "--grid",
                         str(self.root / "grid"), "--authorize-measurements")
        self.explode_at = self.calls + 1
        with self.assertRaises(RuntimeError):
            self.go(argv)
        self.explode_at = None
        pilot = self.pilot_stopping("again", lambda: None)
        saved = self.stamp().read_bytes()
        self.stamp().unlink()
        for label, command in (("second stage", argv + ["--resume"]),
                               ("pilot", pilot + ["--resume"])):
            with self.subTest(label):
                with self.assertRaisesRegex(
                        ValueError, "^no build stamp \\(.*\\): " +
                        re.escape(tg.RESUMING) + "$"):
                    self.go(command)
        self.stamp().write_bytes(saved)
        self.assertEqual(self.go(argv + ["--resume"])[0], 0)
        self.assertEqual(self.go(pilot + ["--resume"])[0], 0)

    def test_a_fresh_extend_is_told_the_words_of_a_grid_that_has_begun(self):
        # Its first stage has been measured: the record has begun, and a
        # prepare costs the first stage, as it costs a stopped grid.
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)
        y = self.commit_counts()
        self.assertEqual(self.run_at(y)[0], 2)
        argv = self.argv("extend", self.root / "ext", "--grid",
                         str(self.root / "grid"), "--authorize-measurements")
        saved = self.stamp().read_bytes()
        self.stamp().unlink()
        with self.assertRaises(ValueError) as caught:
            self.go(argv)
        self.assertRegex(str(caught.exception), "^no build stamp \\(.*\\): "
                         + re.escape(tg.RESUMING) + "$")
        self.assertNotIn("run prepare", str(caught.exception))
        self.stamp().write_bytes(saved)
        stray = self.repo / "notes.txt"
        stray.write_text("x")
        with self.assertRaises(ValueError) as caught:
            self.go(argv)
        self.assertRegex(str(caught.exception), "^harness checkout is not "
                         "clean: " + re.escape(tg.RESUMING) + "$")
        self.assertNotIn("commit first", str(caught.exception))
        self.assertFalse((self.root / "ext").exists())
        stray.unlink()
        self.assertEqual(self.go(argv)[0], 0)

    def test_a_fresh_start_keeps_the_words_of_a_fresh_start(self):
        y = self.commit_counts()
        saved = self.stamp().read_bytes()
        self.stamp().unlink()
        for command in (self.argv("run", self.root / "g", "--candidate", y,
                                  "--authorize-measurements"),
                        self.argv("pilot", self.root / "p",
                                  "--authorize-measurements")):
            with self.assertRaisesRegex(ValueError, "^no build stamp "
                                        "\\(.*\\): run prepare at this "
                                        "commit$"):
                self.go(command)
        self.stamp().write_bytes(saved)
        stray = self.repo / "notes.txt"
        stray.write_text("x")
        with self.assertRaisesRegex(ValueError, "^harness checkout is not "
                                    "clean: commit first$"):
            self.run_at(y, "g")
        stray.unlink()
        self.assertFalse((self.root / "g").exists())

    def test_an_unjudged_end_does_not_tell_the_operator_to_prepare(self):
        y = self.commit_counts()
        saved = self.stamp().read_bytes()
        with self.acting_at(5, self.stamp().unlink):
            with self.assertRaises(tg.CheckoutChanged) as caught:
                self.run_at(y)
        self.assertNotIn("run prepare", str(caught.exception))
        self.assertIn(tg.RESUMING, str(caught.exception))
        self.stamp().write_bytes(saved)
        stray = self.repo / "notes.txt"
        real = self.fake_launch

        def launching(command, output, fds, timeout, stdin=None,
                      append=False):
            found = real(command, output, fds, timeout, stdin, append)
            if "--performance-case" in command and len(self.launched) == 5:
                stray.write_text("x")
            return found
        with patch.object(a, "run_logged", launching):
            with self.assertRaises(tg.CheckoutChanged):
                self.go(self.argv("pilot", self.root / "pilot",
                                  "--authorize-measurements"))
        stored = self.inventory(self.root / "pilot")
        for text in (stored["checkout_unjudged"], *stored["unjudged_ends"]):
            self.assertNotIn("run prepare", text)
            self.assertNotIn("commit first", text)
            self.assertIn(tg.RESUMING, text)
        stray.unlink()
        with self.assertRaisesRegex(ValueError, "could not be judged.*"
                                    "resume it"):
            self.go(["verify-counts", "--grid", str(self.root / "pilot")])

    def test_every_prepare_makes_a_new_digest(self):
        # Configure relinks bin/hol, which differs at each run, so two
        # prepares at one commit stamp the same head and tree and different
        # products (three real runs gave three digests).
        self.commit_counts()
        self.assertEqual(self.prepare()[0], 0)
        first = json.loads(self.stamp().read_text())
        self.assertEqual(self.prepare()[0], 0)
        second = json.loads(self.stamp().read_text())
        self.assertEqual((second["head"], second["tree_outside_performance"]),
                         (first["head"], first["tree_outside_performance"]))
        self.assertNotEqual(second["products"]["sha256"],
                            first["products"]["sha256"])
        self.assertEqual(second["products"]["files"],
                         first["products"]["files"])

    def test_a_prepare_between_a_stop_and_its_resume_is_refused(self):
        # Nothing but prepare itself touches the products here: a stopped
        # grid must not be prepared, and prepare is no way back to it.
        y = self.commit_counts()
        self.explode_at = 5
        with self.assertRaises(RuntimeError):
            self.run_at(y)
        self.explode_at = None
        recorded = self.inventory(self.root / "grid")["checkout"]["products"]
        self.assertEqual(self.prepare()[0], 0)
        self.assertNotEqual(
            json.loads(self.stamp().read_text())["products"]["sha256"],
            recorded)
        calls = self.calls
        with self.assertRaisesRegex(ValueError, "resume with different "
                                    "settings"):
            self.run_at(y, "grid", "--resume")
        self.assertEqual(self.calls, calls)
        # Another prepare does not bring the digest back either.
        self.assertEqual(self.prepare()[0], 0)
        with self.assertRaisesRegex(ValueError, "resume with different "
                                    "settings"):
            self.run_at(y, "grid", "--resume")
        # A lost stamp comes back only from a copy of that same file.
        stamp = self.stamp()
        stamp.unlink()
        with self.assertRaisesRegex(ValueError, "no build stamp"):
            self.run_at(y, "grid", "--resume")

    def test_a_restamp_between_the_stages_is_refused(self):
        self.control = lambda case, size, pairs, seed: (
            GOOD if pairs >= 60 or (case, size) != (CASES[1], 100)
            else WIDE)
        y = self.commit_counts()
        self.assertEqual(self.run_at(y)[0], 2)
        (self.repo / "bin" / "hol.state0").write_text("another")
        self.assertEqual(self.prepare()[0], 0)
        calls = self.calls
        with self.assertRaisesRegex(ValueError, "not the one the first "
                                    "stage was measured in"):
            self.go(self.argv("extend", self.root / "ext", "--grid",
                              str(self.root / "grid"),
                              "--authorize-measurements"))
        self.assertEqual(self.calls, calls)
        self.assertFalse((self.root / "ext").exists())
        # A resumption is judged the same way, first.
        with self.assertRaisesRegex(ValueError, "not the one the first "
                                    "stage was measured in"):
            self.go(self.argv("extend", self.root / "ext", "--grid",
                              str(self.root / "grid"), "--resume",
                              "--authorize-measurements"))

    def test_a_dead_pilot_is_not_predeclared_from_or_resumed(self):
        self.commit_counts()
        real, heap = self.fake_launch, self.repo / "bin" / "hol.state0"

        def launching(command, output, fds, timeout, stdin=None,
                      append=False):
            found = real(command, output, fds, timeout, stdin, append)
            if "--performance-case" in command and len(self.launched) == 5:
                heap.write_text("another")
            return found
        argv = self.argv("pilot", self.root / "again",
                         "--authorize-measurements")
        with patch.object(a, "run_logged", launching):
            with self.assertRaises(tg.CheckoutChanged):
                self.go(argv)
        self.assertIn("checkout_changed", self.inventory(self.root / "again"))
        with self.assertRaisesRegex(ValueError, "changed while the pilot "
                                    "ran"):
            self.go(["predeclare", "--grid", str(self.root / "again"),
                     "--output", str(self.root / "c.json")])
        # A prepare cannot revive it: the record differs.
        self.assertEqual(self.prepare()[0], 0)
        with self.assertRaisesRegex(ValueError, "resume with different "
                                    "settings"):
            self.go(argv + ["--resume"])

    def test_prepare_runs_the_real_build_in_the_root_and_stamps(self):
        y = self.commit_counts()
        self.stamp().unlink()
        status, text = self.prepare()
        self.assertEqual(status, 0, text)
        built = self.built[-1]
        self.assertEqual(built["command"][-len(tg.BUILD):], list(tg.BUILD))
        self.assertEqual(tg.BUILD, ("bin/build", "--stdknl",
                                    "--seq=tools/sequences/upto-parallel"))
        self.assertIn(str(self.repo.resolve()), built["command"])
        self.assertEqual(built["timeout"], tg.BUILD_TIMEOUT)
        self.assertEqual(built["output"], self.stamp().with_name(
            "prepare.log"))
        stamp = json.loads(self.stamp().read_text())
        self.assertEqual(stamp, tg.build_stamp(self.repo))
        self.assertEqual(stamp["head"], y)
        self.assertIn("PREPARED %s" % y, text)

    def test_prepare_runs_the_build_under_the_lock(self):
        self.commit_counts()
        self.stamp().unlink()
        built = len(self.built)
        with a.serial_lock(self.repo):
            with self.assertRaises(a.Blocked):
                self.prepare()
        self.assertEqual(len(self.built), built)
        self.assertFalse(self.stamp().exists())
        seen = []
        real = self.fake_launch

        def holding(command, output, fds, timeout, stdin=None,
                    append=False):
            seen.append(fds)
            return real(command, output, fds, timeout, stdin, append)
        with patch.object(a, "run_logged", holding):
            self.assertEqual(self.prepare()[0], 0)
        self.assertEqual(len(seen), 2)  # configure and the build
        self.assertTrue(all(seen))

    def test_prepare_needs_a_clean_checkout(self):
        built = len(self.built)
        before = self.stamp().read_bytes()
        (self.repo / "src" / "one.sml").write_text("val one = 2\n")
        with self.assertRaisesRegex(ValueError, "not clean"):
            self.prepare()
        self.assertEqual((len(self.built), self.stamp().read_bytes()),
                         (built, before))

    def test_a_failed_build_writes_no_stamp_and_removes_the_old_one(self):
        y = self.commit_counts()
        self.assertTrue(self.stamp().exists())
        self.build_exit = 2
        with self.assertRaisesRegex(ValueError, "build failed \\(exit 2\\)"
                                    ", no build stamp"):
            self.prepare()
        self.assertFalse(self.stamp().exists())
        with self.assertRaisesRegex(ValueError, "no build stamp.*run "
                                    "prepare at this commit"):
            self.run_at(y)

    def test_a_timed_out_build_writes_no_stamp(self):
        self.commit_counts()
        real = self.fake_launch
        patched = lambda *args, **kw: dict(real(*args, **kw),
                                           timed_out=True)
        with patch.object(a, "run_logged", patched):
            with self.assertRaisesRegex(ValueError, "timed out"):
                self.prepare()
        self.assertFalse(self.stamp().exists())

    def test_an_interrupted_build_leaves_no_stamp(self):
        self.commit_counts()
        def interrupted(*args, **kw):
            raise KeyboardInterrupt
        with patch.object(a, "run_logged", interrupted):
            with self.assertRaises(KeyboardInterrupt):
                self.prepare()
        self.assertFalse(self.stamp().exists())

    def test_a_build_that_leaves_the_checkout_unclean_writes_no_stamp(self):
        self.commit_counts()
        def dirty():
            (self.repo / "src" / "one.sml").write_text("val one = 9\n")
        self.build = dirty
        with self.assertRaisesRegex(ValueError, "left the checkout "
                                    "unusable, no build stamp"):
            self.prepare()
        self.assertFalse(self.stamp().exists())

    def test_a_build_that_moves_head_writes_no_stamp(self):
        self.commit_counts()

        def moves():
            self.commit_file("src/one.sml", "val one = 5\n", "moved")
        self.build = moves
        with self.assertRaisesRegex(ValueError, "HEAD moved during the "
                                    "build, no build stamp"):
            self.prepare()
        self.assertFalse(self.stamp().exists())

    def test_prepare_checks_the_place_of_the_ledger(self):
        exclude = self.repo / ".git" / "info" / "exclude"
        exclude.write_text("")
        built = len(self.built)
        with self.assertRaisesRegex(ValueError, "would be tracked by git"):
            self.prepare()
        self.assertEqual(len(self.built), built)

    def test_a_table_without_fixed_seconds_takes_no_stamp(self):
        grid = tg.Grid(tg.Table("toy", "TOY", CASES, self.driver,
                                self.counts, schedule="ramp"))
        with self.assertRaisesRegex(ValueError, "takes no build stamp"):
            grid.execute(["prepare", "--repo", str(self.repo)])

    def test_the_build_is_the_standard_kernel_and_the_stamp_names_it(self):
        self.assertIn("--stdknl", tg.BUILD)
        self.assertEqual(json.loads(self.stamp().read_text())["build"],
                         list(tg.BUILD))
        self.assertEqual(self.built[-1]["command"][-len(tg.BUILD):],
                         list(tg.BUILD))

    def test_the_build_has_no_standard_input_so_it_cannot_wait_for_one(self):
        self.commit_counts()
        # The stand-in build reads its standard input, as bin/build does
        # after its warning, and is killed at the timeout unless it has none.
        self.assertIs(self.built[-1]["stdin"], subprocess.DEVNULL)
        self.assertEqual(self.prepare()[0], 0)
        with patch.object(a, "run_logged", lambda command, output, fds,
                          timeout, stdin=None, append=False:
                          self.fake_launch(command, output, fds, timeout,
                                           append=append)):
            with self.assertRaisesRegex(ValueError, "timed out"):
                self.prepare()
        self.assertFalse(self.stamp().exists())

    def test_a_build_that_warns_of_a_stale_executable_writes_no_stamp(self):
        self.commit_counts()
        self.build_log = ("build log\nWARNING! WARNING!\n  The executable "
                          "bin/hol is older than tools-poly/Holmake/x.sml;\n"
                          "WARNING! WARNING!\nmore log\n")
        for exit_code in (0, 2):
            with self.subTest(exit=exit_code):
                self.build_exit = exit_code
                with self.assertRaisesRegex(
                        ValueError, "older than its sources although "
                        "configure ran just before.*no build stamp: see "
                        + re.escape(str(self.stamp().with_name(
                            "prepare.log")))):
                    self.prepare()
                self.assertFalse(self.stamp().exists())
                self.assertEqual(
                    self.built[-1]["output"].read_text(),
                    self.configure_log + self.build_log)
                self.build_log = self.build_log.replace("log", "text")
        self.build_exit, self.build_log = 0, "build log\n"
        self.assertEqual(self.prepare()[0], 0)
        self.assertTrue(self.stamp().exists())

    def test_prepare_configures_in_the_root_and_then_builds_into_one_log(
            self):
        self.commit_counts()
        self.stamp().unlink()
        self.steps.clear()
        self.assertEqual(self.prepare()[0], 0)
        configure, build = self.steps
        self.assertEqual((configure["kind"], build["kind"]),
                         ("configure", "build"))
        root = str(self.repo.resolve())
        self.assertEqual(tg.CONFIGURE, ("poly",))
        self.assertEqual(configure["command"][-1:], ["poly"])
        self.assertEqual(configure["command"][-2], root)
        # The file configure reads, and no input for the build.
        self.assertEqual(configure["stdin"],
                         self.repo.resolve() / "tools/smart-configure.sml")
        self.assertEqual(tg.CONFIGURE_INPUT, "tools/smart-configure.sml")
        self.assertIs(build["stdin"], subprocess.DEVNULL)
        # One log: the build appends to what configure wrote.
        self.assertEqual((configure["append"], build["append"]),
                         (False, True))
        self.assertEqual(configure["output"], build["output"])
        self.assertEqual(build["output"].read_text(),
                         self.configure_log + self.build_log)
        self.assertEqual((configure["timeout"], build["timeout"]),
                         (tg.BUILD_TIMEOUT, tg.BUILD_TIMEOUT))
        self.assertTrue(configure["fds"])

    def test_prepare_configures_a_checkout_that_was_not(self):
        y = self.commit_counts()
        systeml = self.repo / "tools" / "Holmake" / "Systeml.sml"
        systeml.unlink()
        self.stamp().unlink()
        self.assertEqual(self.prepare()[0], 0)
        self.assertTrue(systeml.is_file())
        self.assertEqual(json.loads(self.stamp().read_text())["head"], y)
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_a_failed_configure_writes_no_stamp_and_runs_no_build(self):
        y = self.commit_counts()
        self.assertTrue(self.stamp().exists())
        built, self.configure_exit = len(self.built), 2
        with self.assertRaisesRegex(ValueError, "configure failed \\(exit 2"
                                    "\\), no build stamp: see .*prepare.log"):
            self.prepare()
        self.assertFalse(self.stamp().exists())
        self.assertEqual((len(self.built), self.steps[-1]["kind"]),
                         (built, "configure"))
        # The stamp of the earlier prepare is gone, so nothing measures.
        with self.assertRaisesRegex(ValueError, "no build stamp"):
            self.run_at(y)
        self.configure_exit = 0
        self.assertEqual(self.prepare()[0], 0)

    def test_a_configure_that_exits_zero_without_its_last_line_is_refused(
            self):
        # The real script swallows an exception and poly exits 0.
        y = self.commit_counts()
        built = len(self.built)
        self.assertTrue(self.stamp().exists())
        for label, log in (("nothing", ""),
                           ("other text", "You must do poly < x\n"),
                           ("part of the line",
                            "Finished configuration! (not)\n")):
            with self.subTest(label):
                self.configure_log = log
                with self.assertRaisesRegex(
                        ValueError, "exited 0 but did not print "
                        "'Finished configuration!'.*no build stamp: see "
                        ".*prepare.log"):
                    self.prepare()
                self.assertFalse(self.stamp().exists())
                self.assertEqual(len(self.built), built)
                with self.assertRaisesRegex(ValueError, "no build stamp"):
                    self.run_at(y)
        self.configure_log = "configure log\n%s\n" % tg.FINISHED
        self.assertEqual(self.prepare()[0], 0)
        self.assertEqual(len(self.built), built + 1)

    def test_the_last_line_of_configure_is_a_whole_line_of_the_log(self):
        log = self.root / "configure.log"
        for text, expected in (
                ("", False), ("other text\n", False),
                ("%s (not)\n" % tg.FINISHED, False),
                ("not %s\n" % tg.FINISHED, False),
                ("%s\n" % tg.FINISHED, True),
                ("log\n  %s  \nmore\n" % tg.FINISHED, True),
                ("%s" % tg.FINISHED, True)):
            with self.subTest(text):
                log.write_text(text)
                self.assertEqual(tg.configure_finished(log), expected)

    def test_a_timed_out_configure_writes_no_stamp_and_runs_no_build(self):
        self.commit_counts()
        built, real = len(self.built), self.fake_launch
        patched = lambda *args, **kw: dict(real(*args, **kw), timed_out=True)
        with patch.object(a, "run_logged", patched):
            with self.assertRaisesRegex(ValueError, "configure failed.*"
                                        "timed out"):
                self.prepare()
        self.assertFalse(self.stamp().exists())
        self.assertEqual(len(self.built), built)

    def test_a_configure_that_leaves_the_wrong_holdir_stops_before_the_build(
            self):
        self.commit_counts()
        built = len(self.built)
        systeml = self.repo / "tools" / "Holmake" / "Systeml.sml"
        for label, text, message in (
                ("none", None, "configure did not leave the checkout "
                 "configured: no .*Systeml.sml"),
                ("no HOLDIR", "val x = 1\n", "configure did not leave a "
                 "single HOLDIR"),
                ("two", 'val HOLDIR = "/a"\nval HOLDIR = "/b"\n',
                 "configure did not leave a single HOLDIR"),
                ("another path", 'val HOLDIR = "/elsewhere/HOL"\n',
                 "configure left the checkout configured for "
                 "/elsewhere/HOL, not for")):
            with self.subTest(label):
                def wrong():
                    systeml.unlink(missing_ok=True)
                    if text is not None:
                        systeml.write_text(text)
                self.configure_actions = wrong
                with self.assertRaisesRegex(ValueError, message):
                    self.prepare()
                self.assertFalse(self.stamp().exists())
                self.assertEqual(len(self.built), built)
        del self.configure_actions
        self.assertEqual(self.prepare()[0], 0)
        self.assertEqual(len(self.built), built + 1)

    def test_a_link_in_the_products_may_not_leave_the_repository(self):
        self.commit_counts()
        outside = self.root / "outside.uo"
        outside.write_text("object")
        (self.repo / "sigobj" / "o.uo").symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "resolves outside the "
                                    "repository"):
            self.prepare()
        self.assertFalse(self.stamp().exists())

    def test_prepare_keeps_one_log_and_does_not_accumulate(self):
        self.commit_counts()
        where = self.stamp().parent
        for text in ("one\n", "two\n", "three\n"):
            self.build_log = text
            self.assertEqual(self.prepare()[0], 0)
            self.assertEqual(sorted(p.name for p in where.glob("prepare*")),
                             ["prepare.log"])
            self.assertEqual((where / "prepare.log").read_text(),
                             self.configure_log + text)
        self.build_exit = 2
        self.build_log = "failed\n"
        with self.assertRaisesRegex(ValueError, "prepare.log"):
            self.prepare()
        self.assertEqual((where / "prepare.log").read_text(),
                         self.configure_log + "failed\n")


class Sleeping(ChainRig):
    """The child process of `Terminated`: a real grid on a real repository
    whose one cell is a real process group that sleeps, holding the lock it
    inherits as a cell does."""

    def sleeps(self, marks):
        marks = Path(marks)
        # The parent looks at the repository after this process is gone, and
        # removes it with `marks`: the exit must not.
        self.tmp._finalizer.detach()
        y = self.commit_counts()
        out = self.root / "grid"

        def cell(options):
            # The edit the judgement of the stop has to find.
            self.edit_one()
            fds = [int(x) for x in os.environ[
                "HOL4_PERF_LOCK_FDS"].split(",")]
            # Nested: as `run_paired` starts its builds, in a session of
            # its own, holding the lock descriptors it inherits.
            nested = "setsid " if os.environ.get("NESTED") else ""
            script = (nested + 'sleep 600 & echo $! > "$1/grandchild"; '
                      'echo $$ > "$1/cell"; wait')
            return REAL_RUN_LOGGED(
                ["/bin/sh", "-c", script, "cell", str(marks)],
                marks / "cell.log", fds, 600)
        (marks / "where.json").write_text(json.dumps(
            dict(repo=str(self.repo), out=str(out))))
        with patch.object(a, "run", cell):
            return self.grid.main(self.argv(
                "run", out, "--candidate", y, "--authorize-measurements"))


CHILD = ("import sys; import test_timing_grid as T; "
         "c = T.Sleeping('sleeps'); c.setUp(); "
         "sys.exit(c.sleeps(sys.argv[1]))")


def alive(pid):
    """The process exists and is not a zombie waiting to be reaped."""
    try:
        state = Path("/proc/%d/stat" % pid).read_text().rsplit(")", 1)[1]
    except (FileNotFoundError, ProcessLookupError):
        return False
    return state.split()[0] != "Z"


@unittest.skipUnless(Path("/proc/self/stat").exists(), "needs /proc")
class Terminated(unittest.TestCase):
    """A termination signal takes the path of an interrupt, in a real
    process: the cell's group is killed, the lock is released, and the end
    of the attempt is judged. The assertions are about what the driver
    did: nothing here kills the cell before they are made."""

    def cleanup(self, child, marks, pids):
        """After the assertions: what a failed test left running."""
        if child.poll() is None:
            # SIGTERM first: a live driver takes its own path, which
            # kills a cell whose mark was never read.
            child.terminate()
            try:
                child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
        # Marks written but not read by a wait that failed first.
        for name in ("grandchild", "cell")[len(pids):]:
            try:
                pids.append(int((marks / name).read_text()))
            except (FileNotFoundError, ValueError):
                break
        for pid in pids:
            if alive(pid):
                with contextlib.suppress(ProcessLookupError):
                    os.kill(pid, signal.SIGKILL)
        if len(pids) > 1 and alive(pids[1]):
            with contextlib.suppress(ProcessLookupError):
                os.killpg(pids[1], signal.SIGKILL)

    def await_pids(self, child, marks, pids):
        """Fill `pids` (grandchild, cell) as each mark is read, so that
        `cleanup`, which holds the list, kills what a failed wait saw."""
        deadline = time.monotonic() + 120
        while len(pids) < 2:
            if child.poll() is not None or time.monotonic() > deadline:
                self.fail("no cell started: %s" % (
                    marks / "child.log").read_text())
            name = ("grandchild", "cell")[len(pids)]
            try:
                pids.append(int((marks / name).read_text()))
            except (FileNotFoundError, ValueError):
                time.sleep(0.05)

    def await_session(self, pid):
        """Wait until `pid` has left its parent's group by `setsid`."""
        end = time.monotonic() + 60
        while True:
            try:
                if os.getsid(pid) == pid:
                    return
            except ProcessLookupError:
                self.fail("process %d is gone" % pid)
            self.assertLess(time.monotonic(), end)
            time.sleep(0.01)

    def terminate(self, number, nested=False):
        # Removed after `cleanup`, which may still read its marks.
        t = tempfile.mkdtemp(prefix="timing-grid-signal-")
        self.addCleanup(shutil.rmtree, t, True)
        marks = Path(t)
        env = {k: v for k, v in os.environ.items()
               if k not in ("HOL4_PERF_LOCK_FDS", "NESTED")}
        env["TMPDIR"] = t  # the child's rig is removed with `marks`
        if nested:
            env["NESTED"] = "1"
        pids = []
        with (marks / "child.log").open("w") as log:
            child = subprocess.Popen(
                [sys.executable, "-B", "-c", CHILD, t],
                cwd=Path(__file__).parent, env=env, stdout=log,
                stderr=subprocess.STDOUT,
                # Whatever the suite inherited (a run under `nohup`
                # ignores SIGHUP), the signal under test is at its
                # default here, and SIGTERM, which `cleanup` sends.
                preexec_fn=lambda: [signal.signal(n, signal.SIG_DFL)
                                    for n in {number, signal.SIGTERM}])
        self.addCleanup(self.cleanup, child, marks, pids)
        self.await_pids(child, marks, pids)
        for pid in pids:
            self.assertTrue(alive(pid))
        if nested:
            # `setsid` is exec'd after the marks are written: the
            # signal must not land while it is still in the cell's
            # group.
            self.await_session(pids[0])
        child.send_signal(number)
        code = child.wait(timeout=60)
        log = (marks / "child.log").read_text()
        # It died of the interrupt, not of the signal.
        self.assertNotIn(code, (0, -number), log)
        self.assertIn("KeyboardInterrupt", log)
        deadline = time.monotonic() + 10
        while any(alive(pid) for pid in pids) and \
                time.monotonic() < deadline:
            time.sleep(0.05)
        where = json.loads((marks / "where.json").read_text())
        if nested:
            # The cell's group is killed; the process it started in a
            # session of its own is not, and keeps the lock.
            self.assertEqual([alive(pid) for pid in pids], [True, False])
            with patch.dict(os.environ), self.assertRaisesRegex(
                    a.Blocked, "lock busy"):
                with a.serial_lock(where["repo"]):
                    pass
            os.kill(pids[0], signal.SIGKILL)
            deadline = time.monotonic() + 10
            while alive(pids[0]) and time.monotonic() < deadline:
                time.sleep(0.05)
        else:
            self.assertEqual([alive(pid) for pid in pids],
                             [False, False])
        with patch.dict(os.environ), a.serial_lock(where["repo"]):
            pass  # the lock is free
        ledger = Path(where["repo"]) / ".agent-files" / "evidence" / \
            "toy" / "attempts.jsonl"
        lines = [json.loads(x) for x in ledger.read_text().splitlines()]
        self.assertEqual([(x["event"], x.get("status")) for x in lines],
                         [("open", None), ("close", "checkout-changed")])
        inventory = json.loads(
            (Path(where["out"]) / "inventory.json").read_text())
        self.assertIn("tracked file", inventory["checkout_changed"])

    def test_sigterm_is_judged_like_an_interrupt(self):
        self.terminate(signal.SIGTERM)

    def test_sighup_is_judged_like_an_interrupt(self):
        self.terminate(signal.SIGHUP)

    def test_the_lock_stays_with_a_process_in_a_session_of_its_own(self):
        if shutil.which("setsid") is None:
            self.skipTest("needs setsid")
        self.terminate(signal.SIGTERM, nested=True)

    def test_an_ignored_signal_stays_ignored_in_a_real_process(self):
        # As under `nohup`: SIGHUP is ignored at the start.
        with tempfile.TemporaryDirectory(prefix="timing-grid-ign-") as t:
            marks = Path(t)
            code = (
                "import signal, sys, time; import timing_grid as tg\n"
                "from pathlib import Path\n"
                "marks = Path(sys.argv[1])\n"
                "assert signal.getsignal(signal.SIGHUP) == signal.SIG_IGN\n"
                "with tg.terminating_as_interrupt():\n"
                "    assert signal.getsignal(signal.SIGHUP) == "
                "signal.SIG_IGN\n"
                "    assert signal.getsignal(signal.SIGTERM) is "
                "signal.default_int_handler\n"
                "    (marks / 'ready').write_text('x')\n"
                "    end = time.monotonic() + 60\n"
                "    while not (marks / 'go').exists():\n"
                "        assert time.monotonic() < end\n"
                "        time.sleep(0.02)\n"
                "assert signal.getsignal(signal.SIGHUP) == signal.SIG_IGN\n"
                "print('finished')\n")
            with (marks / "log").open("w") as log:
                child = subprocess.Popen(
                    [sys.executable, "-B", "-c", code, t],
                    cwd=Path(__file__).parent, stdout=log,
                    stderr=subprocess.STDOUT,
                    # SIGTERM is at its default, whatever was inherited.
                    preexec_fn=lambda: [
                        signal.signal(signal.SIGHUP, signal.SIG_IGN),
                        signal.signal(signal.SIGTERM, signal.SIG_DFL)])
            self.addCleanup(lambda: child.poll() is None and child.kill())
            deadline = time.monotonic() + 60
            while not (marks / "ready").exists():
                self.assertIsNone(child.poll(), (marks / "log").read_text())
                self.assertLess(time.monotonic(), deadline)
                time.sleep(0.02)
            child.send_signal(signal.SIGHUP)
            time.sleep(0.3)
            self.assertIsNone(child.poll(), (marks / "log").read_text())
            (marks / "go").write_text("x")
            self.assertEqual(child.wait(timeout=60), 0,
                             (marks / "log").read_text())
            self.assertEqual((marks / "log").read_text(), "finished\n")

    def test_an_ignored_signal_is_not_replaced_and_is_left_as_found(self):
        saved = {n: signal.getsignal(n) for n in (signal.SIGTERM,
                                                  signal.SIGHUP)}
        for number, handler in saved.items():
            self.addCleanup(signal.signal, number, handler)
        signal.signal(signal.SIGHUP, signal.SIG_IGN)
        signal.signal(signal.SIGTERM, signal.SIG_DFL)
        with tg.terminating_as_interrupt():
            self.assertIs(signal.getsignal(signal.SIGHUP), signal.SIG_IGN)
            self.assertIs(signal.getsignal(signal.SIGTERM),
                          signal.default_int_handler)
        self.assertIs(signal.getsignal(signal.SIGHUP), signal.SIG_IGN)
        self.assertIs(signal.getsignal(signal.SIGTERM), signal.SIG_DFL)

    def test_the_handlers_are_put_back_and_only_main_installs_them(self):
        # A known value of its own: earlier calls of `main` may have left
        # the handler of an interrupt in place.
        saved = {n: signal.getsignal(n) for n in (signal.SIGTERM,
                                                  signal.SIGHUP)}
        for number, handler in saved.items():
            self.addCleanup(signal.signal, number, handler)
            signal.signal(number, signal.SIG_DFL)
        before = [signal.getsignal(n) for n in (signal.SIGTERM,
                                                signal.SIGHUP)]
        self.assertEqual(before, [signal.SIG_DFL, signal.SIG_DFL])
        with tg.terminating_as_interrupt():
            for number in (signal.SIGTERM, signal.SIGHUP):
                self.assertIs(signal.getsignal(number),
                              signal.default_int_handler)
        self.assertEqual([signal.getsignal(n) for n in (
            signal.SIGTERM, signal.SIGHUP)], before)
        seen = []
        grid = tg.Grid(tg.Table(
            "toy", "TOY", CASES, Path(__file__), Path("c.json"),
            schedule="ramp", ledger=None))
        with patch.object(grid, "execute", lambda *a_, **k: seen.append(
                signal.getsignal(signal.SIGTERM)) or 0):
            self.assertEqual(grid.main([]), 0)
        self.assertEqual(seen, [signal.default_int_handler])


class Refusals(Rig):
    """A command that decided nothing ends with a status no grid has."""

    def main(self, argv):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            return self.grid.main(argv), out.getvalue(), err.getvalue()

    def test_the_status_of_a_refusal_is_not_that_of_a_grid(self):
        self.assertNotIn(tg.REFUSED, (0, 1, 2))
        self.assertEqual(tg.REFUSED, 3)

    def test_a_refusal_is_one_line_and_that_status_and_no_traceback(self):
        argv = self.argv("run", self.root / "grid", "--candidate",
                         CANDIDATE)
        code, out, err = self.main(argv)
        self.assertEqual((code, out), (tg.REFUSED, ""))
        self.assertEqual(err, "REFUSED: exclusive window required\n")
        self.assertFalse((self.root / "grid").exists())

    def test_a_held_lock_and_a_changed_checkout_are_refusals_too(self):
        argv = self.argv("run", self.root / "grid", "--candidate",
                         CANDIDATE, "--authorize-measurements")
        with a.serial_lock(self.repo):
            code, out, err = self.main(argv)
        self.assertEqual((code, err.count("\n")), (tg.REFUSED, 1))
        self.assertTrue(err.startswith("REFUSED: "), err)

        def changed(repo, commit=None, stamp=None):
            seen.append(commit)
            return self.fake_checkout(repo, commit, stamp) if len(
                seen) < 3 else dict(head=commit, tree_outside_performance=
                                    "u" * 64, products=PRODUCTS)
        seen = []
        with patch.object(tg, "checkout_identity", changed):
            code, out, err = self.main(argv)
        self.assertEqual((code, err.count("\n")), (tg.REFUSED, 1))
        self.assertIn("not the one recorded", err)

    def test_any_other_error_is_a_traceback_and_a_refusal_line_and_status(
            self):
        for error in (FileNotFoundError("gone"), KeyError("field"),
                      OSError(28, "No space left on device"),
                      subprocess.CalledProcessError(1, "git")):
            with self.subTest(type(error).__name__):
                with patch.object(self.grid, "execute", side_effect=error):
                    code, out, err = self.main(["replay"])
                self.assertEqual((code, out), (tg.REFUSED, ""))
                self.assertIn("Traceback (most recent call last)", err)
                last = err.rstrip("\n").splitlines()[-1]
                self.assertTrue(last.startswith("REFUSED: %s: " % type(
                    error).__name__), last)

    def test_the_real_error_of_a_missing_output_is_one_too(self):
        code, out, err = self.main(self.replay_argv(self.root / "nowhere"))
        self.assertEqual((code, out), (tg.REFUSED, ""))
        self.assertIn("Traceback", err)
        self.assertIn("REFUSED: FileNotFoundError: ", err)

    def test_an_interrupt_is_not_caught(self):
        with patch.object(self.grid, "execute",
                          side_effect=KeyboardInterrupt):
            with self.assertRaises(KeyboardInterrupt):
                self.main(["replay"])

    def test_a_record_that_is_not_json_is_refused_by_its_name(self):
        grid = self.root / "grid"
        grid.mkdir()
        (grid / "inventory.json").write_text("{not json")
        code, out, err = self.main(self.replay_argv(grid))
        self.assertEqual((code, err.count("\n")), (tg.REFUSED, 1))
        self.assertRegex(err, "REFUSED: .*inventory.json is not valid JSON")
        self.assertNotIn("Traceback", err)

    def test_a_grid_keeps_its_own_statuses(self):
        argv = self.argv("run", self.root / "pass", "--candidate",
                         CANDIDATE, "--authorize-measurements")
        self.assertEqual(self.main(argv)[0], 0)
        self.candidate = lambda case, size, pairs, seed: (1.04, 1.08)
        argv[2] = str(self.root / "fail")
        self.assertEqual(self.main(argv)[0], 1)
        self.candidate = lambda case, size, pairs, seed: WIDE
        argv[2] = str(self.root / "open")
        self.assertEqual(self.main(argv)[0], 2)


class Logged(unittest.TestCase):
    """The log of a command that must not wait for input."""

    def test_a_child_with_no_standard_input_does_not_wait_for_one(self):
        with tempfile.TemporaryDirectory(prefix="timing-grid-log-") as tmp:
            log = Path(tmp) / "log"
            real, given = subprocess.Popen, []

            def spy(*args, **kw):
                given.append(kw.get("stdin", "not given"))
                return real(*args, **kw)
            with patch.object(subprocess, "Popen", spy):
                found = a.run_logged(
                    ["/bin/sh", "-c", 'read line; echo "read [$line]"'], log,
                    [], 60, stdin=subprocess.DEVNULL)
            self.assertEqual((found["exit"], found["timed_out"]), (0, False))
            self.assertEqual(log.read_text(), "read []\n")
            self.assertEqual(given, [subprocess.DEVNULL])

    def test_a_path_is_a_file_the_child_reads_and_a_log_may_be_appended_to(
            self):
        with tempfile.TemporaryDirectory(prefix="timing-grid-log-") as tmp:
            log, source = Path(tmp) / "log", Path(tmp) / "input"
            source.write_text("from the file\n")
            for stdin in (source, str(source)):
                log.unlink(missing_ok=True)
                found = a.run_logged(
                    ["/bin/sh", "-c", "cat"], log, [], 60, stdin=stdin)
                self.assertEqual((found["exit"], found["timed_out"]),
                                 (0, False))
                self.assertEqual(log.read_text(), "from the file\n")
            # The second command of one log: the end of the file, and
            # without `append` an existing log is refused.
            found = a.run_logged(["/bin/sh", "-c", "echo second"], log, [],
                                 60, stdin=subprocess.DEVNULL, append=True)
            self.assertEqual(log.read_text(), "from the file\nsecond\n")
            self.assertEqual(found["log_hash"], a.seal(log))
            with self.assertRaises(FileExistsError):
                a.run_logged(["/bin/true"], log, [], 60)

    def test_the_default_is_the_inherited_standard_input(self):
        self.assertIsNone(
            inspect.signature(a.run_logged).parameters["stdin"].default)


class Options(Rig):
    def test_the_command_line_names_provenance_and_no_ledger(self):
        parser, sub = self.grid.parser()
        for name in ("run", "extend", "replay"):
            options = {o for action in sub.choices[name]._actions
                       for o in action.option_strings}
            self.assertIn("--pilot", options, name)
            self.assertNotIn("--attempts", options, name)
        options = {o for action in sub.choices["predeclare"]._actions
                   for o in action.option_strings}
        self.assertEqual(options & {"--layout-seed", "--pairs", "--samples"},
                         set())
        self.assertLessEqual({"--revises", "--rescale", "--repilot"}, options)

    def test_prepare_says_it_configures_and_that_its_timeout_is_each_ones(
            self):
        parser, sub = self.grid.parser()
        summary = [x.help for x in sub._choices_actions
                   if x.dest == "prepare"][0]
        self.assertRegex(summary, "configure.*build.*stamp")
        text = " ".join(sub.choices["prepare"].format_help().split())
        self.assertRegex(text, "each of the two commands")

    def test_the_baseline_defaults_to_the_tables(self):
        self.table.baseline = "e" * 40
        parser, sub = self.grid.parser()
        for name in ("pilot", "run"):
            found = [x.default for x in sub.choices[name]._actions
                     if "--baseline" in x.option_strings]
            self.assertEqual(found, ["e" * 40], name)


class Hygiene(Rig):
    """What a stopped run leaves behind is never evidence."""

    def interrupted(self):
        self.explode_at = 4
        with self.assertRaises(RuntimeError):
            self.first()
        self.explode_at = None
        return self.root / "grid"

    def resume(self, out):
        return self.go(self.argv(
            "run", out, "--candidate", CANDIDATE, "--resume",
            "--authorize-measurements"))

    def test_an_unfinished_archive_is_swept_on_resume(self):
        out = self.interrupted()
        for name in ("x.json.partial", "x.json.partial.xz"):
            (out / name).write_text("half")
        status, _ = self.resume(out)
        self.assertEqual(status, 0)
        self.assertEqual(list(out.glob("*.partial*")), [])

    def test_an_unrecorded_archive_is_set_aside_not_trusted(self):
        out = self.interrupted()
        stray = out / ("%s-100.json.xz" % CASES[1])
        stray.write_bytes(b"not a recorded archive")
        status, text = self.resume(out)
        self.assertEqual(status, 0)
        self.assertEqual(text.count("START "), 9)
        self.assertEqual((out / (stray.name + ".unrecorded-1")).read_bytes(),
                         b"not a recorded archive")
        self.assertEqual(self.go(self.replay_argv(out))[0], 0)

    def test_the_archive_appears_only_when_it_is_complete(self):
        calls = []

        def broken(archive, output, real):
            calls.append(Path(archive).name)
            raise RuntimeError("interrupted")
        with self.grid_only(broken), \
                self.assertRaises(RuntimeError):
            self.first()
        out = self.root / "grid"
        self.assertEqual(list(out.glob("*.json.xz")), [])
        self.assertEqual([p.name for p in out.glob("*.partial.xz")],
                         ["%s-0.json.xz.partial.xz" % CASES[0]])
        self.assertEqual(calls, ["%s-0.json.xz.partial.xz" % CASES[0]])


class Helpers(unittest.TestCase):
    def test_protocol_quotes_the_words_of_a_resumption_to_the_byte(self):
        text = " ".join(
            (Path(__file__).with_name("PROTOCOL.md")).read_text().split())
        self.assertIn('"%s"' % " ".join(tg.RESUMING.split()), text)
        self.assertNotIn("a prepare or a commit ends the grid", text)

    def test_set_aside_numbers_its_names(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "c.json.xz"
            for number in (1, 2):
                path.write_text(str(number))
                tg.set_aside(path, "failed")
                self.assertFalse(path.exists())
            self.assertEqual((Path(tmp) / "c.json.xz.failed-1").read_text(),
                             "1")
            self.assertEqual((Path(tmp) / "c.json.xz.failed-2").read_text(),
                             "2")


class Git(unittest.TestCase):
    """The git helpers and the counts commit, on a private repository."""

    def git(self, *args):
        return subprocess.run(
            ["git", "-C", str(self.repo), "-c", "user.name=t", "-c",
             "user.email=t@example.org", *args], check=True, text=True,
            stdout=subprocess.PIPE).stdout.strip()

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="timing-grid-git-")
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        self.git("init", "-q")
        (self.repo / "src").mkdir()
        (self.repo / "src" / "f.txt").write_text("one\n")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "first")
        self.first = self.git("rev-parse", "HEAD")
        (self.repo / "counts.json").write_text("{}\n")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "counts")
        self.second = self.git("rev-parse", "HEAD")
        (self.repo / "other.txt").write_text("x\n")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "later")
        self.third = self.git("rev-parse", "HEAD")
        self.grid = tg.Grid(tg.Table("toy", "TOY", CASES, "d.py",
                                     self.repo / "counts.json",
                                     schedule="ramp"))

    def test_a_blob_is_the_git_object_or_none(self):
        self.assertEqual(tg.git_blob(self.repo, self.third, "src/f.txt"),
                         self.git("hash-object", "src/f.txt"))
        self.assertIsNone(tg.git_blob(self.repo, self.first, "counts.json"))
        with self.assertRaisesRegex(ValueError, "unknown revision"):
            tg.git_blob(self.repo, "f" * 40, "src/f.txt")

    def test_the_introducing_commit_is_the_only_one_to_change_the_file(self):
        self.assertEqual(tg.git_commits(
            self.repo, self.third, "counts.json"), [self.second])
        self.assertEqual(tg.git_introduced(
            self.repo, self.third, "counts.json"), self.second)
        (self.repo / "counts.json").write_text("{\"a\": 1}\n")
        self.git("commit", "-q", "-a", "-m", "revised")
        fourth = self.git("rev-parse", "HEAD")
        self.assertEqual(tg.git_commits(
            self.repo, fourth, "counts.json"), [fourth, self.second])
        # A file committed twice was not fixed at one point: refused.
        with self.assertRaisesRegex(ValueError, "exactly one commit.*not 2"):
            tg.git_introduced(self.repo, fourth, "counts.json")
        # The earlier candidate still has the one commit.
        self.assertEqual(tg.git_introduced(
            self.repo, self.third, "counts.json"), self.second)
        with self.assertRaisesRegex(ValueError, "exactly one commit.*not 0"):
            tg.git_introduced(self.repo, self.first, "counts.json")

    def merged(self, side_file, side_text, how):
        """A side branch from the first commit, merged into the main line
        (which holds the counts file at the second commit)."""
        main = self.git("rev-parse", "--abbrev-ref", "HEAD")
        self.git("reset", "-q", "--hard", self.third)
        self.git("checkout", "-q", "-b", "side", self.first)
        (self.repo / side_file).write_text(side_text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "side")
        self.git("checkout", "-q", main)
        how()
        merge = self.git("rev-parse", "HEAD")
        self.git("branch", "-q", "-D", "side")
        return merge

    def test_a_merge_does_not_hide_or_invent_a_second_commit(self):
        counts = self.repo / "counts.json"
        honest = self.merged("side.txt", "s\n", lambda: self.git(
            "merge", "-q", "--no-ff", "-m", "merge", "side"))
        self.assertEqual(tg.git_commits(self.repo, honest, "counts.json"),
                         [self.second])
        # A side branch that committed the file again and won the merge.
        replaced = self.merged("counts.json", "{\"v\": 2}\n", lambda:
                               self.git("merge", "-q", "--no-ff", "-X",
                                        "theirs", "-m", "merge", "side"))
        self.assertEqual(counts.read_text(), "{\"v\": 2}\n")
        self.assertEqual(len(tg.git_commits(
            self.repo, replaced, "counts.json")), 3)
        with self.assertRaisesRegex(ValueError, "exactly one commit.*not 3"):
            tg.git_introduced(self.repo, replaced, "counts.json")

        # A merge commit that edits the file.
        def edit():
            self.git("merge", "-q", "--no-ff", "--no-commit", "side")
            counts.write_text("{\"evil\": 1}\n")
            self.git("commit", "-q", "-a", "-m", "merge")
        edited = self.merged("side.txt", "s\n", edit)
        self.assertEqual(len(tg.git_commits(
            self.repo, edited, "counts.json")), 2)
        with self.assertRaisesRegex(ValueError, "exactly one commit.*not 2"):
            tg.git_introduced(self.repo, edited, "counts.json")

    def test_the_difference_lists_every_changed_file_below_the_tree(self):
        (self.repo / "src" / "g.txt").write_text("new\n")
        (self.repo / "src" / "f.txt").write_text("two\n")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "tree")
        fourth = self.git("rev-parse", "HEAD")
        self.assertEqual(
            tg.git_difference(self.repo, self.third, fourth, "src"),
            [["A", "src/g.txt"], ["M", "src/f.txt"]])
        self.assertEqual(
            tg.git_difference(self.repo, self.third, fourth, "other.txt"),
            [])

    def test_the_counts_file_must_be_what_the_candidate_holds(self):
        counts = self.repo / "counts.json"
        self.assertEqual(self.grid.counts_commit(
            self.repo, self.third, counts), self.second)
        with self.assertRaisesRegex(ValueError, "not committed"):
            self.grid.counts_commit(self.repo, self.first, counts)
        counts.write_text("{\"edited\": 1}\n")
        with self.assertRaisesRegex(ValueError, "not committed"):
            self.grid.counts_commit(self.repo, self.third, counts)
        outside = Path(self.tmp.name).parent / "elsewhere.json"
        with self.assertRaisesRegex(ValueError, "outside the repository"):
            self.grid.counts_commit(self.repo, self.third, outside)


class RealRecord(unittest.TestCase):
    """`git_seal`, `git_head` and `check_code_record` on a private
    repository, with names below subdirectories, a file the commit lacks,
    and paths outside the repository or relative to another directory."""

    def git(self, *args):
        return subprocess.run(
            ["git", "-C", str(self.repo), "-c", "user.name=t", "-c",
             "user.email=t@example.org", *args], check=True, text=True,
            stdout=subprocess.PIPE).stdout.strip()

    def commit(self, message):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)
        return self.git("rev-parse", "HEAD")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="timing-grid-rec-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.git("init", "-q")
        self.empty_head = tg.git_head(self.repo)
        (self.repo / "sub" / "deep").mkdir(parents=True)
        self.code = self.repo / "sub" / "deep" / "code.py"
        self.code.write_text("one\n")
        self.code_commit = self.commit("code")
        self.was = a.seal(self.code)
        self.counts = self.repo / "sub" / "counts.json"
        self.counts.write_text("{}\n")
        self.counts_commit = self.commit("counts")
        self.code.write_text("two, later\n")
        self.later = self.commit("later")
        outside = self.root / "outside.py"
        outside.write_text("outside\n")
        self.outside = outside
        self.where = {"sub/deep/code.py": self.code}
        self.grid = tg.Grid(tg.Table("toy", "TOY", CASES, "d.py",
                                     self.counts, schedule="ramp"))
        self.grid.replay_paths = lambda: dict(self.where)

    def record(self, **seals):
        return {"files": {}, "code": seals or {
            "sub/deep/code.py": self.was}}

    def check(self, recorded, candidate=None, counts=None):
        return self.grid.check_code_record(
            recorded, self.repo, counts or self.counts, candidate)

    def test_the_seal_of_a_file_below_a_directory_is_that_of_the_commit(self):
        self.assertEqual(tg.git_seal(self.repo, self.code_commit, self.code),
                         self.was)
        self.assertEqual(tg.git_seal(self.repo, self.later, self.code),
                         a.seal(self.code))
        self.assertNotEqual(self.was, a.seal(self.code))

    def test_a_file_the_commit_lacks_has_no_seal(self):
        self.assertIsNone(tg.git_seal(self.repo, self.code_commit,
                                      self.counts))
        self.assertIsNone(tg.git_seal(self.repo, self.later,
                                      self.repo / "sub" / "gone.py"))

    def test_a_path_outside_the_repository_is_refused_in_words(self):
        with self.assertRaisesRegex(ValueError, "outside.py is outside the "
                                    "repository$"):
            tg.git_seal(self.repo, self.later, self.outside)

    def test_the_head_is_the_commit_or_none_in_an_empty_repository(self):
        self.assertEqual(tg.git_head(self.repo), self.later)
        self.assertIsNone(self.empty_head)

    def test_a_record_equal_to_the_commit_of_the_counts_passes(self):
        self.check(self.record(), self.later)
        self.check(self.record(), self.counts_commit)
        self.check(self.record())  # HEAD's history introduced the counts

    def test_a_record_is_compared_by_name_with_the_commit_not_the_code(self):
        now = a.seal(self.code)
        for candidate in (None, self.later):
            with self.subTest(candidate), self.assertRaisesRegex(
                    ValueError, "differs from the commit of the counts: "
                    "sub/deep/code.py; predeclare again at the pilot's "
                    "code, or commit the code change after the counts$"):
                self.check(self.record(**{"sub/deep/code.py": now}),
                           candidate)

    def test_a_file_the_commit_lacks_is_named_as_absent(self):
        self.where["sub/gone.py"] = self.repo / "sub" / "gone.py"
        seal = dict(bytes=1, sha256="0" * 64)
        for candidate in (None, self.later):
            with self.subTest(candidate), self.assertRaisesRegex(
                    ValueError, "counts: sub/gone.py \\(absent\\);"):
                self.check(self.record(**{"sub/gone.py": seal}), candidate)

    def test_a_replay_file_outside_the_repository_is_refused(self):
        self.where["x.py"] = self.outside
        with self.assertRaisesRegex(ValueError, "outside.py is outside the "
                                    "repository"):
            self.check(self.record(**{"x.py": a.seal(self.outside)}),
                       self.later)

    def test_a_relative_counts_path_is_resolved_from_the_directory(self):
        cwd = os.getcwd()
        self.addCleanup(os.chdir, cwd)
        os.chdir(self.repo / "sub")
        self.check(self.record(), self.later, Path("counts.json"))
        os.chdir(self.root)
        self.check(self.record(), self.later,
                   Path("repo") / "sub" / "counts.json")
        self.assertEqual(self.grid.counts_commit(
            self.repo, self.later, Path("repo/sub/counts.json")),
            self.counts_commit)

    def test_counts_outside_the_repository(self):
        elsewhere = self.root / "elsewhere.json"
        elsewhere.write_text("{}\n")
        with self.assertRaisesRegex(
                ValueError, "elsewhere.json is outside the repository .*"
                "repo given by --repo: use the checkout that holds it"):
            self.check(self.record(), self.later, elsewhere)
        # A verification compares the record with the working tree, and
        # says so.
        self.code.write_text("one\n")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.check(self.record(), None, elsewhere)
        self.assertIn("outside the repository", out.getvalue())
        self.code.write_text("two, later\n")
        with contextlib.redirect_stdout(io.StringIO()), \
                self.assertRaisesRegex(
                    ValueError, "differs from the files as they are in the "
                    "working tree: sub/deep/code.py; predeclare again"):
            self.check(self.record(), None, elsewhere)

    def test_uncommitted_counts_are_compared_with_the_working_tree(self):
        new = self.repo / "sub" / "new.json"
        new.write_text("{}\n")
        self.code.write_text("one\n")
        self.check(self.record(), None, new)
        self.code.write_text("two\n")
        with self.assertRaisesRegex(ValueError, "working tree: "
                                    "sub/deep/code.py"):
            self.check(self.record(), None, new)

    def pilot_at(self, head):
        pilot = self.root / "pilot"
        pilot.mkdir(exist_ok=True)
        (pilot / "inventory.json").write_text(
            json.dumps({"checkout": {"head": head}}))
        return pilot

    def pilot_check(self, record, counts, candidate, head, **kw):
        pilot = self.pilot_at(head)
        kw.setdefault("pilot_seal", a.seal(pilot / "inventory.json"))
        self.grid.check_code_record(
            record, self.repo, counts, candidate, pilot, **kw)

    def test_the_code_must_be_that_of_the_pilot_head_too(self):
        # The record equals the commit of the counts (code_commit's code
        # was committed before it), not the later change.
        for head in (self.code_commit, self.counts_commit):
            self.pilot_check(self.record(), self.counts, self.later, head)
        self.code.write_text("two, later\n")
        # A forged record: the seals of the later code, held by a counts
        # commit that follows it; the pilot was at the earlier code.
        forged = self.record(**{"sub/deep/code.py": a.seal(self.code)})
        again = self.repo / "sub" / "again.json"
        again.write_text("{}\n")
        final = self.commit("counts again")
        self.pilot_check(forged, again, final, self.later)
        remedy = ("pilot again, or predeclare at the pilot head's code "
                  "and commit the code change after the counts$")
        with self.assertRaisesRegex(
                ValueError, "the code changed between the follow-up pilot "
                "\\(%s\\) and the counts commit: sub/deep/code.py; %s"
                % (self.code_commit[:12], remedy)):
            self.pilot_check(forged, again, final, self.code_commit)
        # Without a pilot it is not asked.
        self.grid.check_code_record(forged, self.repo, again, final)

    def test_the_pilot_head_is_compared_for_uncommitted_counts_too(self):
        new = self.repo / "sub" / "new.json"
        new.write_text("{}\n")
        self.code.write_text("two, later\n")
        record = self.record(**{"sub/deep/code.py": a.seal(self.code)})
        self.pilot_check(record, new, None, self.later)
        with self.assertRaisesRegex(
                ValueError, "the code changed between the follow-up pilot "
                "\\(%s\\) and the counts: sub/deep/code.py; pilot again, "
                "or predeclare" % self.code_commit[:12]):
            self.pilot_check(record, new, None, self.code_commit)

    def test_the_pilot_is_the_one_the_counts_seal_before_its_head(self):
        seal = a.seal(self.pilot_at(self.code_commit) / "inventory.json")
        # Another pilot (or none given to the counts) is refused as such.
        for wrong in (dict(pilot_seal=dict(seal, bytes=0)),
                      dict(pilot_seal=None)):
            with self.subTest(wrong), self.assertRaisesRegex(
                    ValueError, "is not the pilot of the counts"):
                self.pilot_check(self.record(), self.counts, self.later,
                                 self.code_commit, **wrong)
        # An inventory without a checkout is refused in words, not a
        # KeyError, once it is the sealed one.
        pilot = self.root / "pilot"
        (pilot / "inventory.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "records no checkout head"):
            self.grid.check_code_record(
                self.record(), self.repo, self.counts, self.later, pilot,
                a.seal(pilot / "inventory.json"))
        (pilot / "inventory.json").unlink()
        with self.assertRaisesRegex(ValueError, "no pilot inventory"):
            self.grid.check_code_record(
                self.record(), self.repo, self.counts, self.later, pilot,
                seal)

    def test_a_pilot_head_the_repository_lacks_is_said_so(self):
        with self.assertRaisesRegex(
                ValueError, "the pilot head ffffffffffff is not in this "
                "repository: the pilot must be made at a commit in the "
                "candidate's history$"):
            self.pilot_check(self.record(), self.counts, self.later,
                             "f" * 40)

    def test_the_commit_of_the_counts_must_change_that_file_alone(self):
        (self.repo / "sub" / "more.json").write_text("{}\n")
        self.git("rm", "-q", "--cached", "sub/counts.json")
        self.counts.write_text('{"again": 1}\n')
        # A fresh counts file committed together with a code change.
        again = self.repo / "sub" / "again.json"
        again.write_text("{}\n")
        self.code.write_text("three\n")
        together = self.commit("counts and code")
        for candidate in (None, together):
            with self.subTest(candidate), self.assertRaisesRegex(
                    ValueError, "must change only that file, not also "
                    "sub/counts.json, sub/deep/code.py, sub/more.json: "
                    "commit the counts alone"):
                self.check(self.record(), candidate, again)


class Checkout(unittest.TestCase):
    """The checkout a measurement runs in (checkout_identity), and the ref
    that keeps what was measured, on a private repository shaped like the
    project's: sources, the performance area, and ignored products (the
    executable, the heap, sigobj with links, as `prepare` stamps them)."""

    git = Git.git

    def setUp(self):
        Git.setUp(self)
        perf = self.repo / "src" / "simp" / "tests" / "performance"
        perf.mkdir(parents=True)
        (perf / "p.sml").write_text("val p = 1\n")
        (self.repo / "src" / "a.sml").write_text("val a = 1\n")
        simp = self.repo / "src" / "simp" / "src"
        simp.mkdir(parents=True)
        (simp / "s.sml").write_text("val s = 1\n")
        (self.repo / ".gitignore").write_text(
            "bin/\nsigobj/\n.hol\n.agent-files\n")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "sources")
        self.head = self.git("rev-parse", "HEAD")
        (self.repo / "bin").mkdir()
        self.hol = self.repo / "bin" / "hol"
        self.heap = self.repo / "bin" / "hol.state0"
        self.holmake = self.repo / "bin" / "Holmake"
        self.hol.write_text("executable")
        self.heap.write_text("heap")
        self.holmake.write_text("holmake")
        # sigobj holds links into the built directories, as the real one.
        built = self.repo / "src" / ".hol" / "objs"
        built.mkdir(parents=True)
        (self.repo / "sigobj").mkdir()
        self.product = built / "aTheory.uo"
        self.product.write_text("object")
        self.theory = built / "aTheory.dat"
        self.theory.write_text("theory data")
        self.source = built / "aTheory.sml"
        self.source.write_text("theory source")
        (self.repo / "sigobj" / "aTheory.uo").symlink_to(self.product)
        self.stamp = self.repo / ".agent-files" / "build-stamp.json"
        self.stamp.parent.mkdir()
        self.perf = perf
        self.prepare()

    def prepare(self):
        """What `prepare` writes after a build that succeeded."""
        self.stamp.write_text(json.dumps(tg.build_stamp(self.repo)))

    def identity(self, commit="head"):
        return tg.checkout_identity(
            self.repo, self.head if commit == "head" else commit, self.stamp)

    def test_a_stamped_clean_checkout_at_the_commit_is_the_identity(self):
        found = self.identity()
        stamped = json.loads(self.stamp.read_text())
        self.assertEqual(found, dict(
            head=self.head, tree_outside_performance=tg.git_tree_outside(
                self.repo, self.head), products=stamped["products"]["sha256"]))
        self.assertEqual(self.identity(None), found)
        self.assertEqual(sorted(stamped), ["build", "head", "products",
                                           "tree_outside_performance"])
        self.assertEqual(stamped["head"], self.head)
        self.assertEqual(stamped["build"], list(tg.BUILD))
        # bin/hol, bin/hol.state0, bin/Holmake, one link, one data file and
        # one theory source.
        self.assertEqual(stamped["products"]["files"], 6)
        self.assertEqual(found["products"], stamped["products"]["sha256"])

    def test_the_head_must_be_the_commit_measured(self):
        with self.assertRaisesRegex(ValueError, "not at the commit"):
            self.identity(self.third)

    def test_an_unclean_tree_is_refused(self):
        (self.repo / "src" / "a.sml").write_text("val a = 2\n")
        with self.assertRaisesRegex(ValueError, "not clean"):
            self.identity()

    def test_an_unclean_tree_and_a_bad_stamp_are_unjudged_not_different(
            self):
        # They say nothing of the record, which a grid is dead for.
        (self.repo / "notes.txt").write_text("x")
        with self.assertRaises(tg.CheckoutUnjudged):
            self.identity()
        (self.repo / "notes.txt").unlink()
        stamped = tg.build_stamp(self.repo)
        for label, text in (("none", None), ("text", "not json"),
                            ("build", json.dumps(dict(stamped,
                                                      build=["bin/build"])))):
            with self.subTest(label):
                if text is None:
                    self.stamp.unlink()
                else:
                    self.stamp.write_text(text)
                with self.assertRaises(tg.CheckoutUnjudged):
                    self.identity()
        # A different head, tree or product is a difference.
        self.prepare()
        self.heap.write_text("other")
        for label, commit in (("product", "head"), ("head", self.third)):
            with self.subTest(label):
                with self.assertRaises(ValueError) as caught:
                    self.identity(commit)
                self.assertNotIsInstance(caught.exception,
                                         tg.CheckoutUnjudged)
        self.heap.write_text("heap")
        (self.repo / "src" / "a.sml").write_text("val a = 2\n")
        self.git("commit", "-q", "-a", "-m", "source")
        with self.assertRaises(ValueError) as caught:
            tg.checkout_identity(self.repo, self.git("rev-parse", "HEAD"),
                                 self.stamp)
        self.assertNotIsInstance(caught.exception, tg.CheckoutUnjudged)

    def test_the_head_is_judged_before_the_tree_is_looked_at(self):
        # A head that is not the commit measured is a difference even when
        # the tree is not clean: it is not merely unjudged.
        (self.repo / "notes.txt").write_text("x")
        with self.assertRaises(ValueError) as caught:
            self.identity(self.third)
        self.assertNotIsInstance(caught.exception, tg.CheckoutUnjudged)
        self.assertIn("not at the commit", str(caught.exception))

    def recorded(self):
        found = tg.build_stamp(self.repo)
        return dict(head=found["head"], products=found["products"]["sha256"],
                    tree_outside_performance=found[
                        "tree_outside_performance"])

    def test_a_known_difference_needs_neither_a_clean_tree_nor_the_stamp(
            self):
        recorded = self.recorded()
        self.assertIsNone(tg.known_difference(self.repo, recorded))
        # Untracked files and a missing stamp say nothing.
        (self.repo / "notes.txt").write_text("x")
        self.stamp.unlink()
        self.assertIsNone(tg.known_difference(self.repo, recorded))
        self.assertEqual(tg.tracked_changes(self.repo), [])
        (self.repo / "notes.txt").unlink()
        # Any change of a tracked file does, wherever it is, a documentation
        # file and the performance area included.
        (self.repo / "doc.md").write_text("notes\n")
        self.git("add", "doc.md")
        self.git("commit", "-q", "-m", "doc")
        recorded = self.recorded()
        for label, change, undo in (
                ("source", lambda: (self.repo / "src" / "a.sml").write_text(
                    "val a = 2\n"), lambda: self.git(
                        "checkout", "HEAD", "--", "src/a.sml")),
                ("doc", lambda: (self.repo / "doc.md").write_text("more\n"),
                 lambda: self.git("checkout", "HEAD", "--", "doc.md")),
                ("performance area", lambda: (self.perf / "p.sml")
                 .write_text("val p = 2\n"), lambda: self.git(
                     "checkout", "HEAD", "--", str(self.perf / "p.sml"))),
                ("removed", (self.repo / "doc.md").unlink, lambda:
                 self.git("checkout", "HEAD", "--", "doc.md")),
                ("staged", lambda: (
                    (self.repo / "doc.md").write_text("staged\n"),
                    self.git("add", "doc.md")), lambda: self.git(
                        "checkout", "HEAD", "--", "doc.md"))):
            with self.subTest(label):
                change()
                self.assertRegex(tg.known_difference(self.repo, recorded),
                                 "tracked file.*not the recorded one")
                undo()
                self.assertIsNone(tg.known_difference(self.repo, recorded))

    def test_a_known_difference_of_the_products_comes_before_the_dirt(self):
        recorded = self.recorded()
        self.stamp.unlink()
        (self.repo / "src" / "a.sml").write_text("val a = 2\n")
        self.heap.write_text("other")
        self.assertRegex(tg.known_difference(self.repo, recorded),
                         "products.*not the recorded ones")
        self.heap.write_text("heap")
        self.assertRegex(tg.known_difference(self.repo, recorded),
                         "tracked file")
        self.heap.unlink()
        self.assertRegex(tg.known_difference(self.repo, recorded),
                         "not the recorded ones.*no product")

    def test_a_checkout_without_a_usable_stamp_is_refused(self):
        self.stamp.unlink()
        with self.assertRaisesRegex(ValueError, "no build stamp.*run "
                                    "prepare at this commit"):
            self.identity()
        for what, text in (("text", "not json"), ("list", "[]"),
                           ("keys", json.dumps(dict(head=self.head))),
                           ("no build", json.dumps({k: v for k, v in
                            tg.build_stamp(self.repo).items()
                            if k != "build"}))):
            with self.subTest(what):
                self.stamp.write_text(text)
                with self.assertRaisesRegex(ValueError, "malformed build "
                                            "stamp.*run prepare at this "
                                            "commit"):
                    self.identity()

    def test_a_commit_touching_only_the_performance_area_passes(self):
        # The counts file is committed after the checkout was prepared.
        found = self.identity()
        (self.perf / "counts.json").write_text("{}\n")
        (self.perf / "p.sml").write_text("val p = 2\n")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "counts")
        self.assertEqual(
            tg.checkout_identity(self.repo, self.git("rev-parse", "HEAD"),
                                 self.stamp)["tree_outside_performance"],
            found["tree_outside_performance"])

    def test_a_round_trip_to_the_same_tree_passes(self):
        # Git rewrites the files of a commit it passes through; the content
        # at the end is the same, only the times differ.
        main = self.git("rev-parse", "--abbrev-ref", "HEAD")
        self.git("checkout", "-q", "-b", "side")
        (self.repo / "src" / "a.sml").write_text("val a = 2\n")
        (self.repo / "src" / "simp" / "src" / "s.sml").write_text(
            "val s = 2\n")
        self.git("commit", "-q", "-a", "-m", "side")
        self.git("checkout", "-q", main)
        stamp = self.stamp.read_bytes()
        self.assertEqual(self.identity()["head"], self.head)
        self.assertEqual(self.stamp.read_bytes(), stamp)

    def test_a_touched_heap_passes_for_the_content_is_the_same(self):
        for path in (self.heap, self.hol, self.product):
            os.utime(path, (4_000_000_000, 4_000_000_000))
        for path in (self.repo / "src" / "a.sml", self.perf / "p.sml"):
            os.utime(path, (4_000_000_001, 4_000_000_001))
        self.assertEqual(self.identity()["head"], self.head)

    def test_an_edited_product_is_refused(self):
        sigobj = self.repo / "sigobj"
        for label, change, undo in (
                ("heap", lambda: self.heap.write_text("other"),
                 lambda: self.heap.write_text("heap")),
                ("executable", lambda: self.hol.write_text("other"),
                 lambda: self.hol.write_text("executable")),
                ("linked file", lambda: self.product.write_text("other"),
                 lambda: self.product.write_text("object")),
                ("added file", lambda: (sigobj / "b.ui").write_text("x"),
                 lambda: (sigobj / "b.ui").unlink()),
                ("removed link", lambda: (sigobj / "aTheory.uo").unlink(),
                 lambda: (sigobj / "aTheory.uo").symlink_to(self.product)),
                ("heap removed", self.heap.unlink,
                 lambda: self.heap.write_text("heap")),
                ("Holmake", lambda: self.holmake.write_text("other"),
                 lambda: self.holmake.write_text("holmake")),
                ("theory data", lambda: self.theory.write_text("other"),
                 lambda: self.theory.write_text("theory data")),
                ("added theory data", lambda: (self.product.parent /
                                               "b.dat").write_text("x"),
                 lambda: (self.product.parent / "b.dat").unlink()),
                ("removed theory data", self.theory.unlink,
                 lambda: self.theory.write_text("theory data")),
                ("theory source", lambda: self.source.write_text("other"),
                 lambda: self.source.write_text("theory source")),
                ("added theory source", lambda: (self.product.parent /
                                                 "b.sml").write_text("x"),
                 lambda: (self.product.parent / "b.sml").unlink()),
                ("removed theory source", self.source.unlink,
                 lambda: self.source.write_text("theory source"))):
            with self.subTest(label):
                change()
                with self.assertRaisesRegex(ValueError, "differ from the "
                                            "stamped build.*run prepare at "
                                            "this commit|no product"):
                    self.identity()
                undo()
                self.assertEqual(self.identity()["head"], self.head)

    def test_a_stamp_of_another_build_command_is_refused(self):
        stamped = tg.build_stamp(self.repo)
        for build in (["bin/build", "--seq=tools/sequences/upto-parallel"],
                      [], "bin/build"):
            with self.subTest(build):
                self.stamp.write_text(json.dumps(dict(stamped, build=build)))
                with self.assertRaisesRegex(ValueError, "another build "
                                            "command.*run prepare at this "
                                            "commit"):
                    self.identity()

    def test_a_link_to_a_file_outside_the_repository_is_refused(self):
        outside = Path(tempfile.mkdtemp(prefix="timing-grid-out-"))
        self.addCleanup(shutil.rmtree, outside)
        (outside / "x.uo").write_text("object")
        for label, link, target in (
                ("file", self.repo / "sigobj" / "x.uo", outside / "x.uo"),
                ("directory", self.repo / "sigobj" / "d", outside),
                ("executable", self.hol, outside / "x.uo")):
            with self.subTest(label):
                saved = None
                if link.exists():
                    saved = link.read_text()
                    link.unlink()
                link.symlink_to(target)
                with self.assertRaisesRegex(ValueError, "resolves outside "
                                            "the repository"):
                    tg.products_digest(self.repo)
                link.unlink()
                if saved is not None:
                    link.write_text(saved)
        self.assertEqual(self.identity()["head"], self.head)

    def test_a_dangling_link_in_sigobj_is_refused(self):
        self.product.unlink()
        with self.assertRaisesRegex(ValueError, "no product"):
            self.identity()

    def test_a_source_changed_outside_the_performance_area_is_refused(self):
        for path in ("src/a.sml", "src/simp/src/s.sml"):
            with self.subTest(path):
                (self.repo / path).write_text("val x = 3\n")
                self.git("commit", "-q", "-a", "-m", path)
                with self.assertRaisesRegex(ValueError, "run prepare at "
                                            "this commit"):
                    tg.checkout_identity(
                        self.repo, self.git("rev-parse", "HEAD"),
                        self.stamp)
                # `prepare` stamps this tree, and then it passes.
                self.prepare()
                self.assertEqual(
                    self.identity(self.git("rev-parse", "HEAD"))["head"],
                    self.git("rev-parse", "HEAD"))

    def test_no_file_time_is_read(self):
        # A source newer than the heap (the old check refused it) and a
        # heap older than every source change nothing.
        for path in (self.repo / "src" / "a.sml",
                     self.repo / "src" / "simp" / "src" / "s.sml"):
            os.utime(path, (4_000_000_000, 4_000_000_000))
        os.utime(self.heap, (1_000_000_000, 1_000_000_000))
        self.assertEqual(self.identity()["head"], self.head)

    def test_the_tree_seal_leaves_the_performance_area_out(self):
        before = tg.git_tree_outside(self.repo, self.head)
        (self.perf / "p.sml").write_text("val p = 2\n")
        self.git("commit", "-q", "-a", "-m", "performance only")
        self.assertEqual(tg.git_tree_outside(self.repo, "HEAD"), before)
        (self.repo / "src" / "a.sml").write_text("val a = 2\n")
        self.git("commit", "-q", "-a", "-m", "source")
        self.assertNotEqual(tg.git_tree_outside(self.repo, "HEAD"), before)

    def test_the_measured_commit_is_kept_by_a_ref(self):
        main = self.git("rev-parse", "--abbrev-ref", "HEAD")
        self.git("checkout", "-q", "-b", "candidate")
        (self.repo / "cand.txt").write_text("c\n")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "candidate")
        measured = self.git("rev-parse", "HEAD")
        ref = tg.git_keep(self.repo, "toy", measured)
        self.assertEqual(ref, "refs/performance/toy/" + measured)
        self.git("checkout", "-q", main)
        self.git("branch", "-q", "-D", "candidate")
        self.git("reflog", "expire", "--expire=now", "--all")
        self.git("gc", "-q", "--prune=now")
        self.assertEqual(self.git("rev-parse", ref), measured)
        self.git("cat-file", "-e", measured + "^{commit}")


class Tables(unittest.TestCase):
    def table(self, cases=CASES, **kw):
        kw.setdefault("schedule", "ramp")
        return tg.Table("toy", "TOY", cases, "d.py", "c.json", **kw)

    def test_a_new_table_is_of_the_warmup_schedule(self):
        # The default of the TASK30A validation (PROTOCOL.md): warmup, with
        # headroom 1; ramp, named, keeps headroom 2.
        new = tg.Table("toy", "TOY", CASES, "d.py", "c.json",
                       fixed_seconds=True, seed="s0")
        self.assertEqual((new.schedule, new.headroom), ("warmup", 1))
        old = tg.Table("toy", "TOY", CASES, "d.py", "c.json",
                       fixed_seconds=True, seed="s0", schedule="ramp")
        self.assertEqual((old.schedule, old.headroom), ("ramp", 2))
        self.assertEqual(tg.Table(
            "toy", "TOY", CASES, "d.py", "c.json", fixed_seconds=True,
            seed="s0", headroom=3).headroom, 3)

    def test_the_default_schedule_is_warmup(self):
        self.assertEqual(
            inspect.signature(tg.Table).parameters["schedule"].default,
            "warmup")

    def test_a_table_without_fixed_seconds_names_the_ramp(self):
        # The default schedule is never changed by another argument: the
        # warmup counts follow each cell's predeclared seconds, which only
        # a fixed-seconds table has, so any other table names ramp.
        with self.assertRaisesRegex(ValueError, 'schedule="ramp"'):
            tg.Table("toy", "TOY", CASES, "d.py", "c.json")
        with self.assertRaisesRegex(ValueError, 'schedule="ramp"'):
            tg.Table("toy", "TOY", CASES, "d.py", "c.json",
                     schedule="warmup")
        table = tg.Table("toy", "TOY", CASES, "d.py", "c.json",
                         schedule="ramp")
        self.assertEqual((table.schedule, table.headroom,
                          table.fixed_seconds), ("ramp", 2, False))

    def test_cells_follow_the_matrix_size_sets(self):
        table = self.table()
        self.assertEqual(table.keys(), [(c, s) for c in CASES
                                        for s in SIZES])
        self.assertEqual(table.names()[0], "exclude_empty-0")

    def test_invalid_tables_are_refused(self):
        for label, call in (
                ("unknown case", lambda: self.table(("no_such_case",))),
                ("duplicate", lambda: self.table((CASES[0], CASES[0]))),
                ("seconds", lambda: self.table(seconds=0.01)),
                ("long seconds", lambda: self.table(
                    seconds_by_case={CASES[0]: 61})),
                ("extra seconds", lambda: self.table(
                    seconds_by_case={"exclude_batch": 1.0}))):
            with self.subTest(label), self.assertRaises(ValueError):
                call()

    def test_seconds_per_case(self):
        table = self.table(seconds_by_case={CASES[0]: 1.0},
                           fixed_seconds=True, seed="s0")
        self.assertEqual(table.seconds_for(CASES[0]), 1.0)
        self.assertEqual(table.seconds_for(CASES[1]), 0.3)
        self.assertEqual(table.seconds_map()["exclude_empty-0"], 1.0)
        self.assertEqual(self.table().seconds_map(), {})

    def test_the_engine_is_sealed_unless_a_table_predates_it(self):
        self.assertEqual(self.table().code(),
                         ("driver", "engine", "acceptance"))
        self.assertEqual(self.table(engine=False).code(),
                         ("driver", "acceptance"))


class Hooks(unittest.TestCase):
    def test_a_module_step_is_looked_up_when_called(self):
        class Module:
            STEPS = ("summary",)

            @staticmethod
            def summary(reports):
                return "module"
        engine = tg.Grid(tg.Table("toy", "TOY", CASES, "d.py", "c.json",
                                  schedule="ramp"))
        engine.h = tg.Hooks(Module, engine)
        self.assertEqual(engine.h.summary({}), "module")
        self.assertEqual(engine.h.cell_seconds,
                         engine.cell_seconds)
        Module.summary = staticmethod(lambda reports: "patched")
        self.assertEqual(engine.h.summary({}), "patched")


class Statuses(unittest.TestCase):
    def test_status_code(self):
        self.assertEqual([tg.status_code(dict(status=s)) for s in (
            "pass", "fail", "inconclusive", "blocked")], [0, 1, 2, 2])

    def test_canonical_orders_archived_keys_like_live_ones(self):
        live = {i: i for i in range(12)}
        stored = json.loads(json.dumps(live))
        self.assertEqual(tg.canonical(live), tg.canonical(stored))
        self.assertNotEqual(tg.canonical(live),
                            tg.canonical(dict(stored, **{"3": 4})))

    def test_canonical_ignores_insertion_order_and_sees_content(self):
        self.assertEqual(
            tg.canonical({"b": 1, "a": [2, {"y": 1, "x": 2}]}),
            tg.canonical({"a": [2, {"x": 2, "y": 1}], "b": 1}))
        self.assertNotEqual(tg.canonical({"a": 1}), tg.canonical({"a": 2}))

    def test_checkpoint_replaces_atomically(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "inventory.json"
            tg.checkpoint(path, {"runs": [1]})
            tg.checkpoint(path, {"runs": [1, 2]})
            self.assertEqual(json.loads(path.read_text()), {"runs": [1, 2]})
            self.assertEqual([p.name for p in Path(tmp).iterdir()],
                             ["inventory.json"])


if __name__ == "__main__":
    unittest.main()
