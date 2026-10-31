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
import contextlib
import gzip
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
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
GOOD = (0.99, 1.01)
WIDE = (0.95, 1.06)


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
                (tg, ("checkout_identity", self.fake_checkout)))

    def make_table(self, cases=CASES, **kw):
        options = dict(seconds=0.3, seconds_by_case={CASES[0]: LONG},
                       fixed_seconds=True, pairs=self.pairs,
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
                    t.pilot_pairs, t.pilot_samples, t.seed, t.sealed))
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

    def fake_checkout(self, repo, commit=None):
        """The checkout is clean and at the commit measured."""
        self.bound.append(commit)
        return dict(head=commit or COMMIT,
                    tree_outside_performance=self.fake_tree(repo, commit))

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
                layout_seed=None):
        self.analyses.append(dict(
            case=case, size=size, control=candidate == baseline,
            pairs=pairs, samples=samples, seconds=seconds,
            iterations=iterations, seed=layout_seed, policy=policy))
        return self.analysis(case, size, candidate == baseline, pairs,
                             layout_seed, pilot=iterations is None)

    def fake_launch(self, command, output, fds, timeout):
        """A pilot process: both sides the baseline, two develop receipts
        with calibration counts, and one of the loading fixture."""
        self.launched.append(command)
        folder = Path(command[command.index("--output") + 1])
        case = command[command.index("--performance-case") + 1]
        size = int(command[command.index("--performance-size") + 1])
        folder.mkdir(parents=True)
        for pair in range(2):
            receipt = dict(fixture="performance", measurements=dict(
                workloads={case: dict(calibration=[
                    dict(iterations=1),
                    dict(iterations=self.max_count(case, size) // (
                        1 + pair))])}))
            with gzip.open(folder / ("pair-%02d.json.gz" % pair), "wt") as w:
                json.dump(receipt, w)
        with gzip.open(folder / "pair-99.json.gz", "wt") as stream:
            json.dump(dict(fixture="loading"), stream)
        (folder / "manifest.json").write_text(json.dumps(dict(selections={
            side: dict(revision=self.pilot_revision)
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
            code = self.grid.main(argv, **kw)
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
        self.assertEqual(self.bound, [None])
        self.assertEqual(self.inventory(self.root / "pilot")["checkout"],
                         dict(head=COMMIT, tree_outside_performance="t" * 64))

    def test_a_pilot_in_a_checkout_that_is_not_clean_measures_nothing(self):
        def unclean(repo, commit=None):
            raise ValueError("harness checkout is not clean: commit first")
        with patch.object(tg, "checkout_identity", unclean):
            with self.assertRaisesRegex(ValueError, "not clean"):
                self.pilot()
        self.assertEqual(self.launched, [])
        self.assertFalse((self.root / "pilot").exists())

    def test_a_resumed_pilot_is_of_the_same_checkout(self):
        self.interrupted()

        def elsewhere(repo, commit=None):
            return dict(head="e" * 40, tree_outside_performance="t" * 64)
        with patch.object(tg, "checkout_identity", elsewhere):
            with self.assertRaisesRegex(ValueError, "different settings"):
                self.pilot(extra=("--resume",))
        self.assertEqual(self.pilot(extra=("--resume",))[0], 0)

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

    def test_the_command_line_has_no_ledger_option(self):
        with self.assertRaises(SystemExit), \
                contextlib.redirect_stderr(io.StringIO()):
            self.go(self.run_argv() + ["--attempts", str(self.attempts)])

    def test_a_malformed_ledger_is_refused_before_any_cell(self):
        for i, text in enumerate(("not json\n", "[1]\n",
                                  '{"no": "event"}\n')):
            with self.subTest(text):
                self.attempts.write_text(text)
                with self.assertRaisesRegex(ValueError, "malformed attempts"):
                    self.first(name="g%d" % i)
        self.assertEqual(self.calls, 0)

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

    def test_replay_prints_every_attempt_of_the_candidate(self):
        self.candidate = lambda case, size, pairs, seed: (1.04, 1.08)
        one, _, _ = self.first(name="one")
        self.candidate = lambda case, size, pairs, seed: GOOD
        two, _, _ = self.first(name="two")
        status, text = self.go(self.replay_argv(two))
        self.assertEqual(status, 0)
        self.assertIn("ATTEMPTS of %s: 2 in the ledger (4 records, chain "
                      "intact)" % CANDIDATE, text)
        mine = [x for x in text.splitlines() if x.startswith("ATTEMPT ")]
        self.assertEqual(len(mine), 2)
        self.assertRegex(mine[0], r" first opened \S+ resumed 0 status fail$")
        self.assertRegex(mine[1], r" resumed 0 status pass \(this grid\)$")
        self.assertIn(self.inventory(two)["attempt"], mine[1])

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
                         tg.ledger_hash('{"event": "op'))
        self.assertEqual(json.loads(text[3])["prev"],
                         tg.ledger_hash(text[1]))
        status, text = self.go(self.replay_argv(out))
        self.assertEqual(status, 0)
        self.assertNotIn("LEDGER-TORN-LINE", text)
        self.assertIn("ATTEMPTS of %s: 2 in the ledger" % CANDIDATE, text)

    def test_a_cut_line_is_refused_when_it_is_not_the_last(self):
        out, _, _ = self.first()
        before = self.attempts.read_text()
        for what, text in (("terminated", before + '{"event": "op\n'),
                           ("unacknowledged", before + '{"event": "op\n' +
                            before)):
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
                     pin_history={"0" * 64: {}})
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
                     revisions=("c2.json",))
        with self.assertRaisesRegex(ValueError, "repeated counts file"):
            self.make_table(revisions=(self.counts,))


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
        self.assertEqual(self.bound, [CANDIDATE])
        self.assertEqual(self.inventory(out)["checkout"], dict(
            head=CANDIDATE, tree_outside_performance="t" * 64))

    def test_a_checkout_that_is_not_the_candidate_measures_nothing(self):
        def elsewhere(repo, commit=None):
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
        self.assertEqual(self.bound, [CANDIDATE, CANDIDATE])

        def other_tree(repo, commit=None):
            return dict(head=commit, tree_outside_performance="u" * 64)
        calls = self.calls
        with patch.object(tg, "checkout_identity", other_tree):
            with self.assertRaisesRegex(ValueError, "not the one the first"):
                self.go(self.extend_argv(grid, "again"))
        self.assertEqual(self.calls, calls)
        self.assertFalse((self.root / "again").exists())

    def test_replay_sees_a_checkout_that_is_not_the_recorded_one(self):
        out, _, _ = self.first()
        path = out / "inventory.json"
        recorded = json.loads(path.read_text())
        good = recorded["checkout"]
        for label, value in (
                ("head", dict(good, head="e" * 40)),
                ("tree", dict(good, tree_outside_performance="u" * 64)),
                ("keys", dict(good, extra=1)),
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


class Chain(Rig):
    """The operator's whole sequence on a real repository, with git, the
    checkout and the ledger as they are, and only the measurement faked:
    pilot at X, predeclare, the counts committed as Y, run, extend and
    replay of both stages."""

    def git(self, *args):
        return subprocess.run(
            ["git", "-C", str(self.repo), "-c", "user.name=t", "-c",
             "user.email=t@example.org", *args], check=True, text=True,
            stdout=subprocess.PIPE).stdout.strip()

    def git_stand_ins(self):
        return ()

    def make_table(self, **kw):
        """The repository as it is at X: the sources, and a heap built after
        them that git ignores."""
        if not hasattr(self, "base"):
            perf = self.repo / "src" / "simp" / "tests" / "performance"
            perf.mkdir(parents=True)
            (perf / "p.sml").write_text("val p = 1\n")
            for name in ("one", "two"):
                (self.repo / "src" / (name + ".sml")).write_text(
                    "val %s = 1\n" % name)
            (self.repo / ".gitignore").write_text("bin/\n")
            (self.repo / ".git" / "info" / "exclude").write_text(
                ".agent-files\n")
            self.git("add", "-A")
            self.git("commit", "-q", "-m", "X")
            self.base = self.git("rev-parse", "HEAD")
            (self.repo / "bin").mkdir()
            (self.repo / "bin" / "hol.state0").write_text("heap")
            self.pilot_revision = self.base
        kw.setdefault("baseline", self.base)
        kw.setdefault("ledger", None)
        return super().make_table(**kw)

    def provision(self):
        self.make_pilot(self.pilot_dir)
        code, _ = self.go(["predeclare", "--grid", str(self.pilot_dir),
                           "--output", str(self.counts)])
        self.assertEqual(code, 0)
        self.launched.clear()
        self.analyses.clear()

    def commit_counts(self):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "Y: the counts")
        self.candidate_commit = self.git("rev-parse", "HEAD")
        return self.candidate_commit

    def run_at(self, commit, name="grid", *extra):
        return self.go(self.argv("run", self.root / name, "--candidate",
                                 commit, "--authorize-measurements",
                                 *extra))

    def test_pilot_predeclare_commit_run_extend_and_replay(self):
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
        self.assertIn("ATTEMPTS of %s: 2 in the ledger" % y, text)
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
        os.utime(self.repo / "bin" / "hol.state0")
        with self.assertRaisesRegex(ValueError, "not clean"):
            self.run_at(y)
        self.assertEqual(self.calls, 0)

    def test_a_heap_older_than_a_source_is_refused(self):
        y = self.commit_counts()
        old = (self.repo / "bin" / "hol.state0").stat().st_mtime - 100
        os.utime(self.repo / "bin" / "hol.state0", (old, old))
        with self.assertRaisesRegex(ValueError, "heap is older"):
            self.run_at(y)
        self.assertEqual(self.calls, 0)

    def test_a_counts_file_committed_twice_is_refused(self):
        self.commit_counts()
        self.counts.write_text(self.counts.read_text() + "\n")
        self.git("commit", "-q", "-a", "-m", "again")
        with self.assertRaisesRegex(ValueError, "exactly one commit"):
            self.run_at(self.git("rev-parse", "HEAD"))
        self.assertEqual(self.calls, 0)


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
                                     self.repo / "counts.json"))

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


class Checkout(unittest.TestCase):
    """The checkout a measurement runs in (checkout_identity), and the ref
    that keeps what was measured, on a private repository shaped like the
    project's: sources, the performance area, and an ignored heap."""

    git = Git.git

    def setUp(self):
        Git.setUp(self)
        perf = self.repo / "src" / "simp" / "tests" / "performance"
        perf.mkdir(parents=True)
        (perf / "p.sml").write_text("val p = 1\n")
        (self.repo / "src" / "a.sml").write_text("val a = 1\n")
        (self.repo / ".gitignore").write_text("bin/\n")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "sources")
        self.head = self.git("rev-parse", "HEAD")
        (self.repo / "bin").mkdir()
        self.heap = self.repo / "bin" / "hol.state0"
        self.heap.write_text("heap")
        self.perf = perf

    def age(self, path, seconds):
        stamp = self.heap.stat().st_mtime + seconds
        os.utime(path, (stamp, stamp))

    def test_a_clean_checkout_at_the_commit_with_a_fresh_heap(self):
        self.age(self.repo / "src" / "a.sml", -10)
        found = tg.checkout_identity(self.repo, self.head)
        self.assertEqual(found, dict(
            head=self.head, tree_outside_performance=tg.git_tree_outside(
                self.repo, self.head)))
        self.assertEqual(tg.checkout_identity(self.repo), found)
        # A file of the performance area changed after the heap was built
        # is no reason: the heap does not read it.
        self.age(self.perf / "p.sml", 10)
        self.assertEqual(tg.checkout_identity(self.repo, self.head), found)

    def test_the_head_must_be_the_commit_measured(self):
        self.age(self.repo / "src" / "a.sml", -10)
        with self.assertRaisesRegex(ValueError, "not at the commit"):
            tg.checkout_identity(self.repo, self.third)

    def test_an_unclean_tree_is_refused(self):
        self.age(self.repo / "src" / "a.sml", -10)
        (self.repo / "src" / "a.sml").write_text("val a = 2\n")
        self.age(self.repo / "src" / "a.sml", -10)
        with self.assertRaisesRegex(ValueError, "not clean"):
            tg.checkout_identity(self.repo, self.head)

    def test_a_missing_heap_is_refused(self):
        self.heap.unlink()
        with self.assertRaisesRegex(ValueError, "no heap"):
            tg.checkout_identity(self.repo, self.head)

    def test_a_heap_older_than_a_source_is_refused(self):
        self.age(self.repo / "src" / "a.sml", 10)
        with self.assertRaisesRegex(ValueError, "heap is older than "
                                    "src/a.sml"):
            tg.checkout_identity(self.repo, self.head)

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
        return tg.Table("toy", "TOY", cases, "d.py", "c.json", **kw)

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
        engine = tg.Grid(tg.Table("toy", "TOY", CASES, "d.py", "c.json"))
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
