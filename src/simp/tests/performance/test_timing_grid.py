#!/usr/bin/env python3
"""Shared timing grid: cells, counts, resume, replay, second stage, pilot.

Synthetic fixtures only. The acceptance runner and the statistics are
replaced by deterministic stand-ins that build a report exactly as
acceptance.run does (real decisions, real control rule), so the engine's own
logic is what these tests exercise. Nothing is measured and no repository
state is touched: the lock is taken in a throwaway git repository.
"""
import contextlib
import gzip
import io
import json
from pathlib import Path
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
GOOD = (0.99, 1.01)
WIDE = (0.95, 1.06)


def interval_metric(ci, margin=0.03):
    return dict(decision=a.decision(ci[0], ci[1], margin),
                median_paired_ratio=1.0,
                paired_ratio_bootstrap_95_percent=list(ci),
                reason="paired bootstrap", margin=margin)


class Rig(unittest.TestCase):
    """A toy table, its files, a private repository and the stand-ins."""
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
        self.counts = self.root / "toy_iterations.json"
        self.table = self.make_table()
        self.counts.write_text(json.dumps(self.counts_value(self.table)))
        self.grid = tg.Grid(self.table)
        self.runs, self.analyses, self.calls = [], [], 0
        self.control = lambda case, size, pairs, seed: GOOD
        self.candidate = lambda case, size, pairs, seed: GOOD
        self.protocol_failure = lambda case, size: False
        self.explode_at = None
        for target, stand_in in ((a, ("run", self.fake_run)),
                                 (a, ("analyze", self.fake_analyze))):
            patcher = patch.object(target, stand_in[0], stand_in[1])
            patcher.start()
            self.addCleanup(patcher.stop)

    def make_table(self, cases=CASES, **kw):
        options = dict(seconds=0.3, seconds_by_case={CASES[0]: LONG},
                       fixed_seconds=True, pairs=self.pairs,
                       samples=self.samples)
        options.update(kw)
        return tg.Table("toy", "TOY", cases, self.driver, self.counts,
                        **options)

    @staticmethod
    def counts_value(table, **kw):
        keys = table.keys()
        value = dict(schema=table.schema("iterations"), source={},
                     baseline=a.BASE, headroom=2, rule="toy",
                     iterations={"%s-%d" % k: 64 * (1 + i % 3)
                                 for i, k in enumerate(keys)})
        if table.fixed_seconds:
            value["seconds"] = table.seconds_map()
        value.update(kw)
        return value

    # Stand-ins -------------------------------------------------------

    def analysis(self, case, size, control, pairs, seed):
        ci = (self.control if control else self.candidate)(
            case, size, pairs, seed)
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
                             layout_seed)

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
        return [action, "--output", str(out), "--repo", str(self.repo),
                *extra]

    @staticmethod
    def replay_argv(out, *extra):
        return ["replay", "--output", str(out), *extra]

    def go(self, argv, **kw):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = self.grid.main(argv, **kw)
        return code, out.getvalue()

    def first(self, name="grid", extra=(), seed="s0", pairs=None):
        out = self.root / name
        argv = self.argv(
            "run", out, "--candidate", CANDIDATE, "--pairs",
            str(pairs or self.pairs), "--samples", str(self.samples),
            "--authorize-measurements", *extra)
        if seed is not None:
            argv += ["--layout-seed", seed]
        code, text = self.go(argv)
        return out, code, text

    def inventory(self, out):
        return json.loads((out / "inventory.json").read_text())


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
        with self.assertRaisesRegex(ValueError, "needs layout randomiza"):
            self.first(seed=None)
        self.assertEqual(self.calls, 0)
        self.table.require_seed = False
        out, status, _ = self.first(name="unseeded", seed=None)
        self.assertEqual(status, 0)

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
        real = tg.bundle.unpack

        def corrupt(archive, output):
            count = real(archive, output)
            next(Path(output).rglob("evidence.txt")).write_text("x\n")
            return count
        with patch.object(tg.bundle, "unpack", corrupt), \
                self.assertRaisesRegex(ValueError, "transport changed"):
            self.first()

    def test_a_transport_that_loses_a_file_is_refused(self):
        real = tg.bundle.unpack
        with patch.object(tg.bundle, "unpack", lambda archive, output:
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

    def resume(self, out, **kw):
        argv = self.argv(
            "run", out, "--candidate", CANDIDATE, "--pairs", "10",
            "--samples", "3", "--authorize-measurements", "--layout-seed",
            kw.get("seed", "s0"), "--resume")
        return self.go(argv)

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
        with self.assertRaisesRegex(ValueError, "different settings"):
            self.go(self.argv(
                "run", out, "--candidate", CANDIDATE, "--pairs", "20",
                "--samples", "3", "--authorize-measurements",
                "--layout-seed", "s0", "--resume"))
        with self.assertRaisesRegex(ValueError, "different settings"):
            self.resume(out, seed="s1")
        with self.assertRaisesRegex(ValueError, "different settings"):
            self.go(self.argv(
                "run", out, "--candidate", "d" * 40, "--pairs", "10",
                "--samples", "3", "--authorize-measurements",
                "--layout-seed", "s0", "--resume"))

    def test_resume_refuses_changed_counts_and_a_completed_run(self):
        out = self.interrupted()
        value = json.loads(self.counts.read_text())
        value["iterations"]["exclude_empty-0"] *= 2
        self.counts.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError, "changed predeclared"):
            self.resume(out)
        value["iterations"]["exclude_empty-0"] //= 2
        self.counts.write_text(json.dumps(value))
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
            acceptance=a.seal(a.__file__), after=3)])
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
        self.assertEqual(len(self.analyses), 24)
        self.assertEqual({(r["case"], r["size"]): r["seconds"]
                          for r in self.analyses}[(CASES[0], 0)], LONG)
        self.assertEqual({r["iterations"] for r in self.analyses
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
        with self.assertRaisesRegex(ValueError, "differs from predecl"):
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
        out, _, _ = self.first(seed="abc")
        seed = self.inventory(out)["layout_seed"]
        self.assertTrue(seed)
        self.assertEqual({r["seed"] for r in self.analyses}, {seed})
        self.analyses.clear()
        self.go(self.replay_argv(out))
        self.assertEqual(len(self.analyses), 24)
        self.assertEqual({r["seed"] for r in self.analyses}, {seed})

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

    def test_a_grid_without_a_seed_has_no_second_stage(self):
        self.table.require_seed = False
        grid, _, _ = self.first(seed=None)
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
    def setUp(self):
        super().setUp()
        self.launched = []
        patcher = patch.object(a, "run_logged", self.fake_launch)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.max_count = lambda case, size: 2 ** len(str(size))

    def fake_launch(self, command, output, fds, timeout):
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
        # A receipt of the loading fixture carries no counts.
        with gzip.open(folder / "pair-99.json.gz", "wt") as stream:
            json.dump(dict(fixture="loading"), stream)
        Path(output).write_text("log\n")
        return dict(exit=0, timed_out=False)

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
        out_grid, status, _ = self.first()
        self.assertEqual(status, 0)

    def expected(self, case, size):
        count = 1
        while count < 2 * self.max_count(case, size):
            count *= 2
        return count

    def test_predeclare_never_overwrites(self):
        self.pilot()
        out = self.root / "counts.json"
        out.write_text("{}")
        with self.assertRaisesRegex(ValueError, "refusing to overwrite"):
            self.go(["predeclare", "--grid", str(self.root / "pilot"),
                     "--output", str(out)])

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
            self.go(["predeclare", "--grid", str(self.root / "pilot"),
                     "--output", str(self.root / "c.json")])
        path.write_text(json.dumps(good))
        archive = self.root / "pilot" / good["runs"][0]["archive"]
        archive.write_bytes(archive.read_bytes() + b"x")
        with self.assertRaisesRegex(ValueError, "changed archive"):
            self.go(["predeclare", "--grid", str(self.root / "pilot"),
                     "--output", str(self.root / "c.json")])

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
                           fixed_seconds=True)
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
