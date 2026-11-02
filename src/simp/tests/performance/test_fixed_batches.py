#!/usr/bin/env python3
"""Equal operation counts without relaxing timing/consumption/admission gates."""
import argparse
import copy
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import acceptance as a
import audit_evidence as ae
import performance_schema as ps
import runtime_metrics as rm
import test_archive_provenance as fixtures


class FixedBatchTests(unittest.TestCase):
    def events(self, count=4):
        def times(n, wall=0.25):
            return f"{wall},0.20,0.01,0.02,0.005,0.22,0.015,0.02,{n}"
        events = [["observation", "timer.accounting", times(5)],
                  ["check", "timer accounting", "pass"],
                  ["check", "workload inputs", "pass"]]
        n, sink = 1, 5
        while n <= count:
            # Every calibration already exceeds the time target. Fixed mode
            # must still do ALL doublings, identically in both selections.
            events.append(["observation", "calibration.frag_create",
                           f"{n}," + times(n)])
            sink += n
            n *= 2
        for i in range(3):
            events += [["observation", "batch.frag_create",
                        f"{i},{count}," + times(count)],
                       ["check", "results frag_create", "pass"]]
            sink += count
        return events + [["observation", "sink", str(sink)]]

    def validate(self, events, count=4):
        options = ps.suite_options(dict(suite="matrix", case="frag_create",
                                        size=0, batch_iterations=count))
        return ps.validate(events, 3, 0.2, **options)

    def test_full_common_calibration_even_after_target(self):
        _, result = self.validate(self.events())
        workload = result["workloads"]["frag_create"]
        self.assertEqual([r["iterations"] for r in workload["calibration"]],
                         [1, 2, 4])
        self.assertEqual([r["iterations"] for r in workload["batches"]],
                         [4, 4, 4])

    def test_adaptive_mode_cannot_admit_fixed_history(self):
        with self.assertRaises(ValueError):
            ps.validate(self.events(), 3, 0.2, labels=("frag_create",),
                        consumed={"frag_create": 1}, storage=False)

    def test_missing_extra_reordered_and_wrong_counts(self):
        original = self.events()
        mutations = [original[:4] + original[5:],
                     original[:5] + original[4:5] + original[5:],
                     original[:3] + [original[4], original[3]] + original[5:]]
        for index, replacement in ((5, "2"), (6, "0,2")):
            events = copy.deepcopy(original)
            parts = events[index][-1].split(",")
            parts[:len(replacement.split(","))] = replacement.split(",")
            events[index][-1] = ",".join(parts)
            mutations.append(events)
        for events in mutations:
            with self.subTest(events=events), self.assertRaises(ValueError):
                self.validate(events)
        with self.assertRaises(ValueError):
            self.validate(original, count=8)

    def test_duration_and_consumption_guards_still_apply(self):
        for index, field, value in ((5, 1, "0.01"), (6, 2, "0.01"),
                                    (5, -1, "3"), (6, -1, "3")):
            events = self.events()
            fields = events[index][-1].split(",")
            fields[field] = value
            events[index][-1] = ",".join(fields)
            with self.subTest(index=index, field=field):
                with self.assertRaises(ValueError):
                    self.validate(events)

    def test_count_bounds_and_types(self):
        for count in (0, -1, 3, 2**30 + 1, 2**31, True, "4", 4.0, None):
            with self.subTest(count=count), self.assertRaises(ValueError):
                ps.suite_options(dict(suite="matrix", case="frag_create",
                                      size=0, batch_iterations=count))
        for count in (1, 4, 2**30):
            self.assertEqual(ps.batch_iterations(count), count)
        with self.assertRaises(ValueError):
            ps.suite_options(dict(suite="traversal", batch_iterations=4))

    def test_archive_binds_environment_and_requested_count(self):
        fixture = fixtures.ArchiveProvenance(
            "test_complete_archive_reaches_acceptance_automatically")
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        manifest, receipt = fixture.manifest, fixture.receipt
        # Existing synthetic archive has count=1. The optional fixed mode
        # must leave its observations unchanged, but bind every launch.
        manifest["performance"]["batch_iterations"] = 1
        with self.assertRaisesRegex(ValueError, "iteration environment"):
            ae.audit(manifest, receipt)
        receipt["environment"]["PERF_ITERATIONS"] = "1"
        ae.audit(manifest, receipt)
        receipt["environment"]["PERF_ITERATIONS"] = "2"
        with self.assertRaisesRegex(ValueError, "iteration environment"):
            ae.audit(manifest, receipt)
        del manifest["performance"]["batch_iterations"]
        with self.assertRaisesRegex(ValueError, "iteration environment"):
            ae.audit(manifest, receipt)
        del receipt["environment"]["PERF_ITERATIONS"]
        ae.audit(manifest, receipt)
        manifest["performance"]["batch_iterations"] = 1
        fixture.fixture.persist()
        with self.assertRaisesRegex(ValueError, "predeclared batch"):
            fixture.fixture.analyze()

    def test_frontend_propagates_same_count_to_both_experiments(self):
        # Dispatch-only control: synthetic analyses, no HOL timings claimed.
        with tempfile.TemporaryDirectory() as tmp:
            args = argparse.Namespace(
                pairs=10, samples=3, batch_seconds=0.3, batch_iterations=64,
                timeout=100, baseline=a.BASE, candidate="a" * 40,
                authorize_measurements=True, case=["compile_collector"],
                size=[10000], output=Path(tmp) / "result", mode="isolated",
                repo=a.HERE.parents[3], build_manifest=None)
            def result(*args, **kwargs):
                return dict(metrics={"cpu": dict(decision="inconclusive")})
            with patch.object(a, "negative_controls", return_value={}), \
                    patch.object(a, "run_logged", return_value=dict(exit=0)) \
                    as launch, patch.object(a, "analyze", side_effect=result) \
                    as analyze:
                report = a.run(args)
            self.assertTrue(report["success"], report)
            self.assertEqual(launch.call_count, 2)
            for call in launch.call_args_list:
                command = call.args[0]
                index = command.index("--batch-iterations")
                self.assertEqual(command[index + 1], "64")
            self.assertEqual([c.kwargs["iterations"] for c in
                              analyze.call_args_list], [64, 64])

    def test_runner_rejects_invalid_mode_before_creating_output(self):
        runner = a.HERE.parent / "compatibility/run_paired.py"
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "unused"
            for flags in (["--batch-iterations", "4"],
                          ["--matrix-performance", "--performance-pairs", "1",
                           "--performance-case", "frag_create",
                           "--performance-size", "0",
                           "--batch-iterations", "3"]):
                command = [sys.executable, "-B", str(runner),
                           "--output", str(output), *flags]
                result = subprocess.run(command, capture_output=True,
                                        text=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(output.exists())


class WarmupScheduleTests(unittest.TestCase):
    """The warmup schedule: one batch of N, then the samples of N."""
    options = dict(suite="matrix", case="frag_create", size=0,
                   batch_schedule="warmup")

    def events(self, count=5, warm_wall=0.25, sample_wall=0.25, samples=3):
        def times(n, wall):
            return f"{wall},0.20,0.01,0.02,0.005,0.22,0.015,0.02,{n}"
        events = [["observation", "timer.accounting", times(5, 0.25)],
                  ["check", "timer accounting", "pass"],
                  ["check", "workload inputs", "pass"],
                  ["observation", "warmup.frag_create",
                   f"{count}," + times(count, warm_wall)]]
        for i in range(samples):
            events += [["observation", "batch.frag_create",
                        f"{i},{count}," + times(count, sample_wall)],
                       ["check", "results frag_create", "pass"]]
        return events + [["observation", "sink",
                          str(5 + count * (samples + 1))]]

    def validate(self, events, count=5, **extra):
        options = ps.suite_options(dict(self.options, batch_iterations=count,
                                        **extra))
        return ps.validate(events, 3, 0.2, **options)

    def test_one_warm_up_batch_of_any_count_then_the_samples(self):
        for count in (1, 3, 5, 1000, 2 ** 30):
            with self.subTest(count=count):
                _, result = self.validate(self.events(count), count)
                workload = result["workloads"]["frag_create"]
                self.assertEqual([r["iterations"] for r in
                                  workload["calibration"]], [count])
                self.assertEqual([r["iterations"] for r in
                                  workload["batches"]], [count] * 3)
                self.assertEqual(workload["schedule"], "warmup")

    def test_the_ramp_records_name_no_schedule(self):
        _, result = FixedBatchTests().validate(FixedBatchTests().events())
        self.assertNotIn("schedule", result["workloads"]["frag_create"])
        options = ps.suite_options(dict(suite="matrix", case="frag_create",
                                        size=0, batch_iterations=4))
        self.assertNotIn("schedule", options)
        self.assertEqual(ps.suite_options(dict(
            self.options, batch_iterations=3))["schedule"], "warmup")

    def test_the_warm_up_and_every_sample_must_last_half_the_target(self):
        # The target is 0.2 s: 0.1 s passes, less fails closed.
        self.validate(self.events(warm_wall=0.1, sample_wall=0.1))
        with self.assertRaisesRegex(ValueError, "warm-up batch too short"):
            self.validate(self.events(warm_wall=0.0999))
        with self.assertRaisesRegex(ValueError, "batch too short"):
            self.validate(self.events(sample_wall=0.0999))

    def test_the_warm_up_is_neither_missing_extra_nor_reordered(self):
        original = self.events()
        warm = original[3]
        sample = original[4:6]
        mutations = [original[:3] + original[4:],
                     original[:3] + [warm, copy.deepcopy(warm)] + original[4:],
                     original[:3] + sample + [warm] + original[6:],
                     [e if e is not warm else ["observation",
                      "calibration.frag_create", warm[2]] for e in original]]
        for events in mutations:
            with self.subTest(events=events), self.assertRaises(ValueError):
                self.validate(events)
        for field, value in ((0, "4"), (-1, "4")):
            events = copy.deepcopy(original)
            fields = events[3][-1].split(",")
            fields[field] = value
            events[3][-1] = ",".join(fields)
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.validate(events)
        with self.assertRaises(ValueError):
            self.validate(original, count=6)

    def test_the_two_schedules_do_not_mix(self):
        ramp = FixedBatchTests()
        with self.assertRaises(ValueError):
            self.validate(ramp.events(), 4)  # ramp events, warmup option
        with self.assertRaises(ValueError):
            ramp.validate(self.events(4), 4)  # warm-up events, ramp option
        with self.assertRaises(ValueError):
            ramp.validate(self.events(5), 5)  # and not a power of two
        # The validator itself needs a count with a schedule.
        with self.assertRaises(ValueError):
            ps.validate(self.events(), 3, 0.2, labels=("frag_create",),
                        consumed={"frag_create": 1}, storage=False,
                        schedule="warmup")

    def test_option_bounds_and_forms(self):
        for count in (0, -1, 2 ** 30 + 1, True, "4", 4.0, None):
            with self.subTest(count=count), self.assertRaises(ValueError):
                ps.suite_options(dict(self.options, batch_iterations=count))
        for count in (1, 3, 2 ** 30):
            self.assertEqual(ps.batch_iterations(count, "warmup"), count)
        for schedule in ("ramp", "Warmup", "", 1, False):
            with self.subTest(schedule=schedule), self.assertRaises(
                    ValueError):
                ps.suite_options(dict(self.options, batch_iterations=4,
                                      batch_schedule=schedule))
        with self.assertRaises(ValueError):
            ps.suite_options(self.options)  # no fixed count
        with self.assertRaises(ValueError):
            ps.suite_options(dict(self.options, suite="traversal",
                                  batch_iterations=4))
        self.assertEqual(ps.batch_schedule(None), "ramp")
        self.assertEqual(ps.batch_schedule("warmup"), "warmup")

    def test_archive_binds_the_schedule_environment(self):
        fixture = fixtures.ArchiveProvenance(
            "test_complete_archive_reaches_acceptance_automatically")
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        manifest, receipt = fixture.manifest, fixture.receipt
        for event in receipt["result"]["events"]:
            if event[:2] == ["observation", "calibration.frag_create"]:
                event[1] = "warmup.frag_create"
        options = manifest["performance"]
        options.update(batch_iterations=1, batch_schedule="warmup")
        observations, data = ps.validate(
            receipt["result"]["events"], 3, 0.2, **ps.suite_options(options))
        receipt["result"]["observations"] = observations
        receipt["measurements"] = data
        receipt["runtime"] = rm.validate(
            receipt["diagnostics"], data)
        receipt["environment"].update(PERF_ITERATIONS="1",
                                      PERF_SCHEDULE="warmup")
        ae.audit(manifest, receipt)
        # The schedule is bound in both directions.
        del receipt["environment"]["PERF_SCHEDULE"]
        with self.assertRaisesRegex(ValueError, "batch schedule environment"):
            ae.audit(manifest, receipt)
        receipt["environment"]["PERF_SCHEDULE"] = "ramp"
        with self.assertRaisesRegex(ValueError, "batch schedule environment"):
            ae.audit(manifest, receipt)
        receipt["environment"]["PERF_SCHEDULE"] = "warmup"
        del options["batch_schedule"]
        with self.assertRaisesRegex(ValueError, "batch schedule environment"):
            ae.audit(manifest, receipt)
        del receipt["environment"]["PERF_SCHEDULE"]
        with self.assertRaises(ValueError):
            ae.audit(manifest, receipt)  # warm-up events, ramp options
        options["batch_schedule"] = "warmup"
        with self.assertRaisesRegex(ValueError, "batch schedule environment"):
            ae.audit(manifest, receipt)

    def test_ramp_archives_refuse_a_schedule_environment(self):
        fixture = fixtures.ArchiveProvenance(
            "test_complete_archive_reaches_acceptance_automatically")
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        manifest, receipt = fixture.manifest, fixture.receipt
        ae.audit(manifest, receipt)
        receipt["environment"]["PERF_SCHEDULE"] = "warmup"
        with self.assertRaisesRegex(ValueError, "batch schedule environment"):
            ae.audit(manifest, receipt)

    def test_analysis_must_match_the_requested_schedule(self):
        fixture = fixtures.ArchiveProvenance(
            "test_complete_archive_reaches_acceptance_automatically")
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        fixture.fixture.options["schedule"] = "warmup"
        with self.assertRaisesRegex(ValueError, "batch schedule"):
            fixture.fixture.analyze()
        fixture.fixture.options["schedule"] = None
        fixture.manifest["performance"]["batch_schedule"] = "warmup"
        fixture.fixture.persist()
        with self.assertRaisesRegex(ValueError, "batch schedule"):
            fixture.fixture.analyze()

    def args(self, tmp, **extra):
        return argparse.Namespace(
            pairs=10, samples=3, batch_seconds=0.3, batch_iterations=63,
            batch_schedule="warmup", timeout=100, baseline=a.BASE,
            candidate="a" * 40, authorize_measurements=True,
            case=["compile_collector"], size=[10000],
            output=Path(tmp) / "result", mode="isolated",
            repo=a.HERE.parents[3], build_manifest=None, **extra)

    def test_frontend_propagates_the_schedule_to_both_experiments(self):
        with tempfile.TemporaryDirectory() as tmp:
            def result(*args, **kwargs):
                return dict(metrics={"cpu": dict(decision="inconclusive")})
            with patch.object(a, "negative_controls", return_value={}), \
                    patch.object(a, "run_logged", return_value=dict(exit=0)) \
                    as launch, patch.object(a, "analyze", side_effect=result) \
                    as analyze:
                report = a.run(self.args(tmp))
            self.assertTrue(report["success"], report)
            self.assertEqual(launch.call_count, 2)
            for call in launch.call_args_list:
                command = call.args[0]
                self.assertEqual(command[command.index(
                    "--batch-schedule") + 1], "warmup")
                self.assertEqual(command[command.index(
                    "--batch-iterations") + 1], "63")
            self.assertEqual([c.kwargs["schedule"] for c in
                              analyze.call_args_list], ["warmup"] * 2)
            self.assertEqual([c.kwargs["iterations"] for c in
                              analyze.call_args_list], [63, 63])

    def test_the_ramp_command_names_no_schedule(self):
        args = argparse.Namespace(baseline=a.BASE, pairs=10, samples=3,
                                  batch_seconds=0.3, timeout=100,
                                  repo=a.HERE.parents[3])
        command = a.matrix_command(args, "frag_create", 0, "a" * 40,
                                   Path("out"), 64, "seed", None)
        self.assertNotIn("--batch-schedule", command)
        command = a.matrix_command(args, "frag_create", 0, "a" * 40,
                                   Path("out"), 63, "seed", "warmup")
        self.assertEqual(command[command.index("--batch-schedule") + 1],
                         "warmup")

    def test_a_schedule_needs_a_fixed_count(self):
        with tempfile.TemporaryDirectory() as tmp:
            args = self.args(tmp)
            args.batch_iterations = None
            with self.assertRaisesRegex(ValueError, "fixed batch count"):
                a.run(args)
            args = self.args(tmp)
            args.batch_iterations = 0
            with self.assertRaises(ValueError):
                a.run(args)
            self.assertFalse(args.output.exists())

    def test_runner_rejects_a_schedule_without_a_count_or_a_bad_count(self):
        runner = a.HERE.parent / "compatibility/run_paired.py"
        base = ["--matrix-performance", "--performance-pairs", "1",
                "--performance-case", "frag_create",
                "--performance-size", "0"]
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "unused"
            for flags in (["--batch-schedule", "warmup"],
                          ["--batch-schedule", "other",
                           "--batch-iterations", "3"],
                          ["--batch-schedule", "warmup",
                           "--batch-iterations", "0"],
                          ["--batch-schedule", "warmup",
                           "--batch-iterations", str(2 ** 30 + 1)]):
                command = [sys.executable, "-B", str(runner),
                           "--output", str(output), *base, *flags]
                result = subprocess.run(command, capture_output=True,
                                        text=True, timeout=10)
                self.assertNotEqual(result.returncode, 0, flags)
                self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
