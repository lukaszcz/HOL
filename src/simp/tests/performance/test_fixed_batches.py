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


if __name__ == "__main__":
    unittest.main()
