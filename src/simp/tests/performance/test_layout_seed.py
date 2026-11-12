#!/usr/bin/env python3
"""Code-layout randomization: symmetric, replayable, bound to every launch."""
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import acceptance as a
import audit_evidence as ae
import performance_schema as ps
import task29a_grid as grid
import test_archive_provenance as fixtures


class LayoutUnits(unittest.TestCase):
    def test_deterministic_and_in_range(self):
        for pair in range(40):
            for side in ("baseline", "candidate"):
                units = ps.layout_units("s1", pair, side)
                self.assertEqual(units, ps.layout_units("s1", pair, side))
                self.assertTrue(0 <= units < ps.LAYOUT_UNITS)

    def test_sides_and_seeds_draw_independently(self):
        draws = {side: [ps.layout_units("s1", i, side) for i in range(40)]
                 for side in ("baseline", "candidate")}
        self.assertNotEqual(draws["baseline"], draws["candidate"])
        self.assertGreater(len(set(draws["baseline"])), 20)
        self.assertNotEqual(draws["baseline"],
                            [ps.layout_units("s2", i, "baseline")
                             for i in range(40)])

    def test_rejects_bad_keys(self):
        for seed in ("", "a b", "x" * 65, None, 7, "s/1"):
            with self.subTest(seed=seed), self.assertRaises(ValueError):
                ps.layout_units(seed, 0, "baseline")
        for pair, side in ((-1, "baseline"), (True, "baseline"),
                           (0, "control"), ("0", "candidate")):
            with self.subTest(pair=pair), self.assertRaises(ValueError):
                ps.layout_units("s1", pair, side)

    def test_suite_options_bind_seed_and_range(self):
        base = dict(suite="matrix", case="frag_create", size=0)
        ps.suite_options(dict(base, layout_seed="s1",
                              layout_units=ps.LAYOUT_UNITS))
        for extra in (dict(layout_seed="s1"),
                      dict(layout_seed="s1", layout_units=64),
                      dict(layout_units=ps.LAYOUT_UNITS),
                      dict(layout_seed="", layout_units=ps.LAYOUT_UNITS)):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                ps.suite_options(dict(base, **extra))
        with self.assertRaises(ValueError):
            ps.suite_options(dict(suite="traversal", layout_seed="s1",
                                  layout_units=ps.LAYOUT_UNITS))


class Binding(unittest.TestCase):
    def test_archive_binds_layout_environment(self):
        fixture = fixtures.ArchiveProvenance(
            "test_complete_archive_reaches_acceptance_automatically")
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        manifest, receipt = fixture.manifest, fixture.receipt
        ae.audit(manifest, receipt)
        manifest["performance"].update(layout_seed="s1",
                                       layout_units=ps.LAYOUT_UNITS)
        with self.assertRaisesRegex(ValueError, "layout randomization"):
            ae.audit(manifest, receipt)
        units = ps.layout_units("s1", receipt["pair"], receipt["selection"])
        receipt["environment"]["PERF_LAYOUT"] = str(units)
        ae.audit(manifest, receipt)
        receipt["environment"]["PERF_LAYOUT"] = str(units + 1)
        with self.assertRaisesRegex(ValueError, "layout randomization"):
            ae.audit(manifest, receipt)
        del manifest["performance"]["layout_seed"]
        del manifest["performance"]["layout_units"]
        with self.assertRaisesRegex(ValueError, "layout randomization"):
            ae.audit(manifest, receipt)
        del receipt["environment"]["PERF_LAYOUT"]
        ae.audit(manifest, receipt)
        manifest["performance"].update(layout_seed="s1",
                                       layout_units=ps.LAYOUT_UNITS)
        fixture.fixture.persist()
        with self.assertRaisesRegex(ValueError, "randomization seed"):
            fixture.fixture.analyze()

    def test_frontend_propagates_seed_to_both_experiments(self):
        with tempfile.TemporaryDirectory() as tmp:
            args = argparse.Namespace(
                pairs=10, samples=3, batch_seconds=0.3, batch_iterations=64,
                layout_seed="s1", timeout=100, baseline=a.BASE,
                candidate="a" * 40, authorize_measurements=True,
                case=["compile_collector"], size=[10000],
                output=Path(tmp) / "result", mode="isolated",
                repo=a.HERE.parents[3], build_manifest=None)

            def result(*args, **kwargs):
                return dict(metrics={"cpu": dict(decision="inconclusive")})
            with patch.object(a, "negative_controls", return_value={}), \
                    patch.object(a, "run_logged", return_value=dict(exit=0)) \
                    as launch, patch.object(a, "analyze", side_effect=result) \
                    as analyze:
                report = a.run(args)
            self.assertTrue(report["success"], report)
            for call in launch.call_args_list:
                command = call.args[0]
                index = command.index("--layout-seed")
                self.assertEqual(command[index + 1], "s1")
            self.assertEqual([c.kwargs["layout_seed"] for c in
                              analyze.call_args_list], ["s1", "s1"])

    def test_grid_check_report_passes_seed(self):
        report = dict(success=True, policy=a.EQUIVALENCE_POLICY,
                      retained_scaling=None, workloads=[])
        with patch.object(a, "analyze", side_effect=ValueError("stop")) \
                as analyze, self.assertRaisesRegex(ValueError, "stop"):
            grid.check_report(Path("unused"), report, "b", "c", 0.3,
                              "frag_create", 0, 64, layout_seed="s1")
        self.assertEqual(analyze.call_args.kwargs["layout_seed"], "s1")

    def test_runner_rejects_seed_outside_matrix(self):
        runner = a.HERE.parent / "compatibility/run_paired.py"
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "unused"
            for flags in (["--layout-seed", "s1"],
                          ["--matrix-performance", "--performance-pairs", "1",
                           "--performance-case", "frag_create",
                           "--performance-size", "0",
                           "--layout-seed", "bad seed"]):
                command = [sys.executable, "-B", str(runner),
                           "--candidate", "HEAD",
                           "--candidate-signature", "pass",
                           "--candidate-behavior", "baseline",
                           "--output", str(output), *flags]
                result = subprocess.run(command, capture_output=True,
                                        text=True, timeout=10)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn("are required", result.stderr)
                if flags[0] == "--layout-seed":
                    self.assertIn("--layout-seed requires "
                                  "--matrix-performance", result.stderr)
                self.assertFalse(output.exists())

    def test_runner_pads_before_any_dependency(self):
        text = (a.HERE.parent / "compatibility/paired/runner.sml").read_text()
        self.assertEqual(text.count("layoutPadding ();"), 1)
        self.assertLess(text.index("layoutPadding ();"),
                        text.index('Meta.loadPlan tracedUse "CheckSupport"'))
        self.assertIn('OS.Process.getEnv "PERF_LAYOUT"', text)


if __name__ == "__main__":
    unittest.main()
