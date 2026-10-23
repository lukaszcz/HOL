"""CLI decisions include pointwise gates, slopes, controls and uncertainty."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import acceptance as a
from test_acceptance import repository


class SlopeExitTests(unittest.TestCase):
    def execute(self, *, candidate_slope=4, control_slope=4, sizes=a.SIZES,
                zero=False, nonmonotonic=False):
        def analyzed(folder, **options):
            size = options["size"]
            control = str(folder).endswith("-control")
            baseline = 100000 + 4 * size
            slope = control_slope if control else candidate_slope
            candidate = (100000 if control else 10) + slope * size
            if zero:
                baseline = candidate = 10
            if nonmonotonic:
                baseline = candidate = 100000 - size
            stats = a.paired_statistics([
                {"baseline": baseline, "candidate": candidate}
                for _ in range(10)])
            return dict(case="storage_graph", size=size, metrics={
                "cpu": {"decision": "pass"},
                "compiled_increment_words": copy.deepcopy(stats),
                "fragment_increment_words": copy.deepcopy(stats)})

        with tempfile.TemporaryDirectory(prefix="task28-slope-exit-") as d:
            root = Path(d)
            pin = repository(root / "repo")
            output = root / "out"
            args = ["run", "--repo", str(root / "repo"),
                    "--candidate", pin, "--case", "storage_graph",
                    "--pairs", "10", "--samples", "3",
                    "--batch-seconds", "0.1", "--authorize-measurements",
                    "--output", str(output)]
            for size in sizes:
                args += ["--size", str(size)]
            with patch.object(a, "negative_controls", return_value={}), \
                    patch.object(a, "run_logged", return_value={"exit": 0}), \
                    patch.object(a, "analyze", side_effect=analyzed), \
                    patch("builtins.print"):
                status = a.main(args)
            report = json.loads((output / "acceptance.json").read_text())
        self.assertTrue(report["success"])
        return status, report

    def test_pointwise_pass_does_not_hide_failed_slopes(self):
        status, report = self.execute(candidate_slope=5)
        self.assertEqual(status, 1)
        self.assertEqual({m["decision"] for r in report["workloads"]
                          for m in r["candidate"]["metrics"].values()},
                         {"pass"})
        failures = [r for r in report["retained_scaling"]["adjacent_intervals"]
                    if r["selection"] == "candidate"
                    and r["words_per_rule"]["decision"] == "fail"]
        self.assertEqual(len(failures), 10)

    def test_every_gate_passes(self):
        self.assertEqual(self.execute()[0], 0)

    def test_failed_slope_control_blocks_candidate_parity(self):
        status, report = self.execute(control_slope=5)
        self.assertEqual(status, 2)
        candidates = [r["words_per_rule"] for r in report[
            "retained_scaling"]["adjacent_intervals"]
            if r["selection"] == "candidate"]
        self.assertEqual({r["decision"] for r in candidates}, {"inconclusive"})
        self.assertEqual({r["control_decision"] for r in candidates}, {"fail"})

    def test_control_never_excuses_candidate_slope_failure(self):
        self.assertEqual(self.execute(candidate_slope=5, control_slope=5)[0], 1)

    def test_missing_grid_is_not_pass(self):
        status, report = self.execute(sizes=(10,))
        self.assertEqual(status, 2)
        self.assertEqual(report["retained_scaling"]["status"], "blocked")

    def test_zero_and_nonmonotonic_slopes_are_not_pass(self):
        self.assertEqual(self.execute(zero=True)[0], 2)
        self.assertEqual(self.execute(nonmonotonic=True)[0], 2)

    def test_control_uncertainty_cannot_establish_parity(self):
        for decision in ("fail", "inconclusive"):
            for candidate in ("pass", "fail", "inconclusive"):
                data = {"decision": candidate}
                a.apply_control(data, {"decision": decision})
                self.assertEqual(data["decision"], "fail" if candidate ==
                                 "fail" else "inconclusive")
                self.assertEqual(data["control_decision"], decision)

    def test_failure_takes_precedence_over_blocked_slope(self):
        report = dict(success=True, retained_scaling={"status": "blocked"},
                      workloads=[{"candidate": {"metrics": {
                          "cpu": {"decision": "fail"}}}}])
        self.assertEqual(a.report_exit_status(report), 1)
        report["success"] = False
        self.assertEqual(a.report_exit_status(report), 2)


if __name__ == "__main__":
    unittest.main()
