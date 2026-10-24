#!/usr/bin/env python3
"""A policy review is a blocker receipt, not a rule change or runtime pass."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import acceptance as a
import policy_review as p


class ContractReviewTests(unittest.TestCase):
    def test_examples_preserve_every_pair_and_undefined_ratio(self):
        report = p.examples()
        for name in ("zero_over_zero", "positive_over_zero"):
            row = report[name]
            self.assertEqual(row["decision"], "inconclusive")
            self.assertEqual(row["paired_ratios"], [None] * 10)
            self.assertIsNone(row["paired_ratio_bootstrap_95_percent"])
            self.assertEqual(len(row["observations"]), 10)

    def test_more_zero_pairs_cannot_define_a_ratio(self):
        for count in (10, 20, 100):
            rows = [{"baseline": 0, "candidate": 0}] * count
            result = a.paired_statistics(rows)
            self.assertEqual(result["decision"], "inconclusive")
            self.assertEqual(len(result["paired_ratios"]), count)
            self.assertIsNone(result["paired_ratio_bootstrap_95_percent"])

    def test_one_zero_denominator_is_already_sufficient(self):
        for index in range(10):
            rows = [{"baseline": 1, "candidate": 0} for _ in range(10)]
            rows[index]["baseline"] = 0
            result = a.paired_statistics(rows)
            self.assertEqual(result["decision"], "inconclusive")
            self.assertIsNone(result["paired_ratios"][index])
            self.assertEqual(result["observations"], rows)

    def test_precise_straddling_is_not_admitted_or_called_instability(self):
        report = p.examples()
        row = report["precise_equality_straddling"]
        low, high = row["paired_ratio_bootstrap_95_percent"]
        self.assertLess(low, 1)
        self.assertGreater(high, 1)
        self.assertLess(high - low, 3e-6)
        self.assertEqual(row["decision"], "inconclusive")
        self.assertNotIn("instability", row["reason"])
        faster = report["faster_with_uncertain_control"]
        self.assertEqual(faster["decision"], "inconclusive")
        self.assertEqual(faster["reason"], "baseline-control inconclusive")
        self.assertEqual(report["slower_with_uncertain_control"]["decision"],
                         "fail")

    def test_b_b_not_an_absolute_impossibility(self):
        row = p.examples()["exact_positive_equality"]
        self.assertEqual(row["paired_ratio_bootstrap_95_percent"], [1, 1])
        self.assertEqual(row["decision"], "pass")


class ArchivedReviewTests(unittest.TestCase):
    def test_actual_archive_re_admitted_not_just_summary_read(self):
        result = p.zero_cell(p.GRID)
        self.assertEqual(result["measured_samples"], 120)
        self.assertEqual(len(result["processes"]), 40)
        for experiment in ("control", "candidate"):
            processes = [r for r in result["processes"] if
                         r["experiment"] == experiment]
            self.assertEqual({(r["pair"], r["selection"]) for r in processes},
                             {(i, s) for i in range(10) for s in
                              ("baseline", "candidate")})
            metric = result["gc_metrics"][experiment]
            self.assertEqual(metric["paired_ratios"], [None] * 10)
            self.assertEqual(metric["decision"], "inconclusive")
        for process in result["processes"]:
            self.assertEqual([s["sample"] for s in process["samples"]],
                             [0, 1, 2])
            self.assertTrue(all(s["gc"] == 0 for s in process["samples"]))

    def test_changed_archive_and_duplicate_cell_reject(self):
        original = a.load(p.GRID / "inventory.json")
        row, = [r for r in original["runs"] if
                (r["case"], r["size"]) == ("compile_single", 0)]
        changed = copy.deepcopy(original)
        changed["runs"].append(copy.deepcopy(row))
        with patch.object(a, "load", return_value=changed):
            with self.assertRaisesRegex(ValueError, "duplicate reviewed cell"):
                p.zero_cell(p.GRID)
        changed = copy.deepcopy(original)
        reviewed, = [r for r in changed["runs"] if
                     (r["case"], r["size"]) == ("compile_single", 0)]
        reviewed["seal"]["sha256"] = "0" * 64
        with patch.object(a, "load", return_value=changed):
            with self.assertRaisesRegex(ValueError,
                                        "changed reviewed archive"):
                p.zero_cell(p.GRID)

    def test_failed_review_leaves_no_receipt(self):
        with tempfile.TemporaryDirectory(prefix="policy-failure-test-") as tmp:
            output = Path(tmp) / "absent.json"
            with patch.object(sys, "argv", ["policy_review.py", "--output",
                                           str(output)]), patch.object(
                    p, "review", side_effect=ValueError("bad archive")):
                with self.assertRaisesRegex(ValueError, "bad archive"):
                    p.main()
            self.assertFalse(output.exists())

    def test_output_cannot_replace_an_existing_receipt(self):
        with tempfile.TemporaryDirectory(prefix="policy-output-test-") as tmp:
            output = Path(tmp) / "existing.json"
            output.write_text('{"preserve": true}\n')
            run = subprocess.run([
                sys.executable, "-B", str(p.HERE / "policy_review.py"),
                "--output", str(output)], capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0)
            self.assertEqual(json.loads(output.read_text()),
                             {"preserve": True})
            self.assertIn("FileExistsError", run.stderr)


if __name__ == "__main__":
    unittest.main()
