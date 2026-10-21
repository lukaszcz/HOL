"""Fail closed on changed cases/callbacks, not just count differences."""
import copy
import unittest
from pathlib import Path
from unittest.mock import patch

import prior_contracts as prior
import coverage_ledger as coverage
from run_paired import InvalidRun, require

HERE = Path(__file__).resolve().parent


class PriorTests(unittest.TestCase):
    def test_historical_counts(self):
        for fixture, count in prior.COUNTS.items():
            stream = prior.historical(HERE, fixture)
            self.assertEqual(count, sum(s.endswith("OK") and not
                             s.startswith("OBS ") for s in stream))

    def run_stream(self, stream):
        # Use a tiny synthetic oracle, never normalize expected failures.
        with patch.object(prior, "historical", return_value=[
                "one ... OK", "OBS callback=before", "two ... OK"]), \
             patch.dict(prior.COUNTS, {"fixture": 2}):
            return prior.validate(HERE, "fixture", stream, require)

    def test_complete(self):
        self.run_stream("one ... OK\nOBS callback=before\ntwo ... OK\n"
                        "fixture completed ... OK\n")

    def test_missing_case(self):
        with self.assertRaisesRegex(InvalidRun, "case count"):
            self.run_stream("OBS callback=before\ntwo ... OK\n"
                            "fixture completed ... OK\n")

    def test_same_count_wrong_case(self):
        with self.assertRaisesRegex(InvalidRun, "changed ordered"):
            self.run_stream("other ... OK\nOBS callback=before\ntwo ... OK\n"
                            "fixture completed ... OK\n")

    def test_moved_callback(self):
        with self.assertRaisesRegex(InvalidRun, "changed ordered"):
            self.run_stream("OBS callback=before\none ... OK\ntwo ... OK\n"
                            "fixture completed ... OK\n")

    def test_changed_warning(self):
        with self.assertRaisesRegex(InvalidRun, "changed ordered"):
            self.run_stream("one ... OK\nOBS callback=before\n"
                            "<<HOL warning: changed>>\ntwo ... OK\n"
                            "fixture completed ... OK\n")

    def test_interleaved_native_monitor(self):
        self.assertEqual(prior.semantic_stream(
            "a label ... [42]: trace line\n[43]: another trace\nOK\n"),
            ["a label ... OK"])
        self.assertEqual(prior.semantic_stream("a label ... never completed\n"),
                         [])

    def test_no_completion(self):
        with self.assertRaisesRegex(InvalidRun, "completion"):
            self.run_stream("one ... OK\nOBS callback=before\ntwo ... OK\n")

    def test_timing_only(self):
        self.assertEqual(prior.semantic_stream("one ... \b\b(0.123s) OK\n"),
                         ["one ... OK"])
        self.assertEqual(prior.semantic_stream("OBS time=(0.123s)\n"),
                         ["OBS time=(0.123s)"])

    def test_failure_even_with_complete_stream(self):
        with self.assertRaisesRegex(InvalidRun, "assertion failed"):
            self.run_stream("FAILED!\none ... OK\nOBS callback=before\n"
                            "two ... OK\nfixture completed ... OK\n")


class LedgerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ledger = coverage.receipt(HERE / "coverage-ledger.json.gz")

    def test_source_binding(self):
        coverage.verify(self.ledger)

    def test_same_count_changed_label(self):
        altered = copy.deepcopy(self.ledger)
        altered["suites"]["traversal"]["cases"][0]["label"] = "replacement"
        with self.assertRaisesRegex(InvalidRun, "labels/order"):
            coverage.verify(altered)

    def test_lost_source_anchor(self):
        altered = copy.deepcopy(self.ledger)
        altered["suites"]["traversal"]["cases"][0]["sources"] = []
        with self.assertRaisesRegex(InvalidRun, "unmapped case"):
            coverage.verify(altered)

    def test_stale_source(self):
        altered = copy.deepcopy(self.ledger)
        next(iter(altered["sources"].values()))["sha256"] = "wrong"
        with self.assertRaisesRegex(InvalidRun, "stale source"):
            coverage.verify(altered)


if __name__ == "__main__":
    unittest.main()
