#!/usr/bin/env python3
"""Scope, completeness and blocked-admission controls for TASK29."""
import copy
import unittest
from unittest.mock import patch
from pathlib import Path

import task29_gate as gate


class Task29Gate(unittest.TestCase):
    def reports(self):
        return {key: {"success": False, "workloads": [],
                      "failure": "deliberate failed process"}
                for key in gate.keys()}

    def test_exact_scope(self):
        self.assertEqual(len(gate.CASES), 27)
        self.assertEqual(len(gate.keys()), 162)
        for case, size in gate.keys():
            self.assertEqual(gate.get_case(case, size),
                             "MatrixPerformance.sml")
        self.assertEqual(gate.SIZES, (0, 1, 10, 100, 1000, 10000))

    def test_missing_and_extra_rejected(self):
        for key in gate.keys():
            reports = self.reports()
            del reports[key]
            with self.assertRaisesRegex(ValueError, "incomplete TASK29"):
                gate.summary(reports)
        reports = self.reports()
        reports["exclude_missing", 100] = reports[gate.keys()[0]]
        with self.assertRaisesRegex(ValueError, "incomplete TASK29"):
            gate.summary(reports)

    def test_failed_processes_not_passed(self):
        result = gate.summary(self.reports())
        self.assertEqual(result["status"], "blocked")
        self.assertIn("no supported cumulative", result["allocation"])
        self.assertEqual(len(result["workloads"]), 162)
        for row in result["workloads"]:
            self.assertFalse(row["protocol"])
            self.assertEqual(row["exit"], 2)
            self.assertIn("failed process", row["unresolved"])

    def test_uncertainty_and_failure_preserved(self):
        reports = self.reports()
        metric = dict(decision="inconclusive", median_paired_ratio=1.0,
                      paired_ratio_bootstrap_95_percent=[0.99, 1.01],
                      reason="baseline-control inconclusive")
        key = gate.keys()[0]
        row = dict(case=key[0], size=key[1], metrics={"cpu": metric})
        report = dict(success=True, workloads=[{
            "candidate": copy.deepcopy(row), "control": copy.deepcopy(row)}],
                      retained_scaling=None)
        reports[key] = report
        result = gate.summary(reports)
        self.assertEqual(result["workloads"][0]["exit"], 2)
        self.assertEqual(result["workloads"][0]["metrics"]["cpu"], metric)
        metric = report["workloads"][0]["candidate"]["metrics"]["cpu"]
        metric.update(decision="fail", reason="paired bootstrap",
                      paired_ratio_bootstrap_95_percent=[1.001, 1.002])
        result = gate.summary(reports)
        self.assertEqual(result["workloads"][0]["exit"], 1)
        self.assertEqual(result["status"], "blocked")

    def test_live_and_archived_runtime_keys_replay_identically(self):
        # JSON object keys stringify integer pair IDs. Both representations
        # must replay, without modifying original reports or observations.
        result = dict(metrics={"cpu": {"decision": "pass"}},
                      runtime_by_pair={0: {"baseline": "snapshot"}})
        control = copy.deepcopy(result)
        candidate = copy.deepcopy(result)
        gate.a.apply_control(candidate["metrics"]["cpu"],
                             control["metrics"]["cpu"])
        report = dict(success=True, workloads=[dict(
            control=control, candidate=candidate)], retained_scaling=None)
        original = copy.deepcopy(report)
        with patch.object(gate.a, "analyze", side_effect=[
                copy.deepcopy(result), copy.deepcopy(result)]):
            gate.check_report(Path("unused"), report, "base", "candidate",
                              0.3, "frag_create", 0)
        self.assertEqual(report, original)
        archived = gate.json.loads(gate.json.dumps(report))
        with patch.object(gate.a, "analyze", side_effect=[
                copy.deepcopy(result), copy.deepcopy(result)]):
            gate.check_report(Path("unused"), archived, "base", "candidate",
                              0.3, "frag_create", 0)

    def test_wrong_binding_and_unexplained_failure_rejected(self):
        reports = self.reports()
        reports[gate.keys()[0]] = dict(success=True, workloads=[{
            "candidate": dict(case="compile_batch", size=0,
                              metrics={"cpu": {"decision": "pass"}})}])
        with self.assertRaisesRegex(ValueError, "wrong workload binding"):
            gate.summary(reports)
        with self.assertRaisesRegex(ValueError, "unexplained"):
            gate.check_report(None, {"success": False}, None, None,
                              None, None, None)


if __name__ == "__main__":
    unittest.main()
