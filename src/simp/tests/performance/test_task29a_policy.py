#!/usr/bin/env python3
"""TASK29A equivalence policy: margin gate, control window, GC reporting."""
import copy
import json
import os
from pathlib import Path
import random
import tempfile
import unittest
from unittest.mock import patch

import acceptance as a
import task29a_grid as grid

V2 = a.EQUIVALENCE_POLICY
MARGIN = V2["margin"]


def pairs(ratios):
    return [{"baseline": 1.0, "candidate": r} for r in ratios]


def stats(ratios, metric="cpu"):
    margin, gated = a.timing_rule(V2, metric)
    return a.paired_statistics(pairs(ratios), margin, gated)


class Decision(unittest.TestCase):
    def test_margin_boundaries(self):
        self.assertEqual(a.decision(0.99, 1 + MARGIN, MARGIN), "pass")
        self.assertEqual(a.decision(0.99, 1.031, MARGIN), "inconclusive")
        self.assertEqual(a.decision(1 + MARGIN, 1.05, MARGIN), "inconclusive")
        self.assertEqual(a.decision(1.031, 1.05, MARGIN), "fail")

    def test_v1_rule_and_records_unchanged(self):
        # Historical archives recompute byte-identically under POLICY.
        self.assertEqual(a.decision(0.99, 1.0), "pass")
        self.assertEqual(a.decision(0.99, 1.001), "inconclusive")
        self.assertEqual(a.decision(1.001, 1.01), "fail")
        self.assertEqual(a.timing_rule(a.POLICY, "gc"), (0.0, True))
        old = a.paired_statistics(pairs([1.0] * 10))
        self.assertNotIn("margin", old)
        self.assertNotIn("gated", old)
        self.assertIsNone(a.POLICY["budgets"])
        self.assertNotIn("version", a.POLICY)

    def test_neutral_candidate_can_pass(self):
        # The reason for the policy change: under v1 a candidate equal to
        # the baseline is almost always inconclusive.
        rng = random.Random(29)
        v1 = v2 = 0
        for _ in range(200):
            ratios = [rng.lognormvariate(0, 0.01) for _ in range(10)]
            v1 += a.paired_statistics(pairs(ratios))["decision"] == "pass"
            v2 += stats(ratios)["decision"] == "pass"
        self.assertLess(v1, 20)
        self.assertGreater(v2, 190)

    def test_slowdown_beyond_margin_fails(self):
        self.assertEqual(stats([1.05] * 10)["decision"], "fail")
        self.assertEqual(stats([5.0] * 10)["decision"], "fail")

    def test_zero_denominator_stays_inconclusive(self):
        zero = a.paired_statistics([{"baseline": 0, "candidate": 0}] * 10,
                                   MARGIN)
        self.assertEqual(zero["decision"], "inconclusive")
        self.assertIsNone(zero["paired_ratio_bootstrap_95_percent"])


class Control(unittest.TestCase):
    def test_window(self):
        inside = stats([0.98, 1.02] * 5)
        for ratios, valid in (([0.98, 1.02] * 5, True),
                              ([1.0] * 10, True),
                              ([0.96, 1.0] * 5, False),
                              ([1.0, 1.04] * 5, False)):
            data = copy.deepcopy(inside)
            a.apply_control(data, stats(ratios))
            self.assertEqual(data["control_valid"], valid, ratios)
            self.assertEqual(data["decision"],
                             "pass" if valid else "inconclusive")

    def test_null_control_interval_blocks_pass(self):
        data = stats([1.0] * 10)
        control = a.paired_statistics(
            [{"baseline": 0, "candidate": 0}] * 10, MARGIN)
        a.apply_control(data, control)
        self.assertFalse(data["control_valid"])
        self.assertEqual(data["decision"], "inconclusive")

    def test_invalid_control_never_excuses_failure(self):
        data = stats([1.1] * 10)
        a.apply_control(data, stats([0.9, 1.1] * 5))
        self.assertEqual(data["decision"], "fail")

    def test_storage_words_keep_exact_rule(self):
        words = a.paired_statistics(pairs([1.0] * 10))
        a.apply_control(words, a.paired_statistics(pairs([1.0, 1.001] * 5)))
        self.assertEqual(words["decision"], "inconclusive")
        self.assertNotIn("control_valid", words)


class Reporting(unittest.TestCase):
    def report(self, cpu, wall, gc):
        metrics = {"cpu": stats(cpu), "wall": stats(wall, "wall"),
                   "gc": stats(gc, "gc")}
        control = {"cpu": stats([1.0] * 10), "wall": stats([1.0] * 10, "wall"),
                   "gc": stats([2.0] * 10, "gc")}
        for name, value in metrics.items():
            a.apply_control(value, control[name])
        return dict(success=True, policy=V2, retained_scaling=None,
                    workloads=[{"candidate": {"metrics": metrics}}])

    def test_gc_reported_not_gated(self):
        report = self.report([1.0] * 10, [1.0] * 10, [1.6] * 10)
        gc = report["workloads"][0]["candidate"]["metrics"]["gc"]
        self.assertEqual(gc["decision"], "reported")
        self.assertIs(gc["gated"], False)
        self.assertEqual(gc["control_decision"], "reported")
        self.assertEqual(a.report_exit_status(report), 0)

    def test_cpu_and_wall_still_gate(self):
        self.assertEqual(a.report_exit_status(
            self.report([1.05] * 10, [1.0] * 10, [1.0] * 10)), 1)
        self.assertEqual(a.report_exit_status(
            self.report([1.0] * 10, [1.0, 1.06] * 5, [1.0] * 10)), 2)

    def test_reported_requires_ungated(self):
        report = self.report([1.0] * 10, [1.0] * 10, [1.0] * 10)
        del report["workloads"][0]["candidate"]["metrics"]["gc"]["gated"]
        with self.assertRaisesRegex(ValueError, "invalid decisions"):
            a.report_exit_status(report)


class Grid(unittest.TestCase):
    def row(self, decision):
        metric = dict(decision=decision, median_paired_ratio=1.0,
                      paired_ratio_bootstrap_95_percent=[0.99, 1.01],
                      reason="paired bootstrap")
        return dict(success=True, retained_scaling=None, workloads=[{
            "candidate": dict(metrics={"cpu": metric}),
            "control": dict(metrics={"cpu": metric})}])

    def reports(self, decision="pass"):
        result = {}
        for case, size in grid.gate.keys():
            report = self.row(decision)
            for side in ("candidate", "control"):
                report["workloads"][0][side].update(case=case, size=size)
                if case == "storage_graph":
                    words = a.paired_statistics([
                        {"baseline": 1000 + 4 * size,
                         "candidate": 1000 + 4 * size}] * 10)
                    report["workloads"][0][side]["metrics"].update(
                        compiled_increment_words=copy.deepcopy(words),
                        fragment_increment_words=copy.deepcopy(words))
            result[case, size] = report
        return result

    def test_status(self):
        self.assertEqual(grid.summary(self.reports())["status"], "pass")
        reports = self.reports()
        key = grid.gate.keys()[5]
        reports[key] = self.row("inconclusive")
        reports[key]["workloads"][0]["candidate"].update(
            case=key[0], size=key[1])
        self.assertEqual(grid.summary(reports)["status"], "inconclusive")
        reports[key]["workloads"][0]["candidate"]["metrics"]["cpu"][
            "decision"] = "fail"
        decisions = grid.summary(reports)
        self.assertEqual(decisions["status"], "fail")
        self.assertEqual(grid.status_code(decisions), 1)
        self.assertEqual(decisions["policy"], V2)

    def test_incomplete_grid_rejected(self):
        reports = self.reports()
        del reports[grid.gate.keys()[0]]
        with self.assertRaisesRegex(ValueError, "incomplete TASK29"):
            grid.summary(reports)

    def test_check_report_requires_recorded_policy(self):
        report = dict(success=True, policy=a.POLICY, workloads=[],
                      retained_scaling=None)
        with self.assertRaisesRegex(ValueError, "unexpected TASK29A policy"):
            grid.check_report(Path("unused"), report, "b", "c", 0.3,
                              "frag_create", 0, 1)

    def test_check_report_passes_count_and_policy(self):
        result = dict(metrics={"cpu": stats([1.0] * 10)})
        candidate = copy.deepcopy(result)
        a.apply_control(candidate["metrics"]["cpu"], result["metrics"]["cpu"])
        report = dict(success=True, policy=V2, retained_scaling=None,
                      workloads=[dict(control=copy.deepcopy(result),
                                      candidate=candidate)])
        with patch.object(a, "analyze", side_effect=[
                copy.deepcopy(result), copy.deepcopy(result)]) as analyze:
            grid.check_report(Path("unused"), report, "b", "c", 0.3,
                              "frag_create", 0, 64)
        for call in analyze.call_args_list:
            self.assertEqual(call.kwargs["iterations"], 64)
            self.assertIs(call.kwargs["policy"], V2)

    def test_check_report_accepts_archived_pair_keys(self):
        # A real archive is JSON: pair keys are strings. Twenty pairs make
        # string and integer key order differ; the unarchived analysis
        # must still match the stored one.
        result = dict(metrics={"cpu": stats([1.0] * 20)},
                      runtime_by_pair={i: dict(pair=i) for i in range(20)})
        candidate = copy.deepcopy(result)
        a.apply_control(candidate["metrics"]["cpu"], result["metrics"]["cpu"])
        stored = json.loads(json.dumps(dict(
            success=True, policy=V2, retained_scaling=None,
            workloads=[dict(control=result, candidate=candidate)])))
        with patch.object(a, "analyze", side_effect=[
                copy.deepcopy(result), copy.deepcopy(result)]):
            grid.check_report(Path("unused"), stored, "b", "c", 0.3,
                              "frag_create", 0, 64, pairs=20)
        stored["workloads"][0]["candidate"]["runtime_by_pair"]["7"] = {}
        with patch.object(a, "analyze", side_effect=[
                copy.deepcopy(result), copy.deepcopy(result)]), \
                self.assertRaisesRegex(ValueError, "changed point analysis"):
            grid.check_report(Path("unused"), stored, "b", "c", 0.3,
                              "frag_create", 0, 64, pairs=20)

    def test_partial_grid_evidence_is_sealed(self):
        # The interrupted 20-pair run: every retained archive is sealed in
        # its inventory and none of it is a grid decision.
        root = a.HERE / "evidence/task29a/grid-partial"
        inventory = a.load(root / "inventory.json")
        self.assertIn(inventory["driver"], grid.DRIVERS)
        self.assertEqual(inventory["policy"], V2)
        self.assertEqual(inventory["iterations"], a.load(grid.COUNTS))
        self.assertFalse((root / "decisions.json").exists())
        exits = {}
        for row in inventory["runs"]:
            self.assertEqual(a.seal(root / row["archive"]), row["seal"])
            self.assertTrue(row["protocol"])
            exits["%s-%d" % (row["case"], row["size"])] = row["exit"]
        self.assertEqual(len(exits), 20)
        self.assertEqual(sorted(k for k, v in exits.items() if v == 1), [
            "frag_create-10000", "frag_named-10000", "frag_named_rules-1",
            "frag_named_rules-10"])
        self.assertEqual(sorted(p.name for p in root.glob("*.json.xz")),
                         sorted(r["archive"] for r in inventory["runs"]))

    @unittest.skipUnless(os.environ.get("TASK29A_GRID_EVIDENCE"),
                         "set TASK29A_GRID_EVIDENCE=1 to replay archives")
    def test_partial_grid_replays(self):
        root = a.HERE / "evidence/task29a/grid-partial"
        self.assertEqual(grid.main(["replay", "--partial", "--output",
                                    str(root)]), 2)

    def test_checkpoint_rewrites(self):
        with tempfile.TemporaryDirectory(prefix="task29a-test-") as d:
            path = Path(d) / "inventory.json"
            grid.checkpoint(path, {"runs": [1]})
            grid.checkpoint(path, {"runs": [1, 2]})
            self.assertEqual(json.loads(path.read_text()), {"runs": [1, 2]})
            self.assertEqual(sorted(p.name for p in Path(d).iterdir()),
                             ["inventory.json"])

    def test_predeclared_counts_cover_grid(self):
        counts = a.load(a.HERE / "evidence/task29a/iterations.json")
        self.assertEqual(counts["schema"], "task29a-iterations-v1")
        self.assertEqual(set(counts["iterations"]),
                         {"%s-%d" % k for k in grid.gate.keys()})
        for value in counts["iterations"].values():
            self.assertEqual(value & (value - 1), 0)


if __name__ == "__main__":
    unittest.main()
