#!/usr/bin/env python3
"""TASK29A second stage: candidate-blind remeasurement and resume."""
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import acceptance as a
import task29a_grid as grid


def cell(control, candidate=(0.99, 1.01), decision="pass"):
    def metric(ci, decision):
        return dict(decision=decision, paired_ratio_bootstrap_95_percent=ci,
                    margin=0.03)
    metrics = {m: metric(list(candidate), decision) for m in ("cpu", "wall")}
    controls = {m: metric(list(control) if control else None, "reported")
                for m in ("cpu", "wall")}
    for m in metrics:
        a.apply_control(metrics[m], controls[m])
    return dict(success=True, workloads=[dict(
        candidate=dict(metrics=metrics), control=dict(metrics=controls))])


class ExtensionRule(unittest.TestCase):
    def test_valid_control_is_final(self):
        self.assertIsNone(grid.extension_pairs(cell((0.99, 1.02)), 20))

    def test_wide_control_is_capped(self):
        self.assertEqual(grid.extension_pairs(cell((0.965, 1.071)), 20),
                         grid.MAX_PAIRS)

    def test_count_follows_control_width_only(self):
        report = cell((0.975, 1.035), candidate=(0.9, 1.2),
                      decision="inconclusive")
        expected = grid.extension_pairs(report, 20)
        self.assertEqual(expected, 80)
        for candidate in ((0.97, 1.0), (1.0, 1.029), (0.5, 2.0)):
            other = cell((0.975, 1.035), candidate=candidate,
                         decision="pass")
            self.assertEqual(grid.extension_pairs(other, 20), expected)

    def test_narrow_biased_control_still_doubles(self):
        self.assertEqual(grid.extension_pairs(cell((1.031, 1.04)), 20), 40)

    def test_missing_control_interval_uses_maximum(self):
        self.assertEqual(grid.extension_pairs(cell(None), 20),
                         grid.MAX_PAIRS)

    def test_fail_and_protocol_failure_are_final(self):
        failed = cell((0.9, 1.1), candidate=(1.04, 1.08), decision="fail")
        self.assertIsNone(grid.extension_pairs(failed, 20))
        self.assertIsNone(grid.extension_pairs(
            dict(success=False, failure="x"), 20))

    def test_plan_in_grid_order(self):
        keys = grid.gate.keys()
        reports = {k: cell((0.99, 1.01)) for k in keys}
        reports[keys[5]] = cell((0.9, 1.1))
        reports[keys[2]] = cell((1.031, 1.04))
        self.assertEqual(grid.extension_plan(reports, 20),
                         [[*keys[2], 40], [*keys[5], grid.MAX_PAIRS]])

    def test_combined_replaces_remeasured_cells(self):
        keys = grid.gate.keys()
        stage1 = {k: object() for k in keys}
        stage2 = {keys[0]: object()}
        inventory = dict(target=grid.TARGET, max_pairs=grid.MAX_PAIRS,
                         layout_seed="s-ext")
        with patch.object(grid, "summary", return_value={}) as summary:
            decisions = grid.combined(stage1, stage2,
                                      [[*keys[0], 40]], inventory)
        merged = summary.call_args.args[0]
        self.assertIs(merged[keys[0]], stage2[keys[0]])
        self.assertIs(merged[keys[1]], stage1[keys[1]])
        self.assertEqual(decisions["remeasured"]["plan"], [[*keys[0], 40]])
        with self.assertRaisesRegex(ValueError, "incomplete remeasurement"):
            grid.combined(stage1, {}, [[*keys[0], 40]], inventory)


class Resume(unittest.TestCase):
    def test_fresh_and_resumed_outputs(self):
        inventory = dict(schema="x", pairs=20, runs=[])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "out"
            self.assertEqual(grid.begin(root, copy.deepcopy(inventory),
                                        False), {})
            with self.assertRaises(FileExistsError):
                grid.begin(root, copy.deepcopy(inventory), False)
            recorded = dict(inventory, runs=[dict(case="c")])
            a.save(root / "inventory.json", recorded)
            resumed = copy.deepcopy(inventory)
            with patch.object(grid, "replay_rows",
                              return_value={"k": 1}) as rows:
                self.assertEqual(grid.begin(root, resumed, True), {"k": 1})
            self.assertEqual(rows.call_args.args[1], recorded)
            self.assertEqual(resumed["runs"], recorded["runs"])
            with self.assertRaisesRegex(ValueError, "different settings"):
                grid.begin(root, dict(inventory, pairs=30), True)
            a.save(root / "decisions.json", {})
            with self.assertRaisesRegex(ValueError, "already complete"):
                grid.begin(root, copy.deepcopy(inventory), True)


class TwoStage(unittest.TestCase):
    def test_extend_then_replay(self):
        keys = grid.gate.keys()
        stage1 = {k: cell((0.99, 1.01)) for k in keys}
        stage1[keys[3]] = cell((0.95, 1.06), decision="inconclusive")
        first = dict(baseline="b", candidate="c", seconds=0.3, pairs=20,
                     samples=5, outliers="none removed",
                     policy=a.EQUIVALENCE_POLICY, iterations={},
                     iterations_seal={}, layout_seed="g1")
        remeasured = {keys[3]: cell((0.98, 1.02))}

        def measure(root, inventory, cells, args, reports):
            self.assertEqual(cells, [(*keys[3], grid.MAX_PAIRS)])
            self.assertEqual(inventory["layout_seed"], "g1-ext")
            inventory["runs"].append(dict(case=keys[3][0], size=keys[3][1],
                                          pairs=grid.MAX_PAIRS))
            a.save(root / "inventory.json", inventory)
            reports.update(remeasured)
            return reports

        def summary(reports):
            return dict(status="pass" if reports[keys[3]] is
                        remeasured[keys[3]] else "stale")
        with tempfile.TemporaryDirectory() as tmp:
            first_root = Path(tmp) / "grid"
            first_root.mkdir()
            for name in ("inventory.json", "decisions.json"):
                a.save(first_root / name, {})
            ext = Path(tmp) / "ext"
            args = grid.argparse.Namespace(grid=first_root, output=ext,
                                           resume=False, partial=False)
            with patch.object(grid, "replay_grid",
                              return_value=(first, stage1, {})), \
                    patch.object(grid, "measure", side_effect=measure), \
                    patch.object(grid, "summary", side_effect=summary), \
                    patch.object(grid, "check_header"):
                self.assertEqual(grid.extend(args), 0)
                inventory = a.load(ext / "inventory.json")
                self.assertEqual(inventory["grid"], "../grid")
                with patch.object(grid, "replay_rows",
                                  return_value=remeasured):
                    self.assertEqual(grid.replay(args), 0)
                    stage1[keys[4]] = cell((0.9, 1.1))
                    with self.assertRaisesRegex(ValueError, "changed "
                                                "extension plan"):
                        grid.replay(args)


if __name__ == "__main__":
    unittest.main()
