#!/usr/bin/env python3
"""TASK29A second stage: candidate-blind remeasurement and resume."""
import contextlib
import copy
import hashlib
from pathlib import Path
import subprocess
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
    def setUp(self):
        self.checked = patch.object(grid, "check_header")
        self.check = self.checked.start()
        self.addCleanup(patch.stopall)

    def test_fresh_and_resumed_outputs(self):
        inventory = dict(schema="x", pairs=20, runs=[], driver="d",
                         acceptance="a")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "out"
            self.assertEqual(grid.begin(root, copy.deepcopy(inventory),
                                        False), {})
            with self.assertRaises(FileExistsError):
                grid.begin(root, copy.deepcopy(inventory), False)
            recorded = dict(inventory, runs=[
                dict(case="c", archive="c.json.xz")])
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

    def test_resume_records_changed_code(self):
        old = dict(schema="x", pairs=20, driver="d0", acceptance="a0",
                   runs=[dict(case="c", archive="c.json.xz")])
        with tempfile.TemporaryDirectory() as tmp, \
                patch.object(grid, "replay_rows", return_value={}):
            root = Path(tmp)
            a.save(root / "inventory.json", old)
            new = dict(old, driver="d1", runs=[])
            grid.begin(root, new, True)
            self.check.assert_called_with(old)
            self.assertEqual(new, dict(old, resumed=[
                dict(driver="d1", acceptance="a0", after=1)]))
            (root / "inventory.json").unlink()
            a.save(root / "inventory.json", dict(new, runs=new["runs"] * 2))
            again = dict(old, driver="d1", runs=[])
            grid.begin(root, again, True)
            self.assertEqual(again["resumed"], new["resumed"])
            (root / "inventory.json").unlink()
            a.save(root / "inventory.json", again)
            last = dict(old, acceptance="a1", driver="d1", runs=[])
            grid.begin(root, last, True)
            self.assertEqual(last["resumed"][1],
                             dict(driver="d1", acceptance="a1", after=2))
            self.assertEqual((last["driver"], last["acceptance"]),
                             ("d0", "a0"))

    def test_header_checks_resumed_code(self):
        self.checked.stop()
        header = dict(driver=a.seal(grid.__file__),
                      acceptance=grid.LAYOUT_ACCEPTANCE[0],
                      layout_seed="s", baseline=a.BASE,
                      policy=a.EQUIVALENCE_POLICY,
                      iterations=a.load(grid.COUNTS))
        grid.check_header(header)
        grid.check_header(dict(header, resumed=[dict(
            driver=grid.DRIVERS[-1], acceptance=a.seal(a.__file__),
            after=3)]))
        with self.assertRaisesRegex(ValueError, "layout-seeded acceptance"):
            grid.check_header(dict(header, resumed=[dict(
                driver=grid.DRIVERS[-1], acceptance=grid.ACCEPTANCE[0],
                after=3)]))
        with self.assertRaisesRegex(ValueError, "changed driver"):
            grid.check_header(dict(header, resumed=[dict(
                driver="x", acceptance=a.seal(a.__file__), after=3)]))


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
                                           resume=False, partial=False,
                                           repo=None)
            with patch.object(grid, "replay_grid",
                              return_value=(first, stage1, {})), \
                    patch.object(grid, "measure", side_effect=measure), \
                    patch.object(grid, "summary", side_effect=summary), \
                    patch.object(grid.ENGINE, "locked",
                                 lambda repo: contextlib.nullcontext()), \
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


class Disposition(unittest.TestCase):
    def decisions(self, **open_cells):
        def row(name, cpu="pass", wall="pass", reason="paired bootstrap"):
            case, size = name.rsplit("-", 1)
            metrics = dict(cpu=dict(decision=cpu, reason=reason),
                           wall=dict(decision=wall, reason=reason),
                           gc=dict(decision="reported"))
            return dict(case=case, size=int(size), protocol=True,
                        metrics=metrics)
        rows = [row(n, **open_cells.get(n, dict(cpu="inconclusive",
                                                wall="inconclusive")))
                for n in grid.DISPOSITION["attributed"]]
        rows.append(row("frag_record-0", **open_cells.get("frag_record-0",
                                                          {})))
        rows.append(row("frag_ac-0", "inconclusive", "inconclusive",
                        grid.CONTROL))
        return dict(workloads=rows, remeasured={}, retained_scaling=dict(
            status="measured", adjacent_intervals=[dict(
                selection="candidate",
                words_per_rule=dict(decision="pass"))]))

    def test_listed_cells_do_not_block(self):
        result = grid.dispose(self.decisions())
        self.assertEqual(result["status"], "pass")
        self.assertEqual(result["cells"]["unresolvable"], ["frag_ac-0"])
        self.assertEqual(result["counts"]["attributed"], 5)

    def test_fail_unlisted_and_scaling_still_block(self):
        fail = self.decisions(**{"frag_record-0": dict(cpu="fail")})
        self.assertEqual(grid.dispose(fail)["status"], "fail")
        other = self.decisions(**{"frag_record-0": dict(
            wall="inconclusive")})
        self.assertEqual(grid.dispose(other)["cells"]["blocking"],
                         ["frag_record-0"])
        scaling = self.decisions()
        scaling["retained_scaling"]["status"] = "blocked"
        self.assertEqual(grid.dispose(scaling)["status"], "blocked")

    def test_attribution_must_match_open_cells(self):
        stale = self.decisions(**{"frag_merge-100": {}})
        with self.assertRaisesRegex(ValueError, "stale attribution"):
            grid.dispose(stale)
        with self.assertRaisesRegex(ValueError, "second stage"):
            grid.dispose({"workloads": []})

    def test_a_protocol_failure_always_blocks(self):
        broken = self.decisions()
        broken["workloads"][-2]["protocol"] = False
        result = grid.dispose(broken)
        self.assertEqual(result["status"], "blocked")
        self.assertEqual(result["cells"]["blocking"], ["frag_record-0"])


class Table(unittest.TestCase):
    """TASK29A keeps the settings its recorded runs used."""

    def test_the_table_is_the_recorded_policy_and_settings(self):
        table = grid.TABLE
        self.assertEqual((table.pairs, table.samples, table.headroom,
                          table.seconds, table.target, table.max_pairs),
                         (10, 3, 2, 0.3, 0.015, 120))
        self.assertEqual(table.seconds_by_case, {})
        self.assertFalse(table.fixed_seconds)
        # The default being warmup, ramp here means the table names it.
        self.assertEqual(table.schedule, "ramp")
        # The recorded runs predate the engine seal and need no seed.
        self.assertFalse(table.engine)
        self.assertFalse(table.require_seed)

    def test_the_acceptance_seal_of_the_lock_move_is_recorded(self):
        commit = "294bb61c3"
        path = "src/simp/tests/performance/acceptance.py"
        found = subprocess.run(
            ["git", "-C", str(a.HERE), "show", "%s:%s" % (commit, path)],
            capture_output=True)
        if found.returncode:
            self.skipTest("commit %s is not available" % commit)
        self.assertIn(dict(bytes=len(found.stdout),
                           sha256=hashlib.sha256(found.stdout).hexdigest()),
                      grid.LAYOUT_ACCEPTANCE)


if __name__ == "__main__":
    unittest.main()
