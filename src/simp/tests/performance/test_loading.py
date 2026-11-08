#!/usr/bin/env python3
"""Non-timing loading protocol regressions; synthetic logs are NOT evidence."""
import copy
import gzip
import importlib.util
import json
import math
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import loading as l
import timing_grid as tg

HERE = Path(__file__).resolve().parent
RAW = "1,0.4,0.1,0.1,0.1,0.5,0.2,0.1"
EMPTY = "0.000001,0,0,0,0,0,0,0"


class LoadingProtocol(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="loading-validator-")
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        self.dst = self.repo / "baseline"
        self.dst.mkdir()
        (self.repo / "sigobj").mkdir()
        for name in ("Paired", "Traverse", "simpLib", "congLib", "selftest"):
            (self.dst / (name + ".sml")).write_text("(* synthetic *)\n")
        self.args = dict(side="baseline", dst=self.dst, repo=self.repo,
                         names={"Traverse", "simpLib", "congLib"}, sources={},
                         module="simpLib")
        self.events = [
            ["begin", "baseline", "loading", "none"],
            ["cwd", str(self.dst)],
            ["holdir", str(self.repo), str(self.repo)],
            ["preloaded", "HolKernel,Paired"],
            ["heapfile", str(self.dst / "Paired.sml")],
            ["search", str(self.dst)],
            ["search", str(self.repo / "sigobj")],
            ["observation", "timer.accounting", RAW],
            ["observation", "timer.empty", EMPTY],
            ["observation", "loading.begin", "simpLib"],
        ]
        for name in ("Traverse", "simpLib"):
            self.events += [[kind, str(self.dst / (name + ".sml"))]
                            for kind in ("use", "used")]
        self.events += [
            ["observation", "loading.end", "simpLib"],
            ["observation", "loading.raw", RAW],
            ["observation", "loading.extensions", l.NO_EXTENSIONS],
            ["use", str(self.dst / "selftest.sml")],
            ["check", "ordinary exact kernel equality", "pass"],
            ["used", str(self.dst / "selftest.sml")],
        ]
        self.events += [["loaded", str(self.dst / (name + ".sml"))]
                        for name in ("Paired", "Traverse", "simpLib",
                                     "selftest")]
        self.events += [["end", "pass", "1"]]

    def receipt(self, events=None):
        es = self.events if events is None else events
        text = "".join(l.rp.PREFIX + str(i) + "\t" + "\t".join(e) + "\n"
                       for i, e in enumerate(es))
        return dict(stdout=text, exit=0, timed_out=False)

    def check(self, events=None, **changes):
        receipt = self.receipt(events)
        receipt.update(changes)
        return l.validate(receipt, **self.args)

    def test_complete_actual_import_inside_timer(self):
        result, measured = self.check()
        self.assertEqual(result["outcome"], "pass")
        self.assertTrue(measured["calibrated"])
        self.assertAlmostEqual(measured["raw"]["cpu"], 0.7)
        self.assertAlmostEqual(measured["raw"]["gc_cpu"], 0.2)
        self.assertAlmostEqual(measured["raw"]["gc_user_only"], 0.1)

    def test_cong_first_has_both_actual_imports_and_two_proofs(self):
        es = copy.deepcopy(self.events)
        for event in es:
            if event[:2] in (["observation", "loading.begin"],
                             ["observation", "loading.end"]):
                event[2] = "congLib"
        index = next(i for i, e in enumerate(es)
                     if e[:2] == ["observation", "loading.end"])
        path = str(self.dst / "congLib.sml")
        es[index:index] = [["use", path], ["used", path]]
        index = next(i for i, e in enumerate(es) if e[0] == "check")
        es.insert(index + 1,
                  ["check", "congruence exact kernel equality", "pass"])
        es.insert(-1, ["loaded", path])
        es[-1][-1] = "2"
        self.args["module"] = "congLib"
        self.assertTrue(self.check(es)[1]["calibrated"])

    def test_exit_timeout_and_footer_are_required(self):
        for changes in ({"exit": 7}, {"timed_out": True}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                self.check(**changes)
        for es in ([], self.events[:-1], self.events[:-2]):
            with self.assertRaises(ValueError):
                self.check(es)

    def test_missing_duplicate_reordered_or_wrong_target(self):
        for kind in ("missing", "duplicate", "reordered", "wrong"):
            es = copy.deepcopy(self.events)
            index = next(i for i, e in enumerate(es)
                         if e[:2] == ["observation", "loading.raw"])
            if kind == "missing":
                del es[index]
            elif kind == "duplicate":
                es.insert(index, es[index])
            elif kind == "reordered":
                es[index], es[index - 1] = es[index - 1], es[index]
            else:
                es[index - 1][-1] = "congLib"
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.check(es)

    def test_preloaded_or_loaded_before_timer_rejected(self):
        es = copy.deepcopy(self.events)
        es[3][-1] += ",simpLib"
        with self.assertRaisesRegex(ValueError, "already present"):
            self.check(es)
        es = copy.deepcopy(self.events)
        start = next(i for i, e in enumerate(es)
                     if e[:2] == ["observation", "loading.begin"])
        uses = es[start + 1:start + 5]
        del es[start + 1:start + 5]
        es[start:start] = uses
        with self.assertRaisesRegex(ValueError, "timed import region"):
            self.check(es)

    def test_selftest_pending_cannot_encapsulate_import(self):
        es = copy.deepcopy(self.events)
        source = ["use", str(self.dst / "selftest.sml")]
        es.remove(source)
        es.insert(7, source)
        with self.assertRaisesRegex(ValueError, "unordered source-use"):
            self.check(es)

    def test_incomplete_actual_inventory(self):
        es = [e for e in self.events if e !=
              ["loaded", str(self.dst / "simpLib.sml")]]
        with self.assertRaisesRegex(ValueError, "untraced"):
            self.check(es)

    def test_wrong_path_and_changed_source(self):
        path = self.dst / "simpLib.sml"
        other = self.repo / "candidate"
        other.mkdir()
        (other / path.name).write_bytes(path.read_bytes())
        es = [[str(other / path.name) if f == str(path) else f for f in e]
              for e in self.events]
        with self.assertRaisesRegex(ValueError, "wrong loaded simplifier"):
            self.check(es)
        self.args["sources"][str(path)] = l.a.seal(path)
        path.write_text("changed\n")
        with self.assertRaisesRegex(ValueError, "source changed"):
            self.check()

    def test_transport_corruption(self):
        for text in (self.receipt()["stdout"][:-1],
                     self.receipt()["stdout"].replace("@@PAIR\t5\t",
                                                     "@@PAIR\t6\t")):
            with self.assertRaises(ValueError):
                l.validate(dict(stdout=text, exit=0, timed_out=False),
                           **self.args)

    def test_bad_timer_fields_and_accounting(self):
        for value in ("nan", "inf", "-1", "~1", "bad"):
            fields = RAW.split(",")
            fields[0] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                l.numbers(",".join(fields))
        with self.assertRaisesRegex(ValueError, "field count"):
            l.numbers("0,1")
        with self.assertRaisesRegex(ValueError, "accounting"):
            l.numbers("1,0,0,0,0,1,0,0")
        self.assertEqual(l.numbers(RAW.replace("0.4", "4E~1"))["nongc_usr"],
                         0.4)

    def test_forced_gc_must_exercise_both_gc_timer_views(self):
        for raw in ("0,0,0,0,0,0,0,0",
                    "1,0.4,0.1,0,0,0.4,0.1,0",
                    "1,0.4,0.1,0.001,0,0.401,0.1,0",
                    "1,0.4,0.1,0,0,0.4,0.1,0.001"):
            es = copy.deepcopy(self.events)
            for event in es:
                if event[:2] == ["observation", "timer.accounting"]:
                    event[2] = raw
            with self.subTest(raw=raw), self.assertRaisesRegex(
                    ValueError, "did not exercise GC"):
                self.check(es)

    def test_zero_gc_import_is_allowed_after_positive_control(self):
        es = copy.deepcopy(self.events)
        for event in es:
            if event[:2] == ["observation", "loading.raw"]:
                event[2] = "1,0.4,0.1,0,0,0.4,0.1,0"
        self.assertEqual(self.check(es)[1]["raw"]["gc_cpu"], 0)

    def test_sub_resolution_import_is_inconclusive_not_rebatched(self):
        es = copy.deepcopy(self.events)
        for e in es:
            if e[:2] == ["observation", "loading.raw"]:
                e[2] = EMPTY
        self.assertFalse(self.check(es)[1]["calibrated"])

    def test_generated_runner_times_dynamic_load_not_static_fixture(self):
        with patch.object(l.rp, "install_fixtures"):
            runner = (l.rp.HERE / "paired/runner.sml").read_text()
            (self.dst / "runner.sml").write_text(runner)
            l.install(self.dst, "congLib")
        text = (self.dst / "runner.sml").read_text()
        self.assertIn("loadingMeasure (fn () => Meta.loadPlan tracedUse name)",
                      text)
        self.assertLess(text.index('tracedUse "CheckSupport";'),
                        text.index('loadingImport ();'))
        self.assertLess(text.index('loadingImport ();'),
                        text.index('tracedUse (Paired.env "PAIR_TARGET")'))
        prefix = text[:text.index("val result =")]
        self.assertNotIn("simpLib.", prefix)
        makefile = (self.dst / "Holmakefile").read_text()
        self.assertIn("-o $@ $<", makefile)
        self.assertNotIn("SignatureCheck", makefile)


class PairingTests(unittest.TestCase):
    def rows(self, n=10):
        return [dict(pair=i, selection=side, accepted=True, exit=0,
                     measurement=dict(calibrated=True,
                                      raw={k: 1 for k in l.METRICS}))
                for i, side in l.plan(n)]

    def test_alternating_fresh_ab_ba(self):
        self.assertEqual(l.plan(2), [(0, "baseline"), (0, "candidate"),
                                     (1, "candidate"), (1, "baseline")])
        self.assertEqual(len(l.plan(10)), 20)

    def test_ten_pairs_and_mandatory_completeness(self):
        result = l.statistics(self.rows(), 10, False)
        self.assertEqual(result["metrics"]["wall"]["decision"], "pass")
        for rows in (self.rows()[:-1], list(reversed(self.rows())),
                     self.rows() + [self.rows()[0]]):
            with self.assertRaisesRegex(ValueError, "fresh pair"):
                l.statistics(rows, 10, False)
        with self.assertRaisesRegex(ValueError, ">=10"):
            l.statistics(self.rows(1), 1, False)
        self.assertEqual(l.statistics(self.rows(1), 1, True)["decision"],
                         "smoke-only")

    def test_failed_exit_missing_and_nonfinite_not_accepted(self):
        for change in ({"accepted": False}, {"exit": 1}):
            rows = self.rows()
            rows[0].update(change)
            with self.assertRaises(ValueError):
                l.statistics(rows, 10, False)
        rows = self.rows()
        rows[0]["measurement"]["raw"]["cpu"] = math.inf
        with self.assertRaises(ValueError):
            l.statistics(rows, 10, False)

    def test_zero_gc_is_reported_not_gated_and_no_pairs_dropped(self):
        rows = self.rows()
        rows[0]["measurement"]["raw"]["gc_cpu"] = 0
        result = l.statistics(rows, 10, False)["metrics"]["gc_cpu"]
        self.assertEqual(result["decision"], "reported")
        self.assertEqual(len(result["observations"]), 10)

    def test_calibration_failure_not_pass(self):
        rows = self.rows()
        rows[4]["measurement"]["calibrated"] = False
        result = l.statistics(rows, 10, False)
        self.assertEqual({k: m["decision"] for k, m in
                          result["metrics"].items()},
                         {"wall": "inconclusive", "cpu": "inconclusive",
                          "gc_cpu": "reported"})


class UnitAndPolicyTests(unittest.TestCase):
    """The loading unit and the timing grid's equivalence policy."""

    def rows(self, n, reps, value, phase_scale=1.0):
        """`value(pair, side, rep)` is the wall and cpu of each process."""
        return [dict(pair=i, selection=side, rep=r, accepted=True, exit=0,
                     measurement=dict(calibrated=True, raw={
                         "wall": value(i, side, r) * (
                             phase_scale if side == "candidate" else 1),
                         "cpu": value(i, side, r) * (
                             phase_scale if side == "candidate" else 1),
                         "gc_cpu": 0.1}))
                for i, side, r in l.schedule(n, reps)]

    def test_policy_is_the_grids_single_definition(self):
        import timing_grid
        self.assertIs(l.POLICY, l.a.EQUIVALENCE_POLICY)
        self.assertIs(timing_grid.a.EQUIVALENCE_POLICY, l.POLICY)
        self.assertEqual(l.POLICY["margin"], 0.03)
        self.assertEqual(l.POLICY["gated_timing"], ["cpu", "wall"])
        self.assertEqual(l.a.timing_rule(l.POLICY, "gc_cpu"), (0.0, False))

    def test_schedule_is_fresh_processes_ab_ba_interleaved(self):
        self.assertEqual(l.schedule(2, 1), [(i, s, 0) for i, s in l.plan(2)])
        self.assertEqual(l.schedule(2, 2), [
            (0, "baseline", 0), (0, "candidate", 0),
            (0, "baseline", 1), (0, "candidate", 1),
            (1, "candidate", 0), (1, "baseline", 0),
            (1, "candidate", 1), (1, "baseline", 1)])
        self.assertEqual(len(l.schedule(30, l.REPS)), 60 * l.REPS)

    def test_sample_is_the_mean_of_its_fresh_processes(self):
        rows = self.rows(10, 3, lambda i, s, r: 1 + r)
        result = l.statistics(rows, 10, False, 3)["metrics"]["wall"]
        self.assertEqual(result["observations"][0],
                         {"baseline": 2.0, "candidate": 2.0})
        with self.assertRaisesRegex(ValueError, "fresh pair"):
            l.statistics(rows[:-1], 10, False, 3)
        with self.assertRaisesRegex(ValueError, "fresh pair"):
            l.statistics(rows, 10, False, 2)

    def decide(self, scale, control_spread):
        wiggle = lambda i, s, r: 1 + control_spread * (
            (i * 7 + r * 3 + (s == "candidate")) % 5 - 2) / 2
        results = {
            "control": l.statistics(self.rows(10, 1, wiggle), 10, False),
            "candidate": l.statistics(
                self.rows(10, 1, lambda i, s, r: 1.0, scale), 10, False)}
        for metric, data in results["candidate"]["metrics"].items():
            l.a.apply_control(data, results["control"]["metrics"][metric])
        return {m: d["decision"] for m, d in
                results["candidate"]["metrics"].items()}

    def test_two_percent_passes_under_the_margin_with_a_valid_control(self):
        got = self.decide(1.02, 0.0)
        self.assertEqual((got["wall"], got["cpu"]), ("pass", "pass"))
        self.assertEqual(l.exit_status({k: {"decision": v}
                                        for k, v in got.items()}), 0)

    def test_five_percent_slowdown_fails(self):
        got = self.decide(1.05, 0.0)
        self.assertEqual((got["wall"], got["cpu"]), ("fail", "fail"))

    def test_wide_control_makes_the_comparison_inadmissible(self):
        got = self.decide(1.0, 0.4)
        self.assertEqual((got["wall"], got["cpu"]),
                         ("inconclusive", "inconclusive"))
        self.assertEqual(l.exit_status({k: {"decision": v}
                                        for k, v in got.items()}), 2)

    def test_exit_status_ignores_reported_and_requires_gated_pass(self):
        self.assertEqual(l.exit_status({
            "wall": {"decision": "pass"}, "cpu": {"decision": "pass"},
            "gc_cpu": {"decision": "reported"}}), 0)
        self.assertEqual(l.exit_status({
            "wall": {"decision": "pass"}, "cpu": {"decision": "fail"},
            "gc_cpu": {"decision": "reported"}}), 1)

    def control(self, half_width):
        ci = [math.exp(-half_width), math.exp(half_width)]
        return {"metrics": {m: {"paired_ratio_bootstrap_95_percent": ci}
                            for m in l.POLICY["gated_timing"]}}

    def test_second_stage_count_is_the_grids_rule(self):
        t, n = tg.TARGET, l.PAIRS
        self.assertEqual(l.control_width(self.control(0.01)),
                         tg.control_half_width({"control": self.control(
                             0.01)}))
        for width in (0.0, t, 1.5 * t, 2 * t, 5 * t):
            control = self.control(width)
            self.assertEqual(
                l.second_stage_count(control, n),
                tg.second_stage_pairs(tg.control_half_width(
                    {"control": control}), n, t, tg.MAX_PAIRS))
        self.assertEqual(l.second_stage_count(self.control(0.0), n), 2 * n)
        self.assertEqual(l.second_stage_count(self.control(5 * t), n),
                         tg.MAX_PAIRS)
        infinite = {"metrics": {m: {"paired_ratio_bootstrap_95_percent":
                                    None} for m in ("cpu", "wall")}}
        self.assertEqual(l.second_stage_count(infinite, n), tg.MAX_PAIRS)

    def test_first_stage_covers_the_unit_sd_it_is_sized_for(self):
        self.assertEqual(l.required_units(0.054), 79)
        self.assertLessEqual(l.required_units(l.UNIT_SD_BOUND),
                             l.PAIRS * l.REPS)
        self.assertGreater(l.required_units(l.UNIT_SD_BOUND * 1.2),
                           l.PAIRS * l.REPS)
        self.assertEqual((l.PAIRS, l.REPS), (40, 5))

    def test_calibration_is_covered_by_the_one_unit_sd_bound(self):
        def found(*uppers):
            return dict(metrics={
                "m%d" % i: dict(gated=True, unit_sd_upper=u)
                for i, u in enumerate(uppers)})
        bound = l.UNIT_SD_BOUND
        self.assertTrue(l.covered(found(bound, 0.01)))
        self.assertFalse(l.covered(found(bound + 1e-9, 0.01)))
        # The units the first stage has are what the bound requires.
        self.assertGreaterEqual(l.PAIRS * l.REPS, l.required_units(bound))
        # A metric that is only reported does not decide it.
        data = found(0.01)
        data["metrics"]["gc"] = dict(gated=False, unit_sd_upper=1.0)
        self.assertTrue(l.covered(data))
        self.assertFalse(l.covered(dict(metrics={})))

    def test_chi_square_upper_bound(self):
        self.assertAlmostEqual(l.chi2_quantile(0.05, 11), 4.5748, places=3)
        self.assertAlmostEqual(l.chi2_quantile(0.05, 19), 10.1170, places=3)
        self.assertAlmostEqual(l.chi2_quantile(0.5, 2), 2 * math.log(2),
                               places=6)
        self.assertAlmostEqual(l.sd_upper_bound(1.0, 12),
                               math.sqrt(11 / 4.5748), places=3)
        self.assertLess(l.sd_upper_bound(1.0, 40),
                        l.sd_upper_bound(1.0, 12))

    def test_jitter_reports_the_derivation_quantities(self):
        n, reps = 12, 4
        # Per-process log values: a pair offset (drift, invisible to s1) and
        # a within-cell deviation of known size.
        def value(i, side, r):
            drift = 0.2 * i
            dev = (-1.5, -0.5, 0.5, 1.5)[r] * 0.01
            gap = 0.02 * (-1) ** i if side == "candidate" else 0.0
            return math.exp(drift + dev + gap)

        rows = [dict(pair=i, selection=side, rep=r, measurement=dict(raw={
            m: value(i, side, r) for m in l.METRICS}))
                for i, side, r in l.schedule(n, reps)]
        control = l.statistics(
            [dict(r, accepted=True, exit=0, measurement=dict(
                r["measurement"], calibrated=True)) for r in rows],
            n, False, reps)
        got = l.jitter(rows, control, n, reps)
        wall = got["metrics"]["wall"]
        # Cell values deviate by +-0.015, +-0.005 about their mean.
        ss = 0.01 ** 2 * (1.5 ** 2 + 0.5 ** 2) * 2
        self.assertAlmostEqual(wall["process_log_sd"], math.sqrt(ss / 3),
                               places=9)
        # The pair offset never reaches the paired log ratio: it is +-0.02
        # around zero, i.e. the sd of 0.02 * (-1)^i over 12 pairs.
        paired = 0.02 * math.sqrt(12 / 11)
        self.assertAlmostEqual(wall["paired_log_ratio_sd"], paired, places=9)
        self.assertAlmostEqual(wall["unit_sd"], paired * 2, places=9)
        self.assertAlmostEqual(wall["unit_sd_upper"],
                               l.sd_upper_bound(paired * 2, 12), places=9)
        self.assertEqual(wall["required_units"],
                         l.required_units(wall["unit_sd_upper"]))
        self.assertEqual(got["required_units"], wall["required_units"])
        self.assertEqual(got["configured_units"], l.PAIRS * l.REPS)

    def test_layout_units_are_replayable_and_independent(self):
        key = ("seed", "control", 3, "candidate", 2)
        self.assertEqual(l.layout_units(*key), l.layout_units(*key))
        self.assertEqual(l.layout_units("seed", "control", 3, "candidate", 2),
                         l.layout_units("seed", "candidate", 3, "candidate",
                                        2))
        drawn = {l.layout_units("seed", "control", i, side, r)
                 for i in range(10) for side in ("baseline", "candidate")
                 for r in range(5)}
        self.assertGreater(len(drawn), 20)
        self.assertTrue(all(0 <= u < l.ps.LAYOUT_UNITS for u in drawn))
        self.assertNotEqual(
            [l.layout_units("seed", "control", i, "baseline", 0)
             for i in range(20)],
            [l.layout_units("seed-ext", "control", i, "baseline", 0)
             for i in range(20)])


class ExtensionAbsenceTests(LoadingProtocol):
    def with_extensions(self, value):
        es = copy.deepcopy(self.events)
        for e in es:
            if e[:2] == ["observation", "loading.extensions"]:
                e[2] = value
        return es

    def test_absent_extensions_pass_when_enforced(self):
        _, measured = self.check_enforced(self.events)
        self.assertEqual(measured["extensions_loaded"], [])
        self.assertTrue(measured["extension_absence_enforced"])

    def check_enforced(self, es):
        receipt = self.receipt(es)
        return l.validate(receipt, enforce_absence=True, **self.args)

    def test_loaded_extension_name_rejected_for_the_candidate(self):
        for value in ("simpExtLib", "congExtLib,TraverseExt",
                      "SplitData", "trackedSimpDefaults", "splitLib"):
            with self.subTest(value=value), \
                    self.assertRaisesRegex(ValueError, "extension module"):
                self.check_enforced(self.with_extensions(value))

    def test_extension_source_in_the_actual_trace_rejected(self):
        es = copy.deepcopy(self.events)
        index = next(i for i, e in enumerate(es) if e[0] == "loaded")
        es.insert(index, ["loaded", str(self.dst / "splitLib.sml")])
        with self.assertRaisesRegex(ValueError, "splitLib"):
            self.check_enforced(es)

    def test_baseline_records_but_does_not_reject(self):
        _, measured = self.check(self.with_extensions("SplitData"))
        self.assertEqual(measured["extensions_loaded"], ["SplitData"])
        self.assertFalse(measured["extension_absence_enforced"])

    def test_extension_observation_names_must_be_extensions(self):
        for value in ("simpLib", "none,SplitData", "SplitData,none", ""):
            with self.subTest(value=value), \
                    self.assertRaisesRegex(ValueError, "loading.extensions"):
                self.check_enforced(self.with_extensions(value))

    def test_stems_the_baseline_never_loads_are_rejected(self):
        rows = []
        for side, extra in (("baseline", []), ("baseline", ["x"]),
                            ("candidate", ["x"])):
            _, measured = self.check_enforced(self.events)
            measured = dict(measured, loaded_stems=measured[
                "loaded_stems"] + extra)
            rows.append(dict(actual_selection=side, measurement=measured))
        l.check_new_stems(rows)
        rows.append(dict(actual_selection="candidate", measurement=dict(
            rows[0]["measurement"], loaded_stems=["Paired", "newHelper"])))
        with self.assertRaisesRegex(ValueError, "newHelper"):
            l.check_new_stems(rows)
        with patch.object(l, "STEM_ALLOWANCE", frozenset({"newHelper"})):
            l.check_new_stems(rows)
        self.assertEqual(l.STEM_ALLOWANCE, frozenset())

    def test_loaded_stems_come_from_every_load_event(self):
        _, measured = self.check_enforced(self.events)
        self.assertEqual(measured["loaded_stems"], sorted({
            "Paired", "Traverse", "simpLib", "selftest"}))

    def test_missing_extension_observation_rejected(self):
        es = [e for e in self.events
              if e[:2] != ["observation", "loading.extensions"]]
        with self.assertRaises(ValueError):
            self.check_enforced(es)

    def test_name_predicate_matches_the_api_audit(self):
        text = (l.AUDIT / "selftest.sml").read_text()
        block = re.search(r"val forbidden_names\s*=\s*\[(.*?)\]", text,
                          re.S)[1]
        audit = re.findall(r'"([^"]+)"', block)
        self.assertGreater(len(audit), 10)
        # One source: the audit's list, in the audit's order.
        self.assertEqual(list(l.extension_names()), audit)
        for name in audit:
            self.assertTrue(l.extension_name(name), name)
        # The audit's own patterns are the predicate's.
        for pattern in ('isSuffix "Ext"', 'isSuffix "ExtLib"',
                        'isPrefix "simpMarker"'):
            self.assertIn(pattern, text)
        for name in ("simpExtLib", "boolSimpsExt", "simpMarkerLib",
                     "SplitData", "someNewExt", "otherExtLib",
                     "simpMarkerNew"):
            self.assertTrue(l.extension_name(name), name)
        for name in ("simpLib", "congLib", "Traverse", "Cond_rewr",
                     "pureSimps", "boolSimps", "Trace"):
            self.assertFalse(l.extension_name(name), name)

    def test_generated_runner_probes_the_same_names(self):
        timing = l.timing_source()
        for name in l.extension_names():
            self.assertIn('"%s"' % name, timing)
        # Every structure of the global name space is tested, so a heap
        # binding that matches only a pattern is seen too.
        self.assertIn("#allStruct PolyML.globalNameSpace ()", timing)
        self.assertNotIn("lookupStruct", timing)
        for pattern in ('"Ext"', '"ExtLib"', '"simpMarker"'):
            self.assertIn(pattern, timing)
        for mark in ("@PROBE@", "@NONE@"):
            self.assertNotIn(mark, timing)


class ImportTests(unittest.TestCase):
    CODE = (
        "import sys\n"
        "sys.path.insert(0, sys.argv[1])\n"
        "import loading\n"
        "print('timing_grid' in sys.modules,\n"
        "      loading.extension_names.cache_info().currsize)\n")

    def test_importing_loading_runs_no_grid_and_reads_no_audit_file(self):
        # The allocation harness imports this module and lists neither
        # timing_grid.py nor the audit's selftest.sml among its inputs.
        done = subprocess.run(
            [sys.executable, "-I", "-B", "-c", self.CODE, str(HERE)],
            stdin=subprocess.DEVNULL, capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(done.stdout.split(), ["False", "0"])


class SemanticGateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="loading-gate-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.build((l.AUDIT / "audit_constants.py").read_text())

    def build(self, constants_text):
        """The audited tree, with the audit's constants module as given."""
        shutil.rmtree(self.root / "src", ignore_errors=True)
        self.audit = self.root / "src/simp/tests/api-audit"
        self.audit.mkdir(parents=True)
        self.constants_file = self.audit / "audit_constants.py"
        self.constants_file.write_text(constants_text)
        self.constants = l.audit_constants(self.audit)
        native = self.root / "src/simp/src"
        self.selected, actual = [], {}
        for module in self.constants.NATIVE_MODULES:
            for suffix in (".sig", ".sml"):
                name = module + suffix
                path = native / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("synthetic " + name)
                seal = l.a.seal(path)
                self.selected.append(dict(git_path="src/simp/src/" + name,
                                          **seal))
                actual[str(path)] = dict(resolved=str(path), **seal)
        sources = {}
        for name in self.constants.SOURCES:
            if name != "audit_constants.py":
                (self.audit / name).write_text("synthetic audit fixture\n")
            sources[name] = l.a.seal(self.audit / name)
        inventory = self.audit / "actual-files.json.gz"
        inventory.write_bytes(gzip.compress(json.dumps(actual).encode()))
        self.receipt = dict(pass_=True, sources=sources,
                            actual_files=dict(file=inventory.name,
                                              seal=l.a.seal(inventory),
                                              count=len(actual)), cases=[])
        self.receipt["pass"] = self.receipt.pop("pass_")
        for order, kind, owner in l.itertools.product(
                ("simp-first", "cong-first"), ("attribute", "exporter"),
                ("before", "after")):
            count = self.constants.CASE_CHECKS[kind, owner]
            text = "OK\n" * count + "OBS result=pass\n" + "".join(
                "OBS used.path=" + raw + "\n" for raw in actual)
            path = self.audit / (order + kind + owner + ".gz")
            path.write_bytes(gzip.compress(text.encode()))
            self.receipt["cases"].append(dict(
                order=order, foreign_kind=kind, foreign_owner=owner,
                checks=count, returncode=0, validation_error=None,
                log=path.name, log_seal=l.a.seal(path),
                environment=dict(API_AUDIT_SRC=str(native),
                                 API_AUDIT_ORDER=order, API_AUDIT_KIND=kind,
                                 API_AUDIT_OWNER=owner), **{"pass": True}))
        self.path = self.audit / "receipt.json"

    def check(self):
        self.path.write_text(json.dumps(self.receipt))
        return l.semantic_gate(self.path, self.root, self.selected)

    def test_all_eight_actual_source_bound_scenarios(self):
        self.assertEqual(self.check()["cases"], 8)

    def test_gate_follows_the_audits_constants_not_a_copy(self):
        text = (l.AUDIT / "audit_constants.py").read_text()
        changed = text.replace('"SimpTracking", ', "").replace(
            "172", "178").replace("168", "174").replace("176", "182")
        self.assertNotEqual(changed, text)
        self.build(changed)
        self.assertNotIn("SimpTracking", self.constants.NATIVE_MODULES)
        self.assertEqual(self.check()["cases"], 8)
        # A receipt of the old counts no longer fits the new constants.
        self.build(changed)
        for case in self.receipt["cases"]:
            case["checks"] -= 6
        with self.assertRaisesRegex(ValueError, "failed semantic process"):
            self.check()

    def test_audit_run_py_validates_with_the_same_constants(self):
        spec = importlib.util.spec_from_file_location(
            "audit_run_under_test", l.AUDIT / "run.py")
        run = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(run)
        real = l.audit_constants(l.AUDIT)
        self.assertEqual(run.CASE_CHECKS, real.CASE_CHECKS)
        self.assertEqual(run.NATIVE_MODULES, real.NATIVE_MODULES)
        self.assertEqual(run.SOURCES, real.SOURCES)
        self.assertIn("audit_constants.py", real.SOURCES)
        # What run.py accepts per case is what the gate reads.
        for (kind, owner), count in real.CASE_CHECKS.items():
            used = "".join("OBS used.path=%s\n" % (run.ROOT / "src/simp/src"
                                                    / (m + suffix))
                           for m in real.NATIVE_MODULES
                           for suffix in (".sig", ".sml"))
            text = "OK\n" * count + "OBS result=pass\n" + used
            present = all((run.ROOT / "src/simp/src" / (m + s)).is_file()
                          for m in real.NATIVE_MODULES
                          for s in (".sig", ".sml"))
            if present:
                self.assertEqual(
                    run.validate_output(text, 0, kind, owner), count)
            with self.assertRaises(ValueError):
                run.validate_output(text + "OK\n", 0, kind, owner)

    def test_duplicate_missing_failed_or_unbound_semantics_rejected(self):
        original = copy.deepcopy(self.receipt)
        for kind in ("duplicate", "missing", "failed", "source", "log"):
            self.receipt = copy.deepcopy(original)
            if kind == "duplicate":
                self.receipt["cases"][-1] = self.receipt["cases"][0]
            elif kind == "missing":
                self.receipt["cases"].pop()
            elif kind == "failed":
                self.receipt["cases"][0]["returncode"] = 1
            elif kind == "source":
                self.selected[0]["sha256"] = "0" * 64
            else:
                self.receipt["cases"][0]["log_seal"]["sha256"] = "0" * 64
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.check()
            self.selected[0]["sha256"] = l.a.seal(
                self.root / self.selected[0]["git_path"])["sha256"]


class ExitTests(unittest.TestCase):
    def test_cli_does_not_turn_uncertainty_or_failure_into_pass(self):
        argv = ["--baseline", "a" * 40, "--candidate", "b" * 40,
                "--module", "congLib", "--output", "/unused"]
        for decision, code in (("pass", 0), ("fail", 1),
                               ("inconclusive", 2)):
            report = dict(success=True, mode="isolated-source",
                          module="congLib", stage="first",
                          results={"candidate": {"metrics": {
                              "cpu": {"decision": decision}}}})
            with self.subTest(decision=decision), \
                    patch.object(l, "run", return_value=report):
                self.assertEqual(l.main(argv), code)

    def test_cli_requires_inputs_except_for_replay(self):
        self.assertEqual(l.main(["--module", "simpLib"]), 1)
        with patch.object(l, "replay", return_value={"exit": None}) as r:
            self.assertEqual(l.main(["--replay", "/unused"]), 0)
        r.assert_called_once()


if __name__ == "__main__":
    unittest.main()
