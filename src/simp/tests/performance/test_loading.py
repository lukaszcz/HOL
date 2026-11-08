#!/usr/bin/env python3
"""Non-timing loading protocol regressions; synthetic logs are NOT evidence."""
import copy
import gzip
import json
import math
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import loading as l

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

    def test_zero_gc_inconclusive_and_no_pairs_dropped(self):
        rows = self.rows()
        rows[0]["measurement"]["raw"]["gc_cpu"] = 0
        result = l.statistics(rows, 10, False)["metrics"]["gc_cpu"]
        self.assertEqual(result["decision"], "inconclusive")
        self.assertEqual(len(result["observations"]), 10)

    def test_calibration_failure_not_pass(self):
        rows = self.rows()
        rows[4]["measurement"]["calibrated"] = False
        result = l.statistics(rows, 10, False)
        self.assertTrue(all(m["decision"] == "inconclusive"
                            for m in result["metrics"].values()))


class SemanticGateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="loading-gate-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.audit = self.root / "src/simp/tests/api-audit"
        self.audit.mkdir(parents=True)
        native = self.root / "src/simp/src"
        self.selected, actual = [], {}
        modules = ("simpLib", "congLib", "Traverse", "Cond_rewr", "Trace",
                   "simpExtLib", "TraverseExt",
                   "Cond_rewrExt", "congExtLib")
        for module in modules:
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
        for name in ("run.py", "Holmakefile", "selftest.sml", "ordinary.ML",
                     "runtime.ML", "Documentation.sml"):
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
            count = {("attribute", "before"): 178,
                     ("attribute", "after"): 174,
                     ("exporter", "before"): 182,
                     ("exporter", "after"): 177}[kind, owner]
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
            report = dict(success=True, mode="isolated-source", module="congLib",
                          results={"candidate": {"metrics": {
                              "cpu": {"decision": decision}}}})
            with self.subTest(decision=decision), \
                    patch.object(l, "run", return_value=report):
                self.assertEqual(l.main(argv), code)


if __name__ == "__main__":
    unittest.main()
