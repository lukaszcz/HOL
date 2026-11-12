#!/usr/bin/env python3
"""Synthetic protocol controls only; never runs an ML benchmark."""
import copy
import gzip
import json
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

import performance_schema as schema
from audit_evidence import audit
from summarize import summarize

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "compatibility"))
import run_paired as runner


def observations():
    # wall, non-GC usr/sys, GC usr/sys, inclusive usr/sys, GC user, consumed
    times = "0.25,0.20,0.01,0.02,0.005,0.22,0.015,0.02,"
    es = [["observation", "timer.accounting", times + "5"],
          ["check", "timer accounting", "pass"],
          ["check", "workload inputs", "pass"]]
    counts = (1, 2, 1, 1, 2, 67)
    for label, count in zip(schema.TRAVERSAL_LABELS, counts):
        es.append(["observation", "calibration." + label,
                   "1," + times + str(count)])
        for i in range(3):
            es += [["observation", "batch." + label,
                    f"{i},1," + times + str(count)],
                   ["check", "results " + label, "pass"]]
    return es + [["observation", "sink", str(5 + 4 * sum(counts))]]


class TraversalSchemaTests(unittest.TestCase):
    def setUp(self):
        self.events = observations()
        self.options = schema.suite_options({"suite": "traversal"})

    def validate(self, es):
        return schema.validate(es, 3, 0.2, **self.options)

    def test_complete_and_defaults_unchanged(self):
        _, data = self.validate(self.events)
        self.assertEqual(tuple(data["workloads"]), schema.TRAVERSAL_LABELS)
        self.assertEqual(data["storage"], [])
        self.assertEqual(schema.suite_options({}), {})
        with self.assertRaises(ValueError):
            schema.validate(self.events, 3, 0.2)
        with self.assertRaisesRegex(ValueError, "unknown performance suite"):
            schema.suite_options({"suite": "typo"})

    def test_every_event_required(self):
        for i in range(len(self.events)):
            with self.subTest(i=i), self.assertRaises(ValueError):
                self.validate(self.events[:i] + self.events[i + 1:])

    def test_wrong_consumption_and_iteration_counts(self):
        for i, event in enumerate(self.events):
            if not event[1].startswith(("calibration.", "batch.")):
                continue
            fields_to_break = ((-1, 0, 1) if event[1].startswith("batch.")
                               else (-1, 0))
            for field in fields_to_break:
                es = copy.deepcopy(self.events)
                fields = es[i][-1].split(",")
                fields[field] = str(int(fields[field]) + 1)
                es[i][-1] = ",".join(fields)
                with self.subTest(i=i, field=field):
                    with self.assertRaises(ValueError):
                        self.validate(es)

    def test_extras_and_wrong_suite_fail_closed(self):
        for event in (self.events[-1], ["exception", "Fail", "bad proof"],
                      ["observation", "storage", "0"]):
            with self.assertRaises(ValueError):
                self.validate(self.events + [event])
        es = copy.deepcopy(self.events)
        es[3][1] = "calibration.raw_reuse_1000"
        with self.assertRaisesRegex(ValueError, "ordered performance event"):
            self.validate(es)


class TraversalHarnessTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="traversal-protocol-")
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.private = self.repo / "baseline"
        self.private.mkdir()
        for name in ("Paired", "Traverse", "Performance"):
            (self.private / (name + ".sml")).write_text("(* synthetic *)\n")
        options = schema.suite_options({"suite": "traversal"})
        obs, data = schema.validate(observations(), 3, 0.2, **options)
        checks = sum(e[0] == "check" for e in obs)
        es = [["begin", "baseline", "performance", "none"],
              ["cwd", str(self.private)],
              ["holdir", str(self.repo), str(self.repo)],
              ["preloaded", "HolKernel,Paired"],
              ["heapfile", str(self.private / "Paired.sml")],
              ["search", str(self.private)],
              ["search", str(self.repo / "sigobj")]]
        for name in ("Traverse", "Performance"):
            path = str(self.private / (name + ".sml"))
            es += [["use", path]] + (obs if name == "Performance" else [])
            es += [["used", path]]
        es += [["loaded", str(self.private / (name + ".sml"))]
               for name in ("Paired", "Traverse", "Performance")]
        es += [["end", "pass", str(checks)]]
        self.args = dict(selection="baseline", fixture="performance",
                         control="none", private=self.private, repo=self.repo,
                         private_names={"Traverse", "simpLib"},
                         flavor="baseline", signature="pass", source_hashes={},
                         expected_observations=obs, traversal_performance=True)
        text = "".join(runner.PREFIX + str(i) + "\t" + "\t".join(e) + "\n"
                       for i, e in enumerate(es))
        self.receipt = dict(stdout=text, exit=0, timed_out=False,
                            accepted=True, selection="baseline", pair=0,
                            fixture="performance", cwd=str(self.private),
                            command=[str(self.private / "paired.exe")],
                            measurements=data, environment={
                                "PAIR_SELECTION": "baseline",
                                "PAIR_PRIVATE": str(self.private),
                                "PAIR_FIXTURE": "performance",
                                "PAIR_TARGET": "Performance",
                                "PAIR_CONTROL": "none",
                                "PERF_SAMPLES": "3", "PERF_SECONDS": "0.2"})
        self.receipt["result"] = runner.validate(self.receipt, **self.args)

    def test_flag_requires_pairs_before_creating_output(self):
        output = self.repo / "must-not-exist"
        result = subprocess.run(
            [sys.executable, "-B", str(Path(runner.__file__)),
             "--candidate", "HEAD",
             "--candidate-signature", "pass",
             "--candidate-behavior", "baseline",
             "--traversal-performance", "--output", str(output)],
            capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("requires --performance-pairs", result.stderr)
        self.assertFalse(output.exists())

    def test_installed_fixture_selection(self):
        dst = self.repo / "install"
        dst.mkdir()
        source = Path(__file__).resolve().parent
        for traversal, fixture in ((False, "Performance.sml"),
                                   (True, "TraversalPerformance.sml")):
            runner.install_fixtures(dst, performance=True,
                                    traversal_performance=traversal)
            self.assertEqual((dst / "Performance.sml").read_bytes(),
                             (source / fixture).read_bytes())
            self.assertIn("paired.exe: Performance.uo",
                          (dst / "Holmakefile").read_text())

    def test_traverse_only_and_default_module_guard(self):
        self.assertEqual(self.receipt["result"]["expected_test_count"], 20)
        with self.assertRaisesRegex(runner.InvalidRun,
                                    "selected implementation"):
            runner.validate(self.receipt, **dict(self.args,
                                               traversal_performance=False))

    def test_path_and_footer_still_audited(self):
        wrong = self.repo / "candidate"
        wrong.mkdir()
        (wrong / "Traverse.sml").write_bytes(
            (self.private / "Traverse.sml").read_bytes())
        receipt = dict(self.receipt, stdout=self.receipt["stdout"].replace(
            str(self.private / "Traverse.sml"), str(wrong / "Traverse.sml")))
        with self.assertRaisesRegex(runner.InvalidRun, "wrong loaded.*path"):
            runner.validate(receipt, **self.args)
        receipt = dict(self.receipt, stdout=self.receipt["stdout"].replace(
            "\tend\tpass\t20\n", "\tend\tpass\t19\n"))
        with self.assertRaisesRegex(runner.InvalidRun,
                                    "completion/test count"):
            runner.validate(receipt, **self.args)

    def manifest(self):
        fp = {name + ".sml": runner.fingerprint(self.private / (name + ".sml"))
              for name in ("Paired", "Traverse", "Performance")}
        return dict(success=True, repo=str(self.repo), runs=[], performance={
            "suite": "traversal", "samples": 3,
            "batch_seconds": 0.2, "pairs": 1},
            inputs={"src/simp/tests/performance/TraversalPerformance.sml":
                    fp["Performance.sml"]}, selections={"baseline": {
                        "private": str(self.private), "sources": [{
                            "git_path": "src/simp/src/Traverse.sml",
                            "private_path": str(self.private / "Traverse.sml"),
                            **fp["Traverse.sml"]}],
                        "fixture_products": {k: v for k, v in fp.items()
                                             if k != "Traverse.sml"},
                        "products": {}}})

    def test_archived_audit_fixture_binding(self):
        manifest = self.manifest()
        audit(manifest, self.receipt)
        manifest["inputs"][
            "src/simp/tests/performance/TraversalPerformance.sml"] = {}
        with self.assertRaisesRegex(ValueError, "fixture binding"):
            audit(manifest, self.receipt)

    def test_summary_uses_suite_labels_and_rejects_missing_workload(self):
        manifest = self.manifest()
        for side in ("baseline", "candidate"):
            receipt = dict(self.receipt, selection=side)
            name = side + ".json.gz"
            (self.repo / name).write_bytes(
                gzip.compress(json.dumps(receipt).encode()))
            manifest["runs"].append(dict(receipt=name, accepted=True))
        (self.repo / "manifest.json").write_text(json.dumps(manifest))
        result = summarize(self.repo)
        self.assertEqual(tuple(result["workloads"]), schema.TRAVERSAL_LABELS)
        self.assertEqual(result["storage"],
                         dict(baseline=[[]], candidate=[[]]))
        self.assertEqual(result["workloads"]["deep_factory_64"]["cpu"][
            "median_paired_ratio"], 1.0)
        receipt = copy.deepcopy(self.receipt)
        del receipt["result"]["events"][10]
        (self.repo / "baseline.json.gz").write_bytes(
            gzip.compress(json.dumps(receipt).encode()))
        with self.assertRaises(ValueError):
            summarize(self.repo)


if __name__ == "__main__":
    unittest.main()
