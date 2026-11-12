#!/usr/bin/env python3
"""Synthetic conditional protocol/source controls; no timing claims."""
import copy
import gzip
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import performance_schema as schema
from audit_evidence import audit
from summarize import summarize
from test_traversal_performance import observations as traversal_observations

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "compatibility"))
import run_paired as runner


def observations():
    times = "0.25,0.20,0.01,0.02,0.005,0.22,0.015,0.02,"
    es = [["observation", "timer.accounting", times + "5"],
          ["check", "timer accounting", "pass"],
          ["check", "workload inputs", "pass"]]
    # Independent constants catch an accidental change to callback accounting.
    counts = (1, 1, 2, 2, 1, 1)
    for label, count in zip(schema.CONDITIONAL_LABELS, counts):
        es.append(["observation", "calibration." + label,
                   "1," + times + str(count)])
        for i in range(3):
            es += [["observation", "batch." + label,
                    f"{i},1," + times + str(count)],
                   ["check", "results " + label, "pass"]]
    return es + [["observation", "sink", str(5 + 4 * sum(counts))]]


class ConditionalSchemaTests(unittest.TestCase):
    def setUp(self):
        self.events = observations()
        self.options = schema.suite_options({"suite": "conditional"})

    def validate(self, es):
        return schema.validate(es, 3, 0.2, **self.options)

    def test_complete_and_cross_suite_rejection(self):
        _, data = self.validate(self.events)
        self.assertEqual(tuple(data["workloads"]), schema.CONDITIONAL_LABELS)
        self.assertEqual(data["storage"], [])
        self.assertEqual(schema.suite_options({}), {})
        for suite in ({}, {"suite": "traversal"}):
            with self.assertRaises(ValueError):
                schema.validate(self.events, 3, 0.2,
                                **schema.suite_options(suite))
        with self.assertRaises(ValueError):
            self.validate(traversal_observations())

    def test_every_event_required(self):
        for i in range(len(self.events)):
            with self.subTest(i=i), self.assertRaises(ValueError):
                self.validate(self.events[:i] + self.events[i + 1:])

    def test_wrong_counts_and_invalid_metrics(self):
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
        for bad in ("nan", "inf", "~1", "0"):
            es = copy.deepcopy(self.events)
            fields = es[3][-1].split(",")
            fields[1] = bad
            es[3][-1] = ",".join(fields)
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                self.validate(es)

    def test_extras_rejected(self):
        for event in (self.events[-1], ["exception", "Fail", "bad proof"],
                      ["observation", "storage", "0"]):
            with self.assertRaises(ValueError):
                self.validate(self.events + [event])


class ConditionalHarnessTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="conditional-protocol-")
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.private = self.repo / "baseline"
        self.private.mkdir()
        for name in ("Paired", "Cond_rewr", "Performance"):
            (self.private / (name + ".sml")).write_text("(* synthetic *)\n")
        obs, data = schema.validate(
            observations(), 3, 0.2,
            **schema.suite_options({"suite": "conditional"}))
        checks = sum(e[0] == "check" for e in obs)
        es = [["begin", "baseline", "performance", "none"],
              ["cwd", str(self.private)],
              ["holdir", str(self.repo), str(self.repo)],
              ["preloaded", "HolKernel,Paired"],
              ["heapfile", str(self.private / "Paired.sml")],
              ["search", str(self.private)],
              ["search", str(self.repo / "sigobj")]]
        for name in ("Cond_rewr", "Performance"):
            path = str(self.private / (name + ".sml"))
            es += [["use", path]] + (obs if name == "Performance" else [])
            es += [["used", path]]
        es += [["loaded", str(self.private / (name + ".sml"))]
               for name in ("Paired", "Cond_rewr", "Performance")]
        es += [["end", "pass", str(checks)]]
        self.args = dict(selection="baseline", fixture="performance",
                         control="none", private=self.private, repo=self.repo,
                         private_names={"Cond_rewr", "Traverse", "simpLib",
                                        "Cond_rewrExt", "FutureExtLib"},
                         flavor="baseline", signature="pass", source_hashes={},
                         expected_observations=obs,
                         conditional_performance=True)
        self.receipt = dict(stdout=self.encode(es), exit=0, timed_out=False,
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

    @staticmethod
    def encode(es):
        return "".join(runner.PREFIX + str(i) + "\t" + "\t".join(e) + "\n"
                       for i, e in enumerate(es))

    def test_flags_fail_before_output_creation(self):
        output = self.repo / "must-not-exist"
        script = str(Path(runner.__file__))
        for flags, reason in ((["--conditional-performance"],
                               "requires --performance-pairs"),
                              (["--conditional-performance",
                                "--traversal-performance",
                                "--performance-pairs", "1"],
                               "not allowed with argument")):
            result = subprocess.run(
                [sys.executable, "-B", script,
                 "--candidate", "HEAD",
                 "--candidate-signature", "pass",
                 "--candidate-behavior", "baseline",
                 *flags, "--output", str(output)],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn(reason, result.stderr)
            self.assertFalse(output.exists())

    def test_installed_fixture_and_hash(self):
        dst = self.repo / "install"
        dst.mkdir()
        runner.install_fixtures(dst, performance=True,
                                conditional_performance=True)
        source = Path(__file__).with_name("ConditionalPerformance.sml")
        self.assertEqual(runner.fingerprint(dst / "Performance.sml"),
                         runner.fingerprint(source))
        self.assertIn("paired.exe: Performance.uo",
                      (dst / "Holmakefile").read_text())
        with self.assertRaisesRegex(runner.InvalidRun, "mutually exclusive"):
            runner.install_fixtures(dst, performance=True,
                                    conditional_performance=True,
                                    traversal_performance=True)

    def test_conditional_only_and_default_guards(self):
        self.assertEqual(self.receipt["result"]["expected_test_count"], 20)
        for flags in (dict(conditional_performance=False),
                      dict(conditional_performance=False,
                           traversal_performance=True)):
            with self.assertRaisesRegex(runner.InvalidRun,
                                        "selected implementation"):
                runner.validate(self.receipt, **dict(self.args, **flags))

    def test_excludes_source_tied_modules_in_all_inventories(self):
        for name in ("Traverse", "simpLib", "Cond_rewrExt", "FutureExtLib"):
            path = str(self.private / (name + ".sml"))
            (self.private / (name + ".sml")).write_text("(* forbidden *)\n")
            for mode in ("used", "heap", "preloaded"):
                es = copy.deepcopy(self.receipt["result"]["events"])
                if mode == "preloaded":
                    es[3][1] += "," + name
                else:
                    if mode == "heap":
                        es.insert(5, ["heapfile", path])
                    else:
                        es[7:7] = [["use", path], ["used", path]]
                    es.insert(-1, ["loaded", path])
                receipt = dict(self.receipt, stdout=self.encode(es))
                with self.subTest(name=name, mode=mode):
                    with self.assertRaises(runner.InvalidRun):
                        runner.validate(receipt, **self.args)

    def test_physical_extension_alias_rejected(self):
        extension = self.private / "Cond_rewrExt.sml"
        extension.write_text("(* forbidden *)\n")
        alias = self.private / "Alias.sml"
        alias.symlink_to(extension)
        es = copy.deepcopy(self.receipt["result"]["events"])
        es[7:7] = [["use", str(alias)], ["used", str(alias)]]
        es.insert(-1, ["loaded", str(alias)])
        receipt = dict(self.receipt, stdout=self.encode(es))
        with self.assertRaisesRegex(runner.InvalidRun, "non-direct module"):
            runner.validate(receipt, **self.args)

    def test_source_paths_hashes_and_footer(self):
        wrong = self.repo / "candidate"
        wrong.mkdir()
        (wrong / "Cond_rewr.sml").write_bytes(
            (self.private / "Cond_rewr.sml").read_bytes())
        receipt = dict(self.receipt, stdout=self.receipt["stdout"].replace(
            str(self.private / "Cond_rewr.sml"), str(wrong / "Cond_rewr.sml")))
        with self.assertRaisesRegex(runner.InvalidRun, "wrong loaded.*path"):
            runner.validate(receipt, **self.args)
        hashes = {str(self.private / "Performance.sml"):
                  runner.fingerprint(self.private / "Performance.sml")}
        (self.private / "Performance.sml").write_text("(* changed *)\n")
        with self.assertRaisesRegex(runner.InvalidRun, "source changed"):
            runner.validate(self.receipt,
                            **dict(self.args, source_hashes=hashes))
        receipt = dict(self.receipt, stdout=self.receipt["stdout"].replace(
            "\tend\tpass\t20\n", "\tend\tpass\t19\n"))
        with self.assertRaisesRegex(runner.InvalidRun,
                                    "completion/test count"):
            runner.validate(receipt, **self.args)

    def manifest(self):
        fp = {name + ".sml": runner.fingerprint(self.private / (name + ".sml"))
              for name in ("Paired", "Cond_rewr", "Performance")}
        sources = [{"git_path": "src/simp/src/Cond_rewr.sml",
                    "private_path": str(self.private / "Cond_rewr.sml"),
                    **fp["Cond_rewr.sml"]}]
        # Exclusion names come from selected source inventory, not a frozen
        # list of extension modules known to the test harness.
        sources += [{"git_path": "src/simp/src/" + n + ".sml",
                     "private_path": str(self.private / (n + ".sml")),
                     "sha256": "0" * 64, "bytes": 0}
                    for n in ("Traverse", "simpLib", "Cond_rewrExt",
                              "FutureExtLib")]
        return dict(success=True, repo=str(self.repo), runs=[], performance={
            "suite": "conditional", "samples": 3,
            "batch_seconds": 0.2, "pairs": 1},
            inputs={"src/simp/tests/performance/ConditionalPerformance.sml":
                    fp["Performance.sml"]}, selections={"baseline": {
                        "private": str(self.private), "sources": sources,
                        "fixture_products": {k: v for k, v in fp.items()
                                             if k != "Cond_rewr.sml"},
                        "products": {}}})

    def test_archived_audit_fixture_and_source_binding(self):
        manifest = self.manifest()
        audit(manifest, self.receipt)
        changed = copy.deepcopy(manifest)
        changed["inputs"][
            "src/simp/tests/performance/ConditionalPerformance.sml"] = {}
        with self.assertRaisesRegex(ValueError, "fixture binding"):
            audit(changed, self.receipt)
        receipt = copy.deepcopy(self.receipt)
        receipt["result"]["paths"][str(self.private / "Cond_rewr.sml")][
            "sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "source/hash mismatch"):
            audit(manifest, receipt)
        for kind in ("loaded", "heapfile", "preloaded"):
            receipt = copy.deepcopy(self.receipt)
            value = ("FutureExtLib" if kind == "preloaded" else
                     str(self.private / "FutureExtLib.sml"))
            receipt["result"]["events"].insert(-1, [kind, value])
            with self.assertRaisesRegex(ValueError, "non-direct module"):
                audit(manifest, receipt)

    def test_summary_uses_suite_labels(self):
        manifest = self.manifest()
        for side in ("baseline", "candidate"):
            receipt = dict(self.receipt, selection=side)
            name = side + ".json.gz"
            (self.repo / name).write_bytes(
                gzip.compress(json.dumps(receipt).encode()))
            manifest["runs"].append(dict(receipt=name, accepted=True))
        (self.repo / "manifest.json").write_text(json.dumps(manifest))
        result = summarize(self.repo)
        self.assertEqual(tuple(result["workloads"]), schema.CONDITIONAL_LABELS)
        self.assertEqual(result["storage"],
                         dict(baseline=[[]], candidate=[[]]))
        self.assertEqual(result["workloads"]["conditional_construct"]["cpu"][
            "median_paired_ratio"], 1.0)
        manifest["performance"]["suite"] = "traversal"
        (self.repo / "manifest.json").write_text(json.dumps(manifest))
        with self.assertRaises(ValueError):
            summarize(self.repo)


if __name__ == "__main__":
    unittest.main()
