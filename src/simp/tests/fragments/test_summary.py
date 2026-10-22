"""Synthetic analyzer tests: no HOL processes, builds or benchmark runs."""
import contextlib
import copy
import gzip
import hashlib
import io
import json
import math
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import summarize as summary


def seal(raw):
    return dict(sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw))


def write_json(path, value):
    raw = json.dumps(value).encode()
    path.write_bytes(gzip.compress(raw, mtime=0) if path.suffix == ".gz"
                     else raw)


def fixture(root, matched=False):
    """One tiny deterministic synthetic fixed-schedule run, with receipts."""
    root.mkdir()
    src = root / "local.sml"
    src.write_text("synthetic source\n")
    selected = dict(reference="pinned", revision="same-revision",
                    sources=[dict(git_path="local.sml",
                                  **seal(src.read_bytes()))],
                    graphs={label: [[n, n+2] for n in summary.SIZES]
                            for label in summary.LABELS},
                    runtime_options=["--gcthreads=1"], supplement_sources=[])
    fixed = {key: 8 for key in summary.KEYS}
    m = dict(schema_version=1, success=True, evidence_id="TASK15-fragments-v1",
             repo=str(root), machine="synthetic", inputs={}, tools={},
             shared_products={}, selections={s: copy.deepcopy(selected)
                                              for s in summary.SIDES},
             performance=dict(pairs=10, samples=3, seconds=.03,
                              fixed_iterations=fixed,
                              fixed_iterations_path="synthetic.json"),
             environment=dict(matched=matched,
                              heap_mb=256 if matched else None,
                              preloads=[], supplement_snapshot=[]), runs=[])
    for side in summary.SIDES:
        receipt = dict(accepted=True, exit=0, timed_out=False,
                       selection=side, fixture="behavior", pair=-1,
                       result=dict(outcome="pass", observations=[]),
                       measurements=selected["graphs"])
        write_json(root / (side + "-behavior--1.json.gz"), receipt)
        for pair in range(10):
            measurements, observations = {}, []
            for key in summary.KEYS:
                # Nonidentical samples demonstrate median-per-process use.
                measurements[key] = [dict(iterations=8, **{
                    metric: v for metric in summary.METRICS})
                    for v in (.5, 1.0, 100.0)]
                observations.append(["observation", "calibration." + key,
                                     "8," + ",".join(["1"]*8) + ",8"])
                for sample in range(3):
                    observations.append(["observation", "batch." + key,
                        str(sample) + ",8," + ",".join(["1"]*8) + ",8"])
            name = side + "-performance-" + str(pair) + ".json.gz"
            receipt = dict(accepted=True, exit=0, timed_out=False,
                           selection=side, fixture="performance", pair=pair,
                           result=dict(outcome="pass",
                                       observations=observations),
                           measurements=measurements,
                           environment=dict(PERF_SAMPLES="3", PERF_FIXED=
                               ",".join(k+"=8" for k in summary.KEYS)))
            write_json(root / name, receipt)
            m["runs"].append(dict(selection=side, pair=pair,
                                  measurements=measurements, receipt=name))
    write_json(root / "manifest.json", m)
    return m


class StatisticsTests(unittest.TestCase):
    def test_student_quantiles_and_fractional_welch_df(self):
        self.assertAlmostEqual(summary.student_inverse(.975, 9),
                               2.26215716274099, places=9)
        self.assertAlmostEqual(summary.student_inverse(.975, 18),
                               2.10092204024096, places=9)
        for df in (1, 9, 13.37, 18):
            for p in (.975, 1-.05/180):
                t = summary.student_inverse(p, df)
                self.assertAlmostEqual(summary.student_cdf(t, df), p,
                                       places=13)
        p = 1-.05/180
        self.assertAlmostEqual(summary.student_inverse(p, 1),
                               math.tan(math.pi*(p-.5)), places=6)

    def test_logmean_and_intervals_not_ratio_average(self):
        ratios = [math.exp(x) for x in ([.01]*5 + [.03]*5)]
        result = summary.log_summary(ratios)
        self.assertAlmostEqual(result["mean_log"], .02)
        self.assertEqual(result["df"], 9)
        self.assertLess(result["simultaneous95ci"][0], result["t95ci"][0])
        self.assertGreater(result["simultaneous95ci"][1], result["t95ci"][1])
        result = summary.log_summary([1]*9 + [1024])
        self.assertNotAlmostEqual(math.exp(result["mean_log"]),
                                  sum([1]*9 + [1024])/10)

    def test_no_zero_omission_or_pseudocounts(self):
        for ratios in ([1]*9 + [None], [1]*9 + [0], [0]*10):
            result = summary.log_summary(ratios)
            self.assertIsNone(result["mean_log"])
            self.assertIsNone(result["t95ci"])
            self.assertEqual(result["status"], "unresolved_zero_timer")

    def test_welch_contrast(self):
        a = summary.log_summary([math.exp(.1 + i*.01) for i in range(10)])
        b = summary.log_summary([math.exp(i*.02) for i in range(10)])
        c = summary.contrast(a, b)
        self.assertAlmostEqual(c["mean_log"], .055)
        self.assertAlmostEqual(c["df"], 225/17)
        self.assertEqual(c["status"], "estimated")


class EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="task15-summary-test-")
        cls.root = Path(cls.temp.name)
        cls.path = cls.root / "run"
        cls.manifest = fixture(cls.path)
        cls.loaded = summary.load_run(cls.path)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def test_valid_complete_matrix_and_medians(self):
        result = summary.process_statistics(self.loaded, "rewrites.0", "cpu")
        self.assertEqual(result["process_medians"], [[1, 1]]*10)
        self.assertEqual(result["paired_ratios"], [1]*10)
        self.assertEqual(result["mean_log"], 0)
        self.assertEqual(result["t95ci"], [0, 0])

    def check_bad_manifest(self, mutate):
        m = copy.deepcopy(self.manifest)
        mutate(m)
        write_json(self.path / "manifest.json", m)
        try:
            with self.assertRaises(summary.InvalidEvidence):
                summary.load_run(self.path)
        finally:
            write_json(self.path / "manifest.json", self.manifest)

    def test_failed_manifest_missing_pair_workload_and_sample(self):
        mutations = [lambda m: m.update(success=False),
                     lambda m: m["runs"].pop(),
                     lambda m: m["runs"][0]["measurements"].pop(
                         "rewrites.0"),
                     lambda m: m["runs"][0]["measurements"][
                         "rewrites.0"].pop(),
                     lambda m: m["performance"].update(pairs=9),
                     lambda m: m["performance"].update(samples=4),
                     lambda m: m["performance"]["fixed_iterations"].update(
                         {"rewrites.0": True}),
                     lambda m: m["runs"].__setitem__(1, m["runs"][0])]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                self.check_bad_manifest(mutate)

    def test_missing_receipt_and_unaccepted_receipt(self):
        name = self.manifest["runs"][0]["receipt"]
        path = self.path / name
        raw = path.read_bytes()
        try:
            path.unlink()
            with self.assertRaises(OSError):
                summary.load_run(self.path)
            receipt = json.loads(gzip.decompress(raw))
            receipt["accepted"] = False
            write_json(path, receipt)
            with self.assertRaises(summary.InvalidEvidence):
                summary.load_run(self.path)
        finally:
            path.write_bytes(raw)

    def test_missing_or_unequal_calibration(self):
        path = self.path / self.manifest["runs"][0]["receipt"]
        raw = path.read_bytes()
        receipt = json.loads(gzip.decompress(raw))
        for action in ("missing", "unequal", "extra"):
            r = copy.deepcopy(receipt)
            obs = r["result"]["observations"]
            if action == "missing":
                obs.pop(0)
            elif action == "unequal":
                obs[0][2] = "16," + ",".join(["1"]*8) + ",16"
            else:
                obs.insert(0, obs[0])
            try:
                write_json(path, r)
                with self.subTest(action=action):
                    with self.assertRaises(summary.InvalidEvidence):
                        summary.load_run(self.path)
            finally:
                path.write_bytes(raw)

    def test_incomplete_graph_and_current_seal_drift(self):
        self.check_bad_manifest(lambda m:
            m["selections"]["candidate"]["graphs"]["rewrites"].pop())
        audit = summary.audit_current(self.path,
                                      self.loaded["sources"]["candidate"])
        self.assertEqual(audit["matching"], 1)
        src = self.path / "local.sml"
        raw = src.read_bytes()
        try:
            src.write_text("changed source\n")
            audit = summary.audit_current(self.path,
                                           self.loaded["sources"]["candidate"])
            self.assertEqual(audit["changed"], ["local.sml"])
        finally:
            src.write_bytes(raw)

    def test_control_must_be_same_source_and_schedule(self):
        a, b = copy.deepcopy(self.loaded), copy.deepcopy(self.loaded)
        b["sources"]["candidate"]["local.sml"]["sha256"] = "f"*64
        with self.assertRaisesRegex(summary.InvalidEvidence, "same-source"):
            summary.compare_runs(a, b)
        b = copy.deepcopy(self.loaded)
        b["manifest"]["performance"]["fixed_iterations"]["rewrites.0"] = 16
        with self.assertRaisesRegex(summary.InvalidEvidence, "schedule"):
            summary.compare_runs(a, b)

    def test_distinct_snapshot_paths_not_mismatched_sources(self):
        a, b = copy.deepcopy(self.loaded), copy.deepcopy(self.loaded)
        entry = dict(source_path="source.sml", source_physical="source.sml",
                     generated=False, snapshot_path="/temporary/a",
                     **seal(b"x"))
        for run in (a, b):
            run["manifest"]["environment"].update(
                matched=True, supplement_snapshot=[copy.deepcopy(entry)])
        b["manifest"]["environment"]["supplement_snapshot"][0][
            "snapshot_path"] = "/temporary/b"
        self.assertTrue(summary.compare_runs(a, b))
        b["manifest"]["environment"]["supplement_snapshot"][0][
            "sha256"] = "f"*64
        with self.assertRaisesRegex(summary.InvalidEvidence, "supplement"):
            summary.compare_runs(a, b)

    def report(self, mutate=None, control_mutate=None, matched=False):
        a, b = copy.deepcopy(self.loaded), copy.deepcopy(self.loaded)
        for run in (a, b):
            run["manifest"]["environment"]["matched"] = matched
        if mutate:
            mutate(a)
        if control_mutate:
            control_mutate(b)
        with patch.object(summary, "load_run", side_effect=[a, b]):
            return summary.summarize("candidate", "control")

    @staticmethod
    def set_ratios(run, key, logs, metric="cpu"):
        for pair, log in enumerate(logs):
            for row in run["processes"]["candidate", pair][key]:
                row[metric] = math.exp(log)

    def test_one_slow_workload_not_hidden_by_89_speedups(self):
        def mutate(run):
            for key in summary.KEYS:
                self.set_ratios(run, key, [-1.0]*10)
            self.set_ratios(run, "rewrites.0", [.1]*10)
        report = self.report(mutate, matched=True)
        self.assertTrue(report["failure"])
        self.assertEqual(report["row_counts"][
            "reproducible_family_red"]["cpu"], 1)
        self.assertEqual(len(report["rows"]), 90)
        self.assertEqual(report["rows"]["rewrites.0"]["metrics"]["cpu"][
            "candidate"]["simultaneous95_decision"], "red_slowdown")
        self.assertFalse(report["method"]["pooling"])

    def test_individual_red_retained_when_family_inconclusive(self):
        report = self.report(lambda run: self.set_ratios(
            run, "rewrites.0", [0.0]*5 + [.04]*5), matched=True)
        row = report["rows"]["rewrites.0"]["metrics"]["cpu"]
        self.assertTrue(row["decisions"]["raw_t95_red"])
        self.assertFalse(row["decisions"]["raw_family_red"])
        self.assertEqual(report["verdict"], "inconclusive")
        self.assertEqual(report["final_default_wholemodule_gate"],
                         "NOT ESTABLISHED")

    def test_control_does_not_erase_raw_default_red(self):
        mutate = lambda run: self.set_ratios(run, "rewrites.0", [.1]*10)
        default = self.report(mutate, mutate)
        matched = self.report(mutate, mutate, matched=True)
        self.assertTrue(default["failure"])
        self.assertFalse(matched["failure"])
        for report in (default, matched):
            flags = report["rows"]["rewrites.0"]["metrics"]["cpu"][
                "decisions"]
            self.assertTrue(flags["raw_family_red"])
            self.assertFalse(flags["reproducible_family_red"])
            self.assertEqual(report["row_counts"][
                "control_family_red"]["cpu"], 1)

    def test_graph_sensitivity_even_with_fast_timings_and_stale_cache(self):
        def mutate(run):
            m = run["manifest"]
            m["selections"]["candidate"]["graphs"]["rewrites"][0][1] += 1
            m["graph_comparison"] = {"forged": "all nonpositive"}
            run["graphs"] = summary.graph_rows(m)
            for key in summary.KEYS:
                self.set_ratios(run, key, [-1]*10)
        report = self.report(mutate, matched=True)
        self.assertTrue(report["failure"])
        self.assertEqual(report["graph_red_rows"], ["rewrites.0"])
        self.assertEqual(report["rows"]["rewrites.0"]["candidate_graph"][
            "delta_words"], 1)

    def test_deterministic_and_cli_incomplete_result(self):
        self.assertEqual(self.report(), self.report())
        output = self.root / "incomplete-summary.json"
        with contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            status = summary.main(["--candidate", str(self.root / "pending"),
                                   "--control", str(self.path),
                                   "--output", str(output)])
        self.assertEqual(status, 2)
        result = json.loads(output.read_text())
        self.assertFalse(result["valid_evidence"])
        self.assertEqual(result["verdict"], "invalid_or_incomplete")
        output.unlink()


if __name__ == "__main__":
    unittest.main()
