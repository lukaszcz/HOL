#!/usr/bin/env python3
"""Fail-closed telemetry controls; optional REAL two-selection SML selftest.

python3 -B test_runtime_metrics.py
RUNTIME_METRICS_SML=1 RUNTIME_METRICS_EVIDENCE=/tmp/new-runtime.json \
  python3 -B test_runtime_metrics.py
Use compatibility/evidence/task26/root-wrapper.sh if heaps embed the old root.
The SML control intentionally collects, but does not measure performance.
"""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest

import runtime_metrics as rm


def snapshot(counter=10):
    return dict(gcFullGCs=counter, gcPartialGCs=counter * 2,
                gcSharePasses=counter // 2, sizeHeap=2 ** 54,
                sizeHeapFreeLastGC=800, sizeHeapFreeLastFullGC=900,
                sizeAllocation=1000, sizeAllocationFree=700,
                sizeStacks=200, sizeCode=100, rssBytes=4096, hwmBytes=8192)


def runtime(stage, count, counter):
    return dict(schema=1, stage=stage, iterations=count,
                before=snapshot(counter), after=snapshot(counter + 1))


def encode(rows, prefix="@@MATRIX_RUNTIME"):
    return [prefix + "\t" + json.dumps(r) for r in rows]


def release_row():
    return dict(schema=1, scope="controlled-simpset-ref-closure",
                retained=True, collected=True, fullGCs=4,
                releaseCollections=3, status="pass",
                blockedReason="")


class RuntimeTests(unittest.TestCase):
    def setUp(self):
        self.rows = [runtime("calibration", 1, 10),
                     runtime("calibration", 2, 12),
                     runtime("sample", 2, 14), runtime("sample", 2, 16)]
        self.timings = copy.deepcopy(rm.SMOKE_MEASUREMENTS)

    def validate(self):
        return rm.validate(encode(self.rows), self.timings)

    def test_actual_deltas_bytes_and_scopes(self):
        result = self.validate()
        self.assertEqual(result["gcStatus"], "measured")
        self.assertEqual(result["heapStatus"], "measured")
        self.assertEqual(result["rssStatus"], "measured")
        self.assertEqual(result["scopes"], rm.SCOPES)
        for row in result["batches"]:
            self.assertEqual(row["gcCounts"]["gcFullGCs"], 1)
            self.assertEqual(row["gcCounts"]["gcPartialGCs"], 2)
            self.assertIs(type(row["before"]["sizeHeap"]), int)
            self.assertEqual(row["before"]["sizeHeap"], 2 ** 54)
            self.assertEqual(row["hwmDeltaBytes"], 0)
        for field, status in (("allocatedBytes", "allocatedBytesStatus"),
                              ("temporaryPeakBytes", "temporaryPeakStatus")):
            self.assertIsNone(result[field])
            self.assertEqual(result[status], "uncollected")
        self.assertEqual(result["releaseStatus"], "uncollected")

    def test_sample_mapping_and_untouched_timing_input(self):
        original = copy.deepcopy(self.timings)
        result = self.validate()
        self.assertEqual([r["index"] for r in result["batches"]], [0, 1, 0, 1])
        self.assertEqual([r["stage"] for r in result["batches"]],
                         ["calibration", "calibration", "sample", "sample"])
        self.assertEqual(self.timings, original)

    def test_no_gc_is_valid_not_missing(self):
        for row in self.rows:
            for side in ("before", "after"):
                for key in rm.COUNTERS:
                    row[side][key] = 0
        for row in self.validate()["batches"]:
            self.assertEqual(row["gcCounts"], dict.fromkeys(rm.COUNTERS, 0))

    def test_missing_telemetry_never_passes(self):
        for rows in ([], self.rows[:-1], self.rows[1:], self.rows * 2):
            with self.subTest(rows=len(rows)), self.assertRaises(ValueError):
                rm.validate(encode(rows), self.timings)

    def test_absent_or_empty_timing_workloads_rejected(self):
        for timings in ({}, {"workloads": {}}, {"workloads": []},
                        {"workloads": {"x": {}}}):
            with self.subTest(timings=timings), self.assertRaises(ValueError):
                rm.validate(encode(self.rows), timings)

    def test_missing_or_extra_fields_every_level(self):
        for location in ((), ("before",), ("after",)):
            target = self.rows[0]
            for key in location:
                target = target[key]
            for field in list(target) + ["typo"]:
                rows = copy.deepcopy(self.rows)
                mutated = rows[0]
                for key in location:
                    mutated = mutated[key]
                if field == "typo":
                    mutated[field] = 0
                else:
                    del mutated[field]
                with self.subTest(location=location, field=field):
                    with self.assertRaises(ValueError):
                        rm.validate(encode(rows), self.timings)

    def test_strict_integer_types_and_no_nonfinite(self):
        for field in (*rm.COUNTERS, *rm.HEAP, *rm.RSS):
            for value in (True, 1.0, -1, "1", [], {}, float("nan")):
                rows = copy.deepcopy(self.rows)
                rows[0]["before"][field] = value
                with self.subTest(field=field, value=value):
                    with self.assertRaises(ValueError):
                        rm.validate(encode(rows), self.timings)

    def test_strict_stage_count_schema(self):
        for field, values in (("schema", (True, 1.0, 2, None)),
                              ("stage", ("batch", "timer.accounting", None)),
                              ("iterations", (True, 1.0, 0, -1, "1"))):
            for value in values:
                rows = copy.deepcopy(self.rows)
                rows[0][field] = value
                with self.subTest(field=field, value=value):
                    with self.assertRaises(ValueError):
                        rm.validate(encode(rows), self.timings)

    def test_every_timing_iteration_must_match(self):
        for index in range(len(self.rows)):
            rows = copy.deepcopy(self.rows)
            rows[index]["iterations"] *= 2
            with self.subTest(index=index), self.assertRaisesRegex(
                    ValueError, "iteration mismatch"):
                rm.validate(encode(rows), self.timings)

    def test_reordered_and_wrong_stages_rejected(self):
        for index in range(len(self.rows)):
            rows = copy.deepcopy(self.rows)
            rows[index]["stage"] = ("sample" if rows[index]["stage"] ==
                                    "calibration" else "calibration")
            with self.subTest(index=index), self.assertRaises(ValueError):
                rm.validate(encode(rows), self.timings)
        with self.assertRaises(ValueError):
            rm.validate(encode(list(reversed(self.rows))), self.timings)

    def test_all_gc_counters_monotonic_within_and_across_batches(self):
        for field in rm.COUNTERS:
            for index, side in ((0, "after"), (1, "before")):
                rows = copy.deepcopy(self.rows)
                rows[index][side][field] = 0
                with self.subTest(field=field, side=side):
                    with self.assertRaisesRegex(ValueError, "nonmonotonic GC"):
                        rm.validate(encode(rows), self.timings)

    def test_raw_hwm_regression_blocks_rss_never_silently_clamped(self):
        # Approximate RSS/HWM cannot establish a valid high-water delta.
        # Keep independent timers/GC, preserve raw fields, block RSS inference.
        for index, side in ((0, "after"), (1, "before")):
            rows = copy.deepcopy(self.rows)
            rows[index][side]["hwmBytes"] = 4096
            with self.subTest(index=index, side=side):
                result = rm.validate(encode(rows), self.timings)
                self.assertEqual(result["rssStatus"], "blocked")
                self.assertEqual(result["gcStatus"], "measured")
                self.assertEqual(result["batches"][index][side]["hwmBytes"],
                                 4096)
                self.assertTrue(all(r["hwmDeltaBytes"] is None
                                    for r in result["batches"]))
                self.assertIn("nonmonotonic", result["batches"][0][
                    "rssBlockedReason"])

    def test_rss_is_not_monotonic_or_a_temporary_peak(self):
        self.rows[0]["after"]["rssBytes"] = 1024
        result = self.validate()
        self.assertIsNone(result["temporaryPeakBytes"])
        self.assertEqual(result["batches"][0]["hwmDeltaBytes"], 0)

    def test_missing_linux_rss_is_explicitly_blocked(self):
        for field in rm.RSS:
            self.rows[0]["after"][field] = None
        result = self.validate()
        self.assertEqual(result["rssStatus"], "blocked")
        self.assertEqual(result["gcStatus"], "measured")
        row = result["batches"][0]
        self.assertEqual(row["rssStatus"], "blocked")
        self.assertTrue(row["rssBlockedReason"])
        self.assertIsNone(row["hwmDeltaBytes"])

    def test_partial_or_impossible_rss_rejected(self):
        for field, value in (("rssBytes", None), ("hwmBytes", None),
                             ("rssBytes", 0), ("hwmBytes", 1024)):
            rows = copy.deepcopy(self.rows)
            rows[0]["before"][field] = value
            with self.subTest(field=field, value=value):
                with self.assertRaises(ValueError):
                    rm.validate(encode(rows), self.timings)

    def test_gc_updated_heap_sizes_can_shrink(self):
        self.rows[0]["after"]["sizeHeap"] = 100
        self.validate()
        self.rows[0]["after"]["sizeAllocationFree"] = 1001
        with self.assertRaisesRegex(ValueError, "free exceeds capacity"):
            self.validate()

    def test_raw_protocol_rejects_bad_json_duplicate_keys_and_framing(self):
        for line in ("@@MATRIX_RUNTIME", "prefix@@MATRIX_RUNTIME\t{}",
                     "@@MATRIX_RUNTIME\t{}\textra", "@@MATRIX_RUNTIME\t[1]",
                     '@@MATRIX_RUNTIME\t{"schema":1,"schema":1}',
                     "@@MATRIX_RUNTIME\t{", "@@MATRIX_RUNTIME\tNaN"):
            with self.subTest(line=line), self.assertRaises(ValueError):
                rm.parse([line])

    def test_other_output_ignored_not_confused_with_telemetry(self):
        result = rm.validate(["@@PAIR\t0\tbegin", "ordinary stdout",
                              *encode(self.rows), "@@MATRIX_RELEASE\t{}"],
                             self.timings)
        self.assertEqual(len(result["batches"]), 4)


class ReleaseTests(unittest.TestCase):
    def test_actual_release_pass(self):
        row = release_row()
        self.assertEqual(rm.release(encode([row], "@@MATRIX_RELEASE")), row)

    def test_surviving_referent_is_blocked_never_pass(self):
        row = release_row()
        row.update(collected=False, status="blocked", blockedReason=
                   "weak referent survived three explicit full collections")
        result = rm.release(encode([row], "@@MATRIX_RELEASE"))
        self.assertEqual(result["status"], "blocked")
        row["status"] = "pass"
        with self.assertRaises(ValueError):
            rm.release(encode([row], "@@MATRIX_RELEASE"))

    def test_no_absence_or_reachable_words_substitute(self):
        for rows in ([], [release_row(), release_row()],
                     [{"released_root": 0}]):
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                rm.release(encode(rows, "@@MATRIX_RELEASE"))

    def test_retention_collection_and_status_controls(self):
        for field, value in (("schema", True), ("retained", False),
                             ("retained", 1), ("collected", 1),
                             ("fullGCs", 3), ("fullGCs", 4.0),
                             ("releaseCollections", 2),
                             ("releaseCollections", 3.0),
                             ("scope", "all-client-closures"),
                             ("blockedReason", "missing"),
                             ("status", "uncollected")):
            row = release_row()
            row[field] = value
            with self.subTest(field=field, value=value):
                with self.assertRaises(ValueError):
                    rm.release(encode([row], "@@MATRIX_RELEASE"))
        for field in release_row():
            row = release_row()
            del row[field]
            with self.subTest(missing=field), self.assertRaises(ValueError):
                rm.release(encode([row], "@@MATRIX_RELEASE"))


@unittest.skipUnless(os.environ.get("RUNTIME_METRICS_SML") == "1",
                     "set RUNTIME_METRICS_SML=1 for real SML selftests")
class RealSMLTests(unittest.TestCase):
    def test_baseline_and_candidate_selftest_launcher(self):
        path = os.environ.get("RUNTIME_METRICS_EVIDENCE")
        with tempfile.TemporaryDirectory(prefix="runtime-test-") as tmp:
            output = Path(path) if path else Path(tmp) / "evidence.json"
            result = rm.smoke(rm.HERE.parents[3], output)
            self.assertTrue(result["success"])
            self.assertEqual(set(result["selections"]),
                             {"baseline", "candidate"})
            for selection in result["selections"].values():
                self.assertEqual(selection["release"]["status"], "pass")
                self.assertEqual(selection["runtime"]["rssStatus"], "measured")
                self.assertEqual(len(selection["runtime"]["batches"]), 4)
                self.assertTrue(selection["paths"])


if __name__ == "__main__":
    unittest.main()
