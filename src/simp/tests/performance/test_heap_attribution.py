#!/usr/bin/env python3
"""Offline boundary-attribution regressions; no builds or timing runs.

python3 -B test_heap_attribution.py
Optional (potentially expensive) offline admission of the first real cell:
HEAP_ATTRIBUTION_REAL_INVENTORY=/path/to/inventory.json \
    python3 -B test_heap_attribution.py
Synthetic receipts below are test data, never performance evidence.
"""
import copy
from contextlib import redirect_stdout
import gzip
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import heap_attribution as h


CASE = "frag_record"


def save(path, value):
    """Rewrite test evidence deliberately; acceptance.save is new-only."""
    data = json.dumps(value, allow_nan=False).encode()
    path.write_bytes(gzip.compress(data, mtime=0)
                     if path.suffix == ".gz" else data)


def snapshot(counters, capacity=4096, rss=True):
    result = dict(zip(h.runtime.COUNTERS, counters))
    result.update(dict.fromkeys(h.runtime.HEAP, capacity))
    result.update(rssBytes=8192 if rss else None,
                  hwmBytes=16384 if rss else None)
    return result


def timing(iterations, per_operation, sample=None):
    # CPU and GC reads are independently rounded: subtraction yields a
    # different number, yet the discrepancy is within protocol tolerance.
    result = dict(iterations=iterations, wall=iterations * 0.5,
                  nongc_usr=iterations * per_operation * 0.75,
                  nongc_sys=iterations * per_operation * 0.25,
                  gc_usr=0.02, gc_sys=0.01, check_gc_user=0.02,
                  consumed=iterations)
    result.update(cpu_usr=result["nongc_usr"] + 0.027,
                  cpu_sys=result["nongc_sys"] + 0.013)
    result.update(cpu=result["cpu_usr"] + result["cpu_sys"], gc=0.03)
    if sample is not None:
        result["sample"] = sample
    return result


def receipt(calibration=(1, 2), samples=(2, 2, 2), capacity=4096,
            rss=True, zero=False, side="baseline", pair=0):
    """Complete timing/boundary inventory, validated by the real mapper."""
    workload = dict(
        calibration=[timing(n, 8) for n in calibration],
        batches=[timing(n, rate, i) for i, (n, rate) in
                 enumerate(zip(samples, (0.25, 0.5, 0.125)))])
    accounting = timing(1, 0.25)
    accounting.pop("iterations")
    measurements = dict(timer_accounting=accounting, storage=[],
                        workloads={CASE: workload},
                        sink=sum(t["consumed"] for ts in workload.values()
                                 for t in ts) + accounting["consumed"])
    raw = []
    for index, (stage, t) in enumerate(
            (stage, t) for stage, key in
            (("calibration", "calibration"), ("sample", "batches"))
            for t in workload[key]):
        before = (0, 0, 0) if zero else (10 * index, 20 * index, 30 * index)
        after = before if zero else tuple(v + d for v, d in
                                         zip(before, (1, 2, 3)))
        raw.append("@@MATRIX_RUNTIME\t" + json.dumps(dict(
            schema=1, stage=stage, iterations=t["iterations"],
            before=snapshot(before, capacity, rss),
            after=snapshot(after, capacity - 128, rss))))
    return dict(accepted=True, exit=0, timed_out=False,
                fixture="performance", control="none", selection=side,
                pair=pair, measurements=measurements, diagnostics=raw,
                storage_graph=[],
                runtime=h.runtime.validate(raw, measurements))


def historical_inventory():
    return dict(schema="task29-experiment-v1", pairs=10, samples=3,
                baseline="synthetic-baseline", candidate="synthetic-candidate",
                seconds=0.3, runs=[dict(
                    case=case, size=size,
                    archive="%s-%d.json.xz" % (case, size),
                    seal={"sha256": "0" * 64, "bytes": 1}, files=1)
                    for case, size in h.grid.keys()])


def driver_inventory():
    return dict(schema="task29-precompiled-driver-v1",
                candidate="synthetic-candidate", archives={
                    name: {"sha256": "0" * 64, "bytes": 1}
                    for name in ("frag_record-0.json.xz",
                                 "compile_collector-10000.json.xz")})


class ProcessTests(unittest.TestCase):
    def test_preserves_calibration_samples_raw_timers_and_untimed_gc(self):
        source = receipt()
        original = copy.deepcopy(source)
        result = h.process(source, CASE)
        rows = result["batches"]
        self.assertEqual([(r["stage"], r["index"], r["iterations"])
                          for r in rows],
                         [("calibration", 0, 1), ("calibration", 1, 2),
                          ("sample", 0, 2), ("sample", 1, 2),
                          ("sample", 2, 2)])
        self.assertEqual(result["calibration_iterations"], [1, 2])
        self.assertEqual(result["sample_iterations"], [2, 2, 2])
        self.assertEqual(result["rssStatus"], "measured")
        self.assertIsNone(rows[0]["untimedGapGCCounts"])
        for row, batch in zip(rows, source["runtime"]["batches"]):
            for field in ("before", "after", "gcCounts", "rssStatus",
                          "rssBlockedReason"):
                self.assertEqual(row[field], batch[field])
            key = "calibration" if row["stage"] == "calibration" else "batches"
            self.assertEqual(row["timing"], source["measurements"][
                "workloads"][CASE][key][row["index"]])
            self.assertEqual(row["gcCounts"], dict(zip(
                h.runtime.COUNTERS, (1, 2, 3))))
        for row in rows[1:]:
            self.assertEqual(row["untimedGapGCCounts"], dict(zip(
                h.runtime.COUNTERS, (9, 18, 27))))
        self.assertEqual(result["nongc_seconds_per_operation"], 0.25)
        samples = source["measurements"]["workloads"][CASE]["batches"]
        subtracted = sorted((t["cpu"] - t["gc"]) / t["iterations"]
                            for t in samples)[1]
        self.assertNotEqual(result["nongc_seconds_per_operation"], subtracted)
        self.assertEqual(source, original)

    def test_zero_counters_and_missing_rss_stay_zero_and_null(self):
        result = h.process(receipt(zero=True, rss=False), CASE)
        self.assertEqual(result["rssStatus"], "blocked")
        for i, row in enumerate(result["batches"]):
            self.assertEqual(row["gcCounts"], dict.fromkeys(
                h.runtime.COUNTERS, 0))
            self.assertEqual(row["untimedGapGCCounts"],
                             dict.fromkeys(h.runtime.COUNTERS, 0) if i
                             else None)
            self.assertEqual(row["rssStatus"], "blocked")
            self.assertTrue(row["rssBlockedReason"])
            for phase in ("before", "after"):
                for field in h.runtime.RSS:
                    self.assertIsNone(row[phase][field])

    def test_mutated_boundary_correspondence_rejected(self):
        for index in range(5):
            for field, value in (("index", 99), ("iterations", 99),
                                 ("workload", "other"), ("stage", "other")):
                source = receipt()
                source["runtime"]["batches"][index][field] = value
                with self.subTest(index=index, field=field):
                    with self.assertRaisesRegex(ValueError, "correspondence"):
                        h.process(source, CASE)

    def test_missing_duplicate_and_extra_boundary_inventory_rejected(self):
        for mode in ("missing", "duplicate", "extra"):
            source = receipt()
            batches = source["runtime"]["batches"]
            if mode == "missing":
                batches.pop()
            elif mode == "duplicate":
                batches[3] = copy.deepcopy(batches[2])
            else:
                batches.append(copy.deepcopy(batches[-1]))
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                h.process(source, CASE)

    def test_gc_delta_mutation_and_negative_counters_rejected(self):
        for field in h.runtime.COUNTERS:
            for mode in ("delta", "within", "gap"):
                source = receipt()
                rows = source["runtime"]["batches"]
                if mode == "delta":
                    rows[2]["gcCounts"][field] += 1
                elif mode == "within":
                    rows[2]["after"][field] = rows[2]["before"][field] - 1
                    rows[2]["gcCounts"][field] = -1
                else:
                    # Keep the batch delta consistent; only the untimed
                    # inter-batch counter progression is now invalid.
                    rows[2]["before"][field] = rows[1]["after"][field] - 1
                    rows[2]["gcCounts"][field] = (
                        rows[2]["after"][field] - rows[2]["before"][field])
                with self.subTest(field=field, mode=mode):
                    with self.assertRaisesRegex(ValueError, "GC counts"):
                        h.process(source, CASE)

    def test_wrong_or_additional_timing_workload_rejected(self):
        for extra in (False, True):
            source = receipt()
            workloads = source["measurements"]["workloads"]
            workloads["other"] = copy.deepcopy(workloads[CASE])
            if not extra:
                del workloads[CASE]
            with self.subTest(extra=extra), self.assertRaisesRegex(
                    ValueError, "wrong attribution workload"):
                h.process(source, CASE)


class CompareTests(unittest.TestCase):
    def test_distinct_calibration_counts_and_signed_capacity_differences(self):
        baseline = h.process(receipt(), CASE)
        candidate = h.process(receipt(calibration=(1, 2, 4),
                                      samples=(4, 4, 4), capacity=2048,
                                      rss=False, zero=True), CASE)
        original = copy.deepcopy((baseline, candidate))
        result = h.compare_pair(baseline, candidate)
        self.assertFalse(result["same_calibration_history"])
        self.assertFalse(result["same_sample_counts"])
        self.assertEqual(result["baseline"], baseline)
        self.assertEqual(result["candidate"], candidate)
        self.assertEqual(len(result["samples"]), 3)
        for i, row in enumerate(result["samples"]):
            self.assertEqual(row["index"], i)
            self.assertFalse(row["same_iterations"])
            for phase in ("before_difference", "after_difference"):
                self.assertEqual(row[phase], dict(
                    **dict.fromkeys(h.runtime.HEAP, -2048),
                    **dict.fromkeys(h.runtime.RSS, None)))
            self.assertEqual(row["gc_count_difference"], dict(zip(
                h.runtime.COUNTERS, (-1, -2, -3))))
        self.assertEqual((baseline, candidate), original)

    def test_equal_schedules_and_zero_differences(self):
        baseline = h.process(receipt(zero=True), CASE)
        result = h.compare_pair(baseline, copy.deepcopy(baseline))
        self.assertTrue(result["same_calibration_history"])
        self.assertTrue(result["same_sample_counts"])
        for row in result["samples"]:
            self.assertTrue(row["same_iterations"])
            for field in ("before_difference", "after_difference",
                          "gc_count_difference"):
                self.assertTrue(all(v == 0 for v in row[field].values()))

    def test_unequal_sample_inventories_rejected(self):
        left = h.process(receipt(), CASE)
        right = copy.deepcopy(left)
        right["batches"].pop()
        with self.assertRaisesRegex(ValueError, "unequal sample inventories"):
            h.compare_pair(left, right)


class TemporaryTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="heap-attribution-test-")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)


class DescribeTests(TemporaryTests):
    def test_all_pairs_bound_to_receipts_with_compact_raw_references(self):
        folder = self.root
        runs, runtime = [], {}
        originals = []
        for pair in range(10):
            runtime[pair] = {}
            for side in ("baseline", "candidate"):
                r = receipt(pair=pair, side=side,
                            capacity=4096 if side == "baseline" else 2048)
                name = "%d-%s.json" % (pair, side)
                save(folder / name, r)
                runs.append(dict(receipt=name))
                runtime[pair][side] = r["runtime"]
                originals.append((name, copy.deepcopy(r)))
        save(folder / "manifest.json", dict(runs=runs))
        analysis = dict(case=CASE, options=dict(pairs=10),
                        runtime_by_pair=runtime)
        result = h.describe(folder, analysis)
        self.assertEqual(result["counts"]["processes"], 20)
        self.assertEqual(result["counts"]["batches"], 100)
        self.assertEqual(result["counts"][
            "sample_boundaries_with_different_capacity"]["sizeCode"], 60)
        self.assertEqual(result["nongc_diagnostic"]["paired_ratios"], [1] * 10)
        for row in result["pairs"]:
            for side in ("baseline", "candidate"):
                p = row[side]
                self.assertEqual(p["receipt"]["sha256"], h.a.seal(
                    folder / p["receipt"]["file"])["sha256"])
                self.assertTrue(p["initial_snapshot"])
                for batch in p["batches"]:
                    self.assertNotIn("before", batch)
                    self.assertNotIn("after", batch)
                    self.assertNotIn("timing", batch)
                    self.assertIn("untimedGapGCCounts", batch)
        for name, original in originals:
            self.assertEqual(h.a.load(folder / name), original)
        analysis["runtime_by_pair"][0]["baseline"]["gcStatus"] = "forged"
        with self.assertRaisesRegex(ValueError, "differs from admitted"):
            h.describe(folder, analysis)


class InputTests(TemporaryTests):
    def test_complete_historical_grid_preserves_protocol(self):
        path = self.root / "source.json"
        value = historical_inventory()
        save(path, value)
        rows = h.inputs(path)
        self.assertEqual(len(rows), len(h.grid.keys()))
        self.assertEqual([(r["case"], r["size"]) for r in rows],
                         h.grid.keys())
        for row, source in zip(rows, value["runs"]):
            self.assertEqual(row, dict(source, baseline=value["baseline"],
                                       candidate=value["candidate"],
                                       seconds=0.3, iterations=None))

    def test_incomplete_duplicate_extra_and_wrong_protocol_refused(self):
        for mode in ("missing", "duplicate", "extra", "pairs", "samples",
                     "boolean-size"):
            value = historical_inventory()
            if mode == "missing":
                value["runs"].pop()
            elif mode == "duplicate":
                value["runs"][-1] = copy.deepcopy(value["runs"][0])
            elif mode == "extra":
                value["runs"].append(copy.deepcopy(value["runs"][0]))
            elif mode == "boolean-size":
                value["runs"][0]["size"] = False
            else:
                value[mode] = 1
            path = self.root / "source.json"
            save(path, value)
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                h.inputs(path)

    def test_driver_requires_both_complete_cells(self):
        path = self.root / "source.json"
        value = driver_inventory()
        save(path, value)
        rows = h.inputs(path)
        self.assertEqual([(r["case"], r["size"], r["iterations"])
                          for r in rows],
                         [(CASE, 0, 33554432),
                          ("compile_collector", 10000, 64)])
        for row in rows:
            self.assertEqual(row["seal"], value["archives"][row["archive"]])
            self.assertEqual(row["baseline"], h.a.BASE)
            self.assertEqual(row["seconds"], 0.3)
        for name in value["archives"]:
            incomplete = copy.deepcopy(value)
            del incomplete["archives"][name]
            save(path, incomplete)
            with self.subTest(name=name), self.assertRaises(KeyError):
                h.inputs(path)
        save(path, {"schema": "unknown"})
        with self.assertRaisesRegex(ValueError, "unsupported source"):
            h.inputs(path)


class GenerateReplayTests(TemporaryTests):
    def setUp(self):
        super().setUp()
        self.inventory = self.root / "source.json"
        save(self.inventory, driver_inventory())
        self.rows = h.inputs(self.inventory)
        for row in self.rows:
            (self.root / row["archive"]).write_bytes(b"synthetic archive")
        self.output = self.root / "output"
        self.inspect = self.enterContext(patch.object(
            h, "inspect", side_effect=self.inspection))
        self.enterContext(redirect_stdout(io.StringIO()))

    def inspection(self, archive, metadata):
        self.assertEqual(archive, self.root / metadata["archive"])
        return dict(case=metadata["case"], size=metadata["size"],
                    source=metadata, original_exit=2,
                    gates={s: {"cpu": {"decision": "inconclusive"}}
                           for s in ("control", "candidate")},
                    observations={s: {"counts": {"processes": 20},
                                      "pairs": [{"receipt": "synthetic"}]}
                                  for s in ("control", "candidate")})

    def generate(self):
        return h.generate(self.inventory, self.output)

    def test_roundtrip_seals_summaries_scope_and_complete_inventory(self):
        report = self.generate()
        self.assertEqual(report, h.a.load(self.output / "inventory.json"))
        self.assertEqual(report["schema"], h.SCHEMA)
        self.assertIs(report["complete_inventory"], True)
        self.assertEqual(report["status"], "blocked; NOT task acceptance")
        self.assertEqual(report["limits"], h.LIMITS)
        self.assertEqual(
            report["inventory"],
            dict(path=str(self.inventory), **h.a.seal(self.inventory)))
        self.assertEqual(set(report["inputs"]), {
            "heap_attribution.py", "acceptance.py", "runtime_metrics.py",
            "evidence_bundle.py", "summarize.py", "audit_evidence.py",
            "performance_schema.py", "task29_gate.py", "matrix_schema.py",
            "matrix.json", "MatrixPerformance.sml", "MatrixSupport.sml",
            "ClientPerformance.sml"})
        for cell, metadata in zip(report["cells"], self.rows):
            path = self.output / cell["file"]
            self.assertEqual(cell["seal"], h.a.seal(path))
            self.assertEqual(h.a.load(path), self.inspection(
                self.root / metadata["archive"], metadata))
            self.assertEqual(cell["original_exit"], 2)
            self.assertEqual(cell["gates"]["candidate"]["cpu"], "inconclusive")
            self.assertEqual(cell["counts"]["control"], {"processes": 20})
        h.replay(self.inventory, self.output)
        self.assertEqual(self.inspect.call_count, 4)

    def test_existing_directory_or_file_refused_without_modification(self):
        for kind in ("file", "directory"):
            output = self.root / kind
            if kind == "file":
                output.write_bytes(b"caller-owned sentinel")
                sentinel = output
            else:
                output.mkdir()
                sentinel = output / "sentinel"
                sentinel.write_bytes(b"caller-owned sentinel")
            with self.subTest(kind=kind), self.assertRaisesRegex(
                    ValueError, "output directory must be new"):
                h.generate(self.inventory, output)
            self.assertEqual(sentinel.read_bytes(), b"caller-owned sentinel")
        self.inspect.assert_not_called()

    def test_bad_source_refused_before_creating_output(self):
        value = historical_inventory()
        value["runs"].pop()
        save(self.inventory, value)
        with self.assertRaisesRegex(ValueError, "incomplete/duplicate"):
            self.generate()
        self.assertFalse(self.output.exists())
        self.inspect.assert_not_called()

    def test_partial_failure_stays_incomplete_and_unreplayable(self):
        self.inspect.side_effect = [self.inspection(
            self.root / self.rows[0]["archive"], self.rows[0]),
            ValueError("synthetic admission failure")]
        with self.assertRaisesRegex(ValueError, "synthetic admission failure"):
            self.generate()
        saved = h.a.load(self.output / "inventory.json")
        self.assertIs(saved["complete_inventory"], False)
        self.assertEqual(len(saved["cells"]), 1)
        self.assertEqual(saved["status"], "blocked; NOT task acceptance")
        self.assertEqual(saved["limits"], h.LIMITS)
        self.inspect.reset_mock()
        with self.assertRaisesRegex(ValueError, "incomplete attribution"):
            h.replay(self.inventory, self.output)
        self.inspect.assert_not_called()

    def test_source_changes_during_generation_leave_incomplete_inventory(self):
        original = self.inspection

        def changed(archive, metadata):
            result = original(archive, metadata)
            self.inventory.write_bytes(self.inventory.read_bytes() + b"\n")
            return result

        self.inspect.side_effect = changed
        with self.assertRaisesRegex(ValueError, "changed during attribution"):
            self.generate()
        report = h.a.load(self.output / "inventory.json")
        self.assertFalse(report["complete_inventory"])

    def test_replay_rejects_tampered_summary_inventory_and_scope(self):
        report = self.generate()
        path = self.output / "inventory.json"
        mutations = [
            ("schema", "unknown"), ("complete_inventory", False),
            ("complete_inventory", 1),
            ("status", "pass"), ("limits", []),
            ("limits", h.LIMITS + ["capacities identify native code"]),
            ("cells", report["cells"][:-1]),
            ("cells", list(reversed(report["cells"]))),
            ("inventory", dict(report["inventory"], sha256="0" * 64)),
            ("inventory", dict(report["inventory"], bytes=0)),
            ("inputs", {}),
            ("inputs", dict(report["inputs"], **{
                "heap_attribution.py": {
                    "sha256": "0" * 64, "bytes": 0}})),
            ("inputs", {k: v for k, v in report["inputs"].items()
                        if k != "acceptance.py"}),
        ]
        for field in ("case", "size", "original_exit", "gates", "counts"):
            cells = copy.deepcopy(report["cells"])
            cells[0][field] = {"tampered": True}
            mutations.append(("cells", cells))
        cells = copy.deepcopy(report["cells"])
        cells[0]["size"] = False
        mutations.append(("cells", cells))
        for index, (field, value) in enumerate(mutations):
            changed = copy.deepcopy(report)
            changed[field] = value
            save(path, changed)
            with self.subTest(index=index, field=field):
                with self.assertRaises(ValueError):
                    h.replay(self.inventory, self.output)
        save(path, report)
        h.replay(self.inventory, self.output)

    def test_replay_rejects_changed_source_inventory_bytes(self):
        self.generate()
        self.inventory.write_bytes(self.inventory.read_bytes() + b"\n")
        self.inspect.reset_mock()
        with self.assertRaisesRegex(ValueError, "changed source inventory"):
            h.replay(self.inventory, self.output)
        self.inspect.assert_not_called()

    def test_replay_rejects_receipt_tampering_even_with_resealed_receipt(self):
        report = self.generate()
        path = self.output / report["cells"][0]["file"]
        changed = h.a.load(path)
        changed["observations"]["candidate"]["pairs"][0]["receipt"] = "forged"
        save(path, changed)
        self.inspect.reset_mock()
        with self.assertRaisesRegex(ValueError, "changed attribution receipt"):
            h.replay(self.inventory, self.output)
        self.inspect.assert_not_called()
        report["cells"][0]["seal"] = h.a.seal(path)
        save(self.output / "inventory.json", report)
        with self.assertRaisesRegex(ValueError,
                                    "changed boundary attribution"):
            h.replay(self.inventory, self.output)

    def test_main_never_returns_acceptance_success(self):
        for action in ("generate", "replay"):
            with self.subTest(action=action), patch.object(h, action) as call:
                with patch("sys.argv", ["heap_attribution.py", action,
                                        "--inventory", str(self.inventory),
                                        "--output", str(self.output)]):
                    self.assertEqual(h.main(), 2)
                call.assert_called_once_with(self.inventory.resolve(),
                                             self.output.resolve())


class InspectTests(TemporaryTests):
    def test_retained_scaling_is_recomputed_before_reporting_exit(self):
        archive = self.root / "synthetic.json.xz"
        archive.write_bytes(b"synthetic; unpacking mocked below")
        metadata = dict(seal=h.a.seal(archive), case=CASE, size=0,
                        baseline="synthetic-baseline",
                        candidate="synthetic-candidate", seconds=0.3,
                        iterations=None)
        analyses = {s: dict(metrics={"cpu": {"decision": "fail"}})
                    for s in ("control", "candidate")}
        analyses["candidate"]["metrics"]["cpu"]["control_decision"] = "fail"
        original = dict(success=True, policy=h.a.POLICY,
                        workloads=[analyses], retained_scaling=None)

        def unpack(_archive, root):
            root.mkdir()
            save(root / "acceptance.json", original)
            return 1

        def analyze(folder, **_kwargs):
            side = ("control" if folder.name.endswith("control")
                    else "candidate")
            return copy.deepcopy(analyses[side])

        with patch.object(h.bundle, "unpack", side_effect=unpack), \
                patch.object(h.a, "analyze", side_effect=analyze), \
                patch.object(h, "describe", return_value={}):
            self.assertEqual(h.inspect(archive, metadata)["original_exit"], 1)
            original["retained_scaling"] = dict(status="measured",
                                               adjacent_intervals=[])
            with self.assertRaisesRegex(ValueError, "retained scaling"):
                h.inspect(archive, metadata)

    def test_json_comparison_preserves_numeric_types(self):
        for left, right in ((False, 0), (True, 1), (1.0, 1),
                            ({"index": False}, {"index": 0}),
                            ([True], [1])):
            with self.subTest(left=left, right=right):
                self.assertFalse(h.same_json(left, right))
        self.assertTrue(h.same_json(dict(a=1, b=2), dict(b=2, a=1)))


class RealArchiveTests(unittest.TestCase):
    @unittest.skipUnless(os.environ.get("HEAP_ATTRIBUTION_REAL_INVENTORY"),
                         "opt-in offline archive admission")
    def test_first_real_cell(self):
        source = os.environ["HEAP_ATTRIBUTION_REAL_INVENTORY"]
        inventory = Path(source).resolve()
        metadata = h.inputs(inventory)[0]
        result = h.inspect(h.a.safe_child(inventory.parent,
                                         metadata["archive"]), metadata)
        self.assertEqual((result["case"], result["size"]),
                         (metadata["case"], metadata["size"]))
        self.assertEqual(set(result["observations"]), {"control", "candidate"})
        for observation in result["observations"].values():
            self.assertEqual(observation["counts"]["processes"], 20)
            self.assertEqual(len(observation["pairs"]), 10)


if __name__ == "__main__":
    unittest.main()
