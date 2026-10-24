#!/usr/bin/env python3
"""Offline ordinary-process boundary attribution; never timing acceptance.

Re-admit complete archived B/B and B/C experiments before relating their
unaltered timers to existing runtime snapshots. No runtime instrumentation,
GC, build, timing, outlier filtering or numerical-policy change is performed.
Capacity equality is NOT heap, code, literal-pool or indirect-target identity.
"""
import argparse
import gzip
import json
from pathlib import Path
from statistics import median
import sys
import tempfile

sys.dont_write_bytecode = True
import acceptance as a
import evidence_bundle as bundle
import runtime_metrics as runtime
import task29_gate as grid

HERE = Path(__file__).resolve().parent
SCHEMA = "task29-boundary-attribution-v1"
FIELDS = (*runtime.HEAP, *runtime.RSS)


def input_seals():
    return {p.name: a.seal(p) for p in
            (Path(__file__), Path(a.__file__), Path(runtime.__file__),
             Path(bundle.__file__), HERE / "summarize.py",
             HERE / "audit_evidence.py", HERE / "performance_schema.py",
             HERE / "task29_gate.py", HERE / "matrix_schema.py",
             HERE / "matrix.json", HERE / "MatrixPerformance.sml",
             HERE / "MatrixSupport.sml", HERE / "ClientPerformance.sml")}


def same_json(left, right):
    # Python equality aliases bool/int/float. Evidence types are significant.
    def canonical(value):
        return json.dumps(value, sort_keys=True, allow_nan=False)
    return canonical(left) == canonical(right)


LIMITS = [
    "Historical observations, not new measurements or full-grid closure.",
    "Heap/free values are GC-updated capacities, not live object layouts.",
    "Code capacity does not identify native bodies, literals or targets.",
    "Counter boundaries do not locate individual collections within a batch.",
    "Snapshots allocate outside timing and are not atomic with timer reads.",
    "RSS/HWM are approximate process snapshots, not temporary batch peaks.",
    "Allocation-area capacity/free space is not cumulative allocated bytes.",
    "Differences are observations, not a causal repair or a noise budget.",
]


def delta(before, after, fields):
    """Signed differences; missing values remain missing, never zero-filled."""
    return {k: after[k] - before[k]
            if before[k] is not None and after[k] is not None else None
            for k in fields}


def process(receipt, case):
    """All boundary observations, including calibration and untimed gaps."""
    telemetry = receipt["runtime"]
    timings = receipt["measurements"]["workloads"]
    a.require(set(timings) == {case}, "wrong attribution workload")
    workload = timings[case]
    expected = [(stage, i, t) for stage, key in
                (("calibration", "calibration"), ("sample", "batches"))
                for i, t in enumerate(workload[key])]
    batches = telemetry["batches"]
    a.require(len(batches) == len(expected), "incomplete boundary inventory")
    rows, previous = [], None
    for batch, (stage, index, timing) in zip(batches, expected):
        a.require((batch["workload"], batch["stage"], batch["index"],
                   batch["iterations"]) ==
                  (case, stage, index, timing["iterations"]),
                  "boundary/timing correspondence changed")
        before = runtime.snapshot(batch["before"])
        after = runtime.snapshot(batch["after"])
        counts = delta(before, after, runtime.COUNTERS)
        a.require(counts == batch["gcCounts"] and
                  all(v >= 0 for v in counts.values()),
                  "changed boundary GC counts")
        gap = delta(previous, before, runtime.COUNTERS) if previous else None
        a.require(gap is None or all(v >= 0 for v in gap.values()),
                  "nonmonotonic inter-batch GC counts")
        rows.append(dict(stage=stage, index=index,
                         iterations=timing["iterations"],
                         before=before, after=after, gcCounts=counts,
                         untimedGapGCCounts=gap,
                         rssStatus=batch["rssStatus"],
                         rssBlockedReason=batch["rssBlockedReason"],
                         timing=timing))
        previous = after
    # Independently recorded non-GC timers, NOT inclusive CPU minus GC.
    samples = workload["batches"]
    nongc = median((t["nongc_usr"] + t["nongc_sys"]) / t["iterations"]
                   for t in samples)
    return dict(calibration_iterations=[t["iterations"] for t in
                                        workload["calibration"]],
                sample_iterations=[t["iterations"] for t in samples],
                nongc_seconds_per_operation=nongc,
                rssStatus=telemetry["rssStatus"], batches=rows)


def compare_pair(baseline, candidate):
    """Keep both schedules; never equate samples with different counts."""
    samples = {side: [r for r in p["batches"] if r["stage"] == "sample"]
               for side, p in (("baseline", baseline),
                               ("candidate", candidate))}
    a.require(len(samples["baseline"]) == len(samples["candidate"]),
              "unequal sample inventories")
    comparisons = []
    for left, right in zip(samples["baseline"], samples["candidate"]):
        comparisons.append(dict(
            index=left["index"],
            same_iterations=left["iterations"] == right["iterations"],
            before_difference=delta(left["before"], right["before"], FIELDS),
            after_difference=delta(left["after"], right["after"], FIELDS),
            gc_count_difference=delta(left["gcCounts"], right["gcCounts"],
                                      runtime.COUNTERS)))
    return dict(
        same_calibration_history=(baseline["calibration_iterations"] ==
                                  candidate["calibration_iterations"]),
        same_sample_counts=(baseline["sample_iterations"] ==
                            candidate["sample_iterations"]),
        baseline=baseline, candidate=candidate, samples=comparisons)


def describe(folder, analysis):
    """Called only after acceptance.analyze has re-admitted this experiment."""
    manifest = a.load(folder / "manifest.json")
    case = analysis["case"]
    pairs = {}
    for run in manifest["runs"]:
        path = a.safe_child(folder, run["receipt"])
        receipt = a.load(path)
        if receipt["fixture"] != "performance":
            continue
        pair, side = receipt["pair"], receipt["selection"]
        sides = pairs.setdefault(pair, {})
        a.require(side not in sides, "duplicate attribution process")
        result = process(receipt, case)
        a.require(receipt["runtime"] ==
                  analysis["runtime_by_pair"][pair][side],
                  "attribution runtime differs from admitted analysis")
        result["receipt"] = dict(file=run["receipt"], **a.seal(path))
        sides[side] = result
    a.require(set(pairs) == set(range(analysis["options"]["pairs"])),
              "missing attribution pair")
    rows = []
    for index, sides in sorted(pairs.items()):
        a.require(set(sides) == {"baseline", "candidate"},
                  "incomplete attribution pair")
        rows.append(dict(pair=index, **compare_pair(**sides)))
    nongc = a.paired_statistics([
        {side: row[side]["nongc_seconds_per_operation"]
         for side in ("baseline", "candidate")} for row in rows])
    # Non-GC is a diagnostic decomposition, not an extra acceptance gate.
    nongc["scope"] = "independently recorded non-GC timers; diagnostic only"
    counts = dict(
        processes=2 * len(rows),
        batches=sum(len(row[s]["batches"]) for row in rows
                    for s in ("baseline", "candidate")),
        pairs_with_different_calibration=sum(
            not row["same_calibration_history"] for row in rows),
        pairs_with_different_sample_counts=sum(
            not row["same_sample_counts"] for row in rows),
        processes_with_blocked_rss=sum(
            row[s]["rssStatus"] != "measured" for row in rows
            for s in ("baseline", "candidate")),
        sample_boundaries_with_different_capacity={
            field: sum(sample[phase][field] not in (None, 0)
                       for row in rows for sample in row["samples"]
                       for phase in ("before_difference", "after_difference"))
            for field in runtime.HEAP},
        samples_with_different_gc_counts={
            field: sum(sample["gc_count_difference"][field] != 0
                       for row in rows for sample in row["samples"])
            for field in runtime.COUNTERS})
    # Original sealed receipts already retain every raw snapshot and timer.
    # Keep the derived schedules/differences here, not a second raw archive.
    for row in rows:
        for side in ("baseline", "candidate"):
            p = row[side]
            p["initial_snapshot"] = p["batches"][0]["before"]
            for batch in p["batches"]:
                for field in ("before", "after", "timing"):
                    del batch[field]
    return dict(counts=counts, nongc_diagnostic=nongc, pairs=rows)


def inspect(archive, metadata):
    a.require(a.seal(archive) == metadata["seal"], "changed source archive")
    with tempfile.TemporaryDirectory(prefix="task29-boundaries-") as tmp:
        root = Path(tmp) / "data"
        count = bundle.unpack(archive, root)
        if "files" in metadata:
            a.require(count == metadata["files"], "changed archive file count")
        original = a.load(root / "acceptance.json")
        a.require(original["success"] is True,
                  "boundary attribution requires complete protocol")
        case, size = metadata["case"], metadata["size"]
        analyses, observations = {}, {}
        for selection in ("control", "candidate"):
            folder = root / ("%s-%d-%s" % (case, size, selection))
            analyses[selection] = a.analyze(
                folder, case=case, size=size, baseline=metadata["baseline"],
                candidate=(metadata["baseline"] if selection == "control"
                           else metadata["candidate"]), pairs=10, samples=3,
                seconds=metadata["seconds"],
                iterations=metadata["iterations"])
            # analysis has integer pair keys; serialized analyses use strings.
            observations[selection] = describe(folder, analyses[selection])
        for key, metric in analyses["candidate"]["metrics"].items():
            a.apply_control(metric, analyses["control"]["metrics"][key])
        a.require(same_json([analyses], original["workloads"]),
                  "changed archived analysis or decisions")
        scaling = a.retained_scaling([analyses]) if case == "storage_graph" \
            else None
        a.require(same_json(original["retained_scaling"], scaling),
                  "changed archived retained scaling")
        a.require(same_json(original["policy"], a.POLICY),
                  "changed numerical policy")
        return dict(case=case, size=size, source=metadata,
                    original_exit=a.report_exit_status(original),
                    gates={s: analyses[s]["metrics"] for s in analyses},
                    observations=observations)


def inputs(path):
    """Exactly the historical grid OR all complete repaired-driver cells."""
    value = a.load(path)
    if value.get("schema") == "task29-experiment-v1":
        rows = value["runs"]
        a.require(len(rows) == len(grid.keys()) and
                  all(type(r["size"]) is int for r in rows) and
                  {(r["case"], r["size"]) for r in rows} == set(grid.keys()),
                  "incomplete/duplicate historical grid")
        a.require(same_json([value["pairs"], value["samples"]], [10, 3]),
                  "wrong historical protocol")
        return [dict(case=r["case"], size=r["size"], archive=r["archive"],
                     seal=r["seal"], files=r["files"],
                     baseline=value["baseline"], candidate=value["candidate"],
                     seconds=value["seconds"], iterations=None) for r in rows]
    a.require(value.get("schema") == "task29-precompiled-driver-v1",
              "unsupported source inventory")
    result = []
    for case, size, count in (("frag_record", 0, 33554432),
                              ("compile_collector", 10000, 64)):
        name = "%s-%d.json.xz" % (case, size)
        result.append(dict(case=case, size=size, archive=name,
                           seal=value["archives"][name], baseline=a.BASE,
                           candidate=value["candidate"], seconds=0.3,
                           iterations=count))
    return result


def generate(inventory, output):
    a.require(not output.exists(), "output directory must be new")
    rows = inputs(inventory)
    output.mkdir(parents=True)
    report = dict(schema=SCHEMA, status="blocked; NOT task acceptance",
                  limits=LIMITS, inventory=dict(path=str(inventory),
                                                **a.seal(inventory)),
                  inputs=input_seals(),
                  cells=[])
    try:
        for metadata in rows:
            archive = a.safe_child(inventory.parent, metadata["archive"])
            result = inspect(archive, metadata)
            name = "%s-%d.json.gz" % (metadata["case"], metadata["size"])
            path = output / name
            with path.open("xb") as stream:
                stream.write(gzip.compress(json.dumps(
                    result, separators=(",", ":"), allow_nan=False).encode(),
                    mtime=0))
            report["cells"].append(dict(
                case=result["case"], size=result["size"], file=name,
                seal=a.seal(path), original_exit=result["original_exit"],
                gates={s: {k: v["decision"] for k, v in metrics.items()}
                       for s, metrics in result["gates"].items()},
                counts={s: v["counts"] for s, v in
                        result["observations"].items()}))
            print("ATTRIBUTION %s/%d" % (result["case"], result["size"]),
                  flush=True)
        a.require(a.seal(inventory) == {k: report["inventory"][k]
                                       for k in ("sha256", "bytes")},
                  "source inventory changed during attribution")
        a.require(input_seals() == report["inputs"],
                  "attribution inputs changed during attribution")
        report["complete_inventory"] = True
    finally:
        # Partial diagnostic evidence is explicitly incomplete, never a pass.
        report.setdefault("complete_inventory", False)
        a.save(output / "inventory.json", report)
    return report


def replay(inventory, output):
    saved = a.load(output / "inventory.json")
    a.require(saved["schema"] == SCHEMA and
              saved["complete_inventory"] is True,
              "incomplete attribution inventory")
    a.require(saved["inventory"]["sha256"] == a.seal(inventory)["sha256"] and
              saved["inventory"]["bytes"] == a.seal(inventory)["bytes"],
              "changed source inventory")
    a.require(same_json(saved["inputs"], input_seals()),
              "changed attribution inputs")
    rows = inputs(inventory)
    a.require(len(rows) == len(saved["cells"]), "changed cell inventory")
    a.require(saved["status"] == "blocked; NOT task acceptance" and
              saved["limits"] == LIMITS, "changed attribution scope")
    for metadata, cell in zip(rows, saved["cells"]):
        path = a.safe_child(output, cell["file"])
        a.require(a.seal(path) == cell["seal"], "changed attribution receipt")
        archive = a.safe_child(inventory.parent, metadata["archive"])
        result = inspect(archive, metadata)
        a.require(same_json(a.load(path), result),
                  "changed boundary attribution")
        expected = dict(case=result["case"], size=result["size"],
                        original_exit=result["original_exit"],
                        gates={s: {k: v["decision"]
                                   for k, v in metrics.items()}
                               for s, metrics in result["gates"].items()},
                        counts={s: v["counts"] for s, v in
                                result["observations"].items()})
        a.require(same_json({k: cell[k] for k in expected}, expected),
                  "changed attribution summary")
        print("REPLAY %s/%d" % (result["case"], result["size"]), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("generate", "replay"))
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.action == "generate":
        generate(args.inventory.resolve(), args.output.resolve())
    else:
        replay(args.inventory.resolve(), args.output.resolve())
    # A successful diagnostic is deliberately not a successful numerical gate.
    return 2


if __name__ == "__main__":
    sys.exit(main())
