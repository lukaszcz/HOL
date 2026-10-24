#!/usr/bin/env python3
"""Replay count attribution and new observations; never approve TASK29."""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PERF = HERE.parents[2]
sys.path.insert(0, str(PERF))
import acceptance as a
import evidence_bundle as bundle
import performance_schema as ps

CANDIDATE = "e86df07bf17f22cf18ae04f8b20dcb9ee6d0ad4a"


def experiment(archive, *, case, size, seconds, candidate, iterations=None):
    with tempfile.TemporaryDirectory(prefix="task29-count-replay-") as tmp:
        root = Path(tmp) / "data"
        bundle.unpack(archive, root)
        report = a.load(root / "acceptance.json")
        a.require(report["success"], "failed protocol")
        selections, observations = {}, {}
        for selection in ("control", "candidate"):
            folder = root / ("%s-%d-%s" % (case, size, selection))
            manifest = a.load(folder / "manifest.json")
            selections[selection] = a.analyze(
                folder, case=case, size=size, baseline=a.BASE,
                candidate=a.BASE if selection == "control" else candidate,
                pairs=10, samples=3, seconds=seconds, iterations=iterations)
            rows = []
            for run in manifest["runs"]:
                receipt = a.load(folder / run["receipt"])
                if receipt["fixture"] != "performance":
                    continue
                data = receipt["measurements"]["workloads"][case]
                batches = [row for row in receipt["runtime"]["batches"]
                           if row["stage"] == "sample"]
                rows.append(dict(
                    pair=receipt["pair"], side=receipt["selection"],
                    calibration_counts=[r["iterations"] for r in
                                        data["calibration"]],
                    sample_counts=[r["iterations"] for r in data["batches"]],
                    sample_gc_seconds=[r["gc"] for r in data["batches"]],
                    sample_heaps_bytes=[r["before"]["sizeHeap"]
                                        for r in batches],
                    sample_gc_counts=[r["gcCounts"] for r in batches]))
            observations[selection] = dict(
                load_before=manifest["machine"]["load_average_before"],
                load_after=manifest["machine"]["load_average_after"],
                processes=rows)
        for key, metric in selections["candidate"]["metrics"].items():
            a.apply_control(metric, selections["control"]["metrics"][key])
        a.require(json.dumps([selections], sort_keys=True) ==
                  json.dumps(report["workloads"], sort_keys=True),
                  "changed analysis")
        return dict(archive=a.seal(archive), observations=observations,
                    metrics={side: data["metrics"] for side, data in
                             selections.items()})


def main():
    validation = a.load(HERE / "validation.json")
    a.require(set(validation["archives"]) == {
        "collector-10000.json.xz", "client-smoke.json.xz",
        "short-negative.json.xz"}, "missing/extra diagnostic archive")
    for name, expected in validation["archives"].items():
        a.require(a.seal(HERE / name) == expected, "changed diagnostic archive")
    grid = HERE.parent / "full-grid"
    inventory = a.load(grid / "inventory.json")
    original = {}
    for case, size in (("compile_collector", 10000), ("compile_single", 0)):
        name = "%s-%d.json.xz" % (case, size)
        entry, = [row for row in inventory["runs"] if row["archive"] == name]
        a.require(entry["seal"] == a.seal(grid / name), "changed original")
        original[name] = experiment(grid / name, case=case, size=size,
                                    seconds=0.3, candidate=inventory["candidate"])
    zero = original["compile_single-0.json.xz"]["observations"]
    a.require(all(row["sample_gc_seconds"] == [0, 0, 0]
                  for selection in zero.values()
                  for row in selection["processes"]),
              "zero-rule GC observation changed")
    fresh = experiment(HERE / "collector-10000.json.xz",
                       case="compile_collector", size=10000,
                       seconds=0.3, candidate=CANDIDATE, iterations=64)
    # Client fixture follows the same count schedule; this is a one-pair
    # semantic/protocol smoke, not ten-pair numerical acceptance.
    with tempfile.TemporaryDirectory(prefix="task29-client-replay-") as tmp:
        root = Path(tmp) / "data"
        bundle.unpack(HERE / "client-smoke.json.xz", root)
        manifest = a.load(root / "manifest.json")
        a.require(manifest["success"], "client smoke failed")
        for side, pin in (("baseline", a.BASE), ("candidate", CANDIDATE)):
            a.require(manifest["selections"][side]["revision"] == pin,
                      "wrong client pin")
        client = 0
        for run in manifest["runs"]:
            receipt = a.load(root / run["receipt"])
            if receipt["fixture"] == "performance":
                a.audit(manifest, receipt)
                a.archive_protocol(manifest, receipt)
                client += 1
        a.require(client == 2, "missing client smoke")
    with tempfile.TemporaryDirectory(prefix="task29-negative-replay-") as tmp:
        root = Path(tmp) / "data"
        bundle.unpack(HERE / "short-negative.json.xz", root)
        manifest = a.load(root / "manifest.json")
        a.require(not manifest["success"], "negative passed")
        for side, pin in (("baseline", a.BASE), ("candidate", CANDIDATE)):
            a.require(manifest["selections"][side]["revision"] == pin,
                      "wrong negative pin")
        receipt = a.load(root / "pair-00-baseline.json.gz")
        a.require(not receipt["accepted"] and receipt["exit"] != 0,
                  "short batch accepted")
        try:
            ps.validate(receipt["events"], 3, 0.3, **ps.suite_options(
                manifest["performance"]))
        except ValueError as error:
            rejection = str(error)
        else:
            raise ValueError("short-batch negative admitted on replay")
        a.require(rejection == receipt["rejection"] ==
                  "fixed calibration too short; new experiment required",
                  "wrong negative rejection")
    return dict(scope="isolated diagnostics, NOT TASK29 closure",
                original=original, equal_count=fresh,
                client_smoke_processes=client, short_negative=rejection,
                allocation="blocked; profiling is not a validated total",
                task29="blocked; unchanged full-grid failures/uncertainty")


if __name__ == "__main__":
    print(json.dumps(main(), indent=2, allow_nan=False))
