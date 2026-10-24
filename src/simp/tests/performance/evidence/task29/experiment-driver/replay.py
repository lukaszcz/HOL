#!/usr/bin/env python3
"""Re-admit complete post-driver experiments; never approve TASK29."""
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PERF = HERE.parents[2]
sys.path.insert(0, str(PERF))
import acceptance as a
import evidence_bundle as bundle

CANDIDATE = "40f2189c3e4bd5c22c374e996e0d4831509b20de"
CASES = (("frag_record", 0, 33554432), ("compile_collector", 10000, 64))


def replay():
    validation = a.load(HERE / "validation.json")
    results = {}
    for case, size, count in CASES:
        name = "%s-%d.json.xz" % (case, size)
        archive = HERE / name
        a.require(a.seal(archive) == validation["archives"][name],
                  "changed experiment archive")
        with tempfile.TemporaryDirectory(prefix="task29-driver-replay-") as tmp:
            root = Path(tmp) / "data"
            bundle.unpack(archive, root)
            original = a.load(root / "acceptance.json")
            a.require(original["success"], "failed experiment protocol")
            selections, processes = {}, {}
            for side in ("control", "candidate"):
                folder = root / ("%s-%d-%s" % (case, size, side))
                manifest = a.load(folder / "manifest.json")
                for fixture in ("MatrixPerformance.sml",
                                "ClientPerformance.sml"):
                    key = "src/simp/tests/performance/" + fixture
                    a.require(manifest["inputs"][key] ==
                              validation["sources"][key],
                              "experiment not bound to repaired fixture")
                selections[side] = a.analyze(
                    folder, case=case, size=size, baseline=a.BASE,
                    candidate=a.BASE if side == "control" else CANDIDATE,
                    pairs=10, samples=3, seconds=0.3, iterations=count)
                timed = [a.load(folder / run["receipt"])
                         for run in manifest["runs"]
                         if a.load(folder / run["receipt"])["fixture"] ==
                         "performance"]
                a.require(len(timed) == 20, "incomplete timed processes")
                processes[side] = len(timed)
            for key, metric in selections["candidate"]["metrics"].items():
                a.apply_control(metric, selections["control"]["metrics"][key])
            a.require(json.dumps([selections], sort_keys=True) ==
                      json.dumps(original["workloads"], sort_keys=True),
                      "changed paired statistics/decisions")
            results[name] = dict(processes=processes, metrics={
                side: selections[side]["metrics"] for side in selections})
    a.require(any(metric["decision"] == "fail" for metric in
                  results["frag_record-0.json.xz"]["metrics"][
                      "candidate"].values()), "fragment failure lost")
    a.require(all(metric["decision"] == "inconclusive" for metric in
                  results["compile_collector-10000.json.xz"]["metrics"][
                      "candidate"].values()), "collector uncertainty lost")
    smokes = {}
    for name, case, count in (
            ("client-fixed", "traversal_construct", 1048576),
            ("client-adaptive", "traversal_construct", None),
            ("matrix-adaptive", "compile_excluded", None)):
        archive = HERE / (name + ".json.xz")
        a.require(a.seal(archive) == validation["archives"][archive.name],
                  "changed smoke archive")
        with tempfile.TemporaryDirectory(prefix="task29-driver-smoke-") as tmp:
            root = Path(tmp) / "data"
            bundle.unpack(archive, root)
            manifest = a.load(root / "manifest.json")
            a.require(manifest["success"] and
                      manifest["performance"]["case"] == case and
                      manifest["performance"].get("batch_iterations") == count,
                      "wrong smoke protocol")
            timed = 0
            for run in manifest["runs"]:
                receipt = a.load(root / run["receipt"])
                if receipt["fixture"] == "performance":
                    a.audit(manifest, receipt)
                    a.archive_protocol(manifest, receipt)
                    timed += 1
            a.require(timed == 2, "incomplete smoke")
            smokes[name] = timed
    return dict(scope="two complete ten-pair experiments; NOT full-grid closure",
                task29="blocked", experiments=results,
                smoke_processes=smokes)


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2, allow_nan=False))
