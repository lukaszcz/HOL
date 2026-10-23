#!/usr/bin/env python3
"""Untimed Poly/ML telemetry and controlled-release validation (TASK28).

Integration: validate(raw_stdout.splitlines(), performance_schema metrics).
It requires exactly one raw runtime record for EVERY calibration/sample.
release(raw_lines) requires a separate actual weak-collection probe record.
Neither function resolves loading/downstream/independent-build prerequisites.

CLI runs an untimed instrumentation selftest in both exact-source selections,
not performance measurements or independent repository build acceptance.
"""
import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
COUNTERS = ("gcFullGCs", "gcPartialGCs", "gcSharePasses")
HEAP = ("sizeHeap", "sizeHeapFreeLastGC", "sizeHeapFreeLastFullGC",
        "sizeAllocation", "sizeAllocationFree", "sizeStacks", "sizeCode")
RSS = ("rssBytes", "hwmBytes")
SCOPES = {
    "gcCounts": "actual batch-boundary counters; record/timer overhead can "
                "contribute; /proc reads and verification excluded",
    "heap": "GC-updated heap/free sizes; not allocated-byte totals",
    "allocationArea": "capacity/free space; not cumulative allocation",
    "rss": "Linux /proc/self/status snapshots in bytes; not atomic with GC",
    "hwm": "process-lifetime maximum including startup/loading/other batches",
    "hwmDelta": "increase in process maximum; not exact temporary peak",
    "release": "controlled simpset ref captured by known closure only",
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def integer(value, minimum=0):
    return type(value) is int and value >= minimum


def keys(value, expected, name):
    require(type(value) is dict and set(value) == set(expected),
            "wrong " + name + " fields")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def records(lines, prefix):
    result = []
    for line in lines:
        if prefix not in line:
            continue
        fields = line.split("\t")
        require(len(fields) == 2 and fields[0] == prefix,
                "malformed " + prefix + " record")
        def reject_constant(value):
            raise ValueError("nonfinite JSON value: " + value)
        result.append(json.loads(fields[1], object_pairs_hook=unique_object,
                                 parse_constant=reject_constant))
    return result


def snapshot(value):
    keys(value, (*COUNTERS, *HEAP, *RSS), "snapshot")
    require(all(integer(value[k]) for k in (*COUNTERS, *HEAP)),
            "invalid runtime counter/heap bytes")
    # Last-full-GC free space can exceed CURRENT heap size after resizing.
    # Do not falsely constrain GC-updated values to contemporaneous sizes.
    require(value["sizeAllocationFree"] <= value["sizeAllocation"],
            "allocation-area free exceeds capacity")
    missing = [value[k] is None for k in RSS]
    require(all(missing) or not any(missing), "partial RSS snapshot")
    if not any(missing):
        require(all(integer(value[k], 1) for k in RSS) and
                value["hwmBytes"] >= value["rssBytes"], "invalid RSS/HWM")
    return value


def parse(lines):
    """Strict raw records; no absence-as-pass and no inferred GC counts."""
    rows = records(lines, "@@MATRIX_RUNTIME")
    require(bool(rows), "missing runtime records")
    previous = None
    for row in rows:
        keys(row, ("schema", "stage", "iterations", "before", "after"),
             "runtime")
        require(type(row["schema"]) is int and row["schema"] == 1,
                "wrong runtime schema")
        require(row["stage"] in ("calibration", "sample") and
                integer(row["iterations"], 1), "invalid runtime stage/count")
        before, after = snapshot(row["before"]), snapshot(row["after"])
        for first, last in ((before, after), (previous, before)):
            if first is None:
                continue
            require(all(last[k] >= first[k] for k in COUNTERS),
                    "nonmonotonic GC counters")
        previous = after
    return rows


def validate(lines, measurements):
    """Map telemetry to the ordered, already-validated timing workloads.

    Returns raw snapshots + actual counter deltas. Missing Linux RSS is
    explicitly blocked, while the independent GC/heap observations remain
    measured. Zero HWM delta is valid and is NOT a zero temporary peak.
    """
    rows = parse(lines)
    workloads = measurements.get("workloads")
    require(type(workloads) is dict and bool(workloads),
            "missing timing workloads")
    expected = []
    for label, workload in workloads.items():
        require(type(workload) is dict, "invalid timing workload")
        for stage, key in (("calibration", "calibration"),
                           ("sample", "batches")):
            timings = workload.get(key)
            require(type(timings) is list and bool(timings),
                    "missing timing " + key)
            for index, timing in enumerate(timings):
                require(type(timing) is dict and
                        integer(timing.get("iterations"), 1),
                        "invalid timing iterations")
                expected.append((label, stage, index, timing["iterations"]))
    require(len(rows) == len(expected), "missing/extra runtime batch records")
    # Linux documents these /proc RSS fields as approximate. Observed raw
    # VmHWM can decrease across a full-GC unmap. Preserve it, block the RSS
    # inference, and keep independent valid timers/GC counters; never clamp.
    hwms = [s["hwmBytes"] for row in rows
            for s in (row["before"], row["after"])]
    rss_reason = ("Linux /proc/self/status VmRSS/VmHWM unavailable"
                  if None in hwms else
                  "nonmonotonic raw Linux VmHWM; RSS/peak inference blocked"
                  if any(b < a for a, b in zip(hwms, hwms[1:])) else "")
    mapped = []
    for row, (label, stage, index, count) in zip(rows, expected):
        require(row["stage"] == stage and row["iterations"] == count,
                "runtime/timing stage or iteration mismatch")
        before, after = row["before"], row["after"]
        rss_present = not rss_reason
        mapped.append(dict(
            row, workload=label, index=index,
            gcCounts={k: after[k] - before[k] for k in COUNTERS},
            rssStatus="measured" if rss_present else "blocked",
            rssBlockedReason=rss_reason,
            hwmDeltaBytes=(after["hwmBytes"] - before["hwmBytes"]
                           if rss_present else None)))
    return {"schema": 1, "scopes": dict(SCOPES), "batches": mapped,
            "gcStatus": "measured", "heapStatus": "measured",
            "rssStatus": ("measured" if all(r["rssStatus"] == "measured"
                                          for r in mapped) else "blocked"),
            "temporaryPeakBytes": None,
            "temporaryPeakStatus": "uncollected",
            "allocatedBytes": None, "allocatedBytesStatus": "uncollected",
            "releaseStatus": "uncollected"}


def release(lines):
    rows = records(lines, "@@MATRIX_RELEASE")
    require(len(rows) == 1, "missing/duplicate release record")
    row = rows[0]
    keys(row, ("schema", "scope", "retained", "collected", "fullGCs",
               "releaseCollections", "status", "blockedReason"), "release")
    require(type(row["schema"]) is int and row["schema"] == 1 and
            row["scope"] == "controlled-simpset-ref-closure",
            "invalid release schema/scope")
    require(row["retained"] is True and type(row["collected"]) is bool,
            "release retention control failed")
    require(integer(row["releaseCollections"]) and
            row["releaseCollections"] == 3 and integer(row["fullGCs"], 4),
            "release missing actual full collections")
    require((row["collected"] and row["status"] == "pass" and
             row["blockedReason"] == "") or
            (not row["collected"] and row["status"] == "blocked" and
             row["blockedReason"] ==
             "weak referent survived three explicit full collections"),
            "release status not supported by collection evidence")
    return row


SELFTEST = '''open HolKernel
val _ = new_theory "runtime_metrics_selftest"
fun batch stage count = let
  val _ = PolyML.fullGC ()
  val before = RuntimeMetrics.beforeBatch ()
  val _ = funpow count PolyML.fullGC ()
  val _ = RuntimeMetrics.afterBatch (stage,count,before)
in () end
val _ = batch "calibration" 1
val _ = batch "calibration" 2
val _ = batch "sample" 2
val _ = batch "sample" 2
val released = RuntimeMetrics.release ()
val _ = Paired.check "runtime release" (#retained released andalso
                                        #collected released)
'''
SMOKE_MEASUREMENTS = {"workloads": {"full_gc_control": {
    "calibration": [{"iterations": 1}, {"iterations": 2}],
    "batches": [{"iterations": 2}, {"iterations": 2}]}}}


def smoke(repo, output, baseline=None, candidate="HEAD", timeout=180):
    """Private selftest smoke; exclusive evidence, automatic cleanup."""
    sys.path.insert(0, str(HERE.parent / "compatibility"))
    import run_paired as rp
    repo, output = Path(repo).resolve(), Path(output).resolve()
    logpath = output.with_suffix(".log")
    require(output != logpath and not output.exists() and not logpath.exists(),
            "evidence JSON and sibling .log must be new and distinct")
    require(integer(timeout, 1), "timeout must be positive")
    output.parent.mkdir(parents=True, exist_ok=True)
    result = {"schema": 1, "success": False,
              "scope": "untimed instrumentation/controlled-release smoke; "
                       "not performance or independent-build acceptance",
              "repo": str(repo), "inputs": {}, "selections": {}}
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "PAIR_", "PERF_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    with output.open("x") as evidence, logpath.open("x") as log:
        try:
            inputs = [HERE / "RuntimeMetrics.sml", Path(__file__).resolve(),
                      HERE / "test_runtime_metrics.py",
                      Path(rp.__file__).resolve(),
                      *sorted((rp.HERE / "paired").glob("*.sml")),
                      rp.HERE / "paired/Holmakefile",
                      *(repo / p for p in
                        ("bin/Holmake", "bin/hol", "bin/hol.state0"))]
            result["inputs"] = {str(p): rp.fingerprint(p) for p in inputs}
            with tempfile.TemporaryDirectory(prefix="runtime-metrics-") as tmp:
                root = Path(tmp)
                for selection, ref in (("baseline", baseline or rp.BASE),
                                       ("candidate", candidate)):
                    dst = root / selection
                    dst.mkdir()
                    rev = rp.git(repo, "rev-parse", ref + "^{commit}")
                    rev = rev.decode().strip()
                    inventory = rp.extract(repo, rev, dst)
                    rp.install_fixtures(dst)
                    (dst / "RuntimeMetrics.sml").write_bytes(
                        (HERE / "RuntimeMetrics.sml").read_bytes())
                    (dst / "selftest.sml").write_text(SELFTEST)
                    with (dst / "Holmakefile").open("a") as f:
                        f.write("\npaired.exe: RuntimeMetrics.uo\n")
                    hashes = {str(p): rp.fingerprint(p) for p in dst.iterdir()
                              if p.is_file()}
                    command = [str(repo / "bin/Holmake"), "--no-project",
                               "--no-cache", "--no_prereqs",
                               "--holstate=" + str(repo / "bin/hol.state0"),
                               "-C", str(dst), "-j1", "paired.exe"]
                    build = rp.execute(command, root, env, timeout)
                    log.write(selection + " build\n" + build["stdout"])
                    log.flush()
                    info = {"revision": rev, "sources": inventory,
                            "build": {k: v for k, v in build.items()
                                      if k != "stdout"}}
                    result["selections"][selection] = info
                    require(build["exit"] == 0 and not build["timed_out"],
                            selection + " private Holmake failed")
                    runenv = dict(env, PAIR_SELECTION=selection,
                                  PAIR_FIXTURE="selftest", PAIR_CONTROL="none",
                                  PAIR_PRIVATE=str(dst),
                                  PAIR_TARGET="selftest")
                    receipt = rp.execute([str(dst / "paired.exe")], dst,
                                         runenv, timeout)
                    log.write(selection + " selftest\n" + receipt["stdout"])
                    log.flush()
                    audit = rp.validate(
                        receipt, selection=selection, fixture="selftest",
                        control="none", private=dst, repo=repo,
                        private_names={Path(s["git_path"]).stem
                                       for s in inventory}, flavor="baseline",
                        signature="pass", source_hashes=hashes,
                        expected_observations=[
                            ["check", "runtime release", "pass"]])
                    lines = receipt["stdout"].splitlines()
                    info["runtime"] = validate(lines, SMOKE_MEASUREMENTS)
                    info["release"] = release(lines)
                    require(info["runtime"]["rssStatus"] == "measured",
                            selection + " Linux RSS unavailable")
                    for row in info["runtime"]["batches"]:
                        require(row["gcCounts"]["gcFullGCs"] >=
                                row["iterations"],
                                "full GC control did not increment counts")
                    info["paths"] = audit["paths"]
                    info["checks"] = audit["observations"]
                    info["receipt"] = {k: v for k, v in receipt.items()
                                       if k != "stdout"}
                    print(selection + " runtime/release smoke pass",
                          flush=True)
            for path, fingerprint in result["inputs"].items():
                require(rp.fingerprint(Path(path)) == fingerprint,
                        "instrumentation input changed: " + path)
            result["success"] = True
        except Exception as error:
            result["failure"] = str(error)
            raise
        finally:
            json.dump(result, evidence, indent=2, sort_keys=True)
            evidence.write("\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[3])
    parser.add_argument("--baseline")
    parser.add_argument("--candidate", default="HEAD")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    smoke(args.repo, args.output, args.baseline, args.candidate, args.timeout)


if __name__ == "__main__":
    main()
