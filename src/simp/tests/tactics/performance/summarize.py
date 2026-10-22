#!/usr/bin/env python3
"""Per-workload paired inference, not a numerical-parity acceptance gate.

Process median -> paired log ratios. No outliers discarded, no workload pooling,
no subtracting baseline-control noise from raw results. T intervals assume
independent approximately normal pair log ratios. Family intervals cover all
66 workloads per metric (not jointly all metrics/analyses). Zero timers and
intervals spanning one are unresolved, never evidence of parity.
"""
import argparse
import gzip
import importlib.util
import json
import math
from pathlib import Path
import statistics
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import schema
require = schema.require
spec = importlib.util.spec_from_file_location(
    "task18_interval_math", schema.TESTS / "fragments/summarize.py")
interval_math = importlib.util.module_from_spec(spec)
spec.loader.exec_module(interval_math)


def read_json(path):
    raw = path.read_bytes()
    if path.suffix == ".gz":
        raw = gzip.decompress(raw)
    return json.loads(raw, object_pairs_hook=schema.unique)


def load(root, control):
    manifest = read_json(root / "manifest.json")
    require(manifest["success"] is True and
            manifest["evidence_id"] == schema.EVIDENCE and
            manifest["baseline_control"] is control, "invalid manifest")
    require(not manifest.get("gc_trace", False),
            "debug trace must not enter timing inference")
    perf = manifest["performance"]
    keys = schema.selected_keys(perf.get("rows"))
    pairs, samples = perf["pairs"], perf["samples"]
    require(type(pairs) is int and pairs >= 10 and
            type(samples) is int and samples >= 3, "insufficient observations")
    fixed = schema.fixed_iterations(perf["fixed_iterations"])
    selections = manifest["selections"]
    ordinary = {"simpLib.sml", "simpLib.sig"}
    baseline_matches = selections["baseline"]["compiler_matches_pinned"]
    require(selections["baseline"]["reference"] == schema.paired.BASE and
            set(baseline_matches) == ordinary and
            all(v is True for v in baseline_matches.values()),
            "baseline not pinned byte-exact ordinary sources")
    if control:
        identical = manifest["ordinary_source_byte_identical"]
        require(selections["candidate"]["reference"] == schema.paired.BASE and
                set(identical) == ordinary and
                all(v is True for v in identical.values()),
                "control sources differ")
    expected = [(pair, side) for pair in range(pairs) for side in
                (("baseline", "candidate") if pair % 2 == 0 else
                 ("candidate", "baseline"))]
    require([(r["pair"], r["selection"]) for r in manifest["runs"]] == expected,
            "missing/duplicate/reordered process pairs")
    data, durations = {}, {}
    for entry in manifest["runs"]:
        name = entry["receipt"]
        require(Path(name).name == name and entry["accepted"] is True,
                "invalid receipt entry")
        r = read_json(root / name)
        pair, side = entry["pair"], entry["selection"]
        require(r["accepted"] is True and r["exit"] == 0 and
                r["timed_out"] is False and r["result"]["outcome"] == "pass" and
                (r["pair"], r["selection"], r["fixture"]) ==
                (pair, side, "tactic-performance"), "unsuccessful receipt")
        protocol = r["result"]["events"]
        payload = [e for e in protocol if e[0] in
                   ("observation", "check", "exception")]
        obs, measurements = schema.timing_events(payload, samples, fixed, keys)
        checks = sum(e[0] == "check" for e in obs)
        require(obs == r["result"]["observations"] and
                protocol[0] == ["begin", side, "tactic-performance", "none"]
                and protocol[-1] == ["end", "pass", str(checks)] and
                r["result"]["expected_test_count"] == checks,
                "archived protocol/footer drift")
        expected_fixed = ",".join(f"{k}={v}" for k, v in fixed.items())
        require(r["environment"]["PERF_FIXED"] == expected_fixed and
                r["environment"]["PERF_SAMPLES"] == str(samples),
                "receipt environment/schedule mismatch")
        if "rows" in perf:
            require(r["environment"]["PERF_ROWS"] == ",".join(keys),
                    "receipt row filter mismatch")
        require(measurements == r["measurements"], "measurement drift")
        data[pair, side] = {key: {metric: statistics.median(
            row[metric] for row in rows) for metric in schema.METRICS}
            for key, rows in measurements.items()}
        durations[f"{pair}.{side}"] = {key: [row["raw"][0] for row in rows]
                                      for key, rows in measurements.items()}
    return manifest, data, durations


def interval(mean, se, df):
    result = dict(mean_log=mean, standard_error=se, df=df)
    for name, p in (("individual95", .975),
                    ("family95", 1-.05/(2*len(schema.KEYS)))):
        width = interval_math.student_inverse(p, df)*se
        lo, hi = mean-width, mean+width
        decision = ("slower" if lo > 0 else
                    "nonpositive" if hi <= 0 else "unresolved")
        result[name] = dict(ratio_interval=[math.exp(lo), math.exp(hi)],
                            decision=decision)
    return result


def estimate(ratios):
    if any(r is None or r <= 0 for r in ratios):
        return dict(status="unresolved_zero_timer", logs=None)
    logs = [math.log(r) for r in ratios]
    n = len(logs)
    result = interval(statistics.mean(logs),
                      statistics.stdev(logs)/math.sqrt(n), n-1)
    result.update(status="estimated", logs=logs)
    return result


def analysis(manifest, data):
    pairs = manifest["performance"]["pairs"]
    results = {}
    for key in schema.selected_keys(manifest["performance"].get("rows")):
        results[key] = {}
        for metric in schema.METRICS:
            medians = [[data[pair, side][key][metric]
                        for side in ("baseline", "candidate")]
                       for pair in range(pairs)]
            ratios = [b/a if a > 0 else None for a, b in medians]
            results[key][metric] = dict(process_medians=medians,
                paired_ratios=ratios, inference=estimate(ratios))
    return results


def summarize(candidate, control):
    a, adata, durations = load(candidate, False)
    b, bdata, control_durations = load(control, True)
    require(a["performance"]["fixed_iterations"] ==
            b["performance"]["fixed_iterations"] and
            a["performance"]["samples"] == b["performance"]["samples"] and
            a["performance"].get("rows") == b["performance"].get("rows"),
            "unmatched schedules/samples")
    require(a["tools"] == b["tools"] and
            a["shared_products"] == b["shared_products"],
            "candidate/control shared inputs differ")
    for name in ("TacticInputs.sml", "TacticPerformance.sml"):
        require(a["inputs"][str(HERE / name)] ==
                b["inputs"][str(HERE / name)], "workload sources differ")
    current, noise = analysis(a, adata), analysis(b, bdata)
    contrast = {}
    for key in current:
        contrast[key] = {}
        for metric in schema.METRICS:
            x, y = (r[key][metric]["inference"] for r in (current, noise))
            if x["logs"] is None or y["logs"] is None:
                result = dict(status="unresolved_zero_timer")
            else:
                nx, ny = len(x["logs"]), len(y["logs"])
                vx, vy = (statistics.variance(r["logs"])/n
                          for r, n in ((x, nx), (y, ny)))
                df = ((vx+vy)**2 / (vx*vx/(nx-1) + vy*vy/(ny-1))
                      if vx+vy else nx+ny-2)
                result = interval(x["mean_log"]-y["mean_log"],
                                  math.sqrt(vx+vy), df)
                result["status"] = "estimated_independent_run_contrast"
            contrast[key][metric] = result
    return dict(evidence_id=schema.EVIDENCE, candidate=current, control=noise,
        contrast=contrast, batch_wall_seconds=durations,
        control_batch_wall_seconds=control_durations,
        ordinary_source_byte_identical=a["ordinary_source_byte_identical"],
        scope=__doc__, acceptance="NOT established by inconclusive timings")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--candidate", type=Path, required=True)
    p.add_argument("--control", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    result = summarize(args.candidate.resolve(), args.control.resolve())
    with args.output.open("x") as out:
        json.dump(result, out, indent=2)
        out.write("\n")


if __name__ == "__main__":
    main()
