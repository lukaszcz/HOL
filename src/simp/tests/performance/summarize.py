#!/usr/bin/env python3
"""Recompute diagnostic summaries from complete, validated paired receipts."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import random
from statistics import median

from performance_schema import LABELS, suite_options, validate, require


def fingerprint(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def interval(values):
    # Fixed before the diagnostic runs: no filtering, percentile bootstrap of
    # the paired median, 20,000 resamples, deterministic seed. Small-n caveat
    # is part of the report, not an acceptance allowance.
    rng = random.Random(3003)
    boot = sorted(median(rng.choices(values, k=len(values)))
                  for _ in range(20000))
    return [boot[499], boot[19499]]


def summarize(folder):
    manifest = json.loads((folder / "manifest.json").read_text())
    require(manifest["success"], "failed experiment")
    options = manifest["performance"]
    schema = suite_options(options)
    pairs = {}
    files = {"manifest.json": fingerprint(folder / "manifest.json")}
    order = []
    for run in manifest["runs"]:
        path = folder / run["receipt"]
        files[path.name] = fingerprint(path)
        receipt = json.loads(gzip.decompress(path.read_bytes()))
        if receipt["fixture"] != "performance":
            continue
        require(run["accepted"] and receipt["exit"] == 0 and
                not receipt["timed_out"], "failed performance process")
        _, data = validate(receipt["result"]["events"], options["samples"],
                           options["batch_seconds"], **schema)
        require(data == receipt["measurements"], "altered derived measurements")
        pair, selection = receipt["pair"], receipt["selection"]
        require(selection not in pairs.setdefault(pair, {}), "duplicate process")
        pairs[pair][selection] = data
        order.append([pair, selection])
    expected = [[i, s] for i in range(options["pairs"]) for s in
                (("candidate", "baseline") if i % 2 else
                 ("baseline", "candidate"))]
    require(order == expected, "missing/reordered fresh-process pair")
    workloads = {}
    for label in schema.get("labels", LABELS):
        out = {}
        for metric in ("cpu", "wall", "gc"):
            observations = []
            for pair in pairs.values():
                values = {}
                for side, data in pair.items():
                    batches = data["workloads"][label]["batches"]
                    values[side] = median(b[metric] / b["iterations"]
                                          for b in batches)
                observations.append(values)
            ratios = [r["candidate"] / r["baseline"] for r in observations
                      if r["baseline"] > 0]
            out[metric] = {
                "seconds_per_operation_by_pair": observations,
                "baseline_median": median(r["baseline"] for r in observations),
                "candidate_median": median(r["candidate"] for r in observations),
                "paired_ratios": ratios,
                "median_paired_ratio": median(ratios) if ratios else None,
                "paired_ratio_bootstrap_95_percent": interval(ratios)
                if len(ratios) == len(observations) else None,
                "zero_denominators": len(observations) - len(ratios),
            }
        workloads[label] = out
    storage = {}
    for side in ("baseline", "candidate"):
        storage[side] = [p[side]["storage"] for p in pairs.values()]
    return dict(inputs=files, options=options, order=order,
                workloads=workloads, storage=storage,
                limitations="Diagnostic only; small-n percentile intervals, "
                "not final acceptance or independent clean builds. No outliers "
                "removed; GC ratios undefined when baseline GC is zero.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("experiment", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = summarize(args.experiment)
    with args.output.open("x") as out:
        out.write(json.dumps(result, indent=2) + "\n")
    for label, metrics in result["workloads"].items():
        cpu, wall = metrics["cpu"], metrics["wall"]
        print(f"{label}: CPU {cpu['median_paired_ratio']:.4f} "
              f"{cpu['paired_ratio_bootstrap_95_percent']}; "
              f"wall {wall['median_paired_ratio']:.4f} "
              f"{wall['paired_ratio_bootstrap_95_percent']}")


if __name__ == "__main__":
    main()
