#!/usr/bin/env python3
"""Per-workload TASK15 observations, never a whole-module acceptance gate.

Usage: summarize.py --candidate RUN_DIR --control CONTROL_DIR --output FILE
A manifest.json path also works. Requires ten pairs, three samples and one
common fixed schedule (one calibration per process). Accepted harness receipts
are required; this is not a replacement for the runner's proof/sink/path audit.

Inference unit: median of three samples in each process, then ten paired log
ratios. No samples or workloads are pooled. Two-sided Student intervals assume
independent approximately normal process-pair log ratios. Bonferroni intervals
cover 90 workloads *per metric*, separately for candidate, control and their
contrast; they do not jointly cover all six metrics or all three analyses.
The contrast is an independent-run Welch difference of mean logs, not a pairing
of unrelated process IDs. Variability/control drift and run-order confounding
remain possible. Zero timer medians make inference unresolved, not a speedup.

Exit 2: invalid/incomplete/unmatched evidence. Exit 1: graph growth, or a raw
simultaneous slowdown in default mode, or a matched-diagnostic simultaneous
slowdown also positive against control. Exit 0 does NOT mean acceptance.
Individual t95 red rows are always retained, including when family intervals
or the contrast are inconclusive. No tolerance or baseline-noise subtraction
is applied to raw rows. Current input/tool drift is reported, not retroactively
hidden; worktree candidate source drift prevents a current-source claim.
"""
import argparse
from functools import lru_cache
import gzip
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys

SIZES = (0, 1, 10, 100, 1000, 10000)
LABELS = ("rewrites", "rewrites_with_names", "named_rewrites",
          "named_rewrites_with_names", "SSFRAG", "update", "add_named_rwt",
          "merge", "merge_duplicate", "merge_named", "named_merge",
          "ac_create", "ac_merge", "type_create", "type_lookup")
KEYS = tuple(label + "." + str(n) for n in SIZES for label in LABELS)
METRICS = ("cpu", "wall", "nongc_cpu", "gc_cpu", "user_cpu", "system_cpu")
SIDES = ("baseline", "candidate")


class InvalidEvidence(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise InvalidEvidence(message)


def unique_object(items):
    result = {}
    for key, value in items:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(path):
    raw = path.read_bytes()
    if path.suffix == ".gz":
        raw = gzip.decompress(raw)
    return json.loads(raw, object_pairs_hook=unique_object)


def finite_nonnegative(x):
    return type(x) in (int, float) and math.isfinite(x) and x >= 0


def seal_valid(seal):
    return (isinstance(seal, dict) and type(seal.get("bytes")) is int and
            seal["bytes"] >= 0 and isinstance(seal.get("sha256"), str) and
            len(seal["sha256"]) == 64 and
            all(c in "0123456789abcdef" for c in seal["sha256"]))


def source_inventory(selection):
    result = {}
    for source in selection["sources"]:
        name = source["git_path"]
        require(name not in result and seal_valid(source),
                "missing/duplicate source seal: " + name)
        result[name] = {k: source[k] for k in ("sha256", "bytes")}
    require(bool(result), "empty source inventory")
    return result


def audit_current(repo, inventory):
    """Audit only persistent paths, never vanished private temporary trees."""
    audit = dict(matching=0, changed=[], unavailable=[])
    for name, seal in sorted(inventory.items()):
        require(seal_valid(seal), "invalid seal: " + name)
        path = repo / name
        try:
            raw = path.read_bytes()
        except OSError:
            audit["unavailable"].append(name)
            continue
        if (len(raw) == seal["bytes"] and
                hashlib.sha256(raw).hexdigest() == seal["sha256"]):
            audit["matching"] += 1
        else:
            audit["changed"].append(name)
    return audit


def betacf(a, b, x):
    """Incomplete-beta continued fraction (modified Lentz algorithm)."""
    tiny, eps = 1e-300, 3e-14

    def safe(v):
        return v if abs(v) >= tiny else math.copysign(tiny, v)

    c, d = 1.0, 1.0 / safe(1 - (a + b) * x / (a + 1))
    h = d
    for m in range(1, 501):
        aa = m * (b - m) * x / ((a + 2*m - 1) * (a + 2*m))
        d, c = 1 / safe(1 + aa*d), safe(1 + aa/c)
        h *= d*c
        aa = -(a + m) * (a + b + m) * x / ((a + 2*m) * (a + 2*m + 1))
        d, c = 1 / safe(1 + aa*d), safe(1 + aa/c)
        delta = d*c
        h *= delta
        if abs(delta - 1) < eps:
            return h
    raise ArithmeticError("incomplete-beta convergence failure")


def ibeta(a, b, x):
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    factor = math.exp(math.lgamma(a+b) - math.lgamma(a) - math.lgamma(b)
                      + a*math.log(x) + b*math.log1p(-x))
    if x < (a+1) / (a+b+2):
        return factor * betacf(a, b, x) / a
    return 1 - factor * betacf(b, a, 1-x) / b


def student_cdf(t, df):
    tail = .5 * ibeta(df/2, .5, df / (df+t*t))
    return 1-tail if t >= 0 else tail


@lru_cache(maxsize=4096)
def student_inverse(p, df):
    require(.5 < p < 1 and df > 0, "invalid Student quantile")
    lo, hi = 0.0, 1.0
    while student_cdf(hi, df) < p:
        hi *= 2
    for _ in range(80):
        mid = (lo+hi)/2
        if student_cdf(mid, df) < p:
            lo = mid
        else:
            hi = mid
    return (lo+hi)/2


def interval_result(mean, se, df):
    t95 = student_inverse(.975, df)
    family = student_inverse(1 - .05/(2*90), df)
    individual_ci = [mean-t95*se, mean+t95*se]
    family_ci = [mean-family*se, mean+family*se]
    return dict(mean_log=mean, standard_error=se, df=df,
                t95ci=individual_ci, simultaneous95ci=family_ci,
                t95_decision=decision(individual_ci),
                simultaneous95_decision=decision(family_ci))


def decision(ci):
    if ci[0] > 0:
        return "red_slowdown"
    if ci[1] <= 0:
        return "nonpositive"
    return "unresolved"


def log_summary(ratios):
    # No dropping zeros, replacing them by epsilon, or reducing n below ten.
    if any(r is None or r <= 0 for r in ratios):
        return dict(status="unresolved_zero_timer", mean_log=None,
                    t95ci=None, simultaneous95ci=None,
                    t95_decision="unresolved", simultaneous95_decision=
                    "unresolved", logs=None)
    logs = [math.log(r) for r in ratios]
    result = interval_result(statistics.mean(logs),
                             statistics.stdev(logs)/math.sqrt(10), 9)
    result.update(status="estimated", logs=logs,
                  log_standard_deviation=statistics.stdev(logs))
    return result


def contrast(a, b):
    if a["logs"] is None or b["logs"] is None:
        return dict(status="unresolved_zero_timer", mean_log=None,
                    t95ci=None, simultaneous95ci=None,
                    t95_decision="unresolved",
                    simultaneous95_decision="unresolved")
    va, vb = (statistics.variance(s["logs"])/10 for s in (a, b))
    df = (va+vb)**2 / (va*va/9 + vb*vb/9) if va+vb else 18
    result = interval_result(a["mean_log"]-b["mean_log"],
                             math.sqrt(va+vb), df)
    result["status"] = "estimated"
    return result


def checked_receipt(root, name, side, mode, pair):
    require(Path(name).name == name, "receipt must be in result directory")
    r = read_json(root / name)
    require(r["accepted"] is True and r["exit"] == 0 and
            r["timed_out"] is False and r["result"]["outcome"] == "pass",
            "unsuccessful receipt: " + name)
    require((r["selection"], r["fixture"], r["pair"]) == (side, mode, pair),
            "receipt identity mismatch: " + name)
    return r


def check_calibrations(receipt, measurements, fixed):
    seen = {key: [] for key in KEYS}
    batches = {key: [] for key in KEYS}
    for event in receipt["result"]["observations"]:
        if event[0] != "observation":
            continue
        name = event[1]
        if name.startswith(("calibration.", "batch.")):
            prefix, key = name.split(".", 1)
            require(key in seen, "unknown calibration/batch workload")
            fields = event[2].split(",")
            if prefix == "calibration":
                require(len(fields) == 10, "malformed calibration")
                seen[key].append(int(fields[0]))
                require(int(fields[-1]) == fixed[key],
                        "calibration count mismatch")
            else:
                require(len(fields) == 11, "malformed batch")
                batches[key].append([int(fields[0]), int(fields[1])])
                require(int(fields[-1]) == fixed[key], "batch count mismatch")
    for key in KEYS:
        require(seen[key] == [fixed[key]],
                "missing/extra or unequal fixed calibration: " + key)
        require(batches[key] == [[i, fixed[key]] for i in range(3)],
                "incomplete samples or unequal batch counts: " + key)
        require(all(r["iterations"] == fixed[key]
                    for r in measurements[key]), "unequal sample iterations")


def graph_rows(manifest):
    graphs = {}
    for side in SIDES:
        source = manifest["selections"][side]["graphs"]
        require(set(source) == set(LABELS), "incomplete graph labels")
        graphs[side] = {}
        for label, rows in source.items():
            require([r[0] for r in rows] == list(SIZES) and
                    all(type(r[1]) is int and r[1] >= 0 for r in rows),
                    "incomplete/invalid graph sizes: " + label)
            for n, words in rows:
                graphs[side][label + "." + str(n)] = words
    rows = {}
    for key in KEYS:
        a, b = (graphs[side][key] for side in SIDES)
        rows[key] = dict(baseline_words=a, candidate_words=b,
                         delta_words=b-a, nonincreasing=b <= a)
    # Recompute; do not trust a stale/edited cached graph_comparison.
    return rows


def load_run(path):
    path = Path(path)
    manifest_path = path / "manifest.json" if path.is_dir() else path
    m = read_json(manifest_path)
    require(m["schema_version"] == 1 and m["success"] is True,
            "unsuccessful/incomplete manifest: " + str(manifest_path))
    require(m["evidence_id"] == "TASK15-fragments-v1", "wrong evidence ID")
    perf = m["performance"]
    require(perf["pairs"] == 10 and perf["samples"] == 3,
            "requires exactly 10 pairs and 3 samples")
    fixed = perf["fixed_iterations"]
    require(isinstance(fixed, dict) and set(fixed) == set(KEYS) and
            all(type(n) is int and n > 0 for n in fixed.values()),
            "requires exactly 90 fixed iteration counts")
    require(math.isfinite(perf["seconds"]) and perf["seconds"] > 0,
            "invalid calibration duration")
    root = manifest_path.parent
    require(set(m["selections"]) == set(SIDES), "incomplete selections")
    sources = {s: source_inventory(m["selections"][s]) for s in SIDES}
    graphs = graph_rows(m)
    for side in SIDES:
        behavior = checked_receipt(root, side + "-behavior--1.json.gz",
                                   side, "behavior", -1)
        require(behavior["measurements"] == m["selections"][side]["graphs"],
                "behavior receipt/manifest graphs differ")
    processes = {}
    receipts = set()
    require(len(m["runs"]) == 20, "incomplete process pairs")
    for run in m["runs"]:
        side, pair = run["selection"], run["pair"]
        require(side in SIDES and type(pair) is int and 0 <= pair < 10,
                "unknown selection/pair")
        require((side, pair) not in processes, "duplicate process pair")
        require(run["receipt"] not in receipts, "reused receipt")
        receipts.add(run["receipt"])
        measurements = run["measurements"]
        require(set(measurements) == set(KEYS), "incomplete workload matrix")
        for key, rows in measurements.items():
            require(len(rows) == 3, "incomplete samples: " + key)
            for row in rows:
                require(all(finite_nonnegative(row[x]) for x in METRICS),
                        "invalid timer: " + key)
                require(row["wall"] > 0, "zero wall timer: " + key)
        r = checked_receipt(root, run["receipt"], side, "performance", pair)
        require(r["measurements"] == measurements,
                "receipt/manifest measurements differ")
        require(r["environment"]["PERF_SAMPLES"] == "3", "sample env drift")
        env_fixed = unique_object(item.split("=") for item in
                                  r["environment"]["PERF_FIXED"].split(","))
        require(env_fixed == {k: str(v) for k, v in fixed.items()},
                "fixed schedule environment mismatch")
        check_calibrations(r, measurements, fixed)
        processes[side, pair] = measurements
    require(set(processes) == {(s, p) for s in SIDES for p in range(10)},
            "missing process pair")
    repo = Path(m["repo"])
    audits = {s: audit_current(repo, sources[s]) for s in SIDES}
    audits.update({group: audit_current(repo, m[group]) for group in
                   ("inputs", "tools", "shared_products")})
    supplements = (m.get("environment") or {}).get("supplement_snapshot", [])
    supplement_seals = {}
    for entry in supplements:
        name = entry["source_physical"]
        require(name not in supplement_seals and seal_valid(entry),
                "invalid/duplicate supplement seal")
        supplement_seals[name] = {k: entry[k] for k in ("sha256", "bytes")}
    for side in SIDES:
        for entry in m["selections"][side].get("supplement_sources", []):
            require({k: entry[k] for k in ("sha256", "bytes")} ==
                    supplement_seals.get(entry["source_physical"]),
                    "selected supplement does not match sealed snapshot")
    audits["supplements"] = audit_current(repo, supplement_seals)
    return dict(manifest=m, path=str(manifest_path.resolve()), sources=sources,
                graphs=graphs, processes=processes, current_seals=audits,
                manifest_sha256=hashlib.sha256(
                    manifest_path.read_bytes()).hexdigest())


def process_statistics(run, key, metric):
    medians = [[statistics.median(row[metric] for row in
                                  run["processes"][side, pair][key])
                for side in SIDES] for pair in range(10)]
    ratios = [b/a if a > 0 else None for a, b in medians]
    result = log_summary(ratios)
    result.update(process_medians=medians, paired_ratios=ratios,
                  median_paired_ratio=(statistics.median(ratios)
                                       if None not in ratios else None))
    return result


def comparable_environment(manifest):
    env = dict(manifest.get("environment") or {})
    # Temporary extraction paths necessarily differ across invocations.
    env["supplement_snapshot"] = sorted(
        [{k: v for k, v in entry.items() if k != "snapshot_path"}
         for entry in env.get("supplement_snapshot", [])],
        key=lambda entry: entry["source_path"])
    return env


def compare_runs(candidate, control):
    a, b = candidate["manifest"], control["manifest"]
    require(candidate["sources"]["baseline"] ==
            control["sources"]["baseline"] == control["sources"]["candidate"],
            "control is not same-source baseline/baseline")
    require(a["performance"] == b["performance"],
            "unmatched fixed schedule/calibration settings")
    for field in ("machine", "inputs", "tools", "shared_products", "poly"):
        require(a.get(field) == b.get(field), "unmatched " + field)
    require(comparable_environment(a) == comparable_environment(b),
            "unmatched ambient environment/supplement seals")
    for side in SIDES:
        require(a["selections"][side].get("runtime_options") ==
                b["selections"][side].get("runtime_options"),
                "unmatched runtime options")
    return bool((a.get("environment") or {}).get("matched", False))


def summarize(candidate_path, control_path):
    candidate, control = load_run(candidate_path), load_run(control_path)
    matched = compare_runs(candidate, control)
    rows = {}
    counts = {name: {metric: 0 for metric in METRICS} for name in
              ("raw_t95_red", "raw_family_red", "control_t95_red",
               "control_family_red", "contrast_t95_red",
               "contrast_family_red", "reproducible_family_red",
               "unresolved_log_rows")}
    for key in KEYS:
        metrics = {}
        for metric in METRICS:
            raw = process_statistics(candidate, key, metric)
            noise = process_statistics(control, key, metric)
            difference = contrast(raw, noise)
            flags = dict(
                raw_t95_red=raw["t95_decision"] == "red_slowdown",
                raw_family_red=raw["simultaneous95_decision"] ==
                "red_slowdown",
                control_t95_red=noise["t95_decision"] == "red_slowdown",
                control_family_red=noise["simultaneous95_decision"] ==
                "red_slowdown",
                contrast_t95_red=difference["t95_decision"] == "red_slowdown",
                contrast_family_red=difference["simultaneous95_decision"] ==
                "red_slowdown",
                unresolved_log_rows=raw["logs"] is None or
                noise["logs"] is None)
            flags["reproducible_family_red"] = (flags["raw_family_red"] and
                                                flags["contrast_family_red"])
            for flag, value in flags.items():
                counts[flag][metric] += int(value)
            metrics[metric] = dict(candidate=raw, control=noise,
                                   difference_mean_logs=difference,
                                   decisions=flags)
        rows[key] = dict(candidate_graph=candidate["graphs"][key],
                         control_graph=control["graphs"][key], metrics=metrics)
    graph_red = [key for key in KEYS if not
                 (candidate["graphs"][key]["nonincreasing"] and
                  control["graphs"][key]["nonincreasing"])]
    timing_red = any(counts["reproducible_family_red" if matched else
                            "raw_family_red"].values())
    audits = candidate["current_seals"]["candidate"]
    supplements = candidate["current_seals"]["supplements"]
    current = (candidate["manifest"]["selections"]["candidate"]["reference"]
               == "worktree" and not audits["changed"] and
               not audits["unavailable"] and not supplements["changed"] and
               not supplements["unavailable"])
    result = dict(
        schema_version=1, valid_evidence=True,
        mode="matched_local_diagnostic" if matched else "default_fullmodule",
        verdict="red" if graph_red or timing_red else "inconclusive",
        final_default_wholemodule_gate="NOT ESTABLISHED",
        failure=bool(graph_red or timing_red), graph_red_rows=graph_red,
        row_counts=counts, current_candidate_sources_match=current,
        provenance={name: dict(manifest=r["path"],
            manifest_sha256=r["manifest_sha256"],
            sources=r["sources"], current_seals=r["current_seals"],
            environment=r["manifest"].get("environment"))
            for name, r in (("candidate", candidate), ("control", control))},
        method=dict(pairs=10, samples_per_process=3, workloads=90,
            medians_order=list(SIDES), metrics=list(METRICS),
            confidence="log-scale two-sided Student t95; "
            "Bonferroni 90 per metric",
            paired_t95_critical=student_inverse(.975, 9),
            paired_simultaneous95_critical=student_inverse(1-.05/180, 9),
            contrast="independent-run Welch difference of mean paired logs",
            tolerance=0, pooling=False,
            assumptions="independent approximately normal pair log ratios; "
            "run stationarity not proven by a control", zero_policy=
            "any zero process median: log inference unresolved; no omission",
            failure_rule=("graph delta > 0; raw AND control-contrast "
                "simultaneous lower bounds > 0" if matched else
                "graph delta > 0; raw simultaneous lower bound > 0")),
        unresolved_evidence=[
            "Individual t95 and raw family red rows are not waived by control "
            "variability, matching, other workloads, or other metrics.",
            "Default full-module observations remain separate; matched "
            "registry/context is mixed-source attribution, not production.",
            "Finite timings crossing zero do not prove zero overhead. Inspect "
            "exact local source correspondence, retained work/result escape, "
            "and native code for each unresolved/red workload.",
            "Needed: sealed selected source and emitted native-code evidence "
            "showing equivalent local operations and no extra allocations; "
            "retained graph words are not cumulative transient allocation.",
            "This analyzer supplies no native-code or retained-work proof. "
            "Independent clean builds and the final default whole-module gate "
            "remain external requirements.",
            "Current source/input/tool availability and drift are recorded "
            "separately from run-time manifest seals; missing or changed "
            "worktree sources cannot establish current-source correspondence."
        ], rows=rows)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", required=True, type=Path)
    parser.add_argument("--control", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    # Never overwrite a manifest or a receipt, including through a symlink.
    output = args.output.resolve()
    for source in (args.candidate, args.control):
        root = source if source.is_dir() else source.parent
        require(output != (root / "manifest.json").resolve() and
                output.suffix != ".gz", "output must not overwrite evidence")
    try:
        result = summarize(args.candidate, args.control)
        status = int(result["failure"])
    except (InvalidEvidence, OSError, EOFError, ValueError, KeyError,
            TypeError, IndexError, ArithmeticError) as error:
        result = dict(schema_version=1, valid_evidence=False,
                      verdict="invalid_or_incomplete", error=str(error),
                      final_default_wholemodule_gate="NOT ESTABLISHED")
        status = 2
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True,
                                      allow_nan=False) + "\n")
    print(str(args.output) + ": " + result["verdict"])
    if result.get("valid_evidence"):
        print(json.dumps(result["row_counts"], sort_keys=True))
    else:
        print(result["error"], file=sys.stderr)
    return status


if __name__ == "__main__":
    sys.exit(main())
