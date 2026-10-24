#!/usr/bin/env python3
"""Publish TASK29's full per-case tables and telemetry (no measurements)."""
from collections import Counter
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1]))
import acceptance as a
import evidence_bundle as bundle
import task29_gate as gate


def span(values):
    values = list(values)
    return [min(values), max(values)] if values else None


def interval(metric):
    ci = metric["paired_ratio_bootstrap_95_percent"]
    return metric["decision"][0].upper() + (" [%.9f, %.9f]" % tuple(ci)
                                             if ci else " undefined")


def main():
    root = HERE / "full-grid"
    ledger = a.load(root / "inventory.json")
    decisions = a.load(root / "decisions.json")
    reports, storage, telemetry, inputs = {}, {}, {}, {}
    for entry in ledger["runs"]:
        case, size = entry["case"], entry["size"]
        archive = root / entry["archive"]
        a.require(a.seal(archive) == entry["seal"], "changed archive")
        with tempfile.TemporaryDirectory(prefix="task29-report-") as tmp:
            folder = Path(tmp) / "data"
            bundle.unpack(archive, folder)
            report = a.load(folder / "acceptance.json")
            a.require(report["success"], "report requires complete protocol")
            reports[case, size] = report
            observed = []
            tools = []
            for selection in ("control", "candidate"):
                base = folder / ("%s-%d-%s" % (case, size, selection))
                manifest = a.load(base / "manifest.json")
                tools.append(manifest["tools"])
                for name, seal in manifest["inputs"].items():
                    if name in inputs:
                        a.require(inputs[name] == seal, "changed input")
                    inputs[name] = seal
                for row in manifest["runs"]:
                    if not row["receipt"].startswith("pair-"):
                        continue
                    receipt = a.load(base / row["receipt"])
                    a.require(receipt["exit"] == 0 and receipt["accepted"],
                              "failed process")
                    # The actual loaded path inventory, not selected files,
                    # must be free of simplifier-owned extension modules.
                    forbidden = {"simpExtLib", "TraverseExt", "Cond_rewrExt",
                        "OpeningExt", "TravrulesExt", "congExtLib",
                        "pureSimpsExt", "boolSimpsExt", "combinSimpsExt",
                        "simpMarkerLib", "simpMarkerTheory", "SplitData",
                        "splitLib", "splitPersistLib", "trackedSimpDefaults"}
                    a.require(not any(Path(path).stem in forbidden
                                      for path in receipt["result"]["paths"]),
                              "ordinary measurement loaded an extension")
                    observed.append((selection, receipt))
            a.require(tools[0] == tools[1], "changed tools within cell")
            record = dict(processes=len(observed),
                          extension_paths_absent=True, selections={})
            for selection, side in (("control", "baseline"),
                                    ("control", "candidate"),
                                    ("candidate", "baseline"),
                                    ("candidate", "candidate")):
                receipts = [r for s, r in observed
                            if s == selection and r["selection"] == side]
                samples = [b for r in receipts for b in r["runtime"]["batches"]
                           if b["stage"] == "sample"]
                snapshots = [b[k] for b in samples for k in ("before", "after")]
                gc = [b["gcCounts"]["gcFullGCs"] +
                      b["gcCounts"]["gcPartialGCs"] for b in samples]
                record["selections"][selection + "/" + side] = dict(
                    samples=len(samples),
                    sample_iterations=span(b["iterations"] for b in samples),
                    sample_gc_collections=span(gc),
                    sample_rss_bytes=span(s["rssBytes"] for s in snapshots),
                    sample_hwm_bytes=span(s["hwmBytes"] for s in snapshots),
                    rss_status=dict(Counter(b["rssStatus"] for b in samples)))
                if case == "storage_graph":
                    storage[str(size) + "/" + selection + "/" + side] = {
                        field: sorted({r["storage_graph"][0][field]
                                       for r in receipts})
                        for field in receipts[0]["storage_graph"][0]}
            telemetry[case + "/" + str(size)] = record
    a.require(gate.summary(reports) == decisions, "changed decisions")
    lines = ["# TASK29 per-workload observations", "",
        "**BLOCKED, not completed.** Candidate: `" + ledger["candidate"] + "`.",
        "Baseline: `" + ledger["baseline"] + "`.", "",
        "All 162 cells have ten B/B and ten B/C fresh AB/BA pairs, three",
        "samples per process and a 0.3-second calibrated batch target.",
        "No outlier or pair was removed. P/F/I = pass/fail/inconclusive;",
        "intervals are fixed-seed 20,000-resample paired-ratio 95% intervals.",
        "Candidate decisions already include the unchanged baseline-control",
        "gate. A noisy/failed control never excuses a candidate failure.", "",
        "Each `full-grid/CASE-SIZE.json.xz` losslessly contains raw process",
        "receipts, CPU/wall/GC batch timings, calibrated counts, consumption,",
        "proof checks, source/product/runtime/library seals, commands/exits,",
        "all medians/ratios and unrounded intervals. Transport/replay commands",
        "are in `../../TASK_29_HANDOFF.md`. No table is a release average.", ""]
    for case in gate.CASES:
        lines += ["## " + case, "",
            "| Rules | B/C CPU | B/C wall | B/C GC | B/B CPU | B/B wall | B/B GC |",
            "| ---: | --- | --- | --- | --- | --- | --- |"]
        for size in gate.SIZES:
            results, = reports[case, size]["workloads"]
            values = [interval(results[s]["metrics"][m])
                      for s in ("candidate", "control")
                      for m in ("cpu", "wall", "gc")]
            lines.append("| %d | %s |" % (size, " | ".join(values)))
        lines.append("")
    a.save(HERE / "telemetry.json", dict(
        scope="Sample snapshot ranges, NOT cumulative allocation or exact peaks",
        units=dict(graph="reachable words", rss="bytes", hwm="bytes"),
        processes=sum(r["processes"] for r in telemetry.values()),
        rows=telemetry, storage=storage, inputs=inputs))
    (HERE / "RESULTS.md").write_text("\n".join(lines).rstrip() + "\n")
    print("162 tables rows, 6480 process telemetry receipts, exact graph roots")


if __name__ == "__main__":
    main()
