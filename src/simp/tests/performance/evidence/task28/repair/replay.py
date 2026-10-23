#!/usr/bin/env python3
"""Replay TASK28 repair receipts and real-data mutations after bundle unpack.

No builds or measurements. Original private trees need not exist.
"""
import argparse
import copy
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
import acceptance as a
from audit_evidence import audit
import loading as l
import run_paired as rp


def rejected(label, manifest, receipt):
    try:
        audit(manifest, receipt)
    except (ValueError, KeyError) as error:
        return dict(control=label, rejected=True, reason=str(error))
    raise ValueError("real archive mutation accepted: " + label)


def mutations(folder):
    manifest = a.load(folder / "manifest.json")
    run = next(r for r in manifest["runs"]
               if r["receipt"].startswith("pair-"))
    receipt = a.load(folder / run["receipt"])
    shared = next(p for p, info in receipt["result"]["paths"].items()
                  if p in manifest["shared_inputs"] and
                  info["related_products"])
    result = []
    for label in ("changed-shared-hash", "missing-shared-fingerprint",
                  "escaping-shared-path", "changed-related-product"):
        bad = copy.deepcopy(receipt)
        info = bad["result"]["paths"][shared]
        if label == "changed-shared-hash":
            info["sha256"] = "0" * 64
        elif label == "missing-shared-fingerprint":
            for key in ("sha256", "bytes", "related_products"):
                del info[key]
        elif label == "escaping-shared-path":
            info["physical"] = manifest["repo"] + "/../foreign/prelude.sml"
        else:
            next(iter(info["related_products"].values()))["sha256"] = "0" * 64
        result.append(rejected(label, manifest, bad))
    bad = copy.deepcopy(receipt)
    private = Path(manifest["selections"][receipt["selection"]]["private"])
    entry = next(info for info in bad["result"]["paths"].values()
                 if Path(info["physical"]).is_relative_to(private) and
                 info["related_products"])
    entry["related_products"] = {}
    result.append(rejected("missing-private-products", manifest, bad))
    for label in ("invalid-tools", "wrong-runtime-options"):
        bad = copy.deepcopy(manifest)
        if label == "invalid-tools":
            bad["tools"] = {"unrelated": {}}
        else:
            bad["runtime_options"] = ["--gcthreads=99", "run",
                                      "--holstate=/foreign/heap"]
        result.append(rejected(label, bad, receipt))
    return result


def storage(folder):
    report = a.load(folder / "acceptance.json")
    a.require(report["success"] is True and len(report["workloads"]) == 6,
              "incomplete six-size experiment")
    workloads = []
    count = 0
    for size in a.SIZES:
        results = {}
        for selection in ("control", "candidate"):
            path = folder / ("storage_graph-%d-%s" % (size, selection))
            manifest = a.load(path / "manifest.json")
            options = manifest["performance"]
            result = a.analyze(path, case="storage_graph", size=size,
                baseline=a.BASE, candidate=(a.BASE if selection == "control"
                                           else manifest["selections"][
                                               "candidate"]["revision"]),
                pairs=10, samples=3, seconds=0.3)
            a.require(options["pairs"] == 10, "not ten pairs")
            results[selection] = result
            count += 20
        for key, value in results["candidate"]["metrics"].items():
            a.apply_control(value, results["control"]["metrics"][key])
        workloads.append(results)
    a.require(json.loads(json.dumps(workloads)) == report["workloads"],
              "changed workload analysis")
    a.require(a.retained_scaling(workloads) == report["retained_scaling"],
              "changed slope decisions")
    return dict(receipts=count, exit=a.report_exit_status(report),
                protocol_complete=True, scaling=report["retained_scaling"],
                metrics=[dict(size=r["candidate"]["size"], decisions={
                    k: v["decision"] for k, v in r["candidate"][
                        "metrics"].items()}) for r in workloads],
                mutation_controls=mutations(folder / "storage_graph-10-candidate"))


def client(folder):
    manifest = a.load(folder / "manifest.json")
    a.require(manifest["success"] is True, "failed client protocol")
    count, controls = 0, []
    for run in manifest["runs"]:
        receipt = a.load(folder / run["receipt"])
        if receipt["fixture"] == "performance":
            audit(manifest, receipt)
            count += 1
        elif receipt["control"] != "none":
            a.require(not receipt["accepted"] and not run["accepted"] and
                      "control_failure" not in receipt,
                      "runner failed to detect negative control")
            controls.append([receipt["selection"], receipt["control"]])
    a.require(count == 2 and len(controls) == 12, "missing client controls")
    return dict(receipts=count, runner_controls=controls,
                mutation_controls=mutations(folder))


def loading(folder, module, *, smoke):
    report = a.load(folder / "loading.json")
    a.require(report["success"] is True and report["module"] == module and
              report["mode"] == ("smoke" if smoke else "isolated-source") and
              report["pairs"] == (1 if smoke else 10),
              "failed/wrong-scope loading protocol")
    a.require(len(report["runs"]) == 2 + 4 * report["pairs"],
              "missing loading processes")
    gc, rows, pilots = [], {"control": [], "candidate": []}, []
    for run in report["runs"]:
        path = folder / run["receipt"]
        a.require(a.seal(path) == run["seal"], "changed loading receipt")
        receipt = a.load(path)
        a.require(receipt["accepted"] and receipt["exit"] == 0 and
                  not receipt["timed_out"], "failed loading receipt")
        events = rp.parse_events(receipt["stdout"])
        _, measured = l.observations(events, report["module"])
        a.require(measured == receipt["measurement"], "changed loading data")
        gc.append(measured["accounting"]["gc_cpu"])
        if run["phase"] == "pilot":
            pilots.append(measured)
        else:
            rows[run["phase"]].append(receipt)
        for event in events:
            if event[:2] == ["observation", "timer.accounting"]:
                event[2] = "0,0,0,0,0,0,0,0"
        try:
            l.observations(events, report["module"])
        except ValueError as error:
            a.require("did not exercise GC" in str(error), "wrong GC guard")
        else:
            raise ValueError("zero-GC real loading control accepted")
    a.require(pilots == report["calibration"] and len(pilots) == 2,
              "changed loading calibration")
    results = {phase: l.statistics(data, report["pairs"], smoke)
               for phase, data in rows.items()}
    if not smoke:
        for metric, data in results["candidate"]["metrics"].items():
            a.apply_control(data, results["control"]["metrics"][metric])
            if not all(p["calibrated"] for p in pilots):
                data["decision"] = "inconclusive"
                data["reason"] = "uncalibrated pilot import"
    a.require(results == report["results"], "changed loading statistics")
    return dict(receipts=len(gc), minimum_forced_gc_cpu=min(gc),
                zero_gc_mutations_rejected=len(gc), results=report["results"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--storage", type=Path, required=True)
    parser.add_argument("--client", type=Path, required=True)
    parser.add_argument("--cong", type=Path, required=True)
    parser.add_argument("--simp", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    results = dict(storage=storage(args.storage), client=client(args.client),
                   cong=loading(args.cong, "congLib", smoke=False),
                   simp=loading(args.simp, "simpLib", smoke=True))
    a.save(args.output, results)
    print(json.dumps({"source_bound_matrix_receipts": sum(
        results[k]["receipts"] for k in ("storage", "client")),
        "loading_receipts": sum(results[k]["receipts"] for k in
                                ("cong", "simp")), "replay": "pass"}))


if __name__ == "__main__":
    main()
