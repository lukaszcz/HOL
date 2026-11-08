#!/usr/bin/env python3
"""TASK29 full-grid isolated attribution, lossless archives, and offline replay.

Uses TASK28's unchanged admission/statistics. No result is a release pass:
cumulative allocation is unsupported on this runtime. Failed/uncertain cases
remain blockers; no averaging, retry selection, or baseline subtraction.
"""
import argparse
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import acceptance as a
import evidence_bundle as bundle
from matrix_schema import get_case

CASES = (
    "frag_create", "frag_named", "frag_named_rules", "frag_record",
    "frag_update", "frag_duplicate", "frag_merge", "frag_named_merge",
    "frag_ac", "frag_ac_merge", "frag_typebase", "frag_type_lookup",
    "compile_batch", "compile_single", "compile_empty", "compile_excluded",
    "compile_conditional", "compile_bounded", "compile_ac", "compile_maker",
    "compile_user", "compile_collector", "compile_construct_conv",
    "compile_reuse", "compile_complete", "compile_supplied", "storage_graph")
SIZES = a.SIZES
ALLOCATION = (
    "blocked: Poly/ML 5.9.2 has no supported cumulative allocation counter; "
    "heap/free/allocation-area snapshots are not allocated bytes")


def keys():
    return [(case, size) for case in CASES for size in SIZES]


def summary(reports, cells=None, label="TASK29"):
    """Rows of a grid; `cells` and `label` serve other tasks' grids."""
    cells = keys() if cells is None else list(cells)
    a.require(set(reports) == set(cells), "incomplete %s grid" % label)
    rows, storage = [], []
    for case, size in cells:
        report = reports[case, size]
        a.require(len(report.get("workloads", [])) <= 1,
                  "expected one case/size experiment")
        row = dict(case=case, size=size, protocol=report["success"],
                   exit=a.report_exit_status(report))
        if report["success"]:
            result, = report["workloads"]
            a.require(result["candidate"]["case"] == case and
                      result["candidate"]["size"] == size,
                      "wrong workload binding")
            row["metrics"] = {
                key: {field: value[field] for field in (
                    "decision", "median_paired_ratio",
                    "paired_ratio_bootstrap_95_percent", "reason")}
                for key, value in result["candidate"]["metrics"].items()}
            row["control_metrics"] = {
                key: value["decision"] for key, value in
                result["control"]["metrics"].items()}
            if case == "storage_graph":
                storage.append(result)
        else:
            row["unresolved"] = report.get("failure", report.get("blocked"))
        rows.append(row)
    return dict(schema="task29-gate-v1", status="blocked",
                allocation=ALLOCATION, workloads=rows,
                retained_scaling=a.retained_scaling(storage),
                scope="isolated sources, not independent clean builds",
                uncertainty="No samples removed; inconclusive is not pass. "
                "RSS/HWM are approximate process snapshots, not batch peaks.")


def check_report(folder, report, baseline, candidate, seconds, case, size):
    """Recompute admitted reports; protocol failures are retained, not admitted."""
    if not report["success"]:
        a.require(report.get("failure") or report.get("blocked"),
                  "unexplained incomplete experiment")
        return
    results = {}
    for selection in ("control", "candidate"):
        results[selection] = a.analyze(
            folder / ("%s-%d-%s" % (case, size, selection)),
            case=case, size=size, baseline=baseline,
            candidate=baseline if selection == "control" else candidate,
            pairs=10, samples=3, seconds=seconds)
    for name, value in results["candidate"]["metrics"].items():
        a.apply_control(value, results["control"]["metrics"][name])
    a.require(json.dumps([results], sort_keys=True) ==
              json.dumps(report["workloads"], sort_keys=True),
              "changed point analysis")
    scaling = a.retained_scaling([results]) if case == "storage_graph" else None
    a.require(scaling == report["retained_scaling"], "changed slope analysis")


def run(args):
    root = args.output.resolve()
    root.mkdir(parents=True, exist_ok=False)
    inventory = dict(schema="task29-experiment-v1", baseline=args.baseline,
                     candidate=args.candidate, seconds=args.batch_seconds,
                     pairs=10, samples=3, outliers="none removed", runs=[],
                     driver=a.seal(__file__))
    reports = {}
    # One host/repository lock spans the entire batch, including transport.
    with a.serial_lock(args.repo) as fds:
        import os
        old = os.environ.get("HOL4_PERF_LOCK_FDS")
        os.environ["HOL4_PERF_LOCK_FDS"] = ",".join(map(str, fds))
        try:
            for case, size in keys():
                get_case(case, size)
                name = "%s-%d" % (case, size)
                print("START " + name, flush=True)
                with tempfile.TemporaryDirectory(prefix="task29-") as scratch:
                    folder = Path(scratch) / name
                    options = argparse.Namespace(
                        pairs=10, samples=3, batch_seconds=args.batch_seconds,
                        timeout=args.timeout, baseline=args.baseline,
                        candidate=args.candidate, authorize_measurements=True,
                        case=[case], size=[size], output=folder,
                        mode="isolated", repo=args.repo, build_manifest=None)
                    report = a.run(options)
                    archive = root / (name + ".json.xz")
                    count = bundle.pack(folder, archive)
                    # Verify every original byte before deleting the scratch.
                    restored = Path(scratch) / "roundtrip"
                    a.require(bundle.unpack(archive, restored) == count,
                              "transport count mismatch")
                    for path in folder.rglob("*"):
                        if path.is_file():
                            a.require(a.seal(path) == a.seal(
                                restored / path.relative_to(folder)),
                                "transport changed original bytes")
                    reports[case, size] = report
                    inventory["runs"].append(dict(
                        case=case, size=size, archive=archive.name,
                        seal=a.seal(archive), files=count,
                        exit=a.report_exit_status(report),
                        protocol=report["success"]))
                    # Archive before replay: a replay defect must not lose
                    # the unique original observations during scratch cleanup.
                    check_report(folder, report, args.baseline, args.candidate,
                                 args.batch_seconds, case, size)
                    print("END %s exit=%d protocol=%s" % (
                        name, a.report_exit_status(report), report["success"]),
                        flush=True)
        finally:
            if old is None:
                del os.environ["HOL4_PERF_LOCK_FDS"]
            else:
                os.environ["HOL4_PERF_LOCK_FDS"] = old
            a.save(root / "inventory.json", inventory)
    a.save(root / "decisions.json", summary(reports))


def replay(args):
    root = args.output.resolve()
    inventory = a.load(root / "inventory.json")
    a.require(inventory["driver"] == a.seal(__file__), "changed driver")
    reports = {}
    for row in inventory["runs"]:
        key = row["case"], row["size"]
        a.require(key in keys() and key not in reports, "wrong/duplicate case")
        archive = a.safe_child(root, row["archive"])
        a.require(a.seal(archive) == row["seal"], "changed archive")
        with tempfile.TemporaryDirectory(prefix="task29-replay-") as scratch:
            folder = Path(scratch) / "unpacked"
            a.require(bundle.unpack(archive, folder) == row["files"],
                      "changed archive file count")
            report = a.load(folder / "acceptance.json")
            a.require(row["exit"] == a.report_exit_status(report) and
                      row["protocol"] == report["success"],
                      "changed experiment outcome")
            check_report(folder, report, inventory["baseline"],
                         inventory["candidate"], inventory["seconds"], *key)
            reports[key] = report
        print("REPLAY %s %d" % key, flush=True)
    a.require(summary(reports) == a.load(root / "decisions.json"),
              "changed TASK29 decisions")
    print("TASK29 archives and decisions replayed; gate remains blocked")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("run", "replay"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repo", type=Path, default=a.HERE.parents[3])
    parser.add_argument("--baseline", default=a.BASE)
    parser.add_argument("--candidate")
    parser.add_argument("--batch-seconds", type=float, default=0.3)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--authorize-measurements", action="store_true")
    args = parser.parse_args()
    if args.action == "run":
        a.require(args.authorize_measurements,
                  "measurement authorization required")
        a.exact_pin(args.baseline)
        a.exact_pin(args.candidate)
        run(args)
    else:
        replay(args)
    return 2  # Unsupported allocation and any unresolved rows cannot pass.


if __name__ == "__main__":
    sys.exit(main())
