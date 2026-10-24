#!/usr/bin/env python3
"""Reproduce TASK29A's policy obstruction; never approve or alter a gate.

Re-admits the original zero-GC cell using the ordinary archive auditor. Other
cells and new runtime measurements are deliberately outside this review.
Synthetic examples below demonstrate the executable contract, not host noise.
"""
import argparse
import copy
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
import acceptance as a
import evidence_bundle as bundle
import task29_gate as gate

HERE = Path(__file__).resolve().parent
GRID = HERE / "evidence/task29/full-grid"


def examples():
    """Keep the distinction between undefined ratios and directional tests."""
    def pairs(baseline, candidate):
        return [{"baseline": baseline, "candidate": candidate} for _ in
                range(10)]

    def controlled(candidate, control):
        result = copy.deepcopy(candidate)
        a.apply_control(result, control)
        return result

    zero = a.paired_statistics(pairs(0, 0))
    positive_over_zero = a.paired_statistics(pairs(0, 1))
    equality = a.paired_statistics(pairs(1, 1))
    # Even arbitrarily precise intervals around equality need not pass B/B.
    straddling = a.paired_statistics([
        {"baseline": 1, "candidate": 1 + sign * 1e-6}
        for sign in [-1, 1] * 5])
    faster = a.paired_statistics(pairs(1, 0.9))
    slower = a.paired_statistics(pairs(1, 1.000001))
    return dict(scope="synthetic contract examples, NOT runtime evidence",
                zero_over_zero=zero, positive_over_zero=positive_over_zero,
                exact_positive_equality=equality,
                precise_equality_straddling=straddling,
                faster_with_uncertain_control=controlled(faster, straddling),
                slower_with_uncertain_control=controlled(slower, straddling))


def zero_cell(grid):
    """Full protocol and source/runtime replay, not summary inspection."""
    inventory = a.load(grid / "inventory.json")
    a.require(inventory["driver"] == a.seal(gate.__file__),
              "changed grid driver")
    rows = [r for r in inventory["runs"] if
            (r["case"], r["size"]) == ("compile_single", 0)]
    a.require(len(rows) == 1, "missing/duplicate reviewed cell")
    row, = rows
    archive = a.safe_child(grid, row["archive"])
    a.require(a.seal(archive) == row["seal"], "changed reviewed archive")
    processes = []
    with tempfile.TemporaryDirectory(prefix="task29-policy-review-") as tmp:
        root = Path(tmp) / "unpacked"
        a.require(bundle.unpack(archive, root) == row["files"],
                  "changed reviewed file count")
        report = a.load(root / "acceptance.json")
        a.require(report["success"] and row["protocol"] and
                  a.report_exit_status(report) == row["exit"],
                  "changed reviewed outcome")
        gate.check_report(root, report, inventory["baseline"],
                          inventory["candidate"], inventory["seconds"],
                          "compile_single", 0)
        for experiment in ("control", "candidate"):
            folder = root / ("compile_single-0-" + experiment)
            manifest = a.load(folder / "manifest.json")
            for run in manifest["runs"]:
                path = a.safe_child(folder, run["receipt"])
                receipt = a.load(path)
                if receipt["fixture"] != "performance":
                    continue
                batches = receipt["measurements"]["workloads"][
                    "compile_single"]["batches"]
                processes.append(dict(
                    experiment=experiment, pair=receipt["pair"],
                    selection=receipt["selection"], receipt=run["receipt"],
                    receipt_seal=a.seal(path),
                    timer_accounting=receipt["measurements"][
                        "timer_accounting"],
                    samples=[{key: b[key] for key in
                              ("sample", "iterations", "gc_usr", "gc_sys",
                               "check_gc_user", "gc")} for b in batches]))
    # This report concerns this particular historical observation regime. If
    # it changes, reject rather than silently generalize the review claim.
    a.require(len(processes) == 40 and
              all(len(p["samples"]) == 3 for p in processes),
              "incomplete reviewed samples")
    a.require(all(b[key] == 0 for p in processes for b in p["samples"]
                  for key in ("gc_usr", "gc_sys", "check_gc_user", "gc")),
              "reviewed samples no longer all zero")
    result, = report["workloads"]
    return dict(case="compile_single", size=0, archive=archive.name,
                archive_seal=a.seal(archive),
                baseline=inventory["baseline"],
                candidate=inventory["candidate"],
                fixture="historical driver, NOT repaired-driver acceptance",
                processes=processes, measured_samples=120,
                gc_metrics={side: result[side]["metrics"]["gc"] for side in
                            ("control", "candidate")})


def review(grid=GRID):
    return dict(schema="task29-policy-review-v1", task29a="incomplete",
                status="policy-owner input required; no waiver granted",
                scope="one historical cell re-admitted; NOT full-grid replay "
                      "or fresh timing/layout/allocation evidence",
                policy=a.POLICY,
                sources={p.name: a.seal(p) for p in (
                    Path(__file__), HERE / "acceptance.py",
                    HERE / "summarize.py", HERE / "task29_gate.py",
                    HERE / "PROTOCOL.md", HERE / "evidence_bundle.py",
                    HERE / "test_policy_review.py",
                    HERE / "TASK29A_POLICY_REVIEW.md")},
                grid_inventory=a.seal(grid / "inventory.json"),
                reviewed_cell=zero_cell(grid), contract_examples=examples(),
                conclusions=[
                    "Any zero baseline process median makes its ratio null; "
                    "one such pair prevents a passing ratio-only GC gate.",
                    "Repeating observations that remain all zero cannot "
                    "resolve it. Zero GC is not zero allocation.",
                    "B/B upper-CI<=1 is directional, not an independently "
                    "specified stability test. Straddling equality alone "
                    "does not establish host instability.",
                    "Exact positive equality can pass B/B. This review does "
                    "not prove that every future B/B experiment must block.",
                    "Policy clarification cannot repair measured slowdowns "
                    "or replace the required fresh grid and attribution."],
                required_input=[
                    "Policy owner: confirm whether zero-denominator GC must "
                    "remain nonpassing, including exact zero/zero.",
                    "Policy owner: confirm whether B/B admission is intended "
                    "to require directional upper-CI<=1 rather than a "
                    "separately specified validity/stability criterion."])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--grid", type=Path, default=GRID)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    # Fail before replay if the requested output already exists, then use
    # exclusive creation as well. A failed replay must not leave a receipt.
    if args.output.exists():
        raise FileExistsError(args.output)
    result = review(args.grid)
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, allow_nan=False)
        stream.write("\n")
    return 2  # The review is reproduced; TASK29A is NOT accepted.


if __name__ == "__main__":
    sys.exit(main())
