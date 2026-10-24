#!/usr/bin/env python3
"""Seal TASK29 commands, current inputs and compact unique evidence."""
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
sys.path.insert(0, str(HERE.parents[1]))
import acceptance as a


def main():
    telemetry = a.load(HERE / "telemetry.json")
    for name, expected in telemetry["inputs"].items():
        a.require(a.seal(ROOT / name) == expected,
                  "measured fixture/tool input changed: " + name)
    statuses = {p.stem: int(p.read_text()) for p in HERE.glob("*.exit")}
    a.require(statuses["full-grid"] == statuses["replay"] == 2,
              "blocked gate or replay exit changed")
    a.require(statuses["development-failed"] == 1,
              "development failure missing")
    a.require(all(code == 0 for name, code in statuses.items()
                  if name not in ("full-grid", "replay", "development-failed")),
              "validation command failed")
    sources = ["README.md", "task29_gate.py", "test_task29_gate.py",
               "TASK_29_HANDOFF.md", "TASK_29A_numerical_attribution_closure.md",
               "TASK_29B_allocation_counter.md"]
    sources = {"src/simp/tests/performance/" + name for name in sources}
    structural = {
        "src/simp/tests/compiled-core/assembly/RESULTS.md",
        "src/simp/tests/compiled-core/assembly/evidence/current/manifest.json",
        "src/simp/tests/compatibility/allocation/ASSEMBLY.md",
        "src/simp/tests/compatibility/evidence/task12-allocation/manifest.json"}
    decisions = a.load(HERE / "full-grid/decisions.json")
    rows = decisions["workloads"]
    a.require(len(rows) == 162 and telemetry["processes"] == 6480 and
              sum(r["exit"] == 1 for r in rows) == 43 and
              sum(r["exit"] == 2 for r in rows) == 119,
              "changed published counts")
    a.require(all(r["words_per_rule"]["decision"] == "pass" for r in
                  decisions["retained_scaling"]["adjacent_intervals"]),
              "changed graph slope findings")
    files = {str(p.relative_to(HERE)): a.seal(p)
             for p in sorted(HERE.rglob("*")) if p.is_file()}
    commands = {
        "full-grid": "W python3 -u -B src/simp/tests/performance/"
            "task29_gate.py run --candidate "
            "18e4a1ecb624b9b13bb9a0f3ba3caf8c189bdff8 "
            "--batch-seconds 0.3 --timeout 1800 --authorize-measurements "
            "--output src/simp/tests/performance/evidence/task29/full-grid",
        "replay": "python3 -u -B src/simp/tests/performance/task29_gate.py "
            "replay --output src/simp/tests/performance/evidence/task29/"
            "full-grid",
        "report": "python3 -B src/simp/tests/performance/evidence/task29/"
            "report.py",
        "source-audit": "python3 -B src/simp/tests/compatibility/"
            "audit_task27.py (stdout losslessly gzip-compressed)",
        "performance-tests": "python3 -B -m unittest discover -s "
            "src/simp/tests/performance -p 'test*.py'",
        "compatibility-tests": "python3 -B -m unittest discover -s "
            "src/simp/tests/compatibility -p 'test_*.py'",
        "matrix": "python3 -B src/simp/tests/performance/matrix_schema.py",
        "immutable": "python3 -B src/simp/tests/compatibility/"
            "verify_evidence.py",
        "coverage": "python3 -B src/simp/tests/compatibility/"
            "coverage_ledger.py",
        "pedant": "W tools/h4pedant/h4pedant --nolinelen --unicodeok "
            "src/simp/tests/performance",
        "pedant-final": "W tools/h4pedant/h4pedant --nolinelen --unicodeok "
            "src/simp/tests/performance",
        "whitespace": "git diff --check && git diff --cached --check",
    }
    a.save(HERE / "validation.json", dict(
        schema="task29-validation-v1", status="blocked-not-complete",
        measured_candidate="18e4a1ecb624b9b13bb9a0f3ba3caf8c189bdff8",
        baseline=a.BASE,
        head=subprocess.check_output(["git", "rev-parse", "HEAD"],
                                     cwd=ROOT, text=True).strip(),
        wrapper="sh src/simp/tests/compatibility/evidence/task26/"
                "root-wrapper.sh",
        commands={name: dict(command=command, exit=statuses[name])
                  for name, command in commands.items()},
        development_failure=dict(exit=1,
            scope="preflight driver defect; raw receipts lost, not admitted; "
                  "entire final experiment restarted fresh; no sample reused"),
        sources={p: a.seal(ROOT / p) for p in sorted(sources)},
        measured_inputs=telemetry["inputs"],
        historical_structural_inputs={p: a.seal(ROOT / p)
                                      for p in sorted(structural)},
        evidence=files,
        observations=dict(cells=len(decisions["workloads"]), processes=6480,
                          samples=19440, failed_cells=43, uncertain_cells=119,
                          graph_adjacent_control_passes=10,
                          graph_adjacent_candidate_passes=10),
        blockers=["See full-grid/decisions.json for every numerical blocker",
                  "TASK29A source/layout numerical attribution unresolved",
                  "TASK29B supported cumulative allocator counter required"],
        production_changes=False,
        cleanup="All task-owned private build, receipt and roundtrip trees "
                "removed; unrelated review directories/caches preserved",
        claims="Source isolation Linux/aarch64 Poly/ML 5.9.2, one GC thread; "
               "not independent clean builds or final release acceptance"))
    print("TASK29 evidence sealed; blocked status retained")


if __name__ == "__main__":
    main()
