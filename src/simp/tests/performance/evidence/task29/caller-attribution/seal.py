#!/usr/bin/env python3
"""Seal this diagnostic increment without manufacturing TASK29 approval."""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
PERF = ROOT / "src/simp/tests/performance"


def stamp(path):
    data = path.read_bytes()
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


sources = ["caller_codegen.py", "CallerCodegen.sml", "test_caller_codegen.py",
           "CALLER_CODEGEN.md", "TASK_29_HANDOFF.md",
           "TASK_29A_numerical_attribution_closure.md"]
assert b"Ran 328 tests" in gzip.decompress(
    (HERE / "performance-tests.log.gz").read_bytes())
assert b"Ran 196 tests" in gzip.decompress(
    (HERE / "compatibility-tests.log.gz").read_bytes())
assert b"Ran 12 tests" in gzip.decompress(
    (HERE / "real-tests.log.gz").read_bytes())
assert b"Hol built successfully." in gzip.decompress(
    (HERE / "routine.log.gz").read_bytes())
decisions = json.loads((HERE.parent / "full-grid/decisions.json").read_text())
assert len(decisions["workloads"]) == 162
assert sum(r["exit"] == 1 for r in decisions["workloads"]) == 43
assert sum(r["exit"] == 2 for r in decisions["workloads"]) == 119
for name in ("record-zero", "collector-large"):
    transport = json.loads((HERE / (name + "-transport.json")).read_text())
    assert transport["files"] == 24 and transport["roundtrip"]
    assert transport["archive"] == stamp(HERE / (name + ".json.xz"))
api = ROOT / "src/simp/tests/api-audit/evidence/20261024T070025Z-929ee34d"
inputs = [PERF / name for name in sources]
inputs += [HERE.parent / "full-grid" / name for name in
           ("inventory.json", "decisions.json")]
inputs += list(sorted(p for p in api.iterdir() if p.is_file()))
command_prefix = "W python3 -B src/simp/tests/performance/caller_codegen.py "
commands = {
    "record": dict(command=command_prefix + "--candidate 90e528c41 "
        "--case frag_record --size 0 --batch-iterations 33554432 "
        "--authorize-diagnostic --timeout 900 --output NEW_RECORD_DIRECTORY",
        exit=0),
    "collector": dict(command=command_prefix + "--candidate 90e528c41 "
        "--case compile_collector --size 10000 --batch-iterations 64 "
        "--authorize-diagnostic --timeout 900 --output NEW_COLLECTOR_DIRECTORY",
        exit=0),
    "replay": dict(command="python3 -B .../caller_codegen.py --replay "
        "UNPACKED_DIRECTORY (both final bundles)", exit=0),
    "real-tests": dict(command="CALLER_CODEGEN_EVIDENCE="
        "UNPACKED_RECORD_DIRECTORY python3 -B -m unittest discover "
        "-s src/simp/tests/performance "
        "-p test_caller_codegen.py -v", exit=0, tests=12, real_mutations=7),
    "performance-tests": dict(command="CALLER_CODEGEN_EVIDENCE="
        "UNPACKED_RECORD_DIRECTORY python3 -B -m unittest discover "
        "-s src/simp/tests/performance -p 'test*.py'", exit=0,
        tests=328, unchanged_optional_skips=2),
    "compatibility-tests": dict(command="python3 -B -m unittest discover "
        "-s src/simp/tests/compatibility -p 'test_*.py'", exit=0, tests=196),
    "routine": dict(command="W bin/build -t "
        "--seq=tools/sequences/upto-parallel", exit=0),
    "grid-prefix": dict(command="python3 -u -B "
        "src/simp/tests/performance/task29_gate.py replay --output "
        "src/simp/tests/performance/evidence/task29/full-grid",
        result="caller timeout at 900s, 135 complete cells; NOT exit zero"),
    "grid-suffix": dict(command="python3 -u -B "
        "src/simp/tests/performance/evidence/task29/caller-attribution/"
        "resume_grid_replay.py", exit=0, remaining_cells=27,
        scope="locally trusted prefix plus original suffix checks; "
              "all 162 archive seals and aggregate decisions verified"),
    "equal-count": dict(command="python3 -B src/simp/tests/performance/"
        "evidence/task29/equal-count/replay.py", exit=0,
        meaning="reproduced unresolved failures, not acceptance"),
    "pedant": dict(command="W tools/h4pedant/h4pedant --nolinelen "
        "--unicodeok src/simp/tests/performance", exit=0),
    "whitespace": dict(command="git diff --check && git diff --cached --check",
        exit=0),
}
receipt = dict(schema="task29-caller-attribution-validation-v1",
    status="blocked-not-complete", production_changes=False,
    start=subprocess.check_output(["git", "rev-parse", "90e528c41"],
        cwd=ROOT, text=True).strip(), commands=commands,
    observations=dict(failed_cells=43, inconclusive_cells=119,
        final_compiler_processes=8, final_legacy_fixture_processes=16),
    inputs={str(p.relative_to(ROOT)): stamp(p) for p in inputs},
    evidence={p.name: stamp(p) for p in sorted(HERE.iterdir()) if p.is_file()
              and p.name != "validation.json"},
    blockers=["Every failed/inconclusive timing cell remains unresolved",
        "Pool/indirect-target and ordinary heap/layout attribution unresolved",
        "Allocator branch/failure coverage and native compiler/image lineage",
        "Full 162-cell ten-pair B/B and B/C allocation matrix absent"],
    cleanup="Task-owned private source/build, unpacked/roundtrip trees and "
        "scratch logs removed. Caller-owned review/cache/planning state kept.")
(HERE / "validation.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("Caller attribution sealed; TASK29/TASK29A/TASK29B remain incomplete")
