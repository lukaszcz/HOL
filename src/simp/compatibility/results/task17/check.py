#!/usr/bin/env python3
"""Recheck TASK_17 evidence continuity; not a new library/build test run.

Run from any cwd in the configured checkout. Requires the retained TASK_14–16
receipts and current build tools/heaps. Writes checks.json only on success.
Temporary reporter outputs self-clean; no shared build products are touched.
"""

from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[5]
HERE = ROOT / "src/simp/compatibility"
OUT = Path(__file__).resolve().parent
ENV = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(path):
    data = path.read_bytes()
    return json.loads(gzip.decompress(data) if path.suffix == ".gz" else data)


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def hashes(inventory, base=ROOT):
    mismatches = [p for p, h in inventory.items()
                  if not (base / p).is_file()
                  or sha((base / p).read_bytes()) != h]
    assert not mismatches, mismatches
    return len(inventory)


def command(argv, cwd=ROOT):
    result = subprocess.run(argv, cwd=cwd, env=ENV, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False)
    record = {"argv": list(map(str, argv)), "cwd": str(cwd.relative_to(ROOT)),
              "exit": result.returncode, "stdout": result.stdout.decode(),
              "stdout_sha256": sha(result.stdout)}
    commands.append(record)
    assert result.returncode == 0, record
    return result.stdout


commands = []
verified = {}
start = datetime.now(timezone.utc).isoformat()
verified["candidate_files"] = hashes(load(
    HERE / "results/task16/candidate-files.json.gz"))
t15 = load(HERE / "results/task15/validation.json")
verified["task15_inputs"] = hashes(t15["input_sha256"])
for c in t15["commands"]:
    assert c["exit"] == 0 and not c["failing_targets"]
    raw = gzip.decompress((HERE / "results/task15" / c["log"]).read_bytes())
    assert sha(raw) == c["stdout_sha256"], c["name"]
verified["task15_command_logs"] = len(t15["commands"])

full = load(HERE / "results/task16/validation.json")
assert full["argv"] == ["bin/build", "-t", "-F"] and full["exit"] == 0
assert not full["source_changes_during_build"]
verified["task16_tools_and_driver"] = hashes(full["hashes"])
raw = gzip.decompress((HERE / "results/task16/full.log.gz").read_bytes())
assert sha(raw) == full["raw_sha256"] and b"Hol built successfully." in raw
scope = load(HERE / "results/task16/scope-audit.json")
assert scope["expected_visits_equal_actual_in_order"]
assert scope["visited_count"] == 87 and not scope["required_failures"]
verified["task16_sequences"] = hashes(scope["sequence_files_sha256"])
logs = load(HERE / "results/task16/fresh-selftest-logs.json.gz")
assert len(logs) == scope["fresh_selftest_log_count"] == 34
for name, entry in logs.items():
    assert sha(entry["text"].encode()) == entry["sha256"], name
    assert full["start"] <= entry["mtime_utc"] <= full["end"], name
verified["task16_fresh_log_records"] = len(logs)
verified["task16_visits"] = scope["visited_count"]
verified["task16_theory_timings"] = scope["theory_timing_entries"]
assert verified["task16_theory_timings"] == 650
verified["task16_evidence_hashes"] = hashes(
    load(HERE / "results/task16/final-checks.json")["evidence_sha256"],
    HERE / "results/task16")

for lane_kind in ("paired-verified", "fresh-verified"):
    manifest = load(HERE / "results/task14" / lane_kind / "manifest.json")
    assert manifest["passed"]
    assert all(c["exit"] == 0 for c in manifest["commands"])
    verified[lane_kind + "_branch_sources"] = hashes(
        manifest["lanes"]["branch"]["sources_sha256"])
    for lane in ("reference", "branch"):
        revision = manifest[lane]
        for path, expected in manifest["lanes"][lane]["sources_sha256"].items():
            assert sha(git("show", revision + ":" + path)) == expected, path
    base = HERE if lane_kind == "paired-verified" else HERE / "probes/fresh-load"
    verified[lane_kind + "_inputs"] = hashes(manifest["inputs_sha256"], base)
    if "support_sha256" in manifest:
        verified["paired_support"] = hashes(manifest["support_sha256"], HERE)
    if isinstance(manifest["runner_sha256"], dict):
        hashes(manifest["runner_sha256"], HERE)
    else:
        assert sha((HERE / "run.py").read_bytes()) == manifest["runner_sha256"]

assert (HERE / "inputs/develop/selftest.sml").read_bytes() == git(
    "show", "cccaa27d7099cbadc886983020cbe745db7793f3:src/simp/src/selftest.sml")
verified["original_develop_selftest_byte_equal"] = True
with tempfile.TemporaryDirectory(prefix="compat-task17-report.") as tmp:
    output = Path(tmp) / "comparison"
    command(["python3", str(HERE / "paired_report.py"), "--paired",
             str(HERE / "results/task14/paired-verified"), "--fresh",
             str(HERE / "results/task14/fresh-verified"), "--output", str(output)])
    for name in ("matrix.json.gz", "raw-differences.diff"):
        assert (output / name).read_bytes() == (
            HERE / "results/task14/comparison" / name).read_bytes(), name
    matrix = load(output / "matrix.json.gz")
    verified["paired_ordinary_inputs"] = len(matrix["paired"]["inputs"])
    verified["paired_fresh_inputs"] = len(matrix["fresh"]["inputs"])
    verified["ordered_observation_pairs"] = sum(
        len(row["contracts"]) for group in matrix.values()
        for row in group["inputs"])
assert verified["ordered_observation_pairs"] == 3251
command(["python3", str(HERE / "paired_report_test.py")])
command(["sha256sum", "-c", "inputs/SHA256SUMS"], cwd=HERE)
command(["tools/h4pedant/h4pedant", "src/1", "src/postkernel",
         "src/simp/src", "src/marker", *[
             "src/simp/compatibility/probes/" + name for name in
             ("support", "legacy", "fresh-load", "split-registration",
              "split-persistence")]])
command(["git", "diff", "--check"])
command(["git", "diff", "--cached", "--check"])

# Audit row IDs cover every original checkbox, including regression sections.
ledger = (HERE / "PLAN_AUDIT.md").read_text()
expected = [f"P{phase}.{n}" for phase, count in enumerate(
    (5, 11, 13, 15, 9), start=1) for n in range(1, count + 1)]
expected += [f"C{n}" for n in range(1, 6)]
assert re.findall(r"(?m)^\| (P\d+\.\d+|C\d+) \|", ledger) == expected
verified["plan_items_mapped"] = len(expected)
plan = ROOT / ".agent-files/PLAN_compatibility.md"
if plan.exists():
    sections = re.split(r"(?m)^## ", plan.read_text())
    counts = [len(re.findall(r"(?m)^- \[[ x]\]", s)) for s in sections]
    assert [n for n in counts if n] == [5, 11, 13, 15, 9, 5]
    verified["original_plan_sha256"] = sha(plan.read_bytes())

progress = (ROOT / ".agent-files/tasks/PROGRESS.md").read_text()
assert len(re.findall(r"(?m)^## ", progress)) == 3
for task in range(1, 18):
    assert len(re.findall(rf"(?m)^- TASK_{task:02d}: done", progress)) == 1
    assert len(re.findall(rf"(?m)^- TASK_{task:02d} — ", progress)) == 1
assert "None — all seventeen tasks are complete" in progress
verified["completion_log_lines"] = 17
verified["final_report_and_handoff_sha256"] = {
    path: sha((ROOT / path).read_bytes()) for path in (
        ".agent-files/tasks/PROGRESS.md", ".agent-files/tasks/TASK_INDEX.md",
        "src/simp/compatibility/FINAL_REPORT.md",
        "src/simp/compatibility/PLAN_AUDIT.md")}

# Check whole text of changed/new task files, including docs/tests/JSON that
# directory pedant omits. checks.json is emitted with the same whitespace rule.
paths = set(git("diff", "--name-only", "HEAD").decode().splitlines())
paths.update(git("ls-files", "--others", "--exclude-standard").decode().splitlines())
for path in sorted(paths):
    p = ROOT / path
    if p.is_file():
        text = p.read_text()
        assert "\t" not in text, path
        assert all(line == line.rstrip() for line in text.splitlines()), path
verified["changed_text_paths"] = sorted(paths)

# Only inspect known task scratch names. Never delete caller-owned artifacts.
patterns = ("hol-simp-pair.*", "hol-simp-fresh.*", "compat-task1[0-7]*")
temp_roots = {Path("/tmp"), Path(tempfile.gettempdir())}
leftovers = sorted({str(p) for root in temp_roots for pattern in patterns
                    for p in root.glob(pattern)})
verified["temporary_roots_inspected"] = sorted(map(str, temp_roots))
assert not leftovers, leftovers
assert not list(HERE.rglob("__pycache__"))
assert not list(HERE.rglob(".pytest_cache"))
verified["task_scratch_or_cache_leftovers"] = leftovers
verified["cleanup"] = (
    "Reporter TemporaryDirectory removed; no build products/caller files deleted. "
    "Historical caller-owned investigation and unrelated worktrees untouched.")

receipt = {"started_utc": start, "ended_utc": datetime.now(timezone.utc).isoformat(),
           "revision": git("rev-parse", "HEAD").decode().strip(),
           "tree": git("rev-parse", "HEAD^{tree}").decode().strip(),
           "commands": commands, "verified": verified,
           "audit_driver_sha256": sha(Path(__file__).read_bytes()),
           "scope": "Integrity/audit checks; no new library/full build execution."}
(OUT / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
print("PASS: 58 plan items; final source/gate integrity, whitespace and cleanup")
