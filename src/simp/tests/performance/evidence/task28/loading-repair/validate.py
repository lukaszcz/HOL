#!/usr/bin/env python3
"""Seal TASK28 loading repair evidence; run under the configured-root wrapper."""
import gzip
import json
import lzma
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
sys.path.insert(0, str(ROOT / "src/simp/tests/performance"))
import acceptance as a


def log(name):
    return gzip.decompress((HERE / name).read_bytes()).decode()


def main():
    payload = json.loads(lzma.decompress((HERE / "final.json.xz").read_bytes()))
    a.require(len(payload["files"]) == 101, "incomplete final transport")
    replay = a.load(HERE / "replay.json")
    roundtrip = a.load(HERE / "roundtrip-check.json")
    a.require(a.seal(HERE / "replay.json") == roundtrip["replay_seal"] and
              roundtrip["files"] == 101 and roundtrip["identical"],
              "lossless roundtrip replay differs")
    commands, observations = [], {}
    wrapper = ["sh", "src/simp/tests/compatibility/evidence/task26/"
               "root-wrapper.sh"]
    for module in ("simpLib", "congLib"):
        record = payload["files"][module + "/loading.json"]
        report = json.loads(record["content"])
        a.require(report["schema"] == "task28-loading-v2" and
                  report["success"] and len(report["runs"]) == 42 and
                  all(run["accepted"] for run in report["runs"]),
                  "incomplete real loading experiment")
        # The real driver already checked these at run end. Check them again
        # against live current inputs, before writing the landing's seals.
        for raw, seal in report["inputs"].items():
            a.require(a.seal(raw) == seal, "changed measured input: " + raw)
        libraries = report["dynamic_libraries"]["inputs"]
        a.require(len(libraries) == 6, "wrong linked runtime inventory")
        commands.append(dict(argv=wrapper + ["python3", "-B"] +
                             report["argv"], exit=1,
                             log=module + "-final-cli.log.gz"))
        observations[module] = dict(
            processes=42, libraries=libraries,
            results={phase: {metric: {k: data[k] for k in (
                "decision", "baseline_median", "candidate_median",
                "median_paired_ratio", "paired_ratio_bootstrap_95_percent")}
                for metric, data in result["metrics"].items()}
                for phase, result in report["results"].items()},
            minimum_forced_gc_cpu=replay[module]["minimum_forced_gc_cpu"])
    a.require("Ran 241 tests" in log("holmake-final.log.gz") and
              "OK (skipped=2)" in log("holmake-final.log.gz") and
              "Ran 13 tests" in log("holmake-final.log.gz") and
              "checks=306/306 success=True" in log("holmake-final.log.gz") and
              "checks=336/336 success=True" in log("holmake-final.log.gz"),
              "incomplete maintained integration")
    a.require("Ran 196 tests" in log("compatibility-tests.log.gz") and
              "OK" in log("compatibility-tests.log.gz"),
              "incomplete compatibility tests")
    a.require("Ran 6 tests" in log("previous-review.log.gz") and
              "OK" in log("previous-review.log.gz"), "prior repair regressed")
    probe = a.load(HERE / "review-probe-final.json")
    a.require(probe["scenarios"][0]["accepted_runs"] == 42 and
              probe["scenarios"][0]["success"] and
              not probe["scenarios"][1]["success"] and
              probe["scenarios"][1]["processes"] == 0 and
              "sealed input changed" in probe["scenarios"][1]["failure"],
              "review-v2 source binding regression")
    scratch = Path(report["argv"][report["argv"].index("--output") + 1]).parent
    commands += [dict(argv=wrapper + ["bin/Holmake", "--no-project",
        "--no-cache", "--no_prereqs", "--holstate=" +
        report["repo"] + "/bin/hol.state0", "-C",
        "src/simp/tests/performance", "-j1",
        "PERFORMANCE_CHECK_OUTPUT=" + str(scratch / "check"), "check"],
        exit=0, log="holmake-final.log.gz")]
    for folder, pattern, result, name in (
            ("compatibility", "test_*.py", 0, "compatibility-tests"),):
        commands.append(dict(argv=["python3", "-B", "-m", "unittest",
            "discover", "-s", "src/simp/tests/" + folder, "-p", pattern],
            exit=result, log=name + ".log.gz"))
    commands += [
        dict(command="python3 -B .../loading-repair/review_probe.py "
             "--output .../loading-repair/review-probe-final.json", exit=0),
        dict(command="python3 -B .../review/review_regressions.py -v", exit=0),
        dict(command="W python3 -B .../loading-repair/replay.py "
             "FINAL/simpLib FINAL/congLib --output replay.json", exit=0),
        dict(command="evidence_bundle.py pack FINAL final.json.xz; unpack; "
             "repeat replay on unpacked inputs", exit=0),
        dict(command="python3 -B .../compatibility/coverage_ledger.py", exit=0),
        dict(command="python3 -B .../compatibility/verify_evidence.py", exit=0),
        dict(command="W tools/h4pedant/h4pedant --nolinelen --unicodeok "
             "src/simp/tests/performance", exit=0),
        dict(command="git diff --check", exit=0),
    ]
    inputs = [ROOT / "src/simp/tests/compatibility/run_paired.py"]
    perf = ROOT / "src/simp/tests/performance"
    inputs += [perf / name for name in (
        "loading.py", "test_loading.py", "test_loading_provenance.py",
        "PROTOCOL_LOADING.md", "TASK_28_HANDOFF.md", "matrix.json",
        "matrix_schema.py", "acceptance.py", "audit_evidence.py",
        "performance_schema.py", "summarize.py", "evidence_bundle.py")]
    inputs += list(HERE.glob("*.py")) + [HERE / "README.md"]
    validation = dict(
        landing="TASK28-loading-provenance-v3", schema=1,
        starting_head="859be8ed7672d6c319e231d18b3d5cbfcda34b30",
        baseline=a.BASE,
        status="All bounded TASK28 machinery criteria verified; TASK29 ready",
        scope="Linux/aarch64 Poly/ML 5.9.2; shared-heap isolation only",
        production_source_edits=False, commands=commands,
        observations=observations,
        limitations=["Numerical failures retained, not performance approval",
            "Seven explicit later-gate matrix prerequisites remain",
            "Two unchanged optional real runtime/path tests not repeated",
            "No compiled-source edits; no additional routine build required"],
        development={"compatibility_first_attempt_exit": 1,
            "reason": "transient ENOSPC; complete retry passed",
            "earlier_loading_cli_exits": [2, 2],
            "earlier_loading_processes": 84,
            "rerun_reason": "Archive failed discovery before validation; "
                            "new test and report schema; no SML change"},
        cleanup="All task-owned private trees and roundtrip copies removed; "
                "caller-owned caches, reviews and products preserved",
        inputs={str(p.relative_to(ROOT)): a.seal(p) for p in inputs})
    a.save(HERE / "validation.json", validation)
    evidence = {str(p.relative_to(HERE)): a.seal(p)
                for p in sorted(HERE.rglob("*")) if p.is_file()}
    a.save(HERE / "evidence-seal.json", dict(schema=1, files=evidence))
    print(json.dumps(dict(inputs=len(inputs), evidence=len(evidence),
                          status="verified")))


if __name__ == "__main__":
    main()
