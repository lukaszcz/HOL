#!/usr/bin/env python3
"""Verify preserved evidence, not HOL behavior or performance acceptance.

Run from any directory. Uses only Python's standard library and local Git
objects; does not build, execute probes, measure workloads or write caches.
"""

import ast
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
REVIEW = ROOT / "src/simp/tests/performance/review-20261021"
BASE = "cccaa27d7099cbadc886983020cbe745db7793f3"
CANDIDATE = "cf1f863b4e5a9712ce1b179f18274eb3451f3954"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def git_bytes(revision, path):
    return subprocess.check_output(
        ["git", "-C", str(ROOT), "show", revision + ":" + path]
    )


def log(name):
    path = REVIEW / name
    if path.suffix == ".gz":
        return gzip.decompress(path.read_bytes()).decode()
    return path.read_text()


def read_json(path):
    return json.loads(path.read_text())


def ok_count(text):
    plain = re.sub(r"\x1b\[[0-9;]*m", "", text)
    return len(re.findall(r"\bOK\b", plain))


def main():
    manifest = read_json(HERE / "evidence-manifest.json")
    require(manifest["baseline"] == BASE, "wrong baseline")
    require(manifest["reviewed_candidate"] == CANDIDATE, "wrong candidate")
    entries = manifest["files"]
    require(len(entries) == 37, "incomplete preservation manifest")
    sums = {}
    for line in (HERE / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        require(name not in sums, "duplicate checksum path: " + name)
        sums[name] = digest
    require(len(sums) == len(entries), "checksum inventory mismatch")
    for entry in entries:
        path = ROOT / entry["path"]
        require(path.is_relative_to(ROOT), "path outside repository")
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        require(digest == entry["sha256"] == sums[entry["path"]],
                "hash mismatch: " + entry["path"])
        require(len(data) == entry["bytes"], "size mismatch: " + str(path))
        if entry["kind"] == "immutable baseline differential input":
            source = "src/simp/src/" + path.name
            require(data == git_bytes(BASE, source),
                    "not original develop input: " + source)

    signature = (HERE / "inputs/develop/Traverse.sig").read_bytes()
    expected_abi = (
        b"open Traverse\n"
        + signature.replace(b"signature Traverse =",
                            b"signature LegacyTraverse =")
        + b"\nstructure Reexport : LegacyTraverse = Traverse\n"
        + b'val _ = print "LEGACY_SIGNATURE_OK\\n"\n'
        + b"val _ = OS.Process.exit OS.Process.success\n"
    )
    require((REVIEW / "abicheck.sml").read_bytes() == expected_abi,
            "ABI fixture is not the baseline signature plus wrapper")
    ast.parse((REVIEW / "reproduce.py").read_text())

    results = read_json(REVIEW / "review-results.json")
    validation = read_json(REVIEW / "validation-summary.json")
    details = read_json(REVIEW / "detailed-benchmarks.json")
    require(results["baseline"] == BASE, "wrong result baseline")
    require(results["candidate"] == CANDIDATE, "wrong result candidate")
    require(results["validation"] == validation, "summary disagreement")
    require(len(results["timings_seconds_per_operation"]) == 17,
            "missing historical CPU workloads")
    require(len(details) == 8, "missing historical focused workloads")
    for version in ("develop", "candidate"):
        require(log(version + "-staging.log") ==
                results["staging"][version], "staging log/JSON disagreement")
        require(log(version + "-abicheck.log") ==
                results["signature"][version], "signature log/JSON disagreement")
        memory = dict(re.findall(r"^MEMORY (\d+) (\d+)$",
                                 log(version + "-memory.log"), re.M))
        expected = results["incremental_compiled_words"][version]
        require({k: int(v) for k, v in memory.items()} == expected,
                "retained word log/JSON disagreement")
        for suite in ("legacy", "traversal", "exclusion"):
            suffix = ".log" if suite == "legacy" else ".log.gz"
            text = log(version + "-" + suite + suffix)
            checks = ok_count(text)
            observations = len(re.findall(r"^OBS ", text, re.M))
            require(checks == validation[suite][version + "_ok_count"],
                    "historical assertion count disagreement")
            require(observations ==
                    validation[suite][version + "_observations"],
                    "historical observation count disagreement")
        for batch in (1, 2):
            text = log(f"{version}-timings-{batch}.log")
            labels = re.findall(r"^BENCH (\S+) ", text, re.M)
            require(set(labels) ==
                    set(results["timings_seconds_per_operation"]),
                    "historical CPU workload labels disagree")
            require(len(labels) == 17 and "SINK " in text,
                    "incomplete historical CPU log")
            samples = re.findall(r" reps=(\d+) samples=([^\n]+)", text)
            require(len(samples) == 17 and all(
                int(n) > 0 and len(values.split(",")) == 5
                for n, values in samples), "missing repetitions/samples")
            focused = log(f"{version}-detail-{batch}.log")
            labels = re.findall(r"^DETAIL (\S+) ", focused, re.M)
            require(len(labels) == 8 and set(labels) == set(details)
                    and "SINK " in focused, "incomplete focused log")
    for suite, suffix in (("legacy", ".log"),
                          ("traversal", ".log.gz"),
                          ("exclusion", ".log.gz")):
        before = log("develop-" + suite + suffix)
        after = log("candidate-" + suite + suffix)
        require((before == after) == validation[suite]["same_raw"],
                "historical raw equality claim disagrees")

        def without_build_times(text):
            return re.sub(r'^Theory ".*" took [^\n]+\n', "", text,
                          flags=re.M)

        require((without_build_times(before) == without_build_times(after))
                == validation[suite]["same_excluding_timings"],
                "historical normalized equality claim disagrees")
    for suite in ("native", "native-selftest"):
        checks = ok_count(log(suite + ".log.gz"))
        require(checks == validation[suite]["ok_count"],
                "historical native count disagreement")

    state = read_json(HERE / "initial-state.json")
    require(state["head"] == CANDIDATE, "starting HEAD drift")
    require(state["initial_git_status_porcelain"] == "",
            "incorrect initial dirty-state claim")
    for entry in state["reviewed_simplifier_and_maintained_test_files"]:
        data = git_bytes(CANDIDATE, entry["path"])
        require(hashlib.sha256(data).hexdigest() == entry["sha256"],
                "reviewed source fingerprint disagreement")
    print("TASK_01 evidence integrity: 37 immutable artifacts verified")
    print("Baseline inputs and ABI derivation match pinned Git sources")
    print("Historical JSON/log counts, stages and storage agree")
    print("No HOL tests, elaboration or benchmarks executed; no pass inferred")


if __name__ == "__main__":
    main()
