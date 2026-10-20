#!/usr/bin/env python3
"""Audit retained paired evidence without normalizing contract observations."""

import argparse
import difflib
import gzip
import hashlib
import json
from pathlib import Path
import re

TIMING = re.compile(r'Theory "legacyfailure" took [0-9.]+s to build')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_log(path):
    if path.exists():
        return path.read_bytes()
    return gzip.decompress(path.with_suffix(path.suffix + ".gz").read_bytes())


def compare(directory, fresh):
    manifest = json.loads((directory / "manifest.json").read_text())
    field = "scenarios" if fresh else "suites"
    ref = manifest["lanes"]["reference"][field]
    branch = manifest["lanes"]["branch"][field]
    if not manifest["passed"] or ref.keys() != branch.keys():
        raise ValueError("incomplete/failed paired execution")
    rows, differences = [], []
    for name, r in sorted(ref.items()):
        b = branch[name]
        for record in (r, b):
            if record["run_exit"] != 0 or record.get("build_exit", 0) != 0:
                raise ValueError(f"failed build/run: {name}")
            if fresh and not record["precondition_clean"]:
                raise ValueError(f"unclean launcher: {name}")
        ro, bo = r["observations"], b["observations"]
        if len(ro) != len(bo):
            raise ValueError(f"observation count differs: {name}")
        contracts = []
        for i, (a, c) in enumerate(zip(ro, bo)):
            path_field = fresh and a.startswith("OBS load.path=")
            if path_field:
                equal = (a == "OBS load.path=" + r["expected_load_path"] and
                         c == "OBS load.path=" + b["expected_load_path"])
            else:
                equal = a == c
            if not equal:
                raise ValueError(f"contract differs: {name}, observation {i}")
            contracts.append({
                "observation_index": i, "label": a[4:].split("=", 1)[0],
                "expected": "lane-local recipe" if path_field else "equal",
                "observed": "verified" if path_field else "equal",
            })
        raw = [read_log(directory / f"{lane}-{name}.run.log")
               for lane in ("reference", "branch")]
        # Splitting only on LF preserves CR and terminal-newline differences.
        lines = [data.decode().split("\n") for data in raw]
        for observations, log in zip((ro, bo), lines):
            if observations != [s for s in log if s.startswith("OBS ")]:
                raise ValueError(f"manifest/log observations differ: {name}")
        classified = []
        if len(lines[0]) != len(lines[1]):
            raise ValueError(f"unclassified raw line-count difference: {name}")
        for i, (a, c) in enumerate(zip(*lines)):
            if a == c:
                continue
            if fresh and a == "OBS load.path=" + r["expected_load_path"] and (
                    c == "OBS load.path=" + b["expected_load_path"]):
                reason = "different validated private lane-local recipe paths"
            elif TIMING.fullmatch(a) and TIMING.fullmatch(c):
                reason = "wall-clock theory export duration (not a contract)"
            else:
                raise ValueError(f"unclassified raw difference: {name}: {a!r}")
            classified.append({"line": i + 1, "reference": a, "branch": c,
                               "reason": reason})
        differences.extend(difflib.unified_diff(
            lines[0], lines[1], fromfile=f"reference-{name}.run.log",
            tofile=f"branch-{name}.run.log", lineterm=""))
        if not contracts and (name != "develop-selftest" or raw[0] != raw[1]):
            raise ValueError(f"uninstrumented input lacks raw equality: {name}")
        rows.append({
            "input": name, "expected": "equal legacy contract observables",
            "observed": "equal", "reference_ok": raw[0].count(b"OK"),
            "branch_ok": raw[1].count(b"OK"), "contracts": contracts,
            "raw_byte_equal": raw[0] == raw[1],
            "raw_sha256": [sha(data) for data in raw],
            "raw_differences": classified,
            "uninstrumented_assertions_only": not bool(contracts),
        })
    # Build output is evidence too, including runtime compiler diagnostics.
    builds = []
    for command in manifest["commands"]:
        name = command["combined_log"]
        if not name.startswith("reference-") or not name.endswith(".build.log"):
            continue
        other = name.replace("reference-", "branch-", 1)
        a, b = read_log(directory / name), read_log(directory / other)
        if a != b:
            raise ValueError(f"unclassified build output difference: {name}")
        builds.append({"reference_log": name, "branch_log": other,
                       "raw_byte_equal": True, "sha256": sha(a)})
    return {"manifest_sha256": sha((directory / "manifest.json").read_bytes()),
            "inputs": rows, "build_outputs": builds}, differences


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paired", required=True, type=Path)
    parser.add_argument("--fresh", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path,
                        help="new output directory")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    required = {p.stem for p in (here / "probes/legacy").glob("*.sml")}
    required.add("develop-selftest")
    fresh_required = {"control", "attribute-first", "attribute-after",
                      "set-first", "set-after"}
    matrix, diffs = {}, []
    for name, path, fresh in (("paired", args.paired, False),
                              ("fresh", args.fresh, True)):
        matrix[name], raw_diff = compare(path, fresh)
        inputs = {row["input"] for row in matrix[name]["inputs"]}
        if inputs != (fresh_required if fresh else required):
            raise ValueError(f"required input inventory differs: {name}")
        diffs.extend([f"# {name}", *raw_diff])
    args.output.mkdir(parents=True, exist_ok=False)
    data = (json.dumps(matrix, indent=2, sort_keys=True) + "\n").encode()
    (args.output / "matrix.json.gz").write_bytes(gzip.compress(data, mtime=0))
    (args.output / "raw-differences.diff").write_text("\n".join(diffs) + "\n")
    print("PASS: all ordered contracts and raw-output differences reviewed")


if __name__ == "__main__":
    main()
