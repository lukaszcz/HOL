#!/usr/bin/env python3
"""Replay new loading archives, with immutable Git and linked-library seals.

No deleted private tree is consulted. This verifies recorded consistency, not
hostile-producer authenticity, clean builds or numerical performance parity.
"""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[7]
sys.path.insert(0, str(ROOT / "src/simp/tests/performance"))
import acceptance as a
import loading as l

spec = importlib.util.spec_from_file_location(
    "prior_replay", Path(__file__).resolve().parents[1] / "repair/replay.py")
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)


def archived(folder, info):
    path = a.safe_child(folder, info["receipt"])
    a.require(a.seal(path) == info["seal"], "changed command archive")
    receipt = a.load(path)
    text = receipt["stdout"].encode()
    a.require(l.rp.digest(text) == receipt["stdout_sha256"] and
              len(text) == receipt["stdout_bytes"], "changed stdout transport")
    return receipt


def provenance(folder, report):
    a.require(report["schema"] == "task28-loading-v2",
              "missing v2 provenance contract")
    repo = Path(report["repo"])
    dynamic = report["dynamic_libraries"]
    libs = dynamic["inputs"]
    a.require(libs, "missing runtime libraries")
    for key in ("discovery", "recheck"):
        receipt = archived(folder, dynamic[key])
        a.require(receipt["command"] == ["ldd", str(repo / "bin/hol")],
                  "wrong runtime discovery target")
        a.require(set(l.library_paths(receipt)) == set(libs),
                  "missing/changed runtime library inventory")
    for raw, info in libs.items():
        seal = {k: info[k] for k in ("bytes", "sha256")}
        a.require(Path(raw).is_absolute() and
                  Path(info["resolved"]).is_absolute() and
                  report["inputs"][raw] == seal and
                  report["inputs"][info["resolved"]] == seal,
                  "unsealed runtime library")
    version = archived(folder, report["poly_version"])
    a.require(version["command"] == [report["tools"]["poly"], "--version"]
              and version["exit"] == 0 and not version["timed_out"] and
              version["stdout"].strip() == report["tools"]["poly_version"],
              "invalid compiler version provenance")
    for selected in report["selections"].values():
        private = Path(selected["private"])
        build = archived(folder, selected["build"])
        a.require(build["exit"] == 0 and not build["timed_out"],
                  "failed selected build")
        for source in selected["sources"]:
            name = Path(source["git_path"]).name
            data = l.rp.git(repo, "show", selected["revision"] + ":" +
                            source["git_path"])
            seal = dict(bytes=len(data), sha256=l.rp.digest(data))
            a.require({k: source[k] for k in seal} == seal and
                      source["private_path"] == str(private / name) and
                      selected["products"][name] == seal,
                      "Git extraction/product mismatch")
    for run in report["runs"]:
        receipt = archived(folder, run)
        selected = report["selections"][receipt["actual_selection"]]
        private = Path(selected["private"])

        def check(raw, seal):
            path = Path(raw)
            expected = selected["products"][str(path.relative_to(private))] \
                if path.is_relative_to(private) else \
                report["shared_inputs"][raw]
            a.require(expected == seal, "unbound actual source/product")

        for info in receipt["result"]["paths"].values():
            check(info["physical"], {k: info[k] for k in ("bytes", "sha256")})
            for raw, seal in info["related_products"].items():
                check(raw, seal)
    return dict(libraries=len(libs), sources={side: len(s["sources"])
                for side, s in report["selections"].items()},
                actual_processes=len(report["runs"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("folders", nargs="+", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    results = {}
    for folder in args.folders:
        report = a.load(folder / "loading.json")
        result = provenance(folder, report)
        # Recompute every timer/proof observation and both paired experiments;
        # the existing replay also substitutes zero forced-GC in every process.
        result.update(prior.loading(folder, report["module"], smoke=False))
        result["mutation_controls"] = []
        for fault in ("missing-library", "changed-product"):
            bad = copy.deepcopy(report)
            if fault == "missing-library":
                bad["dynamic_libraries"]["inputs"].pop(next(iter(
                    bad["dynamic_libraries"]["inputs"])))
            else:
                bad["selections"]["candidate"]["products"]["simpLib.sml"][
                    "sha256"] = "0" * 64
            try:
                provenance(folder, bad)
            except (ValueError, KeyError) as error:
                result["mutation_controls"].append(dict(fault=fault,
                                                       rejected=str(error)))
            else:
                raise ValueError("archive mutation accepted: " + fault)
        results[folder.name] = result
    a.save(args.output, results)
    print(json.dumps({k: {field: v[field] for field in
                          ("actual_processes", "libraries", "sources")}
                      for k, v in results.items()}))


if __name__ == "__main__":
    main()
