#!/usr/bin/env python3
"""Offline source-binding audit of archived TASK_03 diagnostic receipts.

The online runner checked actual files before deleting private trees. This
separate audit binds archived paths/hashes back to their selected manifest;
summary metric validation alone is not a provenance validator.
"""
import argparse
import copy
import gzip
import json
from pathlib import Path

from performance_schema import graphs, require, suite_options, validate


def audit(manifest, receipt):
    require(receipt["accepted"] and receipt["exit"] == 0 and
            not receipt["timed_out"], "failed performance receipt")
    selection = receipt["selection"]
    selected = manifest["selections"][selection]
    private = Path(selected["private"])
    require(receipt["cwd"] == str(private) and receipt["command"] ==
            [str(private / "paired.exe")], "wrong selected launcher")
    env = receipt["environment"]
    require(env["PAIR_SELECTION"] == selection and
            env["PAIR_PRIVATE"] == str(private) and
            env["PAIR_FIXTURE"] == "performance" and
            env["PAIR_TARGET"] == "Performance" and
            env["PAIR_CONTROL"] == "none", "wrong process selection")
    options = manifest["performance"]
    require(int(env["PERF_SAMPLES"]) == options["samples"] and
            float(env["PERF_SECONDS"]) == options["batch_seconds"],
            "wrong timing options")
    result = receipt["result"]
    events = result["events"]
    require(events[:2] == [["begin", selection, "performance", "none"],
                           ["cwd", str(private)]], "wrong archived header")
    observations, data = validate(events, options["samples"],
                                  options["batch_seconds"],
                                  **suite_options(options))
    count = sum(e[0] == "check" for e in observations)
    require(result["observations"] == observations and
            result["expected_test_count"] == count and
            result["outcome"] == "pass" and
            events[-1] == ["end", "pass", str(count)] and
            receipt["measurements"] == data, "inconsistent archived result")
    expected = {s["private_path"]: {k: s[k] for k in ("sha256", "bytes")}
                for s in selected["sources"]}
    for key in ("fixture_products", "products"):
        expected.update({str(private / p): info for p, info in
                         selected[key].items()})
    source_names = {Path(s["git_path"]).stem for s in selected["sources"]}
    seen = set()
    for logical, info in result["paths"].items():
        physical = Path(info["physical"])
        if physical.is_relative_to(private):
            require(str(physical) in expected and
                    {k: info[k] for k in ("sha256", "bytes")} ==
                    expected[str(physical)], "private source/hash mismatch")
            require(Path(logical).is_relative_to(private),
                    "wrong logical private source")
            seen.add(physical.name)
        else:
            repo = Path(manifest["repo"])
            require(physical.is_relative_to(repo) and
                    not physical.is_relative_to(repo / "src/simp") and
                    physical.stem not in source_names,
                    "wrong archived simplifier path")
    suite = options.get("suite", "simplifier")
    required = {"Performance.sml"}
    if suite in ("traversal", "conditional"):
        name = "Traversal" if suite == "traversal" else "Conditional"
        fixture = "src/simp/tests/performance/" + name + "Performance.sml"
        require(selected["fixture_products"]["Performance.sml"] ==
                manifest["inputs"][fixture], "wrong " + suite + " fixture binding")
        required.add("Traverse.sml" if suite == "traversal" else "Cond_rewr.sml")
    else:
        required.update(("Traverse.sml", "simpLib.sml"))
    if suite == "matrix":
        from matrix_schema import get_case
        fixture = get_case(options["case"], options["size"])
        require(env["PERF_CASE"] == options["case"] and
                int(env["PERF_SIZE"]) == options["size"],
                "wrong matrix process parameters")
        require(selected["fixture_products"]["Performance.sml"] ==
                manifest["inputs"]["src/simp/tests/performance/" + fixture],
                "wrong matrix fixture binding")
        require(selected["fixture_products"]["RuntimeMetrics.sml"] ==
                manifest["inputs"][
                    "src/simp/tests/performance/RuntimeMetrics.sml"],
                "wrong runtime metrics binding")
        required.add("RuntimeMetrics.sml")
        if fixture == "MatrixPerformance.sml":
            require(selected["fixture_products"]["MatrixSupport.sml"] ==
                    manifest["inputs"][
                        "src/simp/tests/performance/MatrixSupport.sml"],
                    "wrong matrix support binding")
            required.add("MatrixSupport.sml")
        require(receipt["storage_graph"] == graphs(
            receipt["diagnostics"], options["case"], options["size"]),
            "wrong archived storage graph")
        import runtime_metrics
        require(receipt["runtime"] == runtime_metrics.validate(
            receipt["diagnostics"], data), "wrong archived runtime telemetry")
        if options["case"] == "storage_graph":
            require(receipt["release"] == runtime_metrics.release(
                receipt["diagnostics"]), "wrong archived release probe")
    if suite == "conditional":
        forbidden = {n for n in source_names if
                     n in ("Traverse", "simpLib") or
                     n.endswith(("Ext", "ExtLib"))}
        inventory = {Path(p).stem for p in result["paths"]}
        inventory.update(Path(i["physical"]).stem
                         for i in result["paths"].values())
        for event in events:
            if event[0] in ("use", "used", "loaded", "heapfile"):
                inventory.add(Path(event[1]).stem)
            elif event[0] == "preloaded":
                inventory.update(event[1].split(","))
        require(not (inventory & forbidden),
                "non-direct module in conditional performance inventory")
    require(required <= seen, "missing selected implementation")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("experiment", type=Path, nargs="+")
    args = parser.parse_args()
    total = 0
    for folder in args.experiment:
        manifest = json.loads((folder / "manifest.json").read_text())
        require(manifest["success"], "failed experiment")
        runs = []
        for run in manifest["runs"]:
            receipt = json.loads(gzip.decompress(
                (folder / run["receipt"]).read_bytes()))
            if receipt["fixture"] == "performance":
                require(run["accepted"], "manifest rejected receipt")
                audit(manifest, receipt)
                runs.append(receipt)
                total += 1
        # Negative controls use only copied in-memory archived receipts.
        # Wrong selection/paths and changed source bytes must be rejected.
        receipt = runs[0]
        wrong = copy.deepcopy(receipt)
        wrong["selection"] = ("candidate" if receipt["selection"] ==
                              "baseline" else "baseline")
        changed = copy.deepcopy(receipt)
        for path, info in changed["result"]["paths"].items():
            module = ("Cond_rewr.sml" if manifest["performance"].get("suite") ==
                      "conditional" else "Traverse.sml")
            if Path(info["physical"]).name == module:
                info["sha256"] = "0" * 64
        for control in (wrong, changed):
            try:
                audit(manifest, control)
            except ValueError:
                pass
            else:
                raise ValueError("offline provenance negative control accepted")
        print(f"{folder}: {len(runs)} source-bound receipts; "
              "wrong-selection and mutated-source controls rejected")
    print(f"Verified {total} performance receipts")


if __name__ == "__main__":
    main()
