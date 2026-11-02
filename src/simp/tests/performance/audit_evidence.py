#!/usr/bin/env python3
"""Offline source-binding audit of archived performance receipts.

Matrix acceptance requires a sealed manifest inventory, not just receipt-local
hashes. Legacy non-matrix diagnostic receipts retain their original audit.
This checks consistency, not authenticity of an untrusted receipt producer.
"""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path
import re
import shlex

from performance_schema import (graphs, layout_units, require,
                                suite_options, validate)


def archived_path(raw, *, relative=False):
    """Check canonical lexical paths without touching deleted archive roots."""
    require(isinstance(raw, str) and raw and "\x00" not in raw,
            "invalid archived path")
    path = Path(raw)
    require(path.is_absolute() != relative and str(path) == raw and
            not raw.startswith("//") and ".." not in path.parts and
            raw not in (".", "/"),
            "non-normalized archived path")
    return path


def fingerprint(info, message="invalid archived fingerprint"):
    require(isinstance(info, dict) and set(info) == {"sha256", "bytes"} and
            isinstance(info["sha256"], str) and
            re.fullmatch(r"[0-9a-f]{64}", info["sha256"]) is not None and
            type(info["bytes"]) is int and info["bytes"] >= 0, message)
    return info


def source_fingerprint(info):
    return fingerprint({k: info[k] for k in ("sha256", "bytes")})


def shared_entry(repo, logical, info, seals):
    """Validate a shared source and every associated compiled dependency."""
    physical = archived_path(info["physical"])
    for path in (archived_path(logical), physical):
        require(path.is_relative_to(repo) and
                not path.is_relative_to(repo / "src/simp"),
                "wrong archived shared path")
    entries = {str(physical): source_fingerprint(info)}
    require(isinstance(info["related_products"], dict),
            "missing shared related products")
    for raw, value in info["related_products"].items():
        product = archived_path(raw)
        require(product.is_relative_to(repo) and
                not product.is_relative_to(repo / "src/simp") and
                product.stem == physical.stem and
                product.suffix in (".uo", ".ui", ".dat"),
                "wrong shared related product path")
        entries[raw] = fingerprint(value)
    for raw, value in entries.items():
        require(seals.setdefault(raw, value) == value,
                "conflicting shared input/product fingerprint")


def command_record(record, command, repo):
    require(record["command"] == command and record["cwd"] == str(repo) and
            type(record["exit"]) is int and record["exit"] == 0 and
            record["timed_out"] is False and
            isinstance(record["stdout"], str),
            "invalid compiler/runtime command provenance")
    data = record["stdout"].encode()
    require(fingerprint({"sha256": record["stdout_sha256"],
                         "bytes": record["stdout_bytes"]}) ==
            {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)},
            "changed compiler/runtime command output")


def audit_manifest(manifest):
    """Strict offline admission for matrix manifests (no live file reads).

    Old matrix archives without shared_inputs are deliberately inadmissible:
    Deriving it from the same receipts would be circular validation.
    """
    repo = archived_path(manifest["repo"])
    options = ["--gcthreads=1", "run",
               "--holstate=" + str(repo / "bin/hol.state0")]
    require(manifest["runtime_options"] == options,
            "wrong archived runtime options")
    tools = manifest["tools"]
    required = {"bin/hol", "bin/hol.state0", "bin/hol.state.min",
                "bin/Holmake", "holproject.toml"}
    require(isinstance(tools, dict) and required <= tools.keys(),
            "missing runtime/compiler tool hashes")
    for raw, value in tools.items():
        archived_path(raw, relative=not raw.startswith("/"))
        require(raw.startswith("/") or raw in required,
                "unknown relative runtime/compiler tool")
        require(fingerprint(value)["bytes"] > 0, "empty runtime/compiler tool")
    version = manifest["poly_version"]
    command = version["command"]
    require(isinstance(command, list) and len(command) == 2 and
            command[1] == "--version", "wrong compiler version command")
    poly = str(archived_path(command[0]))
    require(poly in tools, "missing compiler fingerprint")
    command_record(version, [poly, "--version"], repo)
    require(re.fullmatch(r"Poly/ML \d+\.\d+(?:\.\d+)?[^\n]*\n?",
                         version["stdout"]) is not None,
            "invalid Poly/ML compiler version")
    linked = manifest["dynamic_libraries"]
    command_record(linked, ["ldd", str(repo / "bin/hol")], repo)
    libraries = re.findall(r"(/[^\s()]+)", linked["stdout"])
    require(libraries and "not found" not in linked["stdout"],
            "missing runtime library provenance")
    for raw in libraries:
        require(str(archived_path(raw)) in tools,
                "missing runtime library fingerprint")
    for raw, value in manifest["inputs"].items():
        archived_path(raw, relative=True)
        fingerprint(value,
                    "invalid input fingerprint / matrix fixture binding")
    require(set(manifest["selections"]) == {"baseline", "candidate"},
            "wrong manifest selections")
    roots = [repo]
    for selected in manifest["selections"].values():
        private = archived_path(selected["private"])
        require(all(not private.is_relative_to(root) and
                    not root.is_relative_to(private) for root in roots),
                "overlapping archived source roots")
        roots.append(private)
        require(type(selected["build_exit"]) is int and
                selected["build_exit"] == 0, "failed selected compiler build")
        seals = {}
        for source in selected["sources"]:
            archived_path(source["git_path"], relative=True)
            path = archived_path(source["private_path"])
            require(path.is_relative_to(private), "wrong selected source path")
            value = source_fingerprint(source)
            require(seals.setdefault(source["private_path"], value) == value,
                    "conflicting selected source fingerprint")
        for key in ("fixture_products", "products"):
            for raw, value in selected[key].items():
                archived_path(raw, relative=True)
                fingerprint(value)
                require(seals.setdefault(str(private / raw), value) == value,
                        "conflicting selected product fingerprint")
        launcher = selected["launcher"]
        require(isinstance(launcher, str), "missing archived launcher")
        lines = launcher.splitlines()
        require(len(lines) == 4 and lines[:2] == ["#!/bin/sh", "set -e"] and
                lines[-1] == "exit 0" and shlex.split(lines[2]) ==
                [str(repo / "bin/hol"), *options, "runner"],
                "wrong archived launcher runtime/options")
        data = launcher.encode()
        require(selected["products"]["paired.exe"] ==
                {"sha256": hashlib.sha256(data).hexdigest(),
                 "bytes": len(data)}, "wrong archived launcher fingerprint")
    shared = manifest["shared_inputs"]
    require(isinstance(shared, dict) and shared,
            "missing shared input inventory")
    seals = {}
    for logical, info in shared.items():
        shared_entry(repo, logical, info, seals)
    for raw, value in manifest["inputs"].items():
        absolute = str(repo / raw)
        require(absolute not in seals or seals[absolute] == value,
                "conflicting manifest input fingerprint")


def audit(manifest, receipt):
    strict = manifest["performance"].get("suite") == "matrix"
    if strict:
        audit_manifest(manifest)
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
    require(env.get("PERF_ITERATIONS") == (
                str(options["batch_iterations"])
                if "batch_iterations" in options else None),
            "wrong fixed iteration environment")
    require(env.get("PERF_SCHEDULE") == options.get("batch_schedule"),
            "wrong batch schedule environment")
    require(env.get("PERF_LAYOUT") == (
                str(layout_units(options["layout_seed"], receipt["pair"],
                                 selection))
                if "layout_seed" in options else None),
            "wrong layout randomization environment")
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
        physical = (archived_path(info["physical"]) if strict else
                    Path(info["physical"]))
        if strict:
            archived_path(logical)
            source_fingerprint(info)
            require(isinstance(info["related_products"], dict),
                    "missing archived related products")
        if physical.is_relative_to(private):
            require(str(physical) in expected and
                    {k: info[k] for k in ("sha256", "bytes")} ==
                    expected[str(physical)], "private source/hash mismatch")
            require(Path(logical).is_relative_to(private),
                    "wrong logical private source")
            if strict:
                path = Path(logical)
                hfs = path.parent / ".hol/objs" / path.name
                require(physical in (path, hfs),
                        "wrong logical/physical private source binding")
                related = {}
                for suffix in (".uo", ".ui", ".dat"):
                    direct = path.with_suffix(suffix)
                    generated = hfs.with_suffix(suffix)
                    for product in (direct, generated):
                        if str(product) in expected:
                            related[str(product)] = expected[str(product)]
                            break
                for raw, value in info["related_products"].items():
                    archived_path(raw)
                    fingerprint(value)
                require(info["related_products"] == related,
                        "private related product mismatch")
            seen.add(physical.name)
        else:
            repo = Path(manifest["repo"])
            require(physical.is_relative_to(repo) and
                    not physical.is_relative_to(repo / "src/simp") and
                    physical.stem not in source_names,
                    "wrong archived simplifier path")
            if strict:
                require(logical in manifest["shared_inputs"],
                        "unbound shared source")
                sealed = manifest["shared_inputs"][logical]
                fields = ("physical", "sha256", "bytes", "related_products")
                require({k: info[k] for k in fields} ==
                        {k: sealed[k] for k in fields},
                        "shared source/product binding mismatch")
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
