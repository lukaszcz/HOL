#!/usr/bin/env python3
"""TASK24: executed recipes, provider and internal consumer closure.

Run in the configured checkout (see evidence/task23/configured-path.sh).
No snapshots, simpset imports, oracle updates or external worktree writes.
"""
import argparse
import gzip
import json
import os
from pathlib import Path
import shutil

from run_paired import HERE, execute, fingerprint, git, require

REPO = HERE.parents[3]
BASELINE = "cccaa27d7099cbadc886983020cbe745db7793f3"
LIBRARIES = [
    ("standard", "src/simp/tests/standard-recipes",
     "STANDARD_RECIPE_CHECKS=118"),
    ("provider", "src/boss/tests/tracked-defaults",
     "TRACKED_DEFAULTS_COMPLETE checks=152"),
    ("numeral", "src/num/arith/tests/tracked-recipes",
     "NUMERAL_RECIPE_CHECKS=91"),
    ("list", "src/list/tests/tracked-recipes",
     "LIST_TRACKED_RECIPE_CHECKS=22"),
    ("set", "src/pred_set/tests/tracked-recipes",
     "PRED_SET_TRACKED_RECIPE_CHECKS=42"),
    ("integer", "src/integer/tests/tracked-recipes",
     "INTEGER_RECIPE_CHECKS=116"),
    ("real", "src/real/tests/tracked-recipes",
     "REAL_RECIPE_CHECKS=124"),
]
CATALOGS = [
    "src/simp/src/combinSimpsExt", "src/boss/trackedSimpDefaults",
    "src/num/arith/src/numSimpsExt", "src/list/src/listSimpsExt",
    "src/pred_set/src/pred_setSimpsExt", "src/integer/intReduceExt",
    "src/integer/integer_wordLibExt", "src/real/realSimpsExt",
]


def inputs():
    paths = {Path(__file__), HERE / "migration/TASK24.md"}
    for _, folder, _ in LIBRARIES:
        paths.update(p for p in (REPO / folder).rglob("*")
                     if p.is_file() and ".hol" not in p.parts and
                     p.suffix in (".sml", ".sig", ".ML", ".md"))
        paths.add(REPO / folder / "Holmakefile")
    for folder in ("src/simp/src", "src/basicProof", "src/num/arith/src",
                   "src/list/src", "src/pred_set/src", "src/boss",
                   "src/integer", "src/real"):
        paths.update(p for p in (REPO / folder).iterdir()
                     if p.is_file() and
                     (p.suffix in (".sml", ".sig") or
                      p.name == "Holmakefile"))
    return sorted(paths)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, HOLDIR=str(REPO), TERM="dumb", LC_ALL="C")
    manifest = {
        "head": git(REPO, "rev-parse", "HEAD").decode().strip(),
        "scope": "TASK24 current-source recipes/internal consumers; "
                 "not clean-build or performance acceptance",
        "inputs": {str(p.relative_to(REPO)): fingerprint(p) for p in inputs()},
        "tools": {p: fingerprint(REPO / p) for p in
                  ("bin/Holmake", "bin/hol", "bin/hol.state0", "bin/build")},
        "runs": [], "success": False,
    }

    def run(label, command, marker=None, timeout=1800):
        receipt = execute(command, REPO, env, timeout)
        path = output / (label + ".json.gz")
        path.write_bytes(gzip.compress(
            (json.dumps(receipt, indent=2) + "\n").encode(), mtime=0))
        manifest["runs"].append({"label": label, "exit": receipt["exit"],
                                 "receipt": path.name})
        require(receipt["exit"] == 0 and not receipt["timed_out"],
                "failed: " + label)
        if marker:
            require(receipt["stdout"].count(marker) == 1,
                    "incomplete/duplicated result: " + label)
        return receipt

    try:
        poly = shutil.which("poly")
        require(poly is not None, "missing Poly/ML")
        manifest["poly"] = fingerprint(Path(poly).resolve())
        run("runtime", [poly, "--version"], "Poly/ML 5.9.2")
        # All unchanged ordinary recipes and the restored core retain the
        # exact pinned bodies, not wrappers with extension dispatch.
        ordinary = ["src/basicProof/BasicProvers.sml"]
        for name in ("Traverse", "simpLib", "congLib", "Opening", "Travrules",
                     "pureSimps", "boolSimps", "combinSimps"):
            ordinary.extend("src/simp/src/" + name + ext
                            for ext in (".sig", ".sml"))
        for path in ordinary:
            require((REPO / path).read_bytes() == git(
                REPO, "show", BASELINE + ":" + path),
                "ordinary source drift: " + path)
        manifest["pinned_ordinary"] = ordinary
        for name in CATALOGS:
            text = (REPO / (name + ".sml")).read_text()
            require("ssfrags_of" not in text and "dest_ssfrag" not in text,
                    "catalog imports ordinary fragments/history: " + name)
        make = [str(REPO / "bin/Holmake"), "--no-project", "--no-cache",
                "-j1"]
        run("routine", [str(REPO / "bin/build"), "-t",
                        "--seq=tools/sequences/upto-parallel"],
            "Hol built successfully.")
        for label, folder, marker in LIBRARIES:
            run(label, make + ["-C", folder, "check"], marker)
        # Seal executed launchers and their source-loading metadata, together
        # with each new catalog's .uo/.ui dependency plan.
        products = []
        for name in CATALOGS:
            source = REPO / name
            products.extend(source.parent / ".hol/objs" /
                            (source.name + ext) for ext in (".uo", ".ui"))
        for _, folder, _ in LIBRARIES:
            directory = REPO / folder
            products.extend((directory / ".hol/objs").glob("*.uo"))
            products.extend((directory / ".hol/objs").glob("*.ui"))
            products.extend(directory.glob("*.exe"))
        manifest["products"] = {
            str(p.relative_to(REPO)): fingerprint(p) for p in products}
        run("integer-all", make + ["-C", "src/integer",
                                   "HOLSELFTESTLEVEL=1", "all"])
        run("real-all", make + ["-C", "src/real",
                                "HOLSELFTESTLEVEL=1", "all"])
        run("native", ["python3", "-B", str(HERE / "run_prior_native.py"),
                       "--output", str(output / "native")])
        run("coverage", ["python3", "-B", str(HERE / "coverage_ledger.py")])
        run("immutable", ["python3", "-B", str(HERE / "verify_evidence.py")])
        run("diff-check", ["git", "diff", "--check"])
        for path, info in manifest["inputs"].items():
            require(fingerprint(REPO / path) == info,
                    "input changed during validation: " + path)
        for path, info in manifest["tools"].items():
            require(fingerprint(REPO / path) == info,
                    "runtime changed: " + path)
        for path, info in manifest["products"].items():
            require(fingerprint(REPO / path) == info,
                    "product changed: " + path)
        manifest["success"] = True
    except Exception as exc:
        manifest["failure"] = str(exc)
    finally:
        (output / "validation.json").write_text(
            json.dumps(manifest, indent=2) + "\n")
    print(output / "validation.json")
    if not manifest["success"]:
        raise SystemExit(manifest["failure"])


if __name__ == "__main__":
    main()
