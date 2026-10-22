#!/usr/bin/env python3
"""Execute native/cleanup cases; no baseline claim for branch-only semantics."""
import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import tempfile

import prior_contracts as prior
import coverage_ledger as coverage
import task10_relocation as relocation
from run_paired import (HERE, execute, fingerprint, git, require)


def source_inputs(repo):
    paths = []
    for folder in (repo / "src/simp/src", HERE.parent):
        for p in folder.rglob("*"):
            if (p.is_file() and p.suffix in (".sml", ".sig", ".ML") and
                    ".hol" not in p.parts and "evidence" not in p.parts):
                paths.append(p)
    return sorted(set(paths + [Path(__file__), HERE / "prior_contracts.py",
                               HERE / "coverage_ledger.py",
                               HERE / "task10_relocation.py",
                               relocation.SUPPLEMENT,
                               HERE / "coverage-ledger.json.gz"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = HERE.parents[3]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "SIMP_", "SPLIT_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    poly = shutil.which("poly", path=env["PATH"])
    require(poly is not None, "poly not found")
    manifest = {"scope": "native current products, not independent clean build",
                "head": git(repo, "rev-parse", "HEAD").decode().strip(),
                "inputs": {str(p.relative_to(repo)): fingerprint(p)
                           for p in source_inputs(repo)},
                "tools": {n: fingerprint(repo / n) for n in
                          ("bin/hol", "bin/hol.state0", "bin/Holmake")},
                "poly_version": execute([poly, "--version"], repo, env, 30),
                "poly": fingerprint(Path(poly).resolve()),
                "runs": [], "success": False}
    ledger = coverage.receipt(HERE / "coverage-ledger.json.gz")
    supplement = relocation.load()

    def run(label, command, cwd, extra=None, suite=True):
        receipt = execute(command, cwd, dict(env, **(extra or {})), 900)
        receipt["environment"] = {k: v for k, v in dict(env, **(extra or {})).items()
                                  if k in ("HOLDIR", "TERM", "LC_ALL", "TZ") or
                                  k.startswith(("SIMP_", "SPLIT_"))}
        if suite:
            receipt["stream"] = [
                "OBS load.path=$REPO/src/simp/src/simpLib" if
                s == "OBS load.path=" + str(repo / "src/simp/src/simpLib")
                else s for s in prior.semantic_stream(receipt["stdout"])]
        manifest["runs"].append({"label": label, "exit": receipt["exit"],
                                 "receipt": label + ".json.gz"})
        (output / (label + ".json.gz")).write_bytes(gzip.compress(
            (json.dumps(receipt, indent=2) + "\n").encode(), mtime=0))
        require(receipt["exit"] == 0 and not receipt["timed_out"],
                "native process failed: " + label)
        require("FAILED!" not in receipt["stdout"], "native assertion failed")
        if suite:
            relocation.validate_stream(ledger, label, receipt["stream"],
                                       supplement)
        return receipt

    try:
        coverage.verify(ledger, supplement)
        manifest["relocation"] = fingerprint(relocation.SUPPLEMENT)
        manifest["coverage"] = {
            "frozen_native_checks": ledger["suites"]["native"]["checks"],
            "current_native_checks": supplement["native"]["checks"],
            "additional_registry_checks":
                len(supplement["native"]["additions"])}
        holmake = [str(repo / "bin/Holmake"), "--no-project", "--no-cache",
                   "--holstate=" + str(repo / "bin/hol.state0"), "-j1"]
        run("build-focused", holmake + ["-C", str(repo / "src/simp/src"),
            "HOLSELFTESTLEVEL=1", "all"], repo, suite=False)
        manifest["products"] = {
            str(p.relative_to(repo)): fingerprint(p)
            for directory in (repo / "src/simp/src", *[
                HERE.parent / n for n in ("contracts", "fresh-load", "markers",
                "replay-order", "split-registration")])
            for p in (directory / ".hol/objs").glob("*")
            if p.is_file() and not (
                directory == repo / "src/simp/src" and
                p.name in ("scratchTheory.sml", "scratchTheory.sig",
                           "scratchTheory.dat"))}
        # The unchanged native selftest exports scratchTheory on every
        # execution. Its generated theory hash can differ between the
        # integrated run and direct launcher; it is an output, not an
        # imported/compiled input. All .uo/.ui and other theory products
        # remain sealed, as do the sources and the exact native stream.
        # Existing launchers are executed, not counted from cached log targets.
        cases = {"native": "src/simp/src/selftest.exe",
                 "traversal": "src/simp/tests/contracts/traversal-contracts.exe",
                 "exclusion": "src/simp/tests/contracts/exclusion-contracts.exe",
                 **{n: "src/simp/tests/" + n + "/selftest.exe" for n in
                    ("markers", "replay-order", "split-registration")}}
        for label, path in cases.items():
            target = repo / path
            receipt = run(label, [str(target)], target.parent)
            manifest.setdefault("launchers", {})[path] = {
                "text": target.read_text(), **fingerprint(target)}
            if label in ("native", "traversal", "exclusion"):
                fixture = {"native": "PriorNative", "traversal": "PriorTraversal",
                           "exclusion": "PriorExclusion"}[label]
                require(ledger["suites"][label]["stream"] ==
                        prior.historical(HERE, fixture),
                        "changed ordered historical contracts: " + label)
        for scenario in ("control", "attribute-first", "set-first",
                         "attribute-after", "set-after", "syntax-first"):
            src = repo / "src/simp/src"
            fresh = HERE.parent / "fresh-load"
            receipt = run("fresh-" + scenario,
                          [str(src / "fresh-load-selftest.exe")], src,
                          {"SIMP_COMPAT_SCENARIO": scenario,
                           "SIMP_COMPAT_PATH": str(src / "simpLib"),
                           "SIMP_COMPAT_CONTROL": str(fresh / "control.ML"),
                           "SIMP_COMPAT_IDENTITY_PREFIX": str(fresh / "identity-")})
            require(receipt["stdout"].count("OBS result=pass\n") == 1,
                    "fresh scenario did not complete")
            if scenario in ("attribute-first", "set-first"):
                for label in (
                    "ordinary load preserves exact foreign handler records",
                    "ordinary load preserves listener functions and order",
                    "ordinary load adds only unchanged legacy marker listeners",
                    "ordinary load installs no private persistence listener"):
                    require(label + " ... OK" in receipt["stream"],
                            "listener/handler identity assertion did not run")
        # Freshly export theories, not caller-owned cached .dat/.uo products.
        with tempfile.TemporaryDirectory(prefix="simp-task06-persistence-") as tmp:
            dst = Path(tmp)
            for p in (HERE.parent / "split-persistence").iterdir():
                if p.suffix in (".sml", ".ML") or p.name == "Holmakefile":
                    shutil.copyfile(p, dst / p.name)
            makefile = dst / "Holmakefile"
            makefile.write_text(makefile.read_text().replace(
                "../../src", str(repo / "src/simp/src")))
            manifest["persistence_makefile"] = makefile.read_text()
            receipt = run("persistence", holmake + ["--no_prereqs", "-C", tmp,
                                                    "check"], repo)
            require(receipt["stdout"].count("OBS result=pass\n") == 8,
                    "missing persistence scenario")
            require("OBS heap=saved\n" in receipt["stdout"] and
                    "OBS heap=reloaded\n" in receipt["stdout"],
                    "heap lifecycle did not execute")
        for path, info in manifest["inputs"].items():
            require(fingerprint(repo / path) == info, "native input changed")
        for path, info in manifest["tools"].items():
            require(fingerprint(repo / path) == info, "native runtime changed")
        for path, info in manifest["products"].items():
            require(fingerprint(repo / path) == info, "native product changed")
        manifest["success"] = True
    except Exception as e:
        manifest["failure"] = str(e)
    finally:
        (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(output / "manifest.json")
    if not manifest["success"]:
        raise SystemExit(manifest["failure"])


if __name__ == "__main__":
    main()
