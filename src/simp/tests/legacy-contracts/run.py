#!/usr/bin/env python3
"""Execute all frozen public clients and quota pins on current native modules."""
import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

HERE = Path(__file__).resolve().parent
COMPAT = HERE.parent / "compatibility"
sys.path.insert(0, str(COMPAT))
import prior_contracts as prior
import public_contracts as public
from run_paired import execute, fingerprint, git, require

REPO = HERE.parents[3]


def validate(receipt, target, labels):
    require(receipt["exit"] == 0 and not receipt["timed_out"],
            "legacy process failed: " + target)
    text = receipt["stdout"]
    require(text.endswith("\n") and text.count(
        "OBS legacy.complete=" + target + ":" + str(len(labels)) + "\n") == 1,
        "missing legacy completion: " + target)
    checks = [s for s in prior.semantic_stream(text) if not s.startswith("OBS ")]
    require(checks == [s + " ... OK" for s in labels],
            "changed legacy assertions: " + target)
    require("Static Errors" not in text and "FAILED!" not in text,
            "legacy elaboration/assertion failure")
    paths = [s.removeprefix("OBS legacy.path=") for s in text.splitlines()
             if s.startswith("OBS legacy.path=")]
    require(paths, "missing actual legacy load paths")
    # Generated signatures/clients are private; simplifier modules must be
    # this checkout's compiled sources, never an unrelated installed sigobj.
    modules = (public.CONTRACTS[target]["modules"]
               if target in public.CONTRACTS else ["Traverse", "simpLib"])
    for name in modules:
        require(any(Path(p).name == name + ".sml" for p in paths),
                "missing ordinary module: " + name)
    for name in ("Traverse", "simpLib", "congLib", "Cond_rewr",
                 "Opening", "Travrules"):
        for path in paths:
            if Path(path).name == name + ".sml":
                actual = Path(path).resolve()
                require(actual.parent == (REPO / "src/simp/src").resolve(),
                        "foreign ordinary module: " + path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    output = args.output.resolve() if args.output else None
    if output:
        output.mkdir(parents=True, exist_ok=False)
    inputs = [*HERE.glob("*.sml"), Path(__file__), HERE / "Holmakefile",
              COMPAT / "public_contracts.py", COMPAT / "prior_contracts.py",
              COMPAT / "public/clients.json", COMPAT / "public/references.json",
              COMPAT / "paired/PriorLimits.sml",
              *sorted((COMPAT / "public").glob("*.sml")),
              *sorted((COMPAT / "inputs/develop").glob("*.sig")),
              *sorted((REPO / "src/simp/src").glob("*.sml")),
              *sorted((REPO / "src/simp/src").glob("*.sig"))]
    manifest = {"head": git(REPO, "rev-parse", "HEAD").decode().strip(),
                "inputs": {str(p.relative_to(REPO)): fingerprint(p)
                           for p in inputs},
                "runtime": {n: fingerprint(REPO / n) for n in
                            ("bin/hol", "bin/hol.state0", "bin/Holmake")},
                "runs": [], "success": False}
    env = {k: v for k, v in os.environ.items() if not k.startswith(
        ("HOL", "POLY", "ML", "SIMP_", "SPLIT_"))}
    env.update(HOLDIR=str(REPO), TERM="dumb", LC_ALL="C")

    def run(label, command, cwd, extra=None, expected_exit=0):
        receipt = execute(command, cwd, dict(env, **(extra or {})), 300)
        manifest["runs"].append({"label": label, "exit": receipt["exit"]})
        if output:
            (output / (label + ".json.gz")).write_bytes(gzip.compress(
                (json.dumps(receipt, indent=2) + "\n").encode(), mtime=0))
        require(receipt["exit"] == expected_exit and not receipt["timed_out"],
                "failed native command: " + label + "\n" +
                receipt["stdout"])
        return receipt

    try:
        refs = public.references(COMPAT, REPO, git, require, fingerprint)
        with tempfile.TemporaryDirectory(prefix="simp-legacy-contracts-") as tmp:
            dst = Path(tmp)
            for name in ("selftest.sml", "Paired.sml", "OriginalScope.sml"):
                shutil.copyfile(HERE / name, dst / name)
            shutil.copyfile(COMPAT / "paired/PriorLimits.sml",
                            dst / "PriorLimits.sml")
            (dst / "Holmakefile").write_text(
                "HOLHEAP = $(HOLDIR)/bin/hol.state0\nINCLUDES = " +
                str(REPO / "src/simp/src") + "\n" +
                "selftest.exe: selftest.uo " + " ".join(
                    t + ".uo" for t in [*public.CONTRACTS, "PriorLimits",
                                        "OriginalScope"]) +
                "\n\t$(HOLMOSMLC) -o $@ $<\n")
            public.install(COMPAT, dst, refs)
            # Paired installation names its private implementation products;
            # native clients depend on current ordinary products instead.
            makefile = dst / "Holmakefile"
            text = makefile.read_text()
            for name in refs:
                directory = (REPO / "sigobj" if name == "ThmAttribute"
                             else REPO / "src/simp/src")
                text = text.replace(" " + name + ".uo\n",
                                    " " + str(directory / name) + ".uo\n")
            makefile.write_text(text)
            run("build", [str(REPO / "bin/Holmake"), "--no-project",
                          "--no-cache", "--no_prereqs", "-j1",
                          "selftest.exe"], dst)
            targets = {t: s["checks"] for t, s in public.CONTRACTS.items()}
            targets["PriorLimits"] = prior.LIMIT_CHECKS
            targets["OriginalScope"] = [
                "ordinary original dependencies load independently"]
            for target, labels in targets.items():
                receipt = run(target, [str(dst / "selftest.exe")], dst,
                              {"SIMP_LEGACY_TARGET": target,
                               "SIMP_LEGACY_CHECKS": str(len(labels))})
                validate(receipt, target, labels)
                print(target + ": " + str(len(labels)) + " checks")
            if args.negative_controls:
                (dst / "ScopeNegative.sml").write_text(
                    'val _ = load "simpExtLib"\n')
                run("negative-build", [str(REPO / "bin/Holmake"),
                    "--no-project", "--no-cache", "--no_prereqs", "-j1",
                    "ScopeNegative.uo"], dst)
                for label, target, count, error in (
                    ("extension", "ScopeNegative", 0,
                     "ordinary test loaded extension: TraverseExt"),
                    ("count", "PriorLimits", 7,
                     "incomplete legacy assertions")):
                    receipt = run("negative-" + label,
                        [str(dst / "selftest.exe")], dst,
                        {"SIMP_LEGACY_TARGET": target,
                         "SIMP_LEGACY_CHECKS": str(count)}, expected_exit=1)
                    require(error in receipt["stdout"],
                            "negative control missed intended guard")
            manifest["products"] = {
                p.name: fingerprint(p) for p in (dst / ".hol/objs").glob("*")
                if p.is_file()}
            manifest["generated"] = {
                p.name: fingerprint(p) for p in dst.iterdir() if p.is_file()}
        for path, info in manifest["inputs"].items():
            require(fingerprint(REPO / path) == info, "legacy source drift")
        manifest["success"] = True
    finally:
        if output:
            (output / "manifest.json").write_text(
                json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
