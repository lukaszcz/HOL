#!/usr/bin/env python3
"""Fresh split exports, load matrix, heap proofs and dispatcher negative."""
import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import tempfile

from run_paired import HERE, execute, fingerprint, git, physical, require


def negative_isolation_problems(log_text, src, private_dir):
    """Problems with the negative run's `OBS repair.loaded.path=` lines: the
    private SplitData.sig/.sml must both be loaded from `private_dir`, and no
    loaded path may lie under the production `src` (src/simp/src). Paths are
    compared by non-strict realpath, so spelling or symlinks cannot hide a
    production module."""
    prefix = "OBS repair.loaded.path="
    real = lambda x: Path(os.path.realpath(x))
    loaded = [real(line[len(prefix):]) for line in log_text.splitlines()
              if line.startswith(prefix)]
    problems = []
    src_real, private_real = real(src), real(private_dir)
    missing = [n for n in ("SplitData.sig", "SplitData.sml")
               if private_real / n not in loaded]
    if missing:
        problems.append("negative did not load private " +
                        ", ".join(missing) + " from " + str(private_dir))
    foreign = sorted(str(x) for x in loaded if x.is_relative_to(src_real))
    if foreign:
        problems.append("negative loaded production src/simp/src "
                        "module(s): " + ", ".join(foreign[:5]))
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = HERE.parents[3]
    src = repo / "src/simp/src"
    tests = HERE.parent
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "SIMP_", "SPLIT_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    inputs = [Path(__file__)]
    inputs += [p for p in src.iterdir() if p.suffix in (".sml", ".sig")]
    inputs += [src / "Holmakefile"]
    for folder in ("split-lifecycle", "split-persistence"):
        inputs += [p for p in (tests / folder).iterdir()
                   if p.suffix in (".sml", ".ML") or p.name == "Holmakefile"]
    manifest = {
        "scope": "fresh fixture exports/processes on current native libraries",
        "head": git(repo, "rev-parse", "HEAD").decode().strip(),
        "inputs": {str(p.relative_to(repo)): fingerprint(p) for p in inputs},
        "tools": {p: fingerprint(repo / p) for p in
                  ("bin/Holmake", "bin/hol", "bin/hol.state0")},
        "poly_version": execute(["poly", "-v"], repo, env, 30),
        "runs": [], "success": False}
    make = [str(repo / "bin/Holmake"), "--no-project", "--no-cache",
            "--holstate=" + str(repo / "bin/hol.state0"), "-j1"]

    def run(label, command, cwd, expected=0, inspect=None):
        receipt = execute(command, cwd, env, 900)
        path = label + ".json.gz"
        (output / path).write_bytes(gzip.compress(
            (json.dumps(receipt, indent=2) + "\n").encode(), mtime=0))
        manifest["runs"].append({"label": label, "exit": receipt["exit"],
                                 "receipt": path})
        if inspect is not None:
            inspect(receipt["stdout"])
        require(not receipt["timed_out"] and receipt["exit"] == expected,
                label + ": unexpected process outcome")
        require("error:" not in receipt["stdout"], label + ": static error")
        return receipt["stdout"]

    try:
        with tempfile.TemporaryDirectory(prefix="simp-task23-") as temp:
            root = Path(temp)
            for folder in ("split-lifecycle", "split-persistence"):
                dst = root / folder
                dst.mkdir()
                for p in (tests / folder).iterdir():
                    if p.suffix in (".sml", ".ML") or p.name == "Holmakefile":
                        shutil.copyfile(p, dst / p.name)
                mf = dst / "Holmakefile"
                mf.write_text(mf.read_text().replace("../../src", str(src)))
                manifest.setdefault("makefiles", {})[folder] = mf.read_text()
            lifecycle = root / "split-lifecycle"
            text = run("fresh", make + ["--no_prereqs", "-C", str(lifecycle),
                                         "check"], repo)
            require(text.count("OBS result=pass\n") == 22,
                    "missing fresh matrix/import/reload case")
            require(text.count("OBS repair=pass\n") == 1,
                    "missing dispatcher repair")
            require(text.count("OBS heap=saved\n") == 1 and
                    text.count("OBS heap=reloaded\n") == 1,
                    "missing separate heap reload")
            require(text.count("persistent-only tactic validates full "
                               "conclusion and hypotheses") == 2,
                    "proofs did not execute on both sides of reload")
            for order in ("simp", "cong"):
                for owner in ("none", "attribute", "set", "syntax"):
                    for timing in (("before",) if owner == "none" else
                                   ("before", "middle", "after")):
                        require(text.count("OBS case=" + "/".join(
                            (order, owner, timing)) + "\n") == 1,
                            "missing or duplicate load case")
            require("FAILED!" not in text, "fresh assertion failed")
            # Audit the actual loader map and traced source uses, not just
            # requested Meta.load paths or checkout-source fingerprints.
            prefixes = ("OBS heapfile=", "OBS used.path=",
                        "OBS loaded.path=", "OBS repair.loaded.path=")
            paths = {line[len(prefix):]
                     for line in text.splitlines() for prefix in prefixes
                     if line.startswith(prefix)}
            require(paths, "missing runtime source inventory")
            production = {p.name: p.resolve() for p in src.iterdir()
                          if p.suffix in (".sig", ".sml") and
                          p.name != "selftest.sml"}
            production.update({p.name: p.resolve()
                               for p in (src / ".hol/objs").glob("*Theory.*")
                               if p.suffix in (".sig", ".sml") and
                               not p.name.startswith("scratchTheory")})
            actual = {}
            products = {}
            for raw in sorted(paths):
                path = physical(raw)
                require(path.is_relative_to(repo) or
                        path.is_relative_to(root),
                        "foreign checkout dependency: " + raw)
                if path.name in production:
                    require(path == production[path.name],
                            "wrong simplifier source: " + raw)
                    for suffix in (".uo", ".ui"):
                        product = src / ".hol/objs" / (path.stem + suffix)
                        require(product.is_file(), "missing loader product")
                        products[str(product)] = {
                            **fingerprint(product),
                            "text": product.read_text()}
                actual[raw] = {"resolved": str(path), **fingerprint(path)}
            manifest["resolved_sources"] = actual
            manifest["simplifier_loader_products"] = products
            require(not (lifecycle / "split-proof.state").exists(),
                    "saved proof heap was not cleaned")
            manifest["observations"] = {
                "fresh_process_cases": 22, "matrix_cases": 20,
                "post_import_and_reload_proofs": 2,
                "checks": text.count(" ... ")}
            # Preserve the exact generated dependency order, not cached exports.
            exports = root / "split-persistence/.hol/objs"
            generated = {}
            for name in ("splitParent", "splitChild", "splitDescendant"):
                ml = exports / (name + "Theory.sml")
                data = ml.read_text()
                generated[name] = {
                    **fingerprint(ml),
                    "dependency_lines": [s for s in data.splitlines()
                                         if "local open" in s or
                                         "load_thydata" in s]}
                if name == "splitParent":
                    require(data.index("splitPersistLib") <
                            data.index("TheoryReader.load_thydata"),
                            "initializer does not precede parent decoding")
                    require("simpMarkerTheory" in data,
                            "missing marker theory export dependency")
            manifest["fresh_export_dependencies"] = generated

            # A private SplitData copy removes only the owned repair branch.
            # No production module is overwritten and no previous process's
            # registration or cache can satisfy this regression.
            neg = root / "negative"
            neg.mkdir()
            for suffix in (".sig", ".sml"):
                shutil.copyfile(src / ("SplitData" + suffix),
                                neg / ("SplitData" + suffix))
            module = neg / "SplitData.sml"
            old = "SOME _ => ignore (ensure_listener ())"
            new = "SOME _ => check_listener ()"
            data = module.read_text()
            require(data.count(old) == 1, "nonunique repair mutation")
            module.write_text(data.replace(old, new))
            shutil.copyfile(tests / "split-lifecycle/repair.sml",
                            neg / "repair.sml")
            (neg / "Holmakefile").write_text(
                "HOLHEAP = $(HOLDIR)/bin/hol.state0\nINCLUDES = " + str(src) +
                "\nrepair.exe: repair.uo\n\t$(HOLMOSMLC) -o $@ $<\n")
            manifest["negative"] = {
                "mutation": {"old": old, "new": new},
                "inputs": {p.name: fingerprint(p) for p in neg.iterdir()}}
            run("negative-build", make + ["--no_prereqs", "-C", str(neg),
                                           "repair.exe"], repo)
            def isolated(out):
                problems = negative_isolation_problems(out, src, neg)
                require(not problems, "; ".join(problems))

            log = run("negative-run", [str(neg / "repair.exe")], neg, 1,
                      inspect=isolated)
            require("explicit initialization repairs missing dispatcher "
                    "identity" in log and "FAILED!" in log,
                    "negative did not fail the intended assertion")
            for name in ("SplitData", "repair"):
                ui = neg / ".hol/objs" / (name + ".ui")
                manifest["negative"].setdefault("loaded_ui", {})[name] = {
                    "path": str(ui), "text": ui.read_text(), **fingerprint(ui)}
        for path, info in manifest["inputs"].items():
            require(fingerprint(repo / path) == info, "input changed: " + path)
        manifest["success"] = True
    except Exception as e:
        manifest["failure"] = str(e)
    finally:
        (output / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n")
    print(output / "manifest.json")
    if not manifest["success"]:
        raise SystemExit(manifest["failure"])


if __name__ == "__main__":
    main()
