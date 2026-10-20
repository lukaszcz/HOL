#!/usr/bin/env python3
"""Holmake-built, mixed-source simplifier differential runner (no repairs)."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REFERENCE = "cccaa27d7099cbadc886983020cbe745db7793f3"


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def stage(revision, directory):
    """Flatten library sources, never copying generated theories or products."""
    paths = git("ls-tree", "-r", "--name-only", revision,
                "src/simp/src", "src/marker", "src/q").decode().splitlines()
    manifest = {}
    for name in paths:
        path = Path(name)
        wanted = (path.parent == Path("src/simp/src") or
                  path.parent == Path("src/simp/src/poly") or
                  (path.parent == Path("src/marker") and
                   path.stem in ("markerLib", "markerSyntax")) or
                  (path.parent == Path("src/q") and
                   path.stem in ("Q", "QLib")))
        if (not wanted or path.suffix not in (".sml", ".sig") or
                path.name == "selftest.sml" or path.stem.endswith("Script")):
            continue
        data = git("show", f"{revision}:{name}")
        target = directory / path.name
        if target.exists():
            raise RuntimeError(f"duplicate staged module: {target}")
        target.write_bytes(data)
        manifest[name] = digest(data)
    (directory / "Holmakefile").write_text(
        "HOLHEAP = $(HOLDIR)/bin/hol.state0\n")
    return manifest


def audit(start, library, work, *, required=None, forbidden=()):
    """Follow Poly .uo load recipes; reject any library-module fallback.

    This is a load-recipe audit, not an independent repository build.
    Hash shared recipes, interfaces and their named source files as well.
    """
    local = {p.stem for p in library.glob("*.sml")}
    seen = set()
    shared = {}
    modules = set()
    recipes = set()
    aliases = {}

    def physical(path):
        if path.is_file():
            return path
        return path.parent / ".hol/objs" / path.name

    def record(path):
        path = physical(path)
        if not path.is_file():
            raise RuntimeError(f"missing load-recipe input: {path}")
        if not path.is_relative_to(work):
            key = str(path).replace(str(ROOT), "$HOLDIR")
            shared[key] = digest(path.read_bytes())

    def visit(path):
        if path in seen:
            return
        seen.add(path)
        if path.suffix in (".uo", ".ui"):
            recipes.add(path.stem)
            if path.stem in forbidden:
                raise RuntimeError(f"forbidden launcher dependency: {path}")
        record(path)
        if path.suffix == ".uo":
            interface = physical(path.with_suffix(".ui"))
            if interface.is_file():
                visit(interface)
        for line in path.read_text().splitlines():
            expanded = line.replace("$(HOLDIR)", str(ROOT))
            dep = Path(expanded)
            if not dep.is_absolute():
                dep = path.parent / dep
            dep = dep.absolute()
            if dep.suffix in (".sml", ".sig"):
                record(dep)
                if dep.stem != "Theory" and dep.name.endswith("Theory.sml"):
                    record(dep.with_suffix(".dat"))
                continue
            if dep.name in local:
                if dep.parent not in (library, library / ".hol/objs"):
                    raise RuntimeError(f"library fallback: {dep}")
                modules.add(dep.name)
            product = physical(Path(str(dep) + path.suffix))
            # Core recipes can retain absent per-directory aliases for
            # already-loaded modules (e.g. Overlay and Table). Record the
            # alias explicitly and fingerprint the installed recipe instead.
            if not product.is_file() and dep.name not in local:
                installed = ROOT / "sigobj" / (dep.name + path.suffix)
                aliases[str(dep).replace(str(ROOT), "$HOLDIR")] = str(
                    installed).replace(str(ROOT), "$HOLDIR")
                product = installed
            if not product.is_file():
                raise RuntimeError(f"missing dependency recipe: {product}")
            visit(product)

    visit(start)
    if required is None:
        required = ("simpLib", "boolSimps", "markerLib", "markerSyntax")
    for name in required:
        if name not in modules:
            raise RuntimeError(f"load-recipe audit missed {name}")
    return {"local_modules": sorted(modules),
            "recipe_modules": sorted(recipes), "shared_sha256": shared,
            "installed_recipe_aliases": aliases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--branch", default="HEAD", help="committed revision")
    parser.add_argument("--output", type=Path, required=True,
                        help="new compact results directory (must not exist)")
    args = parser.parse_args()
    output = args.output.resolve()
    branch = git("rev-parse", args.branch + "^{commit}").decode().strip()
    pinned = HERE / "inputs/develop/selftest.sml"
    original = git("show", f"{REFERENCE}:src/simp/src/selftest.sml")
    if pinned.read_bytes() != original:
        raise RuntimeError("preserved develop selftest differs from pinned git")
    probes = sorted((HERE / "probes/legacy").glob("*.sml"))
    support = [(p, p.read_bytes()) for p in
               sorted((HERE / "probes/support").glob("*.sml"))]
    suites = [(p.stem, p, p.read_bytes()) for p in probes]
    suites.append(("develop-selftest", pinned, original))
    if len({name for name, _, _ in suites}) != len(suites):
        raise RuntimeError("duplicate suite name")
    report = {
        "kind": "mixed-source; NOT independent repository builds",
        "branch": branch, "reference": REFERENCE,
        "working_tree": git("status", "--porcelain=v1",
                            "--untracked-files=all").decode(),
        "inputs_sha256": {str(p.relative_to(HERE)): digest(data)
                          for _, p, data in suites},
        "support_sha256": {str(p.relative_to(HERE)): digest(data)
                           for p, data in support},
        "runner_sha256": digest(Path(__file__).read_bytes()),
        "tools_sha256": {name: digest((ROOT / name).read_bytes()) for name in
                         ("bin/Holmake", "bin/hol", "bin/hol.state0")},
        "commands": [], "lanes": {}, "shared_sha256": {},
    }
    success = True
    output.mkdir(parents=True, exist_ok=False)
    try:
        with tempfile.TemporaryDirectory(prefix="hol-simp-pair.") as scratch:
            work = Path(scratch)

            def run(command, cwd, log):
                result = subprocess.run(command, cwd=cwd,
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, check=False)
                (output / log).write_bytes(result.stdout)
                report["commands"].append({
                    "argv": [str(x).replace(str(work), "$WORK").replace(
                        str(ROOT), "$HOLDIR") for x in command],
                    "cwd": str(cwd).replace(str(work), "$WORK"),
                    "exit": result.returncode, "combined_log": log,
                })
                return result

            holmake = [str(ROOT / "bin/Holmake"), "--no-project",
                       "--no-cache", "--no_prereqs", "-j1",
                       "--holstate=" + str(ROOT / "bin/hol.state0")]
            for lane, revision in (("reference", REFERENCE),
                                   ("branch", branch)):
                library = work / lane / "lib"
                library.mkdir(parents=True)
                lane_report = {"sources_sha256": stage(revision, library),
                               "suites": {}}
                report["lanes"][lane] = lane_report
                targets = sorted(p.stem + ".uo"
                                 for p in library.glob("*.sml"))
                result = run(holmake + targets, library,
                             f"{lane}-libraries.build.log")
                if result.returncode:
                    success = False
                    continue
                for name, _, data in suites:
                    directory = work / lane / name
                    directory.mkdir()
                    (directory / "selftest.sml").write_bytes(data)
                    for path, source in support:
                        (directory / path.name).write_bytes(source)
                    (directory / "Holmakefile").write_text(
                        "HOLHEAP = $(HOLDIR)/bin/hol.state0\n"
                        "INCLUDES = ../lib\n"
                        "selftest.exe: selftest.uo\n"
                        "\t$(HOLMOSMLC) -o $@ $<\n")
                    result = run(holmake + ["selftest.exe"], directory,
                                 f"{lane}-{name}.build.log")
                    suite_report = {"build_exit": result.returncode}
                    lane_report["suites"][name] = suite_report
                    if result.returncode:
                        success = False
                        continue
                    load_audit = audit(
                        directory / ".hol/objs/selftest.uo", library, work)
                    shared = load_audit.pop("shared_sha256")
                    for path, sha in shared.items():
                        old = report["shared_sha256"].setdefault(path, sha)
                        if old != sha:
                            raise RuntimeError(f"shared dependency changed: {path}")
                    load_audit["shared_files"] = len(shared)
                    load_audit["shared_inventory_sha256"] = digest(
                        json.dumps(shared, sort_keys=True).encode())
                    suite_report["load_audit"] = load_audit
                    result = run([str(directory / "selftest.exe")], directory,
                                 f"{lane}-{name}.run.log")
                    text = result.stdout.decode(errors="replace")
                    suite_report.update({
                        "run_exit": result.returncode,
                        "observations": [line for line in text.splitlines()
                                         if line.startswith("OBS ")],
                        "ok_markers": text.count("OK"),
                    })
                    success = success and result.returncode == 0
            # Full stdout can contain timing, ANSI formatting and warnings.
            # Never normalize it into a claim of observational equivalence.
            comparisons = {}
            for name, _, _ in suites:
                ref = report["lanes"]["reference"]["suites"].get(name, {})
                impl = report["lanes"]["branch"]["suites"].get(name, {})
                r_obs, b_obs = ref.get("observations"), impl.get("observations")
                equal = r_obs == b_obs if r_obs or b_obs else None
                comparisons[name] = equal
                success = success and equal is not False
            report["observations_equal"] = comparisons
            success = success and comparisons.get("control") is True
            for name, sha in report["tools_sha256"].items():
                if digest((ROOT / name).read_bytes()) != sha:
                    raise RuntimeError(f"tool changed during run: {name}")
            for name, sha in report["shared_sha256"].items():
                path = Path(name.replace("$HOLDIR", str(ROOT)))
                if digest(path.read_bytes()) != sha:
                    raise RuntimeError(f"shared input changed during run: {name}")
    except BaseException as error:
        success = False
        report["runner_error"] = str(error)
        raise
    finally:
        report["passed"] = success
        save_json(output / "manifest.json", report)
    print(f"{'PASS' if success else 'FAIL'}: {output}")
    return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())
