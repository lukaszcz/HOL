#!/usr/bin/env python3
"""Paired fresh-heap namespace regressions with ordered observations."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile

from run import HERE, ROOT, REFERENCE, audit, digest, git, save_json, stage

SCENARIOS = ("control", "attribute-first", "set-first",
             "attribute-after", "set-after")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--branch", default="HEAD", help="committed revision")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--scenario", choices=SCENARIOS, action="append",
                        help="repeatable; default: all five isolated processes")
    args = parser.parse_args()
    branch = git("rev-parse", args.branch + "^{commit}").decode().strip()
    output = args.output.resolve()
    sources = {name: (HERE / "probes/fresh-load" / name).read_bytes()
               for name in ("selftest.sml", "control.ML", "Holmakefile")}
    scenarios = args.scenario or SCENARIOS
    report = {
        "kind": "mixed-source fresh-load; NOT independent repository builds",
        "reference": REFERENCE, "branch": branch,
        "working_tree": git("status", "--porcelain=v1",
                            "--untracked-files=all").decode(),
        "inputs_sha256": {name: digest(data) for name, data in sources.items()},
        "runner_sha256": {name: digest((HERE / name).read_bytes())
                          for name in ("fresh_load.py", "run.py")},
        "tools_sha256": {name: digest((ROOT / name).read_bytes()) for name in
                         ("bin/Holmake", "bin/hol", "bin/hol.state0")},
        "commands": [], "lanes": {}, "shared_sha256": {},
    }
    success = True
    output.mkdir(parents=True, exist_ok=False)
    try:
        with tempfile.TemporaryDirectory(prefix="hol-simp-fresh.") as scratch:
            work = Path(scratch)

            def clean(text):
                return str(text).replace(str(work), "$WORK").replace(
                    str(ROOT), "$HOLDIR")

            def run(command, cwd, log, environment=None):
                result = subprocess.run(command, cwd=cwd,
                                        env={**os.environ, **(environment or {})},
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, check=False)
                (output / log).write_bytes(result.stdout)
                report["commands"].append({
                    "argv": [clean(x) for x in command], "cwd": clean(cwd),
                    "env": {k: clean(v) for k, v in (environment or {}).items()},
                    "exit": result.returncode, "combined_log": log,
                })
                return result

            def inventory(start, library, **kwargs):
                result = audit(start, library, work, **kwargs)
                shared = result.pop("shared_sha256")
                for path, sha in shared.items():
                    old = report["shared_sha256"].setdefault(path, sha)
                    if old != sha:
                        raise RuntimeError(f"shared input changed: {path}")
                result["shared_files"] = len(shared)
                return result

            holmake = [str(ROOT / "bin/Holmake"), "--no-project", "--no-cache",
                       "--no_prereqs", "-j1",
                       "--holstate=" + str(ROOT / "bin/hol.state0")]
            for lane, revision in (("reference", REFERENCE), ("branch", branch)):
                library = work / lane / "lib"
                library.mkdir(parents=True)
                record = {"sources_sha256": stage(revision, library),
                          "scenarios": {}}
                report["lanes"][lane] = record
                result = run(holmake + sorted(p.stem + ".uo" for p in
                                             library.glob("*.sml")), library,
                             f"{lane}-libraries.build.log")
                record["library_build_exit"] = result.returncode
                if result.returncode:
                    success = False
                    continue
                directory = work / lane / "launcher"
                directory.mkdir()
                for name, data in sources.items():
                    (directory / name).write_bytes(data)
                result = run(holmake + ["selftest.exe"], directory,
                             f"{lane}-launcher.build.log")
                record["launcher_build_exit"] = result.returncode
                if result.returncode:
                    success = False
                    continue
                start = directory / ".hol/objs/selftest.uo"
                record["launcher_recipe"] = clean(start.read_text())
                record["launcher_audit"] = inventory(
                    start, library, required=(), forbidden=("simpLib", "splitLib"))
                record["dynamic_load_audit"] = inventory(
                    library / ".hol/objs/simpLib.uo", library,
                    required=("markerLib", "markerSyntax"))
                # The root recipe itself is simpLib, not an edge in modules.
                for scenario in scenarios:
                    environment = {
                        "SIMP_COMPAT_SCENARIO": scenario,
                        "SIMP_COMPAT_PATH": str(library / "simpLib"),
                        "SIMP_COMPAT_CONTROL": str(directory / "control.ML"),
                    }
                    result = run([str(directory / "selftest.exe")], directory,
                                 f"{lane}-{scenario}.run.log", environment)
                    text = result.stdout.decode(errors="replace")
                    observations = [s for s in text.splitlines()
                                    if s.startswith("OBS ")]
                    precondition = "OBS precondition=clean" in observations
                    passed = (result.returncode == 0 and precondition and
                              "OBS result=pass" in observations)
                    record["scenarios"][scenario] = {
                        "run_exit": result.returncode,
                        "precondition_clean": precondition,
                        "passed": passed, "observations": observations,
                        "expected_load_path": str(library / "simpLib"),
                    }
                    success = success and passed
            # Keep original observations. The sole non-contract field is the
            # deliberately different lane-local recipe path; validate it,
            # then compare every other observation in its original order.
            comparisons = {}
            for scenario in scenarios:
                traces = []
                paths_valid = True
                for lane in ("reference", "branch"):
                    record = report["lanes"][lane]["scenarios"].get(scenario, {})
                    observations = record.get("observations", [])
                    path_lines = [s for s in observations
                                  if s.startswith("OBS load.path=")]
                    paths_valid = paths_valid and path_lines == [
                        "OBS load.path=" + record.get("expected_load_path", "")]
                    traces.append([s for s in observations
                                   if not s.startswith("OBS load.path=")])
                equal = paths_valid and bool(traces[0]) and traces[0] == traces[1]
                comparisons[scenario] = {
                    "load_paths_valid": paths_valid,
                    "ordered_contract_observations_equal": equal,
                    "non_contract_field": "load.path (lane-local recipe)",
                }
                success = success and equal
            report["comparisons"] = comparisons
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
