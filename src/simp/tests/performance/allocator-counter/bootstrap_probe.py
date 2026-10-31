#!/usr/bin/env python3
"""Check whether the sealed Poly/ML native bootstrap can be rebuilt locally.

This is a prerequisite diagnostic, NOT an allocator or HOL acceptance run.
No installed compiler, runtime, HOL heap or caller cache is modified.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import acceptance as a
import loading
from prepare_patch import DEFAULT_SOURCE
import private_runtime as pr


def bootstrap_stages(text):
    """The distributed recipe must execute every source-recompilation stage."""
    stages = [f"******Bootstrap stage {i} of 7******" for i in range(2, 8)]
    positions = [text.find(marker) for marker in stages]
    a.require(all(pos >= 0 and text.count(marker) == 1
                  for pos, marker in zip(positions, stages)),
              "missing/duplicate native bootstrap stage")
    a.require(positions == sorted(positions), "reordered bootstrap stages")
    return stages


def build_native_hol(pristine, dst, repo, env, run, report):
    """Fresh native compiler and HOL; caller owns lock and temporary lifetime.

    Bootstrap without forced traps, then use the separately patched DSO only
    for allocation experiments. All generated ML code has source lineage.
    """
    from private_runtime import verify_source, HOL_SEQUENCE
    source = dst / "native-source"
    prefix = dst / "native-install"
    shutil.copytree(pristine, source)
    verify_source(source)
    run([str(source / "configure"), "--without-x", "--disable-compact32bit",
         "--enable-shared", "--prefix=" + str(prefix)], source)
    report["native_config_log"] = (source / "config.log").read_text()
    report["native_configuration"] = (source / "config.h").read_text()
    report["native_build_inputs"] = {
        str(p.relative_to(source)): a.seal(p)
        for p in source.rglob("*") if p.is_file()}
    result = run(["make", "-j2"], source)
    report["native_stages"] = bootstrap_stages(result["stdout"])
    run(["make", "install"], source)
    report["native_products"] = {
        str(p): a.seal(p) for p in prefix.rglob("*") if p.is_file()}
    head = a.git(repo, "rev-parse", "HEAD")
    hol = dst / "hol-source"
    run(["git", "clone", "--shared", "--no-checkout", str(repo), str(hol)],
        repo)
    run(["git", "checkout", "--detach", head], hol)
    # No copied .uo files/heaps or product cache. The detached clone is a
    # diagnostic snapshot, never a work branch or a modification of repo.
    a.require(not (hol / "bin/hol.state0").exists(), "prebuilt HOL image")
    report["hol_snapshot"] = head
    # Every build step below runs in this clone: HOLDIR names it, never the
    # caller's checkout.
    env["HOLDIR"] = str(hol)
    report["hol_source_inputs"] = {
        name: a.seal(hol / name) for name in a.git(
            hol, "ls-files").splitlines() if (hol / name).is_file()}
    overrides = hol / "tools-poly/poly-includes.ML"
    overrides.write_text(
        'val poly = ' + json.dumps(str(prefix / "bin/poly")) + ';\n' +
        'val polymllibdir = ' + json.dumps(str(prefix / "lib")) + ';\n')
    report["hol_configuration_override"] = overrides.read_text()
    run([str(prefix / "bin/poly"), "--error-exit", "--use",
         "tools/smart-configure.sml"], hol)
    run([str(hol / "bin/build"), "--no-cache", "-j2",
         "--seq=" + HOL_SEQUENCE], hol)
    report["hol_products"] = {str(hol / name): a.seal(hol / name)
                              for name in ("bin/hol", "bin/hol.state0",
                                           "bin/Holmake")}
    # sigobj is what a process searches for loadable modules.
    report["hol_sigobj"] = {
        str(p.relative_to(hol)): a.seal(p)
        for p in sorted((hol / "sigobj").iterdir()) if p.is_file()}
    report["hol_libraries"] = loading.library_inputs(
        run(["ldd", str(hol / "bin/hol")], hol))
    # Configuration writes generated sources; retain the before/after delta
    # explicitly rather than asserting all source bytes survived unchanged.
    report["hol_source_changes"] = {
        name: a.seal(hol / name)
        for name, seal in report["hol_source_inputs"].items()
        if a.seal(hol / name) != seal}
    manifest = json.loads((HERE / "SOURCE_SHA256.json").read_text())["files"]
    for name, digest in manifest.items():
        a.require(a.seal(source / name)["sha256"] == digest,
                  "bootstrap changed source input: " + name)
    return hol


def main(argv=None):
    pr.use_fixed_path()  # as the drivers: git and the tools resolve there
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--repo", type=Path, default=HERE.parents[4])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--authorize-experimental-runtime",
                        action="store_true")
    parser.add_argument("--hol-lineage", action="store_true")
    args = parser.parse_args(argv)
    if not args.authorize_experimental_runtime or args.timeout <= 0:
        parser.error("authorization and positive timeout required")
    from private_runtime import verify_source
    repo = args.repo.resolve(strict=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report = dict(schema="task29-native-bootstrap-probe-v1", success=False,
                  task29b_complete=False, commands=[],
                  scope="native compiler bootstrap only; NOT HOL lineage")
    with args.output.open("x") as stream:
        try:
            a.require(sys.platform == "linux" and
                      platform.machine() == "aarch64", "unsupported host")
            verify_source(args.source)
            report["head"] = a.git(repo, "rev-parse", "HEAD")
            inputs = [HERE / name for name in (
                "bootstrap_probe.py", "run_controls.py", "prepare_patch.py",
                "check_patch.py", "SOURCE_SHA256.json", "PATCHED_SHA256.json",
                "managed-allocation.patch.gz", "counter_impl.inc",
                "managed_alloc_counter.h")]
            inputs += [HERE.parent / name for name in (
                "acceptance.py", "loading.py")]
            report["inputs"] = {str(p): a.seal(p) for p in inputs}
            env = dict(PATH=os.environ["PATH"], HOME="/nonexistent",
                       TMPDIR="/tmp", TERM="dumb", LC_ALL="C", TZ="UTC",
                       CONFIG_SITE="/dev/null")
            for key, name in (("CC", "gcc"), ("CXX", "g++")):
                env[key] = shutil.which(name, path=env["PATH"]) or ""
                a.require(bool(env[key]), "missing compiler: " + name)
            report["environment"] = env
            with a.serial_lock(repo) as fds:
                def run(command, cwd):
                    print("RUN", " ".join(command), flush=True)
                    receipt = loading.execute(command, cwd, env,
                                              args.timeout, fds)
                    report["commands"].append(receipt)
                    a.require(receipt["exit"] == 0 and
                              not receipt["timed_out"],
                              "failed command: " + str(command))
                    return receipt

                for name in ("gcc", "g++", "make", "ld", "as", "ldd"):
                    path = shutil.which(name, path=env["PATH"])
                    a.require(path is not None, "missing tool: " + name)
                    report["inputs"][path] = a.seal(path)
                    run([path, "--version"], repo)
                for compiler, internal in (("gcc", "cc1"), ("g++", "cc1plus"),
                                           ("gcc", "collect2")):
                    path = run([compiler, "-print-prog-name=" + internal],
                               repo)["stdout"].strip()
                    report["inputs"][path] = a.seal(path)
                with tempfile.TemporaryDirectory(
                        prefix="task29-native-bootstrap-") as tmp:
                    if args.hol_lineage:
                        build_native_hol(args.source, Path(tmp), repo, env,
                                         run, report)
                        loading.check_seals(report["inputs"])
                        verify_source(args.source)
                        report["success"] = True
                        print("source-built HOL completed; "
                              "NOT allocation gate")
                        return 0
                    source = Path(tmp) / "source"
                    shutil.copytree(args.source, source)
                    verify_source(source)
                    run([str(source / "configure"), "--without-x",
                         "--disable-compact32bit", "--enable-shared"], source)
                    report["config_log"] = (source / "config.log").read_text()
                    report["configuration"] = (source / "config.h").read_text()
                    a.require("#define HOSTARCHITECTURE_AARCH64 1" in
                              report["configuration"] and
                              "#define POLYML32IN64 1" not in
                              report["configuration"], "wrong word/backend")
                    report["build_inputs"] = {
                        str(p.relative_to(source)): a.seal(p)
                        for p in source.rglob("*") if p.is_file()}
                    result = run(["make", "-j2"], source)
                    report["stages"] = bootstrap_stages(result["stdout"])
                    products = [source / p for p in (
                        ".libs/poly", ".libs/polyimport", "polyexport.o",
                        "libpolyml/.libs/libpolyml.so.16.0.0")]
                    report["products"] = {str(p): a.seal(p) for p in products}
                    report["libraries"] = loading.library_inputs(
                        run(["ldd", str(source / ".libs/poly")], source))
                    run([str(source / "poly"), "--version"], source)
                    # Source inputs, including the portable bytecode seed,
                    # must survive configuration and all seven stages.
                    manifest = json.loads(
                        (HERE / "SOURCE_SHA256.json").read_text())["files"]
                    for name, digest in manifest.items():
                        a.require(a.seal(source / name)["sha256"] == digest,
                                  "bootstrap changed source input: " + name)
                loading.check_seals(report["inputs"])
                verify_source(args.source)
            report["success"] = True
        except Exception as error:
            report["failure"] = str(error)
        finally:
            json.dump(report, stream, indent=2, allow_nan=False)
            stream.write("\n")
    print(report.get("failure", "native bootstrap completed; NOT HOL lineage"))
    return 0 if report["success"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
