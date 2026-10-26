#!/usr/bin/env python3
"""Build a private experimental runtime and execute managed-allocation controls.

Never install, replace the configured runtime, or treat this as TASK29 approval.
All source/build/DSO/fixture copies are deleted after recording their receipts.
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
from prepare_patch import DEFAULT_SOURCE, transformations, sha256
from check_patch import replay, read_patch
from control_schema import observations
import worker_schema
import interpreter_schema
import interpreter_branch_schema
import failure_schema


def runtime_identity(text, library):
    rows = [line.split("\t", 1)[1] for line in text.splitlines()
            if line.startswith("@@TASK29_ALLOC_RUNTIME_V1\t")]
    a.require(len(rows) == 1 and
              Path(rows[0]).resolve(strict=True) == library.resolve(strict=True),
              "snapshot symbol bound to wrong runtime")
    maps = [line.split("\t", 1)[1] for line in text.splitlines()
            if line.startswith("@@TASK29_ALLOC_MAP_V1\t")]
    paths = {line.split(maxsplit=5)[5] for line in maps
             if len(line.split(maxsplit=5)) == 6 and
             "libpolyml" in line.split(maxsplit=5)[5]}
    a.require(paths and all(Path(p).resolve(strict=True) ==
              library.resolve(strict=True) for p in paths),
              "control process has missing/multiple runtime mappings")
    return dict(symbol=rows[0], maps=maps)


def verify_source(source):
    seal = json.loads((HERE / "SOURCE_SHA256.json").read_text())
    entries = list(source.rglob("*"))
    paths = [p for p in entries if p.is_file()]
    a.require(not any(p.is_symlink() for p in entries), "source symlinks")
    a.require({p.relative_to(source).as_posix() for p in paths} ==
              set(seal["files"]), "source inventory mismatch")
    originals = {n: (source / n).read_bytes() for n in seal["files"]}
    a.require(all(sha256(raw) == seal["files"][n]
                  for n, raw in originals.items()), "source hash mismatch")
    canonical = "".join(f"{v}  {n}\n" for n, v in
                        sorted(seal["files"].items())).encode()
    a.require(sha256(canonical) == seal["tree_manifest_sha256"],
              "source manifest mismatch")
    patched = replay(read_patch(), originals)
    a.require(patched == transformations(originals), "patch reproduction failed")
    a.require({n: sha256(raw) for n, raw in patched.items()} == json.loads(
        (HERE / "PATCHED_SHA256.json").read_text()), "patched seal mismatch")
    return patched


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--repo", type=Path, default=Path(
        os.environ.get("HOLDIR", HERE.parents[4])))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--authorize-experimental-runtime", action="store_true")
    args = parser.parse_args(argv)
    if not args.authorize_experimental_runtime or args.timeout <= 0:
        parser.error("authorization and positive timeout required")
    repo = args.repo.resolve(strict=True)
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    report = dict(schema="task29-managed-counter-controls-v3", success=False,
                  task29_complete=False, commands=[], inputs={},
                  scope="experimental runtime controls; NOT allocation gate",
                  command=[sys.executable, *sys.argv])
    with output.open("x") as stream:
        try:
            a.require(sys.platform == "linux" and
                      platform.machine() == "aarch64", "unsupported host")
            inputs = [p for p in HERE.iterdir() if p.is_file()]
            inputs += [HERE.parent / name for name in (
                "acceptance.py", "loading.py", "worker_schema.py",
                "interpreter_schema.py", "interpreter_branch_schema.py",
                "failure_schema.py")]
            inputs += [repo / p for p in (
                "bin/hol", "bin/hol.state0", "bin/Holmake")]
            report["inputs"] = {str(p): a.seal(p) for p in inputs}
            report["head"] = a.git(repo, "rev-parse", "HEAD")
            patched = verify_source(args.source)
            # Do not inherit configure/compiler/make/linker search overrides.
            env = dict(PATH=os.environ["PATH"], HOME="/nonexistent",
                       TMPDIR="/tmp", HOLDIR=str(repo), TERM="dumb",
                       LC_ALL="C", TZ="UTC", CONFIG_SITE="/dev/null")
            for key, name in (("CC", "gcc"), ("CXX", "g++")):
                env[key] = shutil.which(name, path=env["PATH"]) or ""
                a.require(bool(env[key]), "missing compiler: " + name)
            report["environment"] = env
            with a.serial_lock(repo) as fds:
                def run(command, cwd=repo, runtime_env=None):
                    receipt = loading.execute(command, cwd,
                        env if runtime_env is None else runtime_env,
                        args.timeout, fds)
                    receipt["environment"] = dict(
                        env if runtime_env is None else runtime_env)
                    report["commands"].append(receipt)
                    a.require(receipt["exit"] == 0 and not receipt["timed_out"],
                              "failed command: " + str(command))
                    return receipt

                for tool in ("gcc", "g++", "make", "ldd", "nm", "ld", "as"):
                    path = shutil.which(tool, path=env["PATH"])
                    a.require(path is not None, "missing tool: " + tool)
                    report["inputs"][path] = a.seal(path)
                    run([path, "--version"])
                for compiler, internal in (("gcc", "cc1"), ("g++", "cc1plus"),
                                           ("gcc", "collect2")):
                    path = run([compiler, "-print-prog-name=" + internal])[
                        "stdout"].strip()
                    a.require(Path(path).is_file(), "compiler internal missing")
                    report["inputs"][path] = a.seal(path)
                report["ordinary_libraries"] = loading.library_inputs(run(
                    ["ldd", str(repo / "bin/hol")]))
                with tempfile.TemporaryDirectory(prefix="task29-counter-") as tmp:
                    dst = Path(tmp)
                    # Standalone arithmetic tests inject synthetic increments only.
                    for name in ("arithmetic_test.cpp", "counter_impl.inc",
                                 "managed_alloc_counter.h"):
                        shutil.copyfile(HERE / name, dst / name)
                    arithmetic = dst / "arithmetic-test"
                    run([env["CXX"], "-std=c++11", "-pthread", "-O2",
                         "-DHOSTARCHITECTURE_AARCH64=1", "-DSIZEOF_VOIDP=8",
                         str(dst / "arithmetic_test.cpp"), "-o", str(arithmetic)])
                    report["arithmetic_binary"] = a.seal(arithmetic)
                    result = run([str(arithmetic)], dst)
                    a.require(result["stdout"] ==
                        "@@TASK29_ALLOC_ARITHMETIC_V1\tpass\tsynthetic-only\n",
                        "arithmetic/concurrency controls incomplete")
                    source = dst / "source"
                    shutil.copytree(args.source, source)
                    # Recheck the actual copy, not just the caller's inputs.
                    a.require(verify_source(source) == patched, "copy changed")
                    for name, raw in patched.items():
                        (source / name).write_bytes(raw)
                    source_seals = {str(p): a.seal(p) for p in source.rglob("*")
                                    if p.is_file()}
                    run([str(source / "configure"), "--without-x",
                         "--disable-compact32bit", "--enable-shared"], source)
                    report["config_log"] = (source / "config.log").read_text()
                    report["configuration"] = (source / "config.h").read_text()
                    a.require("#define HOSTARCHITECTURE_AARCH64 1" in
                              report["configuration"] and
                              "#define POLYML32IN64 1" not in
                              report["configuration"], "wrong backend/word size")
                    report["build_inputs"] = {str(p.relative_to(source)):
                        a.seal(p) for p in source.rglob("*") if p.is_file()}
                    run(["make", "-C", "libpolyml", "-j2", "libpolyml.la"], source)
                    lib = source / "libpolyml/.libs/libpolyml.so.16.0.0"
                    report["runtime"] = a.seal(lib)
                    symbols = run(["nm", "-D", str(lib)])["stdout"]
                    a.require(" T PolyManagedAllocSnapshotV1\n" in symbols and
                              " T PolyManagedInterpreterAllocSnapshotV1\n"
                              in symbols, "counter symbols not exported")
                    run_env = dict(env, LD_LIBRARY_PATH=str(lib.parent))
                    libraries = loading.library_inputs(run(
                        ["ldd", str(repo / "bin/hol")], runtime_env=run_env))
                    matches = [(p, v) for p, v in libraries.items()
                               if Path(p).name.startswith("libpolyml.so")]
                    a.require(len(matches) == 1 and
                              matches[0][1]["sha256"] == report["runtime"]["sha256"]
                              and Path(matches[0][1]["resolved"]) == lib,
                              "HOL not linked to private counter runtime")
                    report["instrumented_libraries"] = libraries
                    fixture = dst / "fixture"
                    fixture.mkdir()
                    copied = {}
                    for name in ("selftest.sml", "worker_selftest.sml",
                                 "interpreter_selftest.sml",
                                 "interpreter_body.sml", "interpreter_host.sml",
                                 "interpreter_branch_host.sml",
                                 "failure_selftest.sml", "failure_limit.c",
                                 "Holmakefile", "bracket.c",
                                 "managed_alloc_counter.h"):
                        target = fixture / name
                        shutil.copyfile(HERE / name, target)
                        copied[str(target)] = a.seal(HERE / name)
                    shim = fixture / "bracket.so"
                    run([env["CC"], "-std=c11", "-shared", "-fPIC", "-O2",
                         "-Wall", "-Wextra", "-Wl,-z,defs",
                         str(fixture / "bracket.c"),
                         str(fixture / "failure_limit.c"),
                         str(lib), "-ldl",
                         "-o", str(shim)])
                    shim_libs = loading.library_inputs(run(
                        ["ldd", str(shim)], runtime_env=run_env))
                    a.require(any(info["sha256"] == report["runtime"]["sha256"]
                                  for info in shim_libs.values()),
                              "shim not linked to counter runtime")
                    report["shim_libraries"] = shim_libs
                    report["shim"] = a.seal(shim)
                    run([str(repo / "bin/Holmake"), "--no-project", "--no-cache",
                         "--no_prereqs", "--holstate=" + str(repo / "bin/hol.state0"),
                         "-C", str(fixture), "-j1", "counter-controls.exe",
                         "worker-controls.exe", "interpreter-controls.exe",
                         "failure-controls.exe"])
                    launcher = fixture / "counter-controls.exe"
                    report["launcher"] = a.seal(launcher)
                    report["launcher_text"] = launcher.read_text()
                    worker_launcher = fixture / "worker-controls.exe"
                    report["worker_launcher"] = a.seal(worker_launcher)
                    report["worker_launcher_text"] = worker_launcher.read_text()
                    interpreter_launcher = fixture / "interpreter-controls.exe"
                    report["interpreter_launcher"] = a.seal(
                        interpreter_launcher)
                    report["interpreter_launcher_text"] = (
                        interpreter_launcher.read_text())
                    failure_launcher = fixture / "failure-controls.exe"
                    report["failure_launcher"] = a.seal(failure_launcher)
                    report["failure_launcher_text"] = (
                        failure_launcher.read_text())
                    products = {str(p): a.seal(p) for p in fixture.rglob("*")
                                if p.is_file()}
                    # The testutils loader is the only fixture dependency not
                    # already in hol.state0. Record its descriptor and source.
                    testutils = [repo / "src/parse/testutils.sml",
                                 repo / "src/parse/testutils.sig",
                                 repo / "sigobj/testutils.uo",
                                 repo / "sigobj/testutils.ui"]
                    report["inputs"].update({str(p): a.seal(p)
                                              for p in testutils})
                    report["fixture_products"] = products
                    run_env["TASK29_ALLOC_SHIM"] = str(shim)
                    result = run([str(fixture / "counter-controls.exe"),
                                  "--gcthreads=1"], fixture, run_env)
                    report["control_output"] = result["stdout"]
                    report["observations"] = observations(result["stdout"])
                    report["process_identity"] = runtime_identity(
                        result["stdout"], lib)
                    result = run([str(worker_launcher), "--gcthreads=1"],
                                 fixture, run_env)
                    report["worker_output"] = result["stdout"]
                    report["worker_observations"] = worker_schema.observations(
                        result["stdout"])
                    report["worker_process_identity"] = runtime_identity(
                        result["stdout"].replace("@@TASK29_WORKER_",
                                                 "@@TASK29_ALLOC_"), lib)
                    run_env["TASK29_ALLOC_SOURCE"] = str(source)
                    run_env["TASK29_ALLOC_BODY"] = str(
                        fixture / "interpreter_body.sml")
                    run_env["TASK29_ALLOC_HOST"] = str(
                        fixture / "interpreter_host.sml")
                    run_env["TASK29_ALLOC_BRANCH_HOST"] = str(
                        fixture / "interpreter_branch_host.sml")
                    result = run([str(interpreter_launcher), "--gcthreads=1"],
                                 fixture, run_env)
                    report["interpreter_output"] = result["stdout"]
                    # Keep the full original stdout. The strict new parser
                    # admits every branch record before separating protocols.
                    report["interpreter_branch_observations"] = (
                        interpreter_branch_schema.observations(result["stdout"]))
                    original = "\n".join(line for line in
                        result["stdout"].splitlines() if not
                        line.startswith("@@TASK29_IBRANCH"))
                    report["interpreter_observations"] = (
                        interpreter_schema.observations(original))
                    report["interpreter_process_identity"] = runtime_identity(
                        result["stdout"].replace("@@TASK29_INTERPRETER_",
                                                 "@@TASK29_ALLOC_"), lib)
                    result = run([str(failure_launcher), *failure_schema.FLAGS],
                                 fixture, run_env)
                    report["failure_output"] = result["stdout"]
                    report["failure_observations"] = (
                        failure_schema.validate_receipt(result,
                                                        timeout=args.timeout))
                    report["failure_process_identity"] = runtime_identity(
                        result["stdout"].replace("@@TASK29_FAILURE_",
                                                 "@@TASK29_ALLOC_"), lib)
                    loading.check_seals(copied)
                    loading.check_seals(products)
                    loading.check_seals(source_seals)
                    a.require(a.seal(lib) == report["runtime"], "runtime changed")
                    after = loading.library_inputs(run(
                        ["ldd", str(repo / "bin/hol")], runtime_env=run_env))
                    a.require(after == libraries, "instrumented linkage drift")
                    for raw, info in libraries.items():
                        a.require(str(Path(raw).resolve(strict=True)) ==
                                  info["resolved"] and a.seal(raw) == {
                                      k: info[k] for k in ("bytes", "sha256")},
                                  "instrumented library drift: " + raw)
                loading.check_seals(report["inputs"])
                verify_source(args.source)
            report["success"] = True
        except Exception as error:
            report["failure"] = str(error)
        finally:
            json.dump(report, stream, indent=2, allow_nan=False)
            stream.write("\n")
    print(report.get("failure", "runtime controls completed; NOT TASK29 approval"))
    return 0 if report["success"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
