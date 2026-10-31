#!/usr/bin/env python3
"""Build a private experimental runtime; run managed-allocation controls.

Never install, replace the configured runtime, or treat this as TASK29
approval. All source/build/DSO/fixture copies are deleted after recording
their receipts.

The controls always run from the checkout containing this file. That
checkout must be clean and differ from the reference revision only below
src/simp/tests/performance; HOL is built from its committed HEAD with a
source-built native Poly/ML, and the receipt records the harness head, the
reference, the tree identity outside the performance area and the whole
build lineage. The environment's HOLDIR is never consulted.
"""
import argparse
import json
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
from private_runtime import (verify_source, runtime_identity, build_runtime,
                             bind_runtime, build_shim, harness_identity,
                             harness_inputs, check_transient,
                             check_persistent)
from control_schema import observations
import worker_schema
import interpreter_schema
import interpreter_branch_schema
import failure_schema
import path_schema

SCHEMA = "task29-managed-counter-controls-v4"
HARNESS = HERE.parents[4]
# Sources copied to the fixture the launchers are built from.
FIXTURE_SOURCES = (
    "selftest.sml", "worker_selftest.sml", "interpreter_selftest.sml",
    "interpreter_body.sml", "interpreter_host.sml",
    "interpreter_branch_host.sml", "failure_selftest.sml",
    "failure_limit.c", "path_selftest.sml", "interpreter_path_selftest.sml",
    "interpreter_path_body.sml", "interpreter_path_host.sml",
    "failure_path_selftest.sml", "PathThreads.sml", "Holmakefile",
    "bracket.c", "managed_alloc_counter.h")
LAUNCHERS = ("counter-controls.exe", "worker-controls.exe",
             "interpreter-controls.exe", "failure-controls.exe",
             "path-controls.exe", "interpreter-path-controls.exe",
             "failure-path-controls.exe")


def arguments(argv):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--reference", default="simplifier",
                        help="revision this checkout may differ from only "
                        "below src/simp/tests/performance")
    parser.add_argument("--authorize-experimental-runtime",
                        action="store_true")
    parser.add_argument("--bootstrap-hol", action="store_true",
                        help="rebuild native compiler and HOL without "
                        "caches (required: it is the receipt's lineage)")
    args = parser.parse_args(argv)
    if not args.authorize_experimental_runtime or args.timeout <= 0:
        parser.error("authorization and positive timeout required")
    if not args.bootstrap_hol:
        parser.error("--bootstrap-hol is required: a receipt without a "
                     "source-built HOL has no lineage")
    return args


def environment():
    # Do not inherit configure/compiler/make/linker search overrides.
    env = dict(PATH=pr.PATH, HOME="/nonexistent", TMPDIR="/tmp",
               TERM="dumb", LC_ALL="C", TZ="UTC", CONFIG_SITE="/dev/null")
    for key, name in (("CC", "gcc"), ("CXX", "g++")):
        env[key] = shutil.which(name, path=env["PATH"]) or ""
        a.require(bool(env[key]), "missing compiler: " + name)
    return env


def seal_tools(env, run, report):
    report["inputs"].update(pr.seal_tools(env, run))


def arithmetic_controls(dst, env, run, report):
    # Standalone arithmetic tests inject synthetic increments only.
    for name in ("arithmetic_test.cpp", "counter_impl.inc",
                 "managed_alloc_counter.h"):
        shutil.copyfile(HERE / name, dst / name)
    binary = dst / "arithmetic-test"
    run([env["CXX"], "-std=c++11", "-pthread", "-O2",
         "-DHOSTARCHITECTURE_AARCH64=1", "-DSIZEOF_VOIDP=8",
         str(dst / "arithmetic_test.cpp"), "-o", str(binary)])
    report["arithmetic_binary"] = a.seal(binary)
    result = run([str(binary)], dst)
    a.require(result["stdout"] ==
              "@@TASK29_ALLOC_ARITHMETIC_V1\tpass\tsynthetic-only\n",
              "arithmetic/concurrency controls incomplete")


def protocol_runs(run, report, fixture, run_env, lib, source, timeout):
    """Run every launcher process and validate its complete output."""
    def identity(result, old):
        return runtime_identity(
            result["stdout"].replace(old, "@@TASK29_ALLOC_"), lib)

    flags = ("--gcthreads=1",)
    result = run([str(fixture / "counter-controls.exe"), *flags],
                 fixture, run_env)
    report["control_output"] = result["stdout"]
    report["observations"] = observations(result["stdout"])
    report["process_identity"] = runtime_identity(result["stdout"], lib)
    result = run([str(fixture / "worker-controls.exe"), *flags],
                 fixture, run_env)
    report["worker_output"] = result["stdout"]
    report["worker_observations"] = worker_schema.observations(
        result["stdout"])
    report["worker_process_identity"] = identity(result,
                                                 "@@TASK29_WORKER_")
    run_env.update(
        TASK29_ALLOC_SOURCE=str(source),
        TASK29_ALLOC_BODY=str(fixture / "interpreter_body.sml"),
        TASK29_ALLOC_HOST=str(fixture / "interpreter_host.sml"),
        TASK29_ALLOC_BRANCH_HOST=str(
            fixture / "interpreter_branch_host.sml"))
    result = run([str(fixture / "interpreter-controls.exe"), *flags],
                 fixture, run_env)
    report["interpreter_output"] = result["stdout"]
    # Keep the full original stdout. The strict new parser admits every
    # branch record before separating protocols.
    report["interpreter_branch_observations"] = (
        interpreter_branch_schema.observations(result["stdout"]))
    original = "\n".join(line for line in result["stdout"].splitlines()
                         if not line.startswith("@@TASK29_IBRANCH"))
    report["interpreter_observations"] = (
        interpreter_schema.observations(original))
    report["interpreter_process_identity"] = identity(
        result, "@@TASK29_INTERPRETER_")
    result = run([str(fixture / "failure-controls.exe"),
                  *failure_schema.FLAGS], fixture, run_env)
    report["failure_output"] = result["stdout"]
    report["failure_observations"] = failure_schema.validate_receipt(
        result, timeout=timeout)
    report["failure_process_identity"] = identity(result,
                                                  "@@TASK29_FAILURE_")
    path_body = fixture / "interpreter_path_body.sml"
    path_host = fixture / "interpreter_path_host.sml"
    for key, profile, name, extra in (
            ("path", "native-rts", "path-controls.exe", {}),
            ("interpreter_path", "interpreter",
             "interpreter-path-controls.exe",
             dict(TASK29_PATH_BODY=str(path_body),
                  TASK29_PATH_HOST=str(path_host))),
            ("failure_path", "failure", "failure-path-controls.exe", {})):
        result = run([str(fixture / name), *path_schema.FLAGS[profile]],
                     fixture, dict(run_env, **extra))
        report[key + "_output"] = result["stdout"]
        report[key + "_observations"] = path_schema.validate_receipt(
            result, profile, timeout=timeout)
        report[key + "_process_identity"] = identity(result,
                                                     "@@TASK29_PATH_")


def build_launchers(fixture, hol, run, report, env):
    run([str(hol / "bin/Holmake"), "--no-project", "--no-cache",
         "--no_prereqs", "--holstate=" + str(hol / "bin/hol.state0"),
         "-C", str(fixture), "-j1", *LAUNCHERS], hol)
    for key, name in (("launcher", "counter-controls.exe"),
                      ("worker_launcher", "worker-controls.exe"),
                      ("interpreter_launcher", "interpreter-controls.exe"),
                      ("failure_launcher", "failure-controls.exe"),
                      ("path_launcher", "path-controls.exe"),
                      ("interpreter_path_launcher",
                       "interpreter-path-controls.exe"),
                      ("failure_path_launcher",
                       "failure-path-controls.exe")):
        report[key] = a.seal(fixture / name)
        report[key + "_text"] = (fixture / name).read_text()


def controls(args, patched, report, env, run, dst):
    """Everything between the lock and the final seal rechecks."""
    from bootstrap_probe import build_native_hol
    report["lineage"] = {}
    hol = build_native_hol(args.source, dst, HARNESS, env, run,
                           report["lineage"])
    a.require(env["HOLDIR"] == str(hol), "HOLDIR does not name the clone")
    a.require(report["lineage"]["hol_snapshot"] == report["head"],
              "HOL snapshot is not the harness head")
    report["inputs"].update({str(hol / p): a.seal(hol / p) for p in (
        "bin/hol", "bin/hol.state0", "bin/Holmake")})
    # The testutils loader is the only fixture dependency not already in
    # hol.state0. Record its descriptor and source.
    report["inputs"].update({str(hol / p): a.seal(hol / p) for p in (
        "src/parse/testutils.sml", "src/parse/testutils.sig",
        "sigobj/testutils.uo", "sigobj/testutils.ui")})
    report["ordinary_libraries"] = loading.library_inputs(
        run(["ldd", str(hol / "bin/hol")]))
    arithmetic_controls(dst, env, run, report)
    lib, source, source_seals = build_runtime(args.source, dst, run, report,
                                              patched)
    run_env = dict(env, LD_LIBRARY_PATH=str(lib.parent))
    libraries = bind_runtime(run, hol, lib, run_env, report)
    fixture = dst / "fixture"
    fixture.mkdir()
    copied = {}
    for name in FIXTURE_SOURCES:
        shutil.copyfile(HERE / name, fixture / name)
        copied[str(fixture / name)] = a.seal(HERE / name)
    shim, report["shim_libraries"] = build_shim(
        env, run, fixture, lib, run_env, report, extended=True)
    report["shim"] = a.seal(shim)
    build_launchers(fixture, hol, run, report, env)
    products = {str(p): a.seal(p) for p in fixture.rglob("*")
                if p.is_file()}
    report["fixture_products"] = products
    run_env["TASK29_ALLOC_SHIM"] = str(shim)
    protocol_runs(run, report, fixture, run_env, lib, source, args.timeout)
    # Seals are rechecked while the temporary tree still exists, lineage
    # included: the HOL and native products of this very build.
    loading.check_seals(copied)
    loading.check_seals(products)
    loading.check_seals(report["lineage"]["hol_products"])
    loading.check_seals(report["lineage"]["native_products"])
    check_transient(report["inputs"], dst)
    loading.check_seals(source_seals)
    a.require(a.seal(lib) == report["runtime"], "runtime changed")
    after = loading.library_inputs(run(["ldd", str(hol / "bin/hol")],
                                       runtime_env=run_env))
    a.require(after == libraries, "instrumented linkage drift")
    for raw, info in libraries.items():
        a.require(str(Path(raw).resolve(strict=True)) == info["resolved"]
                  and a.seal(raw) == {k: info[k]
                                      for k in ("bytes", "sha256")},
                  "instrumented library drift: " + raw)


def main(argv=None):
    pr.use_fixed_path()
    args = arguments(argv)
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    report = dict(schema=SCHEMA, success=False, task29_complete=False,
                  commands=[], inputs={},
                  scope="experimental runtime controls; NOT allocation gate",
                  command=[sys.executable, *sys.argv])
    with output.open("x") as stream:
        try:
            a.require(sys.platform == "linux" and
                      platform.machine() == "aarch64", "unsupported host")
            report["harness"] = harness_identity(HARNESS, args.reference)
            report["head"] = report["harness"]["head"]
            report["inputs"] = {str(p): a.seal(p)
                                for p in harness_inputs()}
            patched = verify_source(args.source)
            env = environment()
            report["environment"] = env
            with a.serial_lock(HARNESS) as fds:
                def run(command, cwd=HARNESS, runtime_env=None):
                    use = env if runtime_env is None else runtime_env
                    receipt = loading.execute(command, cwd, use,
                                              args.timeout, fds)
                    receipt["environment"] = dict(use)
                    report["commands"].append(receipt)
                    a.require(receipt["exit"] == 0 and
                              not receipt["timed_out"],
                              "failed command: " + str(command))
                    return receipt

                seal_tools(env, run, report)
                with tempfile.TemporaryDirectory(
                        prefix="task29-counter-") as tmp:
                    dst = Path(tmp)
                    controls(args, patched, report, env, run, dst)
                    scratch = dst
                check_persistent(report["inputs"], scratch)
                a.require(verify_source(args.source) == patched,
                          "patched source changed")
            # The harness must be what it was when the controls started.
            a.require(harness_identity(HARNESS, args.reference) ==
                      report["harness"], "harness changed during the run")
            report["success"] = True
        except Exception as error:
            report["failure"] = str(error)
        finally:
            json.dump(report, stream, indent=2, allow_nan=False)
            stream.write("\n")
    print(report.get("failure",
                     "runtime controls completed; NOT TASK29 approval"))
    return 0 if report["success"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
