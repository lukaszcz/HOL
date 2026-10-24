#!/usr/bin/env python3
"""Falsify profiler-sum allocation accounting on one pinned Poly/ML binary.

This is NOT an allocator instrument, performance observation, or TASK29 pass.
A private testutils/selftest launcher injects synthetic unknown-PC profiler
requests. No requested allocation is performed by the C shim. Never call its
private C++ ABI on a merely version-string-compatible library.
"""
import argparse
import json
import os
from pathlib import Path
import platform
import re
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import acceptance as a
import loading

LIB_SHA256 = (
    "8e39afa6fd362322a6e19b16e0055c39a6b3f8aae67d3fb04191feec4961fd7d")
SYMBOL = "_Z19addSynchronousCountPhm"
CASES = (("empty", 0, 0), ("one-word", 1, 1),
         ("million-words", 1048576, 1), ("seven-events", 1048576, 7),
         ("collected", 1048576, 7), ("reset", 0, 0))


def admit_library(libraries):
    matches = [(raw, info) for raw, info in libraries.items()
               if Path(raw).name.startswith("libpolyml.so")]
    a.require(len(matches) == 1, "expected one linked libpolyml")
    raw, info = matches[0]
    a.require(info["sha256"] == LIB_SHA256,
              "unreviewed libpolyml bytes; private ABI probe forbidden")
    return raw


def observations(text):
    rows, complete = [], []
    for line in text.splitlines():
        if line.startswith("@@TASK29_PROFILER_COMPLETE"):
            complete.append(line)
        elif line.startswith("@@TASK29_PROFILER"):
            parts = line.split("\t")
            a.require(len(parts) == 4 and all(
                re.fullmatch(r"[0-9]+", n) for n in parts[2:]),
                "malformed profiler observation")
            rows.append({"label": parts[1], "unknown_count": int(parts[2]),
                         "displayed_total": int(parts[3])})
    a.require(complete == ["@@TASK29_PROFILER_COMPLETE\t6"] and
              [r["label"] for r in rows] == [c[0] for c in CASES],
              "missing/duplicate/reordered profiler controls")
    for row, (_, words, events) in zip(rows, CASES):
        a.require(row["unknown_count"] == events and
                  row["displayed_total"] >= events,
                  "pinned unknown-PC event-count behavior not reproduced")
        row.update(synthetic_request_words=words,
                   synthetic_events=events,
                   synthetic_requested_word_sum=words * events)
    return rows


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(
        os.environ.get("HOLDIR", HERE.parents[3])))
    parser.add_argument("--output", type=Path, required=True,
                        help="new JSON receipt, including failed commands")
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--authorize-runtime-probe", action="store_true")
    args = parser.parse_args(argv)
    if args.timeout <= 0 or not args.authorize_runtime_probe:
        parser.error("positive timeout and --authorize-runtime-probe required")
    repo, output = args.repo.resolve(strict=True), args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    report = {"schema": "task29-profiler-loss-v1", "success": False,
              "scope": "synthetic profiler negative control; NOT allocation",
              "command": [sys.executable, *sys.argv], "commands": [],
              "inputs": {}, "libraries": {}, "observations": [],
              "task29_complete": False}
    with output.open("x") as stream:
        try:
            a.require(sys.platform == "linux" and
                      platform.machine() == "aarch64",
                      "private ABI reviewed only on Linux/aarch64")
            fixture = HERE / "allocator-probe"
            sources = [Path(__file__).resolve(), HERE / "acceptance.py",
                       HERE / "loading.py", *sorted(fixture.iterdir())]
            a.require(all(p.is_file() for p in sources),
                      "fixture directory must contain only source files")
            report["inputs"] = {str(p): a.seal(p) for p in sources}
            for name in ("bin/hol", "bin/hol.state0", "bin/Holmake"):
                report["inputs"][str(repo / name)] = a.seal(repo / name)
            report["head"] = a.git(repo, "rev-parse", "HEAD")
            env = {k: v for k, v in os.environ.items() if not k.startswith(
                ("LD_", "HOL", "POLY", "ML", "TASK29_"))}
            env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
            with a.serial_lock(repo) as fds:
                def run(command, cwd=repo):
                    receipt = loading.execute(command, cwd, env,
                                              args.timeout, fds)
                    report["commands"].append(receipt)
                    a.require(receipt["exit"] == 0 and
                              not receipt["timed_out"],
                              "failed probe command: " + str(command))
                    return receipt

                before = loading.library_inputs(run(
                    ["ldd", str(repo / "bin/hol")]))
                report["libraries"] = before
                lib = admit_library(before)  # BEFORE compiling/loading shim
                tools = {}
                for name in ("g++", "ldd", "objdump"):
                    tool = shutil.which(name, path=env["PATH"])
                    a.require(tool is not None, "missing probe tool: " + name)
                    tools[name] = tool
                    report["inputs"][tool] = a.seal(tool)
                compiler = Path(tools["g++"])
                run([str(compiler), "--version"])
                report["disassembly"] = run([
                    "objdump", "-d", "--disassemble=" + SYMBOL, lib])
                a.require("<" + SYMBOL + ">:" in
                          report["disassembly"]["stdout"],
                          "missing reviewed private profiler symbol")
                with tempfile.TemporaryDirectory(prefix="task29-profiler-") \
                        as tmp:
                    dst = Path(tmp)
                    copied = {}
                    for source in fixture.iterdir():
                        target = dst / source.name
                        shutil.copyfile(source, target)
                        copied[str(target)] = report["inputs"][str(source)]
                    loading.check_seals(copied)
                    shim = dst / "unknown_pc.so"
                    run([str(compiler), "-shared", "-fPIC", "-O2",
                         "-Wl,-z,defs", str(dst / "unknown_pc.cpp"), lib,
                         "-o", str(shim)])
                    report["shim"] = a.seal(shim)
                    shim_libs = loading.library_inputs(run(["ldd", str(shim)]))
                    a.require(admit_library(shim_libs) == lib,
                              "shim resolves a different libpolyml")
                    report["shim_libraries"] = shim_libs
                    run([str(repo / "bin/Holmake"), "--no-project",
                         "--no-cache", "--no_prereqs", "--holstate=" +
                         str(repo / "bin/hol.state0"), "-C", str(dst),
                         "-j1", "profiler-probe.exe"])
                    report["launcher"] = a.seal(dst / "profiler-probe.exe")
                    env["TASK29_PROFILER_SHIM"] = str(shim)
                    result = run([str(dst / "profiler-probe.exe"),
                                  "--gcthreads=1"], dst)
                    report["observations"] = observations(result["stdout"])
                    loading.check_seals(copied)
                after = loading.library_inputs(run(
                    ["ldd", str(repo / "bin/hol")]))
                a.require(after == before,
                          "runtime library resolution changed")
                for raw, info in before.items():
                    a.require(str(Path(raw).resolve(strict=True)) ==
                              info["resolved"] and a.seal(raw) == {
                                  k: info[k] for k in ("bytes", "sha256")},
                              "runtime library changed: " + raw)
                loading.check_seals(report["inputs"])
            report["success"] = True
            report["finding"] = (
                "unknown-PC profiler counts events, not requested words; "
                "displayed totals are not a cumulative allocator counter")
        except Exception as error:
            report["failure"] = str(error)
        finally:
            json.dump(report, stream, indent=2, allow_nan=False)
            stream.write("\n")
    print(report.get("finding", report.get("failure")))
    return 0 if report["success"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
