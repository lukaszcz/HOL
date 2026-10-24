#!/usr/bin/env python3
"""TASK28 strict per-workload measurement machinery, not release approval."""
import argparse
from contextlib import contextmanager
import fcntl
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
from statistics import median
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from performance_schema import require
from summarize import interval, summarize
from audit_evidence import audit

BASE = "cccaa27d7099cbadc886983020cbe745db7793f3"
SIZES = (0, 1, 10, 100, 1000, 10000)
POLICY = {
    "minimum_pairs": 10, "outliers": "none removed",
    "estimator": "median of paired candidate/baseline ratios",
    "bootstrap": "20000 paired resamples; seed 3003; ranks 499/19499",
    "decision": "low > 1: fail; high <= 1: pass; otherwise inconclusive",
    "zero_denominator": "inconclusive, including 0/0; no pairs dropped",
    "budgets": None,
}


class Blocked(ValueError):
    """A required prerequisite is absent, not a successful measurement."""


def seal(path):
    path = Path(path)
    data = path.read_bytes()
    return {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}


def load(path):
    path = Path(path)
    data = path.read_bytes()
    if path.suffix == ".gz":
        data = gzip.decompress(data)
    return json.loads(data)


def save(path, value):
    with Path(path).open("x") as stream:
        json.dump(value, stream, indent=2, allow_nan=False)
        stream.write("\n")


def git(root, *args):
    p = subprocess.run(["git", "-C", str(root), *args], text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       check=True)
    return p.stdout.strip()


@contextmanager
def serial_lock(repo):
    """Host-wide and existing-runner gitdir locks; never unlink lock inodes.

    This is advisory: the caller must also stop unrelated builds/runners.
    Children inherit these descriptors, so killing the parent cannot unlock a
    still-running benchmark. Do not independently relock them in children.
    """
    repo = Path(repo).resolve(strict=True)
    paths = [Path("/tmp") / ("hol4-performance-%d.lock" % os.getuid())]
    for option in ("--absolute-git-dir", "--git-common-dir"):
        raw = Path(git(repo, "rev-parse", option))
        path = (repo / raw).resolve()
        if path not in paths:
            paths.append(path)
    fds = []
    try:
        inherited = [int(fd) for fd in
                     os.environ.get("HOL4_PERF_LOCK_FDS", "").split(",")
                     if fd]
        for i, path in enumerate(paths):
            flags = os.O_RDWR | os.O_CREAT if i == 0 else os.O_RDONLY
            fd = None
            for parent in inherited:
                inherited_stat, expected_stat = os.fstat(parent), path.stat()
                if (inherited_stat.st_dev, inherited_stat.st_ino) == \
                        (expected_stat.st_dev, expected_stat.st_ino):
                    fd = os.dup(parent)
                    break
            if fd is None:
                fd = os.open(path, flags | os.O_NOFOLLOW, 0o600)
            fds.append(fd)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise Blocked("performance/build lock busy: " + str(path)) \
                    from error
        yield tuple(fds)
    finally:
        for fd in reversed(fds):
            os.close(fd)


def decision(low, high):
    require(math.isfinite(low) and math.isfinite(high) and
            0 <= low <= high, "invalid confidence interval")
    return "fail" if low > 1 else "pass" if high <= 1 else "inconclusive"


def paired_statistics(observations):
    """One observation per fresh process pair; no sample/pair filtering."""
    require(len(observations) >= 10, "acceptance requires >=10 pairs")
    for row in observations:
        require(set(row) == {"baseline", "candidate"}, "incomplete pair")
        require(all(type(v) in (int, float) and math.isfinite(v) and v >= 0
                    for v in row.values()), "invalid metric")
    ratios = [r["candidate"] / r["baseline"] if r["baseline"] else None
              for r in observations]
    require(all(r is None or math.isfinite(r) for r in ratios),
            "nonfinite paired ratio")
    ci = interval(ratios) if None not in ratios else None
    return {
        "observations": observations,
        "baseline_median": median(r["baseline"] for r in observations),
        "candidate_median": median(r["candidate"] for r in observations),
        "paired_ratios": ratios,
        "median_paired_ratio": median(ratios) if ci else None,
        "paired_ratio_bootstrap_95_percent": ci,
        "decision": decision(*ci) if ci else "inconclusive",
        "reason": "paired bootstrap" if ci else "zero baseline metric",
    }


def safe_child(folder, name):
    require(isinstance(name, str) and name and not Path(name).is_absolute(),
            "invalid evidence path")
    path = (folder / name).resolve(strict=True)
    require(path.is_relative_to(folder.resolve()) and path.is_file(),
            "evidence path escapes experiment")
    return path


def archive_protocol(manifest, receipt):
    """Replay ordered inventories without needing deleted private trees."""
    side = receipt["selection"]
    selected = manifest["selections"][side]
    private, repo = selected["private"], manifest["repo"]
    events = receipt["result"]["events"]
    require(events[2] == ["holdir", repo, repo] and
            len(events[3]) == 2 and events[3][0] == "preloaded",
            "wrong archived loader header")
    names = {Path(s["git_path"]).stem for s in selected["sources"]}
    require(not (names & set(events[3][1].split(","))),
            "selected implementation preloaded in shared heap")
    index, heaps = 4, []
    while index < len(events) and events[index][0] == "heapfile":
        require(len(events[index]) == 2, "invalid heap inventory")
        heaps.append(events[index][1])
        index += 1
    require(heaps and len(set(heaps)) == len(heaps),
            "missing/duplicate heap inventory")
    require(events[index:index + 2] == [["search", private],
            ["search", str(Path(repo) / "sigobj")]], "wrong search paths")
    used, completed, loaded, pending, loading = [], [], [], None, False
    for event in events[index + 2:-1]:
        kind = event[0]
        if kind == "use":
            require(not loading and len(event) == 2 and pending is None,
                    "unordered archived source use")
            pending = event[1]
            used.append(pending)
        elif kind == "used":
            require(not loading and len(event) == 2 and pending == event[1],
                    "unmatched archived source completion")
            completed.append(pending)
            pending = None
        elif kind in ("observation", "check"):
            require(not loading, "observations after loaded inventory")
        elif kind == "loaded":
            require(len(event) == 2, "invalid loaded inventory")
            loading = True
            loaded.append(event[1])
        else:
            raise ValueError("unknown archived event: " + kind)
    require(pending is None and loaded and len(set(loaded)) == len(loaded) and
            set(loaded) == set(heaps + completed) and
            set(receipt["result"]["paths"]) == set(used + loaded),
            "incomplete archived source inventory")
    require(str(Path(private) / "Performance.sml") in completed,
            "matrix fixture never completed")


def analyze(folder, *, case, size, baseline, candidate, pairs, samples,
            seconds, iterations=None):
    """Revalidate complete protocol and source binding before statistics."""
    folder = Path(folder)
    manifest = load(folder / "manifest.json")
    require(manifest["success"] is True, "failed experiment")
    options = manifest["performance"]
    require(pairs >= 10 and options["pairs"] == pairs and
            options["samples"] == samples and
            options["batch_seconds"] == seconds and
            options["suite"] == "matrix" and options["case"] == case and
            options["size"] == size, "wrong matrix/timing options")
    require(options.get("outliers") == "none removed", "changed outlier rule")
    require(options.get("batch_iterations") == iterations,
            "wrong predeclared batch iterations")
    for side, pin in (("baseline", baseline), ("candidate", candidate)):
        require(manifest["selections"][side]["revision"] == pin,
                "wrong selected revision")
    require(manifest.get("inputs") and manifest.get("tools"),
            "missing input/tool hashes")
    seen, order, graph_rows, runtime_rows = set(), [], {}, {}
    for run in manifest["runs"]:
        path = safe_child(folder, run["receipt"])
        require(path not in seen, "duplicate receipt")
        seen.add(path)
        receipt = load(path)
        require(run["accepted"] is True and receipt["accepted"] is True and
                run["exit"] == receipt["exit"] == 0 and
                receipt.get("control", "none") == "none",
                "failed or negative-control process in acceptance")
        if receipt["fixture"] != "performance":
            continue
        audit(manifest, receipt)
        archive_protocol(manifest, receipt)
        side = receipt["selection"]
        fixture = manifest["selections"][side]["fixture_products"]
        names = ["src/simp/tests/performance/" + name for name in
                 ("MatrixPerformance.sml", "ClientPerformance.sml")]
        require(any(fixture["Performance.sml"] == manifest["inputs"].get(name)
                    for name in names), "wrong matrix fixture binding")
        env = receipt["environment"]
        require(env["PERF_CASE"] == case and int(env["PERF_SIZE"]) == size,
                "wrong matrix process parameters")
        order.append([receipt["pair"], side])
        runtime_rows.setdefault(receipt["pair"], {})[side] = receipt["runtime"]
        if case == "storage_graph":
            graph_rows.setdefault(receipt["pair"], {})[side] = \
                receipt["storage_graph"][0]
    expected = [[i, side] for i in range(pairs) for side in
                (("candidate", "baseline") if i % 2 else
                 ("baseline", "candidate"))]
    require(order == expected, "missing/reordered fresh-process pair")
    summary = summarize(folder)
    require(set(summary["workloads"]) == {case}, "wrong matrix labels")
    metrics = {}
    for metric in ("cpu", "wall", "gc"):
        rows = summary["workloads"][case][metric]
        metrics[metric] = paired_statistics(
            rows["seconds_per_operation_by_pair"])
    for field in ("compiled_increment", "fragment_increment"):
        if case == "storage_graph":
            metrics[field + "_words"] = paired_statistics([
                {side: graph_rows[i][side][field]
                 for side in ("baseline", "candidate")}
                for i in range(pairs)])
    return {"mode": "isolated", "case": case, "size": size,
            "scope": "shared dependencies; NOT independent builds",
            "inputs": summary["inputs"], "options": options,
            "policy": POLICY, "metrics": metrics,
            "runtime_by_pair": runtime_rows,
            "allocation": "uncollected: runtime exposes no cumulative counter",
            "temporary_peaks": "uncollected: process HWM is not a batch peak"}


def apply_control(data, control):
    """A failed/uncertain control cannot establish parity; never excuse fail."""
    data["control_decision"] = control["decision"]
    if control["decision"] != "pass" and data["decision"] != "fail":
        data["decision"] = "inconclusive"
        data["reason"] = "baseline-control " + control["decision"]


def retained_scaling(workloads):
    """All adjacent graph differences, never a fitted/averaged budget."""
    rows = {row["candidate"]["size"]: row for row in workloads
            if row["candidate"]["case"] == "storage_graph"}
    if not rows:
        return None
    missing = sorted(set(SIZES) - rows.keys())
    if missing:
        return {"status": "blocked", "missing_sizes": missing,
                "reason": "storage slope requires the complete six-size grid"}
    result = []
    for lower, upper in zip(SIZES, SIZES[1:]):
        for selection in ("control", "candidate"):
            for metric in ("compiled_increment_words",
                           "fragment_increment_words"):
                left = rows[lower][selection]["metrics"][metric]["observations"]
                right = rows[upper][selection]["metrics"][metric]["observations"]
                require(len(left) == len(right), "incomplete storage slope pairs")
                slopes = [{side: (b[side] - a[side]) / (upper - lower)
                           for side in ("baseline", "candidate")}
                          for a, b in zip(left, right)]
                stats = (paired_statistics(slopes) if all(
                    v >= 0 for row in slopes for v in row.values()) else
                    {"decision": "inconclusive", "observations": slopes,
                     "reason": "nonmonotonic retained graph; inspect raw roots"})
                result.append(dict(lower=lower, upper=upper,
                                   selection=selection, metric=metric,
                                   words_per_rule=stats))
    controls = {(r["lower"], r["upper"], r["metric"]): r["words_per_rule"]
                for r in result if r["selection"] == "control"}
    for row in result:
        if row["selection"] == "candidate":
            apply_control(row["words_per_rule"], controls[
                row["lower"], row["upper"], row["metric"]])
    return {"status": "measured", "adjacent_intervals": result,
            "constant_terms": "see separate size-zero per-workload decisions"}


def report_exit_status(report):
    """Include every requested gate; protocol success is not performance pass."""
    if not report["success"]:
        return 2
    decisions = [m["decision"] for r in report["workloads"]
                 for m in r["candidate"]["metrics"].values()]
    scaling = report.get("retained_scaling")
    if scaling is not None:
        if scaling["status"] != "measured":
            decisions.append("inconclusive")
        else:
            decisions.extend(r["words_per_rule"]["decision"]
                             for r in scaling["adjacent_intervals"]
                             if r["selection"] == "candidate")
    require(decisions and all(d in ("pass", "fail", "inconclusive")
                              for d in decisions), "missing/invalid decisions")
    return 1 if "fail" in decisions else \
        2 if "inconclusive" in decisions else 0


def control_worker(kind):
    """Real process-only perturbations; never modify HOL production sources."""
    if kind == "missing":
        return 0
    import tracemalloc
    tracemalloc.start()
    count = 2 * 1024 * 1024 if kind == "allocation" else 16384
    data = bytearray(b"x") * count
    allocated, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    start_wall, start_cpu = time.perf_counter(), time.process_time()
    duration = 0.015 if kind == "slowdown" else 0.003
    consumed = 0
    while time.process_time() - start_cpu < duration:
        consumed += 1
    cpu = time.process_time() - start_cpu
    wall = time.perf_counter() - start_wall
    result = dict(protocol="task28-control-v1", consumed=consumed,
                  verified=sum(data) == 120 * count, cpu=cpu, wall=wall,
                  allocation_bytes=allocated, peak_bytes=peak)
    print(json.dumps(result), flush=True)
    return 7 if kind == "failed" else 0


def parse_control(process):
    require(process.returncode == 0, "failed control process")
    require(bool(process.stdout.strip()), "missing control result")
    record = json.loads(process.stdout)
    require(record["protocol"] == "task28-control-v1" and
            record["verified"] is True and
            type(record["consumed"]) is int and record["consumed"] > 0,
            "unverified control result")
    for key in ("cpu", "wall", "allocation_bytes", "peak_bytes"):
        value = record[key]
        require(type(value) in (float, int) and math.isfinite(value) and
                value > 0, "invalid control measurement")
    return record


def negative_controls(pairs=10):
    require(pairs >= 10, "controls require >=10 pairs")

    processes = []

    def launch(kind):
        command = [sys.executable, str(Path(__file__).resolve()),
                   "_control-worker", kind]
        process = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, timeout=10)
        processes.append({"argv": command, "exit": process.returncode,
                          "stdout": process.stdout, "stderr": process.stderr})
        return process

    rows = {kind: [] for kind in ("slowdown", "allocation")}
    for kind in rows:
        for i in range(pairs):
            values = {}
            order = ("baseline", "candidate") if i % 2 == 0 else \
                ("candidate", "baseline")
            for side in order:
                values[side] = parse_control(launch(
                    kind if side == "candidate" else "baseline"))
            metric = "cpu" if kind == "slowdown" else "allocation_bytes"
            rows[kind].append({s: r[metric] for s, r in values.items()})
    report = {k: paired_statistics(v) for k, v in rows.items()}
    for kind in rows:
        require(report[kind]["decision"] == "fail",
                "negative control missed intended regression: " + kind)
    for kind, message in (("failed", "failed control process"),
                          ("missing", "missing control result")):
        try:
            parse_control(launch(kind))
        except ValueError as error:
            require(str(error) == message, "control hit wrong guard")
            report[kind] = {"detected": True, "rejection": str(error)}
        else:
            raise ValueError("negative control accepted: " + kind)
    return {"scope": "harness-only real subprocess controls, not HOL data",
            "policy": POLICY, "controls": report, "processes": processes}


def exact_pin(pin):
    require(isinstance(pin, str) and re.fullmatch(r"[0-9a-f]{40}", pin),
            "require exact full git pin")


def clean_root(root, pin, *, pristine=False):
    root = Path(root).resolve(strict=True)
    exact_pin(pin)
    require(git(root, "rev-parse", "--show-toplevel") == str(root),
            "not a worktree root")
    require(git(root, "rev-parse", "HEAD") == pin, "worktree pin changed")
    args = ["status", "--porcelain=v1", "--untracked-files=all"]
    if pristine:
        args.append("--ignored=matching")
    require(not git(root, *args), "worktree is not clean/fresh")
    return root


def contained(root, raw):
    path = Path(raw)
    require(path.is_absolute(), "require absolute build path")
    resolved = path.resolve(strict=True)
    require(resolved.is_relative_to(root) and resolved.is_file(),
            "build product outside selected root")
    return resolved


def verify_builds(path, baseline, candidate):
    """Fail-closed live prerequisite audit, NOT independent performance data.

    A build receipt is a local provenance record, not a cryptographic proof
    against a malicious producer. Keep roots and logs until this audit runs.
    """
    document = load(path)
    require(document["schema"] == "task28-independent-build-v1" and
            document["mode"] == "independent" and
            document["success"] is True, "not successful independent builds")
    require(set(document["selections"]) == {"baseline", "candidate"},
            "missing independent build selection")
    require(document["runtime_options"] == ["--gcthreads=1"],
            "different runtime/thread options")
    tools = document["toolchain"]
    require(set(tools) >= {"poly"}, "missing toolchain hashes")
    for info in tools.values():
        require(Path(info["path"]).is_absolute() and
                seal(info["path"]) == info["fingerprint"], "changed toolchain")
    require(isinstance(tools["poly"]["version"], str) and
            tools["poly"]["version"].strip(),
            "missing compiler/runtime version")
    version = subprocess.run([tools["poly"]["path"], "--version"],
                             text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=10)
    require(version.returncode == 0 and
            version.stdout.strip() == tools["poly"]["version"] and
            version.stdout.startswith("Poly/ML"),
            "compiler/runtime version changed")
    roots, products, logs, commands = [], [], set(), []
    previous_build_end = 0
    for side, pin in (("baseline", baseline), ("candidate", candidate)):
        selected = document["selections"][side]
        require(selected["pin"] == pin, "wrong independent pin")
        root = Path(selected["root"]).resolve(strict=True)
        require(all(not root.is_relative_to(r) and
                    not r.is_relative_to(root) for r in roots),
                "shared/nested independent roots")
        root = clean_root(root, pin)
        roots.append(root)
        require(selected["fresh_before"] is True and
                selected["status_before"] == "" and
                selected["ignored_before"] == "", "not fresh before build")
        start, end = selected["start_ns"], selected["end_ns"]
        require(type(start) is int and type(end) is int and
                previous_build_end <= start <= end <= time.time_ns() and
                start > 0, "invalid/overlapping build times")
        previous_build_end = end
        steps = selected["commands"]
        require([s["phase"] for s in steps] == ["configure", "full"],
                "missing configure/full build commands")
        expected = [[tools["poly"]["path"]],
                    [str(root / "bin/build"), "-t", "-F"]]
        previous = start
        normalized = []
        for step, argv in zip(steps, expected):
            require(step["argv"] == argv and step["cwd"] == str(root) and
                    step["exit"] == 0 and step["timed_out"] is False,
                    "failed/wrong build command")
            require(previous <= step["start_ns"] <= step["end_ns"] <= end,
                    "unordered build command times")
            previous = step["end_ns"]
            require(seal(argv[0]) == step["executable_hash"],
                    "changed build executable")
            stdin = str(root / "tools/smart-configure.sml") \
                if step["phase"] == "configure" else None
            require(step["stdin"] == stdin, "wrong configure input")
            if stdin:
                require(seal(stdin) == step["stdin_hash"],
                        "changed configure input")
            log = Path(step["log"])
            require(log.is_absolute() and log.is_file() and
                    not log.is_symlink() and log.resolve() not in logs and
                    seal(log) == step["log_hash"], "missing/changed build log")
            logs.add(log.resolve())
            require(not any(log.resolve().is_relative_to(r) for r in roots),
                    "build logs must be outside roots")
            normalized.append([step["phase"], Path(argv[0]).name, argv[1:]])
        commands.append(normalized)
        artifacts = selected["products"]
        require(set(artifacts) >= {"bin/hol", "bin/hol.state0", "bin/Holmake",
                                   "bin/hol.state.min", "holproject.toml"},
                "missing fresh runtime/heap/Holmake products")
        require(any(n.startswith("sigobj/") for n in artifacts),
                "missing independent dependency products")
        for name, info in artifacts.items():
            require(not Path(name).is_absolute() and
                    ".." not in Path(name).parts,
                    "invalid product name")
            product = contained(root, info["path"])
            require(Path(info["path"]) == root / name and
                    str(product) == info["physical"] and
                    seal(product) == info["hash"],
                    "wrong/changed build product")
            stat = product.stat()
            require(start <= stat.st_mtime_ns <= end and
                    stat.st_mtime_ns == info["mtime_ns"],
                    "stale build product")
            require(all(not os.path.samefile(product, old)
                        for old in products),
                    "shared independent product inode")
            products.append(product)
        require(set(selected["dependency_inventory"]) ==
                {n for n in artifacts if n.startswith("sigobj/")},
                "incomplete dependency inventory")
        actual = {str(p.relative_to(root))
                  for p in (root / "sigobj").rglob("*")
                  if (p.is_file() or p.is_symlink()) and
                  p.suffix in (".uo", ".ui", ".dat")}
        require(actual == set(selected["dependency_inventory"]),
                "unrecorded/stale dependency product")
    require(commands[0] == commands[1], "different build flags/toolchain")
    require(all(not log.is_relative_to(root)
                for log in logs for root in roots),
            "build log in selected root")
    return {"mode": "independent", "build_prerequisites": "verified",
            "manifest": str(Path(path).resolve()), "hash": seal(path),
            "performance": "blocked",
            "required_input": "TASK32/33 fresh independent launchers, loaded-"
            "path inventories, consumed proof/storage observations and pairs; "
            "shared run_paired results cannot satisfy this prerequisite"}


def run_logged(command, output, fds, timeout):
    expired = False
    code = None
    with Path(output).open("x") as stream:
        env = dict(os.environ, HOL4_PERF_LOCK_FDS=",".join(map(str, fds)))
        p = subprocess.Popen(command, stdout=stream, stderr=subprocess.STDOUT,
                             pass_fds=fds, env=env, start_new_session=True)
        try:
            code = p.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            expired = True
            os.killpg(p.pid, signal.SIGKILL)
            code = p.wait()
        except BaseException:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()
            raise
    return {"argv": command, "exit": code, "timed_out": expired,
            "log": str(output), "log_hash": seal(output)}


def run(args):
    require(args.pairs >= 10 and args.samples >= 3 and
            0.1 <= args.batch_seconds <= 60 and args.timeout > 0,
            "require >=10 pairs, >=3 samples, 0.1..60s batches, timeout >0")
    iterations = getattr(args, "batch_iterations", None)
    if iterations is not None:
        from performance_schema import batch_iterations
        batch_iterations(iterations)
    exact_pin(args.baseline)
    exact_pin(args.candidate)
    require(args.authorize_measurements,
            "require exclusive build/measurement window authorization")
    require(args.case and len(args.case) == len(set(args.case)) and
            all(re.fullmatch(r"[a-z][a-z0-9_]*", c) for c in args.case),
            "require unique safe matrix cases")
    sizes = args.size or [1000]
    require(len(set(sizes)) == len(sizes) and all(n in SIZES for n in sizes),
            "invalid/duplicate matrix sizes")
    output = args.output.resolve()
    with serial_lock(args.repo) as fds:
        output.mkdir(parents=True, exist_ok=False)
        report = {"schema": "task28-acceptance-v1", "mode": args.mode,
                  "success": False, "policy": POLICY, "commands": [],
                  "workloads": [], "claims": "not final release acceptance"}
        try:
            if args.mode == "independent":
                if not args.build_manifest:
                    raise Blocked("independent clean-build manifest required")
                report["independent"] = verify_builds(
                    args.build_manifest, args.baseline, args.candidate)
                raise Blocked(report["independent"]["required_input"])
            report["negative_controls"] = negative_controls()
            from matrix_schema import get_case, load_matrix
            matrix = load_matrix()
            for case in args.case:
                require(case in matrix["cases"], "unknown matrix case")
                grid = matrix["size_sets"][matrix["cases"][case]["sizes"]]
                selected_sizes = args.size or [1000 if 1000 in grid else grid[-1]]
                for size in selected_sizes:
                    get_case(case, size)
                    results = {}
                    for control in (True, False):
                        tag = case + "-" + str(size) + \
                            ("-control" if control else "-candidate")
                        folder = output / tag
                        candidate = (args.baseline if control else
                                     args.candidate)
                        command = [sys.executable, str(HERE.parent /
                                   "compatibility/run_paired.py"),
                                   "--repo", str(args.repo.resolve()),
                                   "--baseline", args.baseline,
                                   "--candidate", candidate,
                                   "--candidate-signature", "pass",
                                   "--candidate-behavior", "baseline",
                                   "--matrix-performance",
                                   "--performance-case",
                                   case, "--performance-size", str(size),
                                   "--performance-pairs", str(args.pairs),
                                   "--samples", str(args.samples),
                                   "--batch-seconds", str(args.batch_seconds),
                                   "--timeout", str(args.timeout),
                                   "--output", str(folder)]
                        if iterations is not None:
                            command += ["--batch-iterations", str(iterations)]
                        command_result = run_logged(
                            command, output / (tag + ".log"), fds, None)
                        report["commands"].append(command_result)
                        require(command_result["exit"] == 0 and
                                not command_result.get("timed_out", False),
                                "runner failed; see " + str(output /
                                                           (tag + ".log")))
                        key = "control" if control else "candidate"
                        results[key] = analyze(
                            folder, case=case, size=size,
                            baseline=args.baseline,
                            candidate=candidate, pairs=args.pairs,
                            samples=args.samples, seconds=args.batch_seconds,
                            iterations=iterations)
                    # Controls are never subtracted as a noise budget.
                    metrics = results["candidate"]["metrics"]
                    for metric, data in metrics.items():
                        check = results["control"]["metrics"][metric]
                        apply_control(data, check)
                    report["workloads"].append(results)
            report["retained_scaling"] = (
                retained_scaling(report["workloads"])
                if "storage_graph" in args.case else None)
            report["success"] = True
        except Blocked as error:
            report["blocked"] = str(error)
        except (ValueError, OSError, KeyError, IndexError, TypeError,
                subprocess.SubprocessError) as error:
            report["failure"] = str(error)
        finally:
            save(output / "acceptance.json", report)
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    worker = sub.add_parser("_control-worker", help=argparse.SUPPRESS)
    worker.add_argument("kind", choices=("baseline", "slowdown", "allocation",
                                        "missing", "failed"))
    controls = sub.add_parser("controls")
    controls.add_argument("--repo", type=Path, default=HERE.parents[3])
    controls.add_argument("--output", type=Path, required=True)
    verify = sub.add_parser("verify-builds")
    verify.add_argument("manifest", type=Path)
    verify.add_argument("--baseline", default=BASE)
    verify.add_argument("--candidate", required=True)
    execute = sub.add_parser("run")
    execute.add_argument("--repo", type=Path, default=HERE.parents[3])
    execute.add_argument("--mode", choices=("isolated", "independent"),
                         default="isolated")
    execute.add_argument("--build-manifest", type=Path)
    execute.add_argument("--baseline", default=BASE)
    execute.add_argument("--candidate", required=True)
    execute.add_argument("--case", action="append", required=True)
    execute.add_argument("--size", type=int, action="append")
    execute.add_argument("--pairs", type=int, default=10)
    execute.add_argument("--samples", type=int, default=5)
    execute.add_argument("--batch-seconds", type=float, default=0.2)
    execute.add_argument("--batch-iterations", type=int,
                         help="common predeclared power-of-two matrix count")
    execute.add_argument("--timeout", type=int, default=1800)
    execute.add_argument("--output", type=Path, required=True)
    execute.add_argument("--authorize-measurements", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.action == "_control-worker":
            return control_worker(args.kind)
        if args.action == "verify-builds":
            print(json.dumps(verify_builds(args.manifest, args.baseline,
                                          args.candidate), indent=2))
            return 0
        if args.action == "controls":
            with serial_lock(args.repo):
                save(args.output, negative_controls())
            return 0
        result = run(args)
        print(args.output / "acceptance.json")
        return report_exit_status(result)
    except (ValueError, OSError, KeyError, IndexError, TypeError,
            subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
