#!/usr/bin/env python3
"""Fresh ordinary first-import timing; NOT independent/release approval."""
import argparse
import functools
import gzip
import hashlib
import importlib.util
import itertools
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import uuid

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "compatibility"))
import acceptance as a
import performance_schema as ps
import run_paired as rp


# `timing_grid` is imported inside the functions that need it, never at the
# top: `allocation_matrix` imports this module, the allocation harness does
# not list timing_grid.py among its inputs, and timing_grid imports this
# module itself (through private_runtime).


def require(ok, message):
    rp.require(ok, message)


MODULES = ("simpLib", "congLib")
FIELDS = ("wall", "nongc_usr", "nongc_sys", "gc_usr", "gc_sys",
          "cpu_usr", "cpu_sys", "gc_user_only")
METRICS = ("wall", "cpu", "gc_cpu")
# Loading unit: every sample is the mean of REPS first imports, each in
# its own fresh process; a module is never loaded twice in one process.
REPS = 5
PAIRS = 40
SCHEMA = "task31-loading-v4"
POLICY = a.EQUIVALENCE_POLICY  # the timing grid's 3% margin, one definition
# Code-layout randomization: a predeclared seed; the second stage draws from
# its own seed. The padding of each process derives from (seed, rep, pair,
# side) with `performance_schema.layout_units`, as the matrix runner does.
LAYOUT_SEED = "task31-loading"
EXTENSION_SEED = LAYOUT_SEED + "-ext"
# A smoke run checks the harness and nothing else: at most this many pairs of
# this many fresh imports, and never the seed of a decision run.
SMOKE_PAIRS, SMOKE_REPS = 2, 1
SMOKE_SEED = LAYOUT_SEED + "-smoke"
# The first stage is sized for a per-unit log sd (the sd of the paired log
# ratio times sqrt(R)) of at most this much: PAIRS * REPS >= required_units.
UNIT_SD_BOUND = 0.08
# Variance model of a sample that is the mean of R processes (see
# PROTOCOL_LOADING.md): the 95% interval half width of the median of n paired
# log ratios of sd s is about Z95 * MEDIAN_FACTOR * s / sqrt(n).
Z95 = 1.959964
MEDIAN_FACTOR = math.sqrt(math.pi / 2)
AUDIT = HERE.parent / "api-audit"


def audit_constants(audit_dir):
    """The API audit's constants module of `audit_dir` (the one run.py
    imports), loaded by path."""
    spec = importlib.util.spec_from_file_location(
        "loading_audit_constants", Path(audit_dir) / "audit_constants.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def audit_forbidden_names(audit_dir=AUDIT):
    """The names the audit's selftest.sml forbids: the one definition."""
    text = (Path(audit_dir) / "selftest.sml").read_text()
    match = re.search(r"val forbidden_names\s*=\s*\[(.*?)\]", text, re.S)
    require(match is not None, "no forbidden_names in the API audit")
    names = tuple(re.findall(r'"([^"]+)"', match[1]))
    require(names, "empty forbidden_names in the API audit")
    return names


@functools.lru_cache(maxsize=None)
def extension_names():
    """Names that no ordinary import may load (patterns catch the rest):
    the audit's list, read on first use and not when this module is
    imported."""
    return audit_forbidden_names()


# Stems a candidate process may load although no baseline process does:
# a reviewed allowance, empty unless the source design requires otherwise.
STEM_ALLOWANCE = frozenset()
NO_EXTENSIONS = "none"


def extension_name(name):
    return (name in extension_names() or name.endswith(("Ext", "ExtLib"))
            or name.startswith("simpMarker"))


# The loading call is a top-level runner operation, NOT inside a pending
# traced selftest use. Thus nested source uses never defeat rp.validate.
TIMING_TEMPLATE = '''fun loadingMeasure f = let
  val cpu = Timer.startCPUTimer ()
  val wall = Timer.startRealTimer ()
  val _ = f ()
  val {nongc={usr,sys},gc={usr=gu,sys=gs}} = Timer.checkCPUTimes cpu
  val {usr=cu,sys=cs} = Timer.checkCPUTimer cpu
  val gc = Timer.checkGCTime cpu
  val elapsed = Timer.checkRealTimer wall
in map Time.toReal [elapsed,usr,sys,gu,gs,cu,cs,gc] end
fun loadingEmit key xs = Paired.observe key
  (String.concatWith "," (map (Real.fmt (StringCvt.SCI (SOME 12))) xs))
val loadingProbe = [@PROBE@]
fun loadingForbidden n = List.exists (fn m => m = n) loadingProbe orelse
  String.isSuffix "Ext" n orelse String.isSuffix "ExtLib" n orelse
  String.isPrefix "simpMarker" n
fun loadingExtensions () = let
  val files = map (fn (f, _) => OS.Path.base f)
    (Binarymap.listItems (Meta.fileDirMap ()))
  val bound = map #1 (#allStruct PolyML.globalNameSpace ())
  val found = List.filter loadingForbidden (Meta.loaded () @ files @ bound)
  fun add (x, acc) = if List.exists (fn y => y = x) acc then acc
                     else acc @ [x]
  val unique = List.foldl add [] found
in case unique of [] => "@NONE@"
                      | xs => String.concatWith "," xs end
fun loadingImport () = let
  val name = Paired.env "LOADING_MODULE"
  val _ = if List.exists (fn n => n = "simpLib" orelse n = "congLib")
              (Meta.loaded ()) then raise Fail "ordinary library preloaded"
          else ()
  val _ = loadingEmit "timer.accounting"
    (loadingMeasure (fn () => PolyML.fullGC ()))
  val _ = loadingEmit "timer.empty" (loadingMeasure (fn () => ()))
  val _ = Paired.observe "loading.begin" name
  val data = loadingMeasure (fn () => Meta.loadPlan tracedUse name)
  val _ = Paired.observe "loading.end" name
  val _ = loadingEmit "loading.raw" data
in Paired.observe "loading.extensions" (loadingExtensions ()) end
'''


def timing_source():
    """The timing code inserted into the runner, with the audit's names."""
    return TIMING_TEMPLATE.replace("@PROBE@", ", ".join(
        '"%s"' % n for n in extension_names())).replace(
            "@NONE@", NO_EXTENSIONS)


VERIFY = '''open HolKernel
val p = mk_var ("loading_p",bool)
val input = boolSyntax.mk_conj (boolSyntax.T,p)
val rules = [boolTheory.AND_CLAUSES]
val proof = simpLib.SIMP_CONV pureSimps.pure_ss rules input
val expected = boolSyntax.mk_eq (input,p)
fun valid th = aconv (concl th) expected andalso null (hyp th)
val _ = Paired.check "ordinary exact kernel equality" (valid proof)
'''
VERIFY_CONG = '''val proof = congLib.CONGRUENCE_EQ_SIMP_CONV
  congLib.empty_congset pureSimps.pure_ss rules input
val _ = Paired.check "congruence exact kernel equality" (valid proof)
'''


def plan(pairs):
    """Each pair uses two fresh processes; labels also apply to B/B."""
    return [(i, side) for i in range(pairs) for side in
            (("baseline", "candidate") if i % 2 == 0 else
             ("candidate", "baseline"))]


def schedule(pairs, reps):
    """(pair, side, rep) in execution order. A pair's sample on each side is
    `reps` fresh processes; the sides alternate inside the pair, and the
    first side alternates between pairs (AB, then BA). With one rep this is
    `plan`. Lengthening the unit adds processes, never repeated imports."""
    return [(i, side, r) for i in range(pairs) for r in range(reps)
            for side in (("baseline", "candidate") if i % 2 == 0 else
                         ("candidate", "baseline"))]


def install(dst, module):
    rp.install_fixtures(dst)
    runner = dst / "runner.sml"
    text = runner.read_text()
    anchor = "val result =\n"
    require(text.count(anchor) == 1, "runner timing insertion anchor changed")
    old = 'Meta.loadPlan tracedUse (Paired.env "PAIR_TARGET"); "pass")'
    require(text.count(old) == 1, "runner loading anchor changed")
    text = text.replace(anchor, timing_source() + anchor).replace(
        old, 'loadingImport ();\n   ' + old)
    runner.write_text(text)
    (dst / "selftest.sml").write_text(
        VERIFY + (VERIFY_CONG if module == "congLib" else ""))
    # Build only the dependency metadata for the proof; it is never linked.
    # Remove unrelated legacy signature fixtures from this launcher target.
    (dst / "Holmakefile").write_text(
        'HOLHEAP = $(HOLDIR)/bin/hol.state0\n'
        'paired.exe: runner.uo CheckSupport.uo selftest.uo\n'
        '\t$(HOLMOSMLC) -o $@ $<\n')


def numbers(value):
    fields = value.split(",")
    require(len(fields) == len(FIELDS), "wrong timer field count")
    try:
        values = [float(s.replace("~", "-")) for s in fields]
    except ValueError as error:
        raise rp.InvalidRun("invalid timer number") from error
    require(all(math.isfinite(v) and v >= 0 for v in values),
            "nonfinite/negative timer field")
    data = dict(zip(FIELDS, values))
    # The three timer reads are successive snapshots, not simultaneous.
    require(abs(data["cpu_usr"] - data["nongc_usr"] - data["gc_usr"])
            < 0.02 and
            abs(data["cpu_sys"] - data["nongc_sys"] - data["gc_sys"])
            < 0.02 and
            abs(data["gc_user_only"] - data["gc_usr"]) < 0.02,
            "timer accounting disagreement")
    data["cpu"] = data["cpu_usr"] + data["cpu_sys"]
    data["gc_cpu"] = data["gc_usr"] + data["gc_sys"]
    return data


def observations(events, module):
    obs = [e for e in events if e[0] in ("observation", "check")]
    keys = ["timer.accounting", "timer.empty", "loading.begin",
            "loading.end", "loading.raw", "loading.extensions"]
    require(len(obs) == 7 + (module == "congLib"),
            "missing/extra loading observation")
    require([e[:2] for e in obs[:6]] ==
            [["observation", key] for key in keys] and
            all(len(e) == 3 for e in obs), "wrong timer observations")
    require(obs[2][2] == obs[3][2] == module, "wrong import target")
    expected = [["check", "ordinary exact kernel equality", "pass"]]
    if module == "congLib":
        expected += [["check", "congruence exact kernel equality", "pass"]]
    require(obs[6:] == expected, "missing exact proof verification")
    start, end = events.index(obs[2]), events.index(obs[3])
    between = events[start + 1:end]
    require(between and all(e[0] in ("use", "used") for e in between),
            "invalid timed import region")
    needed = {module + ".sml", "simpLib.sml"}
    completed = {Path(e[1]).name for e in between if e[0] == "used"}
    require(needed <= completed, "actual import not inside timer")
    require(not any(e[0] in ("use", "used", "heapfile") and
                    Path(e[1]).stem in MODULES for e in events[:start]),
            "ordinary source loaded before timer")
    accounting, empty, raw = [numbers(obs[i][2]) for i in (0, 1, 4)]
    require(accounting["gc_cpu"] > 0 and accounting["gc_user_only"] > 0,
            "forced-GC accounting control did not exercise GC")
    # Operational calibration: first import cannot be batched in one process.
    # Require >=100x empty-bracket overhead AND the 1us timer granularity.
    calibrated = all(raw[k] >= 100 * max(empty[k], 1e-6)
                     for k in ("wall", "cpu"))
    reported = obs[5][2].split(",")
    require(reported == [NO_EXTENSIONS] or
            all(extension_name(n) for n in reported),
            "invalid loading.extensions observation")
    found = sorted(set(reported) - {NO_EXTENSIONS})
    # Also the sources the process actually used and the final file map.
    found = sorted(set(found) | {
        Path(e[1]).stem for e in events
        if e[0] in ("use", "used", "heapfile", "loaded") and
        extension_name(Path(e[1]).stem)})
    stems = sorted({Path(e[1]).stem for e in events
                    if e[0] in ("use", "used", "heapfile", "loaded")})
    return obs, {"raw": raw, "empty": empty, "accounting": accounting,
                 "extensions_loaded": found, "loaded_stems": stems,
                 "calibrated": calibrated,
                 "calibration_rule": "wall/cpu >=100*max(empty,1us)"}


def validate(receipt, *, side, dst, repo, names, sources, module,
             enforce_absence=False, candidate=False):
    """`enforce_absence` is for the candidate: the historical baseline need
    not satisfy the extension split, so its loaded extensions are recorded
    but never rejected. A finding in a process that is not `candidate` is a
    plain rejection (the run fails), only a candidate's is `Blocked`."""
    events = rp.parse_events(receipt["stdout"])
    obs, measurement = observations(events, module)
    measurement["extension_absence_enforced"] = bool(enforce_absence)
    if enforce_absence and measurement["extensions_loaded"]:
        raise (Blocked if candidate else ValueError)(
            "extension module loaded by an ordinary import: " +
            ",".join(measurement["extensions_loaded"]))
    contract = {"target": "selftest", "modules": list(MODULES)
                if module == "congLib" else ["simpLib"],
                "signatures": [], "observations": obs, "red": False,
                "fresh": list(MODULES)}
    result = rp.validate(
        receipt, selection=side, fixture="loading", control="none",
        private=dst, repo=repo, private_names=names, flavor="baseline",
        signature="pass", source_hashes=sources, contract=contract)
    for info in result["paths"].values():
        physical = info["physical"]
        if physical in sources:
            require({k: info[k] for k in ("bytes", "sha256")} ==
                    sources[physical], "changed sealed input")
    return result, measurement


def semantic_gate(path, repo, selected):
    """Replay the eight-process gate; bind actual imports to git bytes.

    It is candidate-only: the historical monolith need not satisfy extension
    absence. Archive paths may refer to a relocated worktree.
    """
    path = path.resolve(strict=True)
    receipt = a.load(path)
    require(receipt["pass"] is True and len(receipt["cases"]) == 8,
            "incomplete eight-process semantic gate")
    audit_dir = repo / "src/simp/tests/api-audit"
    constants = audit_constants(audit_dir)
    for name, seal in receipt["sources"].items():
        require(Path(name).name == name and a.seal(audit_dir / name) == seal,
                "semantic gate fixture changed")
    require(set(receipt["sources"]) == set(constants.SOURCES),
            "missing semantic gate source seals")
    actual_path = a.safe_child(path.parent, receipt["actual_files"]["file"])
    require(a.seal(actual_path) == receipt["actual_files"]["seal"],
            "changed semantic input inventory")
    actual = a.load(actual_path)
    require(len(actual) == receipt["actual_files"]["count"],
            "wrong semantic input count")
    expected = {Path(s["git_path"]).name:
                {k: s[k] for k in ("bytes", "sha256")} for s in selected}
    wanted = set(itertools.product(("simp-first", "cong-first"),
                                  ("attribute", "exporter"),
                                  ("before", "after")))
    used_logs = set()
    for case in receipt["cases"]:
        key = (case["order"], case["foreign_kind"], case["foreign_owner"])
        require(key in wanted, "duplicate/unknown semantic case")
        wanted.remove(key)
        count = constants.CASE_CHECKS[key[1:]]
        require(case["pass"] is True and case["returncode"] == 0 and
                case["validation_error"] is None and case["checks"] == count,
                "failed semantic process")
        log = a.safe_child(path.parent, case["log"])
        require(log not in used_logs and a.seal(log) == case["log_seal"],
                "changed/duplicate semantic log")
        used_logs.add(log)
        text = gzip.decompress(log.read_bytes()).decode()
        clean = re.sub(r"\x1b\[[0-9;]*[mCG]", "", text)
        require(text.endswith("\n") and
                text.splitlines().count("OBS result=pass") == 1 and
                clean.count("OK\n") == count and "FAILED!" not in text,
                "incomplete semantic output")
        env = case["environment"]
        require((env["API_AUDIT_ORDER"], env["API_AUDIT_KIND"],
                 env["API_AUDIT_OWNER"]) == key,
                "wrong semantic environment")
        native = Path(env["API_AUDIT_SRC"])
        used = {line.split("=", 1)[1] for line in text.splitlines()
                if line.startswith("OBS used.path=")}
        for module in constants.NATIVE_MODULES:
            for suffix in (".sig", ".sml"):
                require(str(native / (module + suffix)) in used,
                        "missing actual semantic core/extension import")
        for raw in used:
            name = Path(raw).name
            if name in expected:
                require(Path(raw) == native / name and raw in actual and
                        {k: actual[raw][k] for k in ("bytes", "sha256")} ==
                        expected[name], "semantic gate candidate mismatch")
    require(not wanted, "missing semantic scenarios")
    return {"receipt": str(path), "seal": a.seal(path),
            "actual_files": a.seal(actual_path), "cases": 8,
            "candidate_sources_bound": True}


def execute(command, cwd, env, timeout, fds):
    """Like rp.execute, but preserve serial locks in child processes."""
    started = time.perf_counter()
    proc = subprocess.Popen(command, cwd=cwd, env=env, text=True,
                            stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            start_new_session=True, pass_fds=fds)
    expired = False
    try:
        text, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        expired = True
        os.killpg(proc.pid, signal.SIGKILL)
        text, _ = proc.communicate()
    except BaseException:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.communicate()
        raise
    return {"command": list(map(str, command)), "cwd": str(cwd),
            "exit": proc.returncode, "timed_out": expired, "stdout": text,
            "process_wall": time.perf_counter() - started,
            "stdout_sha256": rp.digest(text.encode()),
            "stdout_bytes": len(text.encode())}


def check_seals(seals):
    for raw, expected in seals.items():
        require(a.seal(raw) == expected, "sealed input changed: " + raw)


def extracted_seals(inventory, dst):
    """Git extraction is the authority, never a post-install/build snapshot."""
    seals = {}
    for item in inventory:
        path = dst / Path(item["git_path"]).name
        require(str(path) == item["private_path"] and
                str(path) not in seals, "invalid extraction inventory")
        seals[str(path)] = {k: item[k] for k in ("bytes", "sha256")}
    require(seals, "empty extraction inventory")
    check_seals(seals)
    return seals


def library_paths(receipt):
    """Linux ldd only: reject partial/unresolved/unsupported discovery."""
    require(receipt["exit"] == 0 and not receipt["timed_out"],
            "runtime library discovery failed")
    text = receipt["stdout"]
    require(text.endswith("\n"), "incomplete runtime library discovery")
    paths = []
    address = r"\s+\(0x[0-9a-fA-F]+\)"
    for line in text.splitlines():
        line = line.strip()
        if not line or re.fullmatch(r"linux-vdso\S*" + address, line):
            continue  # kernel-provided virtual object, not a file
        match = re.fullmatch(r"(?:\S+\s+=>\s+)?(/[^\s()]+)" +
                             address, line)
        require(match is not None, "unresolved/unsupported runtime library: " +
                line)
        path = match[1]
        require(path not in paths, "duplicate runtime library")
        paths.append(path)
    require(paths, "empty runtime library inventory")
    return paths


def library_inputs(receipt):
    inputs = {}
    for raw in library_paths(receipt):
        path = Path(raw)
        target = path.resolve(strict=True)
        require(target.is_file(), "runtime library is not a file: " + raw)
        inputs[raw] = dict(resolved=str(target), **a.seal(path))
    return inputs


def archive(folder, name, receipt):
    path = folder / (name + ".json.gz")
    data = (json.dumps(receipt, indent=2, allow_nan=False) + "\n").encode()
    path.write_bytes(gzip.compress(data, mtime=0))
    return {"receipt": path.name, "seal": a.seal(path)}


def sample(rows, pair, selection, metric):
    """The unit of one side of a pair: the mean over its fresh processes."""
    values = [r["measurement"]["raw"][metric] for r in rows
              if r["pair"] == pair and r["selection"] == selection]
    return math.fsum(values) / len(values)


def statistics(rows, pairs, smoke, reps=1):
    require(len(rows) == 2 * pairs * reps and
            [(r["pair"], r["selection"], r.get("rep", 0)) for r in rows] ==
            schedule(pairs, reps),
            "missing/duplicate/reordered fresh pair")
    require(all(r["accepted"] and r["exit"] == 0 for r in rows),
            "failed process in loading statistics")
    if smoke:
        return {"decision": "smoke-only", "metrics": {}}
    metrics = {}
    for metric in METRICS:
        margin, gated = a.timing_rule(POLICY, metric)
        paired = [{side: sample(rows, i, side, metric)
                   for side in ("baseline", "candidate")}
                  for i in range(pairs)]
        metrics[metric] = a.paired_statistics(paired, margin, gated)
        if gated and not all(r["measurement"]["calibrated"] for r in rows):
            metrics[metric]["decision"] = "inconclusive"
            metrics[metric]["reason"] = "sub-resolution first import"
    return {"metrics": metrics}


def finite(value):
    """JSON cannot hold an infinite width; None stands for it."""
    return value if math.isfinite(value) else None


def control_width(control):
    """The grid's measure of a B/B control: the larger half log-width of the
    gated metrics' intervals (`timing_grid.control_half_width`)."""
    import timing_grid
    return timing_grid.control_half_width({"control": control})


def second_stage_count(control, pairs):
    """The grid's second-stage pair count, from the B/B control alone."""
    import timing_grid as tg
    return tg.second_stage_pairs(control_width(control), pairs, tg.TARGET,
                                 tg.MAX_PAIRS)


def required_units(unit_sd):
    """n * R needed for a 95% interval half width of `tg.TARGET`, when the
    paired log ratio of two R-means has sd `unit_sd / sqrt(R)`."""
    import timing_grid
    return math.ceil((Z95 * MEDIAN_FACTOR * unit_sd /
                      timing_grid.TARGET) ** 2)


def gamma_p(shape, x):
    """Regularized lower incomplete gamma function P(shape, x)."""
    if x <= 0:
        return 0.0
    log_front = -x + shape * math.log(x) - math.lgamma(shape)
    if x < shape + 1:
        term = total = 1 / shape
        n = shape
        while abs(term) > abs(total) * 1e-16:
            n += 1
            term *= x / n
            total += term
        return total * math.exp(log_front)
    tiny = 1e-300
    b = x + 1 - shape
    c, d = 1 / tiny, 1 / b
    h = d
    for i in range(1, 100000):
        an = -i * (i - shape)
        b += 2
        d = an * d + b
        d = d if abs(d) > tiny else tiny
        c = b + an / c
        c = c if abs(c) > tiny else tiny
        d = 1 / d
        delta = d * c
        h *= delta
        if abs(delta - 1) < 1e-15:
            break
    return 1 - math.exp(log_front) * h


def chi2_quantile(p, df):
    """The p quantile of the chi-square distribution (bisection)."""
    low, high = 0.0, max(10.0, 10.0 * df)
    while gamma_p(df / 2, high / 2) < p:
        high *= 2
    for _ in range(200):
        mid = (low + high) / 2
        low, high = (mid, high) if gamma_p(df / 2, mid / 2) < p else (low, mid)
    return (low + high) / 2


def sd_upper_bound(sd, n):
    """One-sided 95% chi-square upper confidence bound on a standard
    deviation estimated from `n` observations."""
    df = n - 1
    return sd * math.sqrt(df / chi2_quantile(0.05, df))


def second_stage_plan(report, results):
    """Pairs of the second stage of a first-stage decision run, from its B/B
    control only; refused unless the control missed its window and nothing
    failed. Every other result, inconclusive ones included, is final."""
    require(report.get("stage") == "first" and
            report["mode"] == "isolated-source" and report["success"],
            "only a successful first-stage decision run has a second stage")
    metrics = results["candidate"]["metrics"]
    gated = [m for m, d in metrics.items() if d.get("gated", True)]
    require(not any(metrics[m]["decision"] == "fail" for m in gated),
            "a first-stage fail is final")
    require(not all(metrics[m].get("control_valid") for m in gated),
            "the B/B control met its window: the first stage is final")
    return second_stage_count(results["control"], report["pairs"])


def check_seed(seed):
    """A seed that every process of a run can use: `layout_units` appends
    the longest suffix, "-pilot", before the schema's length limit."""
    require(isinstance(seed, str), "layout seed must be a string")
    require(len(seed) <= 58, "layout seed: at most 58 characters (the "
            "longest suffix, \"-pilot\", is appended to it)")
    ps.layout_seed(seed + "-pilot")


def layout_units(seed, phase, pair, side, rep):
    """The code-layout padding of one fresh process: independent per
    (rep, pair, side), the same in the B/B and candidate phases, and
    separate for the pilots."""
    if phase == "pilot":
        return ps.layout_units(seed + "-pilot", 0, side)
    return ps.layout_units("%s-r%d" % (seed, rep), pair, side)


def expected_runs(pairs, reps, calibrate):
    """(phase, pair, selection, rep) of every process, in execution order."""
    order = [("pilot", 0, side, 0) for side in ("baseline", "candidate")]
    for phase in ("control",) if calibrate else ("control", "candidate"):
        order += [(phase, i, side, r) for i, side, r in schedule(pairs, reps)]
    return order


class Blocked(ValueError):
    """A finding about the candidate: an extension or a new stem was loaded
    by one of its processes. The attempt closes `blocked`. A rejection of a
    baseline process is a plain failure, void when nothing was admitted."""


def check_stems(stems, base):
    """What a candidate process loads, minus what the baseline processes
    load, is empty or reviewed: the name-independent extension rule."""
    extra = set(stems) - base - STEM_ALLOWANCE
    if extra:
        raise Blocked("candidate loaded what no baseline process loaded: " +
                      ",".join(sorted(extra)))


def check_new_stems(rows):
    base = set()
    for row in rows:
        if row["actual_selection"] == "baseline":
            base |= set(row["measurement"]["loaded_stems"])
    for row in rows:
        if row["actual_selection"] == "candidate":
            check_stems(row["measurement"]["loaded_stems"], base)


def semantic_status(mode):
    return "not admitted: " + ("smoke" if mode == "smoke" else
                               "calibration") + " only"


def jitter(rows, control, pairs, reps):
    """What B/B says about the host, from the control phase's processes.
    Per metric:
      process_log_sd       s1: pooled sd of the logs of the R processes of
                           one side of one pair (None when R = 1);
      paired_log_ratio_sd  sd of the log ratio of the paired R-means;
      unit_sd              paired_log_ratio_sd * sqrt(R);
      unit_sd_upper        its 95% chi-square upper bound (n pairs);
      required_units       n * R that bound asks for."""
    found = {}
    for metric in METRICS:
        logs = {}
        for row in rows:
            logs.setdefault((row["pair"], row["selection"]), []).append(
                math.log(row["measurement"]["raw"][metric])
                if row["measurement"]["raw"][metric] > 0 else None)
        ratios, ss, df = [], 0.0, 0
        for i in range(pairs):
            means = {}
            for side in ("baseline", "candidate"):
                xs = logs[i, side]
                if None in xs:
                    means = None
                    break
                m = math.fsum(xs) / len(xs)
                means[side] = m
                ss += math.fsum((x - m) ** 2 for x in xs)
                df += len(xs) - 1
            if means:
                ratios.append(means["candidate"] - means["baseline"])
        entry = dict(gated=metric in POLICY["gated_timing"])
        if len(ratios) > 1:
            mean = math.fsum(ratios) / len(ratios)
            paired = math.sqrt(math.fsum((x - mean) ** 2 for x in ratios) /
                               (len(ratios) - 1))
            unit = paired * math.sqrt(reps)
            upper = sd_upper_bound(unit, len(ratios))
            entry.update(paired_log_ratio_sd=paired, unit_sd=unit,
                         unit_sd_upper=upper,
                         required_units=required_units(upper))
        entry["process_log_sd"] = math.sqrt(ss / df) if df else None
        found[metric] = entry
    gated = [e["required_units"] for e in found.values()
             if e["gated"] and "required_units" in e]
    width = control_width(control)
    return dict(metrics=found, pairs=pairs, reps=reps,
                required_units=max(gated) if gated else None,
                configured_units=PAIRS * REPS,
                half_log_width=finite(width),
                second_stage_pairs=second_stage_count(control, pairs))


def covered(found):
    """A calibration covers the first stage when every gated metric's
    `unit_sd_upper` is at most `UNIT_SD_BOUND` (the bound the stage is sized
    for): the one acceptance rule."""
    gated = [e for e in found["metrics"].values() if e["gated"]]
    return bool(gated) and all(
        "unit_sd_upper" in e and e["unit_sd_upper"] <= UNIT_SD_BOUND
        for e in gated)


def check_settings(args, first):
    """The counts, seed and baseline a run may have. A decision run is
    exactly PAIRS x REPS; its one second stage is the grid's, driven by the
    first stage's B/B control alone (`--extend`). Nothing else is free."""
    require(args.module in MODULES, "unknown ordinary module")
    require(not (args.smoke and args.calibrate),
            "--smoke and --calibrate are exclusive")
    check_seed(args.layout_seed)
    require(args.timeout > 0, "invalid timeout")
    if args.smoke:
        require(1 <= args.pairs <= SMOKE_PAIRS and
                1 <= args.reps <= SMOKE_REPS,
                "a smoke run is at most %d pairs of %d fresh import (it "
                "checks the harness; it is not a look at the candidate)" %
                (SMOKE_PAIRS, SMOKE_REPS))
        require(args.layout_seed not in (LAYOUT_SEED, EXTENSION_SEED),
                "a smoke run may not use the layout seed of a decision "
                "run or of its second stage")
        return
    if args.calibrate:
        require(args.baseline == args.candidate == a.BASE,
                "a calibration measures the develop pin %s against itself "
                "(--baseline and --candidate, if given, are that pin)" %
                a.BASE)
        require(args.reps >= 1, "invalid repetitions")
        require(args.pairs >= 10, "calibration requires >=10 pairs")
        return
    require(args.baseline == a.BASE,
            "a decision run's baseline is the develop pin " + a.BASE)
    if first is None:
        require((args.pairs, args.reps) == (PAIRS, REPS),
                "a decision run is exactly %d pairs of %d fresh imports "
                "each (only --smoke/--calibrate take other counts; a second "
                "stage is --extend)" % (PAIRS, REPS))
        require(args.layout_seed == LAYOUT_SEED,
                "a decision run uses the layout seed " + LAYOUT_SEED)
        return
    report = first["report"]
    require((args.module, args.reps, args.layout_seed) ==
            (report["module"], report["reps"], EXTENSION_SEED) and
            args.pairs == first["pairs"],
            "the second stage's pairs, repetitions, module and layout seed "
            "are fixed by its first stage")
    for side in ("baseline", "candidate"):
        require(report["selections"][side]["revision"] ==
                getattr(args, side), "the second stage changes the " + side)


# The attempts ledger: the timing grid's (`timing_grid.Ledger`), under this
# table's name. A decision run and a `--extend` each open an attempt before
# the first process and close it with the seal of their `loading.json` and
# the decision.
TABLE = "task31-loading"
FAILED = "failed"  # a run that decided nothing (success false)
BLOCKED = "blocked"  # a finding about the candidate: judged, never void
DECISIONS = {0: "pass", 1: "fail", 2: "inconclusive"}
TREE_PATH = "src/simp/src"  # the tree that `rp.extract` takes the sources of


def ledger_path(repo):
    """The one ledger of the table in a checkout: below its root, in the
    directory git excludes."""
    return (Path(repo).resolve() / ".agent-files" / "evidence" / TABLE /
            "attempts.jsonl")


def extracted_files(repo, revision):
    """The sorted (git_path, git_blob) pairs of the sources that
    `rp.extract` takes from `revision` (sources and signatures of
    TREE_PATH, but no selftest.sml and nothing of mosml/): what is built and
    measured of a candidate. The filter is that of `rp.extract`, which the
    tests compare it with."""
    try:
        listing = rp.git(repo, "ls-tree", "-r", revision, TREE_PATH
                         ).decode().splitlines()
    except subprocess.SubprocessError as error:
        raise ValueError("no %s in %s: %s" % (TREE_PATH, revision, error))
    files = []
    for line in listing:
        meta, path = line.split("\t", 1)
        p = Path(path)
        if p.suffix not in (".sml", ".sig") or p.name == "selftest.sml" or \
                p.parent.name == "mosml":
            continue
        files.append((path, meta.split()[2]))
    require(files, "no %s sources in %s" % (TREE_PATH, revision))
    return sorted(files)


def key_of(pairs):
    """The digest of sorted (git_path, git_blob) pairs: the identity of a
    measured inventory, whatever the commit, its message or the files that
    are not extracted."""
    return hashlib.sha256(json.dumps(
        sorted([list(p) for p in pairs]), separators=(",", ":")
    ).encode()).hexdigest()


def source_key(repo, revision):
    return key_of(extracted_files(repo, revision))


def inventory_key(inventory):
    """The key of the sources a run extracted (its report's `sources`)."""
    return key_of([(s["git_path"], s["git_blob"]) for s in inventory])


# The fields each event of the table has, with the type of each value: the
# one table the readers and the validator share. A line without a field, or
# with a value of another type, is a corrupt ledger and not a traceback.
# `check_ledger`, `gate_attempts`, `attempts_table` and `table_smokes` read
# only fields named here.
STR_OR_NONE = (str, type(None))
EVENT_FIELDS = dict(
    open=dict(attempt=str, stage=str, candidate=str, baseline=str,
              module=str, seed=str, source_key=str, baseline_key=str,
              first_attempt=STR_OR_NONE, output=str, checkout=str),
    close=dict(attempt=str, stage=str, status=str, seal=str, output=str),
    smoke=dict(attempt=str, candidate=str, baseline=str, source_key=str,
               baseline_key=str, module=str, seed=str, pairs=int, reps=int,
               output=str, checkout=str),
    **{"smoke-end": dict(attempt=str, success=bool, seal=STR_OR_NONE)})


def right_type(value, kind):
    """Whether a value is of the type: a bool is no int."""
    return isinstance(value, kind) and not (
        isinstance(value, bool) and kind is int)


def table_lines(state):
    """The lines of the table, each of a known event, with the fields of
    that event and values of their types; anything else is a corrupt
    ledger. A smoke has at most one end line, and an end line belongs to a
    smoke. Lines of the other tables of the shared ledger are skipped."""
    lines, starts, ends = [], set(), set()
    for record in state.records:
        if record.get("table") != TABLE:
            continue
        event = record.get("event")
        require(isinstance(event, str) and event in EVENT_FIELDS,
                "corrupt attempts ledger: a line of unknown event %r" %
                (event,))
        missing = [k for k in EVENT_FIELDS[event] if k not in record]
        require(not missing, "corrupt attempts ledger: a line of event %r "
                "lacks %s" % (event, ", ".join(missing)))
        wrong = [k for k, t in EVENT_FIELDS[event].items()
                 if not any(right_type(record[k], x) for x in (
                     t if isinstance(t, tuple) else (t,)))]
        require(not wrong, "corrupt attempts ledger: a line of event %r "
                "has a value of the wrong type for %s" % (
                    event, ", ".join(wrong)))
        if event == "smoke":
            require(record["attempt"] not in starts,
                    "corrupt attempts ledger: smoke %s is recorded twice" %
                    record["attempt"])
            starts.add(record["attempt"])
        elif event == "smoke-end":
            require(record["attempt"] in starts and
                    record["attempt"] not in ends,
                    "corrupt attempts ledger: smoke %s has no start or "
                    "several ends" % record["attempt"])
            ends.add(record["attempt"])
        lines.append(record)
    return lines


def table_attempts(state):
    """(attempt, stage) -> its `open` and `close` lines, for every attempt of
    the table. An attempt has exactly one opening and at most one close;
    anything else is a corrupt ledger. A `smoke` line is no attempt: it
    judges nothing and is listed apart (`table_smokes`)."""
    found = {}
    for record in table_lines(state):
        if record["event"] in ("smoke", "smoke-end"):
            continue
        row = found.setdefault((record["attempt"], record["stage"]),
                               dict(opens=[], closes=[]))
        row[record["event"] + "s"].append(record)
    for (attempt, stage), row in found.items():
        require(len(row["opens"]) == 1 and len(row["closes"]) <= 1,
                "corrupt attempts ledger: attempt %s (%s stage) has %d "
                "opening and %d close lines" % (
                    attempt, stage, len(row["opens"]), len(row["closes"])))
    return found


def read_ledger(path):
    """The ledger and the attempts of its table, wholly validated: the one
    check every reader and every run applies, a smoke included."""
    import timing_grid as tg
    state = tg.Ledger(path)
    return state, table_attempts(state)


def table_smokes(state, candidate=None, key=None, module=None):
    """The smoke runs the ledger records, in order: all of them, or those of
    this module with this candidate commit or extracted-source key on either
    side. A smoke with no end line is `unfinished` (it has no seal); an
    ended one names its `success` and the `seal` of its loading.json, if
    saved."""
    lines = table_lines(state)
    ended = {r["attempt"]: r for r in lines if r["event"] == "smoke-end"}
    out = []
    for r in lines:
        if r["event"] != "smoke" or (module is not None and
                                     r["module"] != module):
            continue
        if candidate is not None and not (
                candidate in (r["candidate"], r["baseline"]) or
                key in (r["source_key"], r["baseline_key"])):
            continue
        end = ended.get(r["attempt"])
        row = {k: v for k, v in r.items()
               if k not in ("prev", "time", "event", "table")}
        row.update(unfinished=end is None,
                   success=None if end is None else end["success"],
                   seal=None if end is None else end["seal"])
        out.append(row)
    return out


PROCESS_PHASES = ("control", "candidate")


def receipt_label(phase, pair, side, rep):
    """The name (without `.json.gz`) of a process's archived receipt."""
    return "%s-%03d-%s-%02d" % (phase, pair, side, rep)


# The names `receipt_label` gives to control and candidate processes.
RECEIPT_NAME = re.compile(
    r"(control|candidate)-\d{3}-(baseline|candidate)-\d+\.json\.gz")


def judged_because(attempt, stage, row):
    """None when the attempt is void: it measured and decided nothing, shown
    from its own output. Otherwise the reason it counts as the draw. Void
    means exactly one close, with status `failed`, whose output holds a
    `loading.json` of that seal, of this attempt, with `success` false and no
    `blocked`, and whose archived control and candidate receipts are exactly
    the ones the report lists, each sealed and not admitted. Every other
    attempt, closed or not, is judged."""
    if len(row["closes"]) != 1:
        return "no close line" if not row["closes"] else "several closes"
    close = row["closes"][0]
    if close["status"] != FAILED:
        return "closed " + close["status"]
    folder = Path(close["output"])
    if close["output"] != row["opens"][0]["output"]:
        return "its close names another output"
    try:
        path = folder / "loading.json"
        if not path.is_file():
            return "its output is missing: " + str(path)
        if a.seal(path)["sha256"] != close["seal"]:
            return "its loading.json differs from the sealed one: " + \
                str(path)
        report = a.load(path)
        if report["attempt"] != attempt or report["stage"] != stage:
            return "its loading.json is of another attempt"
        if report["success"] is not False or "blocked" in report:
            return "its report is a success or a blocked one"
        listed = {r["receipt"]: r for r in report["runs"]
                  if r["phase"] in PROCESS_PHASES}
        present = {q.name for q in folder.iterdir()
                   if RECEIPT_NAME.fullmatch(q.name)}
        if present != set(listed):
            return "its control and candidate receipts are not those the " \
                "report lists"
        for name, entry in listed.items():
            receipt = a.safe_child(folder, name)
            if a.seal(receipt) != entry["seal"]:
                return "a process receipt differs from its seal: " + name
            if entry["accepted"] is not False or \
                    a.load(receipt)["accepted"] is not False:
                return "a control or candidate process was admitted: " + name
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as e:
        return "its output cannot be read: %s" % e
    return None


def gate_attempts(found, candidate, key, module, stage):
    """attempt id -> its lines, for the table's attempts at `stage` of this
    module and of this candidate commit or this extracted-source key."""
    return {i: row for (i, st), row in found.items()
            if st == stage and row["opens"][0]["module"] == module and
            (row["opens"][0]["candidate"] == candidate or
             (key is not None and
              row["opens"][0]["source_key"] == key))}


def reasons(found):
    """(attempt, stage) -> None when void, else why judged: each attempt's
    output is read once, and everything derived from it uses this."""
    return {k: judged_because(k[0], k[1], row) for k, row in found.items()}


def judged(rows, why=None):
    """The attempts that count as the draw: all but the void ones. `why` is
    the `reasons` of the attempts, when already read."""
    if why is None:
        why = reasons({(i, row["opens"][0]["stage"]): row
                       for i, row in rows.items()})
    return sorted(i for i, row in rows.items()
                  if why[i, row["opens"][0]["stage"]] is not None)


def attempts_table(found, why=None):
    """Every attempt of the table, other candidates' included: what the
    handoff publishes, and what a blocked gate is diagnosed from."""
    why = reasons(found) if why is None else why
    table = []
    for (i, st), r in found.items():
        table.append(dict(
            attempt=i, stage=st, candidate=r["opens"][0]["candidate"],
            source_key=r["opens"][0]["source_key"],
            module=r["opens"][0]["module"],
            statuses=[c["status"] for c in r["closes"]] or ["unclosed"],
            void=why[i, st] is None, judged_because=why[i, st],
            output=r["opens"][0]["output"],
            checkout=r["opens"][0]["checkout"]))
    return table


def require_ignored(path, repo):
    """The ledger, when inside the checkout, is excluded from git."""
    if path.resolve().is_relative_to(Path(repo).resolve()):
        ignored = subprocess.run(
            ["git", "-C", str(repo), "check-ignore", "-q", str(path)],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        require(ignored.returncode == 0, "the attempts ledger would be "
                "tracked by git: exclude .agent-files first, in the file "
                "`git rev-parse --git-path info/exclude` names: %s" % path)


def refuse_second_draw(path, args, stage, key):
    """Under the serial lock, before anything is created: the gate (this
    module, and this candidate commit or extracted-source key) has no judged
    attempt at this stage yet."""
    require_ignored(path, args.repo)
    if not path.exists():
        return
    found = judged(gate_attempts(read_ledger(path)[1],
                                 args.candidate, key, args.module, stage))
    require(not found, "the %s stage of this candidate (or extracted-source "
            "key) and module has a judged attempt already (%s): only a run "
            "that decided nothing and admitted no measurement is void, and "
            "any other new draw needs a written policy decision and a "
            "reviewed harness change (see --ledger-status)%s" % (
                stage, ", ".join(found), "" if stage == "first" else
                "; at most one --extend per first stage"))


def open_attempt(path, args, report, first, output, repo, keys):
    """Append the opening of this run; the attempt id goes into the report."""
    import timing_grid as tg
    path.parent.mkdir(parents=True, exist_ok=True)
    attempt = "%s-%s" % (report["stage"], uuid.uuid4().hex[:12])
    tg.ledger_append(
        path, event="open", stage=report["stage"], table=TABLE,
        attempt=attempt, candidate=args.candidate, module=args.module,
        baseline=args.baseline, seed=args.layout_seed,
        source_key=keys["candidate"], baseline_key=keys["baseline"],
        first_attempt=None if first is None else first["report"]["attempt"],
        output=str(output), checkout=str(repo))
    report["attempt"] = attempt


def ledger_status(args):
    """The attempts of the table (those of `--module` when given), for a
    gate that is blocked, failed or unclosed: no run is replayed."""
    path = args.ledger or ledger_path(Path(args.repo).resolve(strict=True))
    require(path.is_file(), "no attempts ledger: %s" % path)
    state, found = read_ledger(path)
    table = attempts_table(found)
    return dict(ledger=str(path), table=[
        r for r in table if args.module in (None, r["module"])],
        smokes=table_smokes(state, module=args.module))


def open_smoke(path, args, output, keys, repo):
    """Append the start line of a smoke run, before any process: information
    only, never an attempt, never judged or void. Returns its id."""
    import timing_grid as tg
    path.parent.mkdir(parents=True, exist_ok=True)
    attempt = "smoke-" + uuid.uuid4().hex[:12]
    tg.ledger_append(
        path, event="smoke", table=TABLE, attempt=attempt,
        candidate=args.candidate, baseline=args.baseline,
        source_key=keys["candidate"], baseline_key=keys["baseline"],
        module=args.module, seed=args.layout_seed, pairs=args.pairs,
        reps=args.reps, output=str(output), checkout=str(repo))
    return attempt


def end_smoke(path, attempt, report, output, saved):
    """Append the end line of a smoke run, whatever its outcome: its success
    and, when loading.json was saved, the seal of it. When it cannot be
    written the smoke stays listed as unfinished."""
    import timing_grid as tg
    try:
        tg.ledger_append(
            path, event="smoke-end", table=TABLE, attempt=attempt,
            success=report["success"] is True,
            seal=a.seal(output / "loading.json")["sha256"] if saved
            else None)
    except Exception as error:
        print("SMOKE-NOT-ENDED %s: %s" % (attempt, error),
              file=sys.stderr, flush=True)


def close_attempt(path, report, output):
    """Append the close: the seal of loading.json and the decision. When it
    cannot be written the attempt stays open, which counts as judged."""
    import timing_grid as tg
    try:
        seal = a.seal(output / "loading.json")
        status = BLOCKED if report.get("blocked") else FAILED
        if report["success"]:
            status = DECISIONS[exit_status(
                report["results"]["candidate"]["metrics"])]
        tg.ledger_append(
            path, event="close", stage=report["stage"], table=TABLE,
            attempt=report["attempt"], status=status,
            seal=seal["sha256"], output=str(output),
            checkout=report["repo"])
    except Exception as error:
        print("ATTEMPT-NOT-CLOSED %s: %s" % (report["attempt"], error),
              file=sys.stderr, flush=True)


def check_ledger(path, report, seal, status, first_attempt):
    """Replay: this run is the recorded attempt of its stage, closed with
    this seal and decision, and no other judged attempt exists for the same
    gate. Returns the counts of the gate's attempts and every attempt of the
    table."""
    path = Path(path)
    require(path.is_file(), "no attempts ledger: %s" % path)
    state, found = read_ledger(path)
    attempt, stage = report.get("attempt"), report["stage"]
    require((attempt, stage) in found,
            "the attempts ledger has no opening of this run")
    row = found[attempt, stage]
    opened = row["opens"][0]
    chosen = report["selections"]["candidate"]
    key = inventory_key(chosen["sources"])
    require(chosen.get("source_key") == key and
            report["selections"]["baseline"].get("source_key") ==
            inventory_key(report["selections"]["baseline"]["sources"]),
            "the report's source key is not that of its sources")
    want = (chosen["revision"], report["module"],
            report["selections"]["baseline"]["revision"],
            report["layout_seed"], first_attempt, key)
    require((opened["candidate"], opened["module"], opened["baseline"],
             opened["seed"], opened["first_attempt"],
             opened["source_key"]) == want,
            "the ledger's opening disagrees with this run")
    closes = row["closes"]
    require(len(closes) == 1 and closes[0]["seal"] == seal["sha256"] and
            closes[0]["status"] == status,
            "the ledger's close does not name this loading.json and decision")
    why = reasons(found)
    rows = gate_attempts(found, want[0], key, want[1], stage)
    counted = judged(rows, why)
    others = [i for i in counted if i != attempt]
    require(not others and attempt in counted,
            "another judged attempt exists for this candidate (or "
            "extracted-source key), module and stage; every attempt's "
            "output must stay at its recorded path, void ones included: " +
            "; ".join("%s (%s)" % (i, why[i, stage]) for i in others))
    counts = {}
    for st in ("first", "second"):
        got = gate_attempts(found, want[0], key, want[1], st)
        counts[st] = dict(attempts=len(got), judged=len(judged(got, why)))
    counts["table"] = attempts_table(found, why)
    counts["smokes"] = table_smokes(state, want[0], key, want[1])
    places = sorted({r["checkout"] for r in counts["table"]})
    if len(places) > 1:
        counts["checkouts"] = places
    return counts


def source_seals(selections):
    return {side: [(s["git_path"], s["bytes"], s["sha256"])
                   for s in selections[side]["sources"]]
            for side in ("baseline", "candidate")}


def run(args, first=None):
    check_settings(args, first)
    light = args.smoke or args.calibrate
    require(args.authorize_measurements,
            "measurement authorization required")
    a.exact_pin(args.baseline)
    a.exact_pin(args.candidate)
    require(light or args.api_audit,
            "candidate eight-process --api-audit receipt required")
    repo, output = args.repo.resolve(strict=True), args.output.resolve()
    ledger = None if args.calibrate else ledger_path(repo)
    # Before anything is created: a revision without sources is refused here.
    keys = {side: source_key(repo, getattr(args, side))
            for side in ("baseline", "candidate")}
    with a.serial_lock(repo) as fds:
        smoke = None
        if args.smoke:
            # Before anything is created: the whole ledger is read, and
            # the start line is written ahead of the first process.
            require_ignored(ledger, repo)
            if ledger.exists():
                read_ledger(ledger)
            require(not output.exists(), "output exists: %s" % output)
            smoke = open_smoke(ledger, args, output, keys, repo)
        elif ledger is not None:
            refuse_second_draw(ledger, args, "first" if first is None
                               else "second", keys["candidate"])
        if smoke is None:
            output.mkdir(parents=True, exist_ok=False)
        report = {"schema": SCHEMA, "success": False,
                  "mode": "smoke" if args.smoke else
                  "calibration" if args.calibrate else "isolated-source",
                  "claims": "NOT independent-build or release acceptance",
                  "repo": str(repo), "module": args.module,
                  "pairs": args.pairs, "reps": args.reps,
                  "stage": "first" if first is None else "second",
                  "layout_seed": args.layout_seed,
                  "outliers": "none removed",
                  "policy": POLICY, "timer_fields": FIELDS,
                  "timeout": args.timeout, "selections": {}, "runs": [],
                  "argv": sys.argv, "inputs": {}, "tools": {}}
        if ledger is not None and smoke is None:
            open_attempt(ledger, args, report, first, output, repo, keys)
        saved = False
        try:
            if smoke is not None:
                output.mkdir(parents=True, exist_ok=False)
            env = {k: v for k, v in os.environ.items()
                   if not k.startswith(("HOL", "POLY", "ML", "PAIR_",
                                        "PERF_", "LOADING_", "LD_"))}
            env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC",
                       HOL4_PERF_LOCK_FDS=",".join(map(str, fds)))
            report["runtime_options"] = [
                "--gcthreads=1", "run", "--holstate=" +
                str(repo / "bin/hol.state0")]
            paths = [Path(__file__), HERE / "test_loading.py",
                     HERE / "test_loading_provenance.py",
                     HERE / "PROTOCOL_LOADING.md", Path(a.__file__),
                     Path(rp.__file__), HERE / "summarize.py",
                     HERE / "performance_schema.py",
                     HERE / "timing_grid.py", AUDIT / "selftest.sml",
                     AUDIT / "audit_constants.py"]
            paths += sorted((rp.HERE / "paired").glob("*.sml"))
            paths += [rp.HERE / "paired/Holmakefile",
                      HERE / "review-20261021/abicheck.sml"]
            paths += [repo / "bin" / n for n in
                      ("hol", "Holmake", "hol.state0")]
            poly = shutil.which("poly", path=env.get("PATH"))
            require(poly, "Poly/ML runtime not found")
            paths += [Path(poly), Path(sys.executable)]
            inputs = {str(p.resolve()): a.seal(p) for p in paths}
            report["inputs"] = inputs
            version = execute([poly, "-v"], repo, env, args.timeout, fds)
            report["poly_version"] = archive(output, "poly-version", version)
            require(version["exit"] == 0 and not version["timed_out"] and
                    version["stdout"].strip(), "Poly/ML version query failed")
            report["tools"] = {"poly": poly, "python": sys.version,
                               "poly_version": version["stdout"].strip()}
            linked = execute(["ldd", str(repo / "bin/hol")], repo, env,
                             args.timeout, fds)
            report["dynamic_libraries"] = {
                "discovery": archive(output, "runtime-libraries", linked)}
            libraries = library_inputs(linked)
            report["dynamic_libraries"]["inputs"] = libraries
            for raw, info in libraries.items():
                seal = {k: info[k] for k in ("bytes", "sha256")}
                inputs[raw] = seal
                inputs[info["resolved"]] = seal
            report["environment"] = {k: env[k] for k in
                                     ("HOLDIR", "LC_ALL", "PATH", "TERM", "TZ")
                                     if k in env}
            with tempfile.TemporaryDirectory(prefix="simp-loading-") as tmp:
                root = Path(tmp)
                sources, names = {}, set()
                for side, pin in (("baseline", args.baseline),
                                  ("candidate", args.candidate)):
                    dst = root / side
                    dst.mkdir()
                    require(rp.git(repo, "rev-parse", pin + "^{commit}")
                            .decode().strip() == pin, "nonexact revision")
                    inventory = rp.extract(repo, pin, dst)
                    require(inventory_key(inventory) == keys[side],
                            "the extracted sources are not those of the "
                            "source key")
                    sources.update(extracted_seals(inventory, dst))
                    install(dst, args.module)
                    check_seals(sources)
                    # Seal generated fixture inputs BEFORE the build as well.
                    for path in dst.rglob("*"):
                        if path.is_file() and str(path) not in sources:
                            sources[str(path)] = a.seal(path)
                    selected = {"revision": pin, "private": str(dst),
                                "source_key": keys[side],
                                "sources": inventory}
                    report["selections"][side] = selected
                    names.update(Path(s["git_path"]).stem for s in inventory)
                    command = [str(repo / "bin/Holmake"), "--no-project",
                               "--no-cache", "--no_prereqs", "--holstate=" +
                               str(repo / "bin/hol.state0"), "-C", str(dst),
                               "-j1", "paired.exe"]
                    build = execute(command, root, env, args.timeout, fds)
                    selected["build"] = archive(output, side + "-build", build)
                    require(build["exit"] == 0 and not build["timed_out"],
                            side + " loading fixture build failed")
                    # Includes the earlier selection: a later build may not
                    # change it either. Never replace these expected Git seals.
                    check_seals(sources)
                    launcher = (dst / "paired.exe").read_text()
                    require(str(repo / "bin/hol") + " --gcthreads=1 run "
                            in launcher and "--holstate=" +
                            str(repo / "bin/hol.state0") in launcher,
                            "unexpected loading launcher options")
                    selected["launcher"] = launcher
                    selected["products"] = {
                        str(p.relative_to(dst)): a.seal(p)
                        for p in dst.rglob("*") if p.is_file()}
                    for path in dst.rglob("*"):
                        if path.is_file() and str(path) not in sources:
                            sources[str(path)] = a.seal(path)
                if first is not None:
                    require(source_seals(report["selections"]) ==
                            source_seals(first["report"]["selections"]),
                            "the second stage's sources are not the first "
                            "stage's")
                    report["first_stage"] = dict(
                        run=str(first["folder"]), seal=first["seal"],
                        attempt=first["report"]["attempt"],
                        pairs=first["report"]["pairs"],
                        second_stage_pairs=first["pairs"])
                if args.api_audit:
                    report["semantic_gate"] = semantic_gate(
                        args.api_audit, repo,
                        report["selections"]["candidate"]["sources"])
                else:
                    report["semantic_gate"] = semantic_status(report["mode"])
                shared = {}
                every, base_stems = [], set()

                def launch(phase, pair, side, rep=0):
                    actual = "baseline" if phase == "control" else side
                    dst = root / actual
                    runenv = dict(env, PAIR_SELECTION=side,
                                  PERF_LAYOUT=str(layout_units(
                                      args.layout_seed, phase, pair, side,
                                      rep)),
                                  PAIR_FIXTURE="loading", PAIR_CONTROL="none",
                                  PAIR_PRIVATE=str(dst),
                                  PAIR_TARGET="selftest",
                                  LOADING_MODULE=args.module)
                    receipt = execute([str(dst / "paired.exe")], dst,
                                      runenv, args.timeout, fds)
                    receipt.update(phase=phase, pair=pair, selection=side,
                                   rep=rep,
                                   actual_selection=actual,
                                   environment={k: v for k, v in runenv.items()
                                                if k.startswith(("PAIR_",
                                                                 "PERF_",
                                                                 "LOADING_"))},
                                   accepted=False)
                    try:
                        result, measurement = validate(
                            receipt, side=side, dst=dst, repo=repo,
                            names=names,
                            sources=sources, module=args.module,
                            enforce_absence=enforced(actual, args.baseline),
                            candidate=actual == "candidate")
                        # Seal all shared actual inputs across every fresh run.
                        for info in result["paths"].values():
                            for raw, seal in [(info["physical"],
                                              {k: info[k] for k in
                                               ("bytes", "sha256")})] + \
                                    list(info["related_products"].items()):
                                if not Path(raw).is_relative_to(root):
                                    old = shared.setdefault(raw, seal)
                                    require(old == seal,
                                            "shared input changed across runs")
                        receipt.update(result=result, measurement=measurement,
                                       accepted=True)
                        every.append(receipt)
                        if actual == "baseline":
                            base_stems.update(measurement["loaded_stems"])
                        else:
                            check_stems(measurement["loaded_stems"],
                                        base_stems)
                    except (ValueError, OSError) as error:
                        receipt["rejection"] = str(error)
                        if isinstance(error, Blocked):
                            report["blocked"] = str(error)
                            receipt["accepted"] = False
                    label = receipt_label(phase, pair, side, rep)
                    evidence = archive(output, label, receipt)
                    report["runs"].append(dict(evidence, phase=phase,
                                               pair=pair, selection=side,
                                               rep=rep,
                                               accepted=receipt["accepted"]))
                    require(receipt["accepted"],
                            "loading process rejected: " + label + ": " +
                            receipt.get("rejection", "unknown failure"))
                    return receipt

                # Pilot imports are fresh and never reused as measured pairs.
                report["calibration"] = [
                    launch("pilot", 0, side)["measurement"]
                    for side in ("baseline", "candidate")]
                results = {}
                for phase in (("control",) if args.calibrate else
                              ("control", "candidate")):
                    rows = [launch(phase, i, side, r)
                            for i, side, r in schedule(args.pairs,
                                                       args.reps)]
                    results[phase] = statistics(
                        rows, args.pairs, args.smoke, args.reps)
                if args.calibrate:
                    report["jitter"] = jitter(
                        [r for r in every if r["phase"] == "control"],
                        results["control"], args.pairs, args.reps)
                if not light:
                    metrics = results["candidate"]["metrics"]
                    for metric, data in metrics.items():
                        control = results["control"]["metrics"][metric]
                        a.apply_control(data, control)
                        if data.get("gated", True) and not all(
                                m["calibrated"] for m in
                                report["calibration"]):
                            data["decision"] = "inconclusive"
                            data["reason"] = "uncalibrated pilot import"
                report["results"] = results
                check_new_stems(every)
                if not light:
                    report["control_half_log_width"] = finite(
                        control_width(results["control"]))
                    report["second_stage_pairs"] = second_stage_count(
                        results["control"], args.pairs)
                report["shared_inputs"] = shared
                check_seals(inputs)
                check_seals(sources)
                check_seals(shared)
                # Recheck dependency resolution, not ASLR addresses. Keep the
                # original logical paths AND targets to detect retargeting.
                linked_after = execute(["ldd", str(repo / "bin/hol")], repo,
                                       env, args.timeout, fds)
                report["dynamic_libraries"]["recheck"] = archive(
                    output, "runtime-libraries-after", linked_after)
                require(library_inputs(linked_after) == libraries,
                        "runtime library resolution changed")
                report["success"] = True
        except (ValueError, OSError, KeyError, IndexError, TypeError,
                subprocess.SubprocessError) as error:
            report["failure"] = str(error)
            if isinstance(error, Blocked):
                report["blocked"] = str(error)
        finally:
            try:
                a.save(output / "loading.json", report)
                saved = True
            finally:
                if smoke is not None:
                    end_smoke(ledger, smoke, report, output, saved)
        if ledger is not None and smoke is None:
            close_attempt(ledger, report, output)
    return report


def exit_status(metrics):
    """0 only when every gated metric passes; gc_cpu is reported only."""
    decisions = [m["decision"] for m in metrics.values()]
    return 1 if "fail" in decisions else \
        2 if any(d not in ("pass", "reported") for d in decisions) else 0


def enforced(actual, baseline):
    """Extension absence is enforced for the candidate's processes and, when
    the baseline is the develop pin (which has no extensions), for the
    baseline's as well."""
    return actual == "candidate" or baseline == a.BASE


def same(left, right):
    return json.dumps(left, sort_keys=True) == json.dumps(right,
                                                         sort_keys=True)


def replay_gate(report):
    gate = report["semantic_gate"]
    if report["mode"] != "isolated-source":
        require(gate == semantic_status(report["mode"]),
                "a light run has no semantic gate")
        return
    require(isinstance(gate, dict) and gate["cases"] == 8 and
            gate["candidate_sources_bound"] is True,
            "missing semantic gate")
    path = Path(gate["receipt"])
    if path.exists():
        require(a.seal(path) == gate["seal"], "changed semantic receipt")
        receipt = a.load(path)
        require(receipt["pass"] is True and len(receipt["cases"]) == 8,
                "failed semantic gate")
        inventory = a.safe_child(path.parent, receipt["actual_files"]["file"])
        require(a.seal(inventory) == gate["actual_files"],
                "changed semantic input inventory")


def replay_run(folder, report, entry):
    """One archived process: its seal, its label and its recorded fields."""
    path = a.safe_child(folder, entry["receipt"])
    require(a.seal(path) == entry["seal"], "changed process receipt")
    label = receipt_label(entry["phase"], entry["pair"],
                          entry["selection"], entry["rep"])
    require(entry["receipt"] == label + ".json.gz",
            "relabelled process: " + entry["receipt"])
    receipt = a.load(path)
    require(all(receipt[k] == entry[k] for k in
                ("phase", "pair", "selection", "rep")) and
            receipt["accepted"] == entry["accepted"],
            "process receipt disagrees with the report: " + label)
    actual = "baseline" if entry["phase"] == "control" else entry["selection"]
    baseline = report["selections"]["baseline"]["revision"]
    require(receipt["actual_selection"] == actual,
            "wrong actual selection: " + label)
    env = receipt["environment"]
    private = report["selections"][actual]["private"]
    require(receipt["command"] == [private + "/paired.exe"],
            "wrong launcher command: " + label)
    require(receipt["cwd"] == private and env["PAIR_PRIVATE"] == private,
            "wrong launcher directory: " + label)
    require(env["LOADING_MODULE"] == report["module"],
            "wrong module in the environment: " + label)
    require(env["PAIR_SELECTION"] == entry["selection"] and
            env["PERF_LAYOUT"] == str(layout_units(
                report["layout_seed"], entry["phase"], entry["pair"],
                entry["selection"], entry["rep"])),
            "wrong environment or layout: " + label)
    events = rp.parse_events(receipt["stdout"])
    _, measured = observations(events, report["module"])
    measurement = dict(receipt["measurement"])
    flag = measurement.pop("extension_absence_enforced")
    require(same(measured, measurement),
            "changed measurement: " + entry["receipt"])
    require(flag is enforced(actual, baseline),
            "wrong extension enforcement: " + label)
    require(not (flag and measured["extensions_loaded"]),
            "extension module loaded: " + entry["receipt"])
    return dict(receipt, pair=entry["pair"], selection=entry["selection"],
                rep=entry["rep"], accepted=entry["accepted"])


def replay_stage(report, first_dir, ledger):
    """The second stage is bound to its first stage's seal and count.
    Returns the first stage's attempt id (None for a first stage)."""
    if report["stage"] == "first":
        require("first_stage" not in report, "a first stage has no parent")
        if report["mode"] == "isolated-source":
            require((report["pairs"], report["reps"], report["layout_seed"],
                     report["selections"]["baseline"]["revision"]) ==
                    (PAIRS, REPS, LAYOUT_SEED, a.BASE),
                    "a decision run is exactly %d pairs of %d fresh "
                    "imports" % (PAIRS, REPS))
        return None
    require(report["mode"] == "isolated-source", "only decisions extend")
    require("first_stage" in report, "a second stage names its first stage")
    link = report["first_stage"]
    parent = first_stage(first_dir or link["run"],
                         link["seal"]["sha256"], ledger)
    first = parent["report"]
    require(report["pairs"] == parent["pairs"] == link["second_stage_pairs"]
            and link["pairs"] == first["pairs"] and
            report["reps"] == first["reps"] and
            report["layout_seed"] == EXTENSION_SEED and
            report["module"] == first["module"],
            "the second stage differs from the plan of its first stage")
    require(link["attempt"] == first["attempt"],
            "the second stage names another attempt of its first stage")
    for side in ("baseline", "candidate"):
        require(report["selections"][side]["revision"] ==
                first["selections"][side]["revision"],
                "the second stage changes the " + side)
    require(source_seals(report["selections"]) ==
            source_seals(first["selections"]),
            "the second stage's sources are not the first stage's")
    return first["attempt"]


def replay_all(folder, first_dir=None, expect_seal=None, ledger=None):
    """Recompute every observation, extension check and decision of a
    finished run from its archived process receipts. A decision run is also
    checked against the attempts ledger (`ledger`, by default the one of the
    checkout that measured). Returns the summary, the report and its
    results. A malformed report is refused, not a traceback."""
    try:
        return replay_checked(folder, first_dir, expect_seal, ledger)
    except (KeyError, TypeError, IndexError, AttributeError) as error:
        raise ValueError("malformed loading report: %s: %s" % (
            type(error).__name__, error))


def replay_checked(folder, first_dir, expect_seal, ledger):
    folder = Path(folder).resolve(strict=True)
    seal = a.seal(folder / "loading.json")
    require(expect_seal is None or seal["sha256"] == expect_seal,
            "loading.json differs from the expected seal")
    report = a.load(folder / "loading.json")
    require(report.get("schema") == SCHEMA and report["success"],
            "not a successful " + SCHEMA + " run")
    mode = report["mode"]
    require(mode in ("smoke", "calibration", "isolated-source") and
            report.get("stage") in ("first", "second") and
            report["module"] in MODULES, "malformed loading report")
    module, pairs, reps = report["module"], report["pairs"], report["reps"]
    check_seed(report["layout_seed"])
    require(report["policy"] == POLICY, "unexpected loading policy")
    light = mode != "isolated-source"
    require(reps >= 1 and pairs >= (1 if mode == "smoke" else 10),
            "too few pairs or repetitions")
    first_attempt = replay_stage(report, first_dir, ledger)
    order = expected_runs(pairs, reps, mode == "calibration")
    require([(r["phase"], r["pair"], r["selection"], r["rep"])
             for r in report["runs"]] == order,
            "missing, extra or reordered processes")
    by_phase = {}
    for entry in report["runs"]:
        row = replay_run(folder, report, entry)
        by_phase.setdefault(entry["phase"], []).append(row)
    every = [r for rows in by_phase.values() for r in rows]
    check_new_stems(every)
    pilots = by_phase.pop("pilot")
    require(same(report["calibration"], [p["measurement"] for p in pilots]),
            "recomputed calibration differs from the report")
    results = {phase: statistics(rows, pairs, mode == "smoke", reps)
               for phase, rows in by_phase.items()}
    if not light:
        for metric, data in results["candidate"]["metrics"].items():
            a.apply_control(data, results["control"]["metrics"][metric])
            if data.get("gated", True) and not all(
                    p["measurement"]["calibrated"] for p in pilots):
                data["decision"] = "inconclusive"
                data["reason"] = "uncalibrated pilot import"
    require(same(results, report["results"]),
            "recomputed statistics differ from the report")
    if mode == "calibration":
        require(same(jitter(by_phase["control"], results["control"], pairs,
                            reps), report["jitter"]),
                "recomputed jitter differs from the report")
    if not light:
        control = results["control"]
        require(report["control_half_log_width"] ==
                finite(control_width(control)) and
                report["second_stage_pairs"] ==
                second_stage_count(control, pairs),
                "recomputed control width or count differs from the report")
    replay_gate(report)
    status = None if light else exit_status(results["candidate"]["metrics"])
    info = dict(replayed=len(report["runs"]), exit=status,
                stage=report["stage"], seal=seal)
    if mode == "calibration":
        info["covered"] = covered(report["jitter"])
    if not light:
        info["attempts"] = check_ledger(
            ledger or ledger_path(report["repo"]), report, seal,
            DECISIONS[status], first_attempt)
    return info, report, results


def first_stage(folder, expect_seal=None, ledger=None):
    """A replayed first-stage decision run and the pairs of its second."""
    info, report, results = replay_all(folder, expect_seal=expect_seal,
                                       ledger=ledger)
    return dict(folder=Path(folder).resolve(), seal=info["seal"],
                report=report, pairs=second_stage_plan(report, results))


def replay(folder, first_dir=None, expect_seal=None, ledger=None):
    return replay_all(folder, first_dir, expect_seal, ledger)[0]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path)
    parser.add_argument("--baseline")
    parser.add_argument("--candidate")
    parser.add_argument("--module", choices=MODULES)
    parser.add_argument("--pairs", type=int,
                        help="pairs of --smoke (at most %d) or --calibrate "
                        "runs; a decision run is exactly %d" %
                        (SMOKE_PAIRS, PAIRS))
    parser.add_argument("--reps", type=int,
                        help="fresh processes per side of a pair; a "
                        "decision run is exactly %d" % REPS)
    parser.add_argument("--layout-seed",
                        help="code-layout seed (smoke/calibration; not "
                        "a decision run's); a decision run uses " +
                        LAYOUT_SEED)
    parser.add_argument("--calibrate", action="store_true",
                        help="B/B only: measure jitter, derive the counts")
    parser.add_argument("--extend", type=Path, metavar="RUN_DIR",
                        help="the second stage of a first-stage run whose "
                        "B/B control missed its window")
    parser.add_argument("--replay", type=Path, metavar="RUN_DIR",
                        help="recompute a finished run's decisions")
    parser.add_argument("--expect-seal", metavar="SHA256",
                        help="with --replay: the seal of loading.json")
    parser.add_argument("--first-stage", type=Path, metavar="RUN_DIR",
                        help="with --replay: where the first stage now is")
    parser.add_argument("--ledger", type=Path, metavar="FILE",
                        help="with --replay or --ledger-status: "
                        "the attempts ledger of the checkout that measured "
                        "(a copy of it, for --replay and --ledger-status)")
    parser.add_argument("--ledger-status", action="store_true",
                        help="print the ledger's attempts (of --module "
                        "when given), void or why judged, without a replay")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--api-audit", type=Path)
    parser.add_argument("--timeout", type=float)
    parser.add_argument("--smoke", action="store_true",
                        help="a harness check of at most %d pairs of %d "
                        "import, recorded in the attempts ledger" %
                        (SMOKE_PAIRS, SMOKE_REPS))
    parser.add_argument("--authorize-measurements", action="store_true")
    args = parser.parse_args(argv)
    given = {k for k, v in vars(args).items() if v not in (None, False)}
    try:
        require(not (args.replay and args.extend),
                "--replay and --extend are exclusive")
        if args.replay:
            others = given - {"replay", "expect_seal", "first_stage",
                              "ledger"}
            require(not others, "--replay takes only --expect-seal, "
                    "--first-stage and --ledger, not: " +
                    ", ".join(sorted(others)))
            info = replay(args.replay, args.first_stage, args.expect_seal,
                          args.ledger)
            print(json.dumps(info))
            return 0
        if args.ledger_status:
            others = given - {"repo", "ledger", "ledger_status", "module"}
            require(not others, "--ledger-status takes only --repo, "
                    "--ledger and --module, not: " +
                    ", ".join(sorted(others)))
            args.repo = args.repo or HERE.parents[3]
            print(json.dumps(ledger_status(args)))
            return 0
        require(not (given & {"expect_seal", "first_stage", "ledger"}),
                "--expect-seal, --first-stage and --ledger belong to "
                "--replay (--ledger also to --ledger-status)")
        args.repo = args.repo or HERE.parents[3]
        args.timeout = args.timeout or 1800
        first = None
        if args.extend:
            others = given - {"extend", "repo", "output", "api_audit",
                              "timeout", "authorize_measurements"}
            require(not others, "--extend takes its settings from the first "
                    "stage, not: " + ", ".join(sorted(others)))
            require(args.output, "--output is required")
            first = first_stage(args.extend,
                                ledger=ledger_path(args.repo))
            report = first["report"]
            args.baseline = report["selections"]["baseline"]["revision"]
            args.candidate = report["selections"]["candidate"]["revision"]
            args.module = report["module"]
            args.pairs, args.reps = first["pairs"], report["reps"]
            args.layout_seed = EXTENSION_SEED
            args.api_audit = args.api_audit or Path(
                report["semantic_gate"]["receipt"])
        else:
            require(args.baseline and args.module and args.output,
                    "--baseline, --module and --output are required")
            if args.calibrate and args.candidate is None:
                args.candidate = args.baseline
            require(args.candidate, "--candidate required")
            args.layout_seed = args.layout_seed or (
                SMOKE_SEED if args.smoke else LAYOUT_SEED)
            light = args.smoke or args.calibrate
            args.pairs = args.pairs or (
                PAIRS if not light else 1 if args.smoke else 10)
            args.reps = args.reps or (REPS if not light else 1)
        report = run(args, first)
        print(json.dumps({k: report[k] for k in
                          ("success", "mode", "module", "stage")}))
        if not report["success"]:
            return 2
        if args.smoke or args.calibrate:
            return 0
        return exit_status(report["results"]["candidate"]["metrics"])
    except (ValueError, OSError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
