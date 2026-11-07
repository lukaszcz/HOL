#!/usr/bin/env python3
"""Fresh ordinary first-import timing; NOT independent/release approval."""
import argparse
import gzip
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

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "compatibility"))
import acceptance as a
import run_paired as rp

MODULES = ("simpLib", "congLib")
FIELDS = ("wall", "nongc_usr", "nongc_sys", "gc_usr", "gc_sys",
          "cpu_usr", "cpu_sys", "gc_user_only")
METRICS = ("wall", "cpu", "gc_cpu")
# TASK31 loading unit: every sample is the mean of REPS first imports, each in
# its own fresh process; a module is never loaded twice in one process.
REPS = 5
PAIRS = 40
SCHEMA = "task31-loading-v3"
POLICY = a.EQUIVALENCE_POLICY  # the timing grid's 3% margin, one definition
# Names that no ordinary import may load (the API audit's forbidden list).
EXTENSION_NAMES = (
    "TraverseExt", "Cond_rewrExt", "OpeningExt", "TravrulesExt",
    "simpExtLib", "congExtLib", "pureSimpsExt", "boolSimpsExt",
    "combinSimpsExt", "numSimpsExt", "pred_setSimpsExt", "listSimpsExt",
    "intReduceExt", "integer_wordLibExt", "realSimpsExt", "SimpTracking",
    "trackedSimpDefaults", "simpMarkerTheory", "simpMarkerLib",
    "SplitData", "splitLib", "splitPersistLib")
NO_EXTENSIONS = "none"


def extension_name(name):
    return (name in EXTENSION_NAMES or name.endswith(("Ext", "ExtLib"))
            or name.startswith("simpMarker"))
# The loading call is a top-level runner operation, NOT inside a pending
# traced selftest use. Thus nested source uses never defeat rp.validate.
TIMING = '''fun loadingMeasure f = let
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
  val bound = List.filter (fn n =>
    Option.isSome (#lookupStruct PolyML.globalNameSpace n)) loadingProbe
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
TIMING = TIMING.replace("@PROBE@", ", ".join(
    '"%s"' % n for n in EXTENSION_NAMES)).replace("@NONE@", NO_EXTENSIONS)
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


def require(ok, message):
    rp.require(ok, message)


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
    text = text.replace(anchor, TIMING + anchor).replace(
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
            "loading.end", "loading.raw"]
    keys.append("loading.extensions")
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
    found = sorted(set(obs[5][2].split(",")) - {NO_EXTENSIONS})
    # Also the sources the process actually used and the final file map.
    found = sorted(set(found) | {
        Path(e[1]).stem for e in events
        if e[0] in ("use", "used", "heapfile", "loaded") and
        extension_name(Path(e[1]).stem)})
    return obs, {"raw": raw, "empty": empty, "accounting": accounting,
                 "extensions_loaded": found, "calibrated": calibrated,
                 "calibration_rule": "wall/cpu >=100*max(empty,1us)"}


def validate(receipt, *, side, dst, repo, names, sources, module,
             enforce_absence=False):
    """`enforce_absence` is for the candidate: the historical baseline need
    not satisfy the extension split, so its loaded extensions are recorded
    but never rejected."""
    events = rp.parse_events(receipt["stdout"])
    obs, measurement = observations(events, module)
    measurement["extension_absence_enforced"] = bool(enforce_absence)
    require(not (enforce_absence and measurement["extensions_loaded"]),
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
    for name, seal in receipt["sources"].items():
        require(Path(name).name == name and a.seal(audit_dir / name) == seal,
                "semantic gate fixture changed")
    require(set(receipt["sources"]) == {"run.py", "Holmakefile",
            "selftest.sml", "ordinary.ML", "runtime.ML", "Documentation.sml"},
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
        count = {("attribute", "before"): 172,
                 ("attribute", "after"): 168,
                 ("exporter", "before"): 176,
                 ("exporter", "after"): 171}[key[1:]]
        require(case["pass"] is True and case["returncode"] == 0 and
                case["validation_error"] is None and case["checks"] == count,
                "failed semantic process")
        log = a.safe_child(path.parent, case["log"])
        require(log not in used_logs and a.seal(log) == case["log_seal"],
                "changed/duplicate semantic log")
        used_logs.add(log)
        text = gzip.decompress(log.read_bytes()).decode()
        import re
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
        for module in ("simpLib", "congLib", "Traverse", "Cond_rewr",
                       "Trace", "SimpTracking", "simpExtLib", "TraverseExt",
                       "Cond_rewrExt", "congExtLib"):
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


def control_width(control):
    """Larger half log-width of the B/B intervals of the gated metrics: the
    quantity the timing grid's second-stage rule reads."""
    width = 0.0
    for metric, data in control["metrics"].items():
        if data.get("gated", True) is False:
            continue
        ci = data["paired_ratio_bootstrap_95_percent"]
        width = max(width, math.log(ci[1] / ci[0]) / 2
                    if ci and ci[0] > 0 else math.inf)
    return width


def pairs_for(width, pairs):
    """Pairs for the grid's target half width, scaled from a B/B interval of
    `width` at `pairs` pairs (n proportional to width squared)."""
    import timing_grid as tg
    wanted = pairs * (width / tg.TARGET) ** 2
    return None if not math.isfinite(wanted) else \
        max(10, 10 * math.ceil(wanted / 10))


def run(args):
    require(args.module in MODULES, "unknown ordinary module")
    light = args.smoke or args.calibrate
    require(not (args.smoke and args.calibrate),
            "--smoke and --calibrate are exclusive")
    require(args.reps >= 1, "invalid repetitions")
    require(args.pairs >= (1 if args.smoke else 10),
            "acceptance requires >=10 pairs (or explicit --smoke)")
    require(light or (args.pairs >= PAIRS and args.reps >= REPS),
            "acceptance requires >=%d pairs of %d fresh imports each "
            "(or --smoke/--calibrate)" % (PAIRS, REPS))
    require(args.timeout > 0, "invalid timeout")
    require(args.authorize_measurements,
            "measurement authorization required")
    a.exact_pin(args.baseline)
    a.exact_pin(args.candidate)
    require(light or args.api_audit,
            "candidate eight-process --api-audit receipt required")
    repo, output = args.repo.resolve(strict=True), args.output.resolve()
    with a.serial_lock(repo) as fds:
        output.mkdir(parents=True, exist_ok=False)
        report = {"schema": SCHEMA, "success": False,
                  "mode": "smoke" if args.smoke else
                  "calibration" if args.calibrate else "isolated-source",
                  "claims": "NOT independent-build or release acceptance",
                  "repo": str(repo), "module": args.module,
                  "pairs": args.pairs, "reps": args.reps,
                  "outliers": "none removed",
                  "policy": POLICY, "timer_fields": FIELDS,
                  "timeout": args.timeout, "selections": {}, "runs": [],
                  "argv": sys.argv, "inputs": {}, "tools": {}}
        try:
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
                     HERE / "performance_schema.py"]
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
                    sources.update(extracted_seals(inventory, dst))
                    install(dst, args.module)
                    check_seals(sources)
                    # Seal generated fixture inputs BEFORE the build as well.
                    for path in dst.rglob("*"):
                        if path.is_file() and str(path) not in sources:
                            sources[str(path)] = a.seal(path)
                    selected = {"revision": pin, "private": str(dst),
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
                if args.api_audit:
                    report["semantic_gate"] = semantic_gate(
                        args.api_audit, repo,
                        report["selections"]["candidate"]["sources"])
                else:
                    report["semantic_gate"] = "not admitted: smoke only"
                shared = {}

                def launch(phase, pair, side, rep=0):
                    actual = "baseline" if phase == "control" else side
                    dst = root / actual
                    runenv = dict(env, PAIR_SELECTION=side,
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
                                                                 "LOADING_"))},
                                   accepted=False)
                    try:
                        result, measurement = validate(
                            receipt, side=side, dst=dst, repo=repo,
                            names=names,
                            sources=sources, module=args.module,
                            enforce_absence=actual == "candidate")
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
                    except (ValueError, OSError) as error:
                        receipt["rejection"] = str(error)
                    label = "%s-%03d-%s-%02d" % (phase, pair, side, rep)
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
                    rows = [dict(launch(phase, i, side, r), rep=r)
                            for i, side, r in schedule(args.pairs,
                                                       args.reps)]
                    results[phase] = statistics(
                        rows, args.pairs, args.smoke, args.reps)
                if args.calibrate:
                    report["jitter"] = jitter(results["control"], args.pairs,
                                              args.reps)
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
                if not light:
                    width = control_width(results["control"])
                    report["control_half_log_width"] = width
                    report["pairs_for_target"] = pairs_for(width, args.pairs)
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
        finally:
            a.save(output / "loading.json", report)
    return report


def exit_status(metrics):
    """0 only when every gated metric passes; gc_cpu is reported only."""
    decisions = [m["decision"] for m in metrics.values()]
    return 1 if "fail" in decisions else \
        2 if any(d not in ("pass", "reported") for d in decisions) else 0


def jitter(control, pairs, reps):
    """What B/B says about the host: per metric the median and interval of
    the paired ratio, and the pairs the grid's rule would ask for."""
    found = {}
    for metric, data in control["metrics"].items():
        ci = data["paired_ratio_bootstrap_95_percent"]
        logs = [math.log(v) for row in data["observations"]
                for v in row.values() if v > 0]
        mean = math.fsum(logs) / len(logs) if logs else None
        sd = (math.sqrt(math.fsum((x - mean) ** 2 for x in logs) /
                        (len(logs) - 1)) if len(logs) > 1 else None)
        found[metric] = dict(
            median=data["median_paired_ratio"], ci95=ci,
            sample_log_sd=sd, gated=data.get("gated", True))
    width = control_width(control)
    return dict(metrics=found, half_log_width=width,
                pairs_for_target=pairs_for(width, pairs), pairs=pairs,
                reps=reps)


def replay(folder):
    """Recompute every observation, extension check and decision of a
    finished run from its archived process receipts."""
    folder = Path(folder).resolve(strict=True)
    report = a.load(folder / "loading.json")
    require(report.get("schema") == SCHEMA and report["success"],
            "not a successful " + SCHEMA + " run")
    module, pairs, reps = report["module"], report["pairs"], report["reps"]
    require(report["policy"] == POLICY, "unexpected loading policy")
    light = report["mode"] != "isolated-source"
    by_phase = {}
    for run_ in report["runs"]:
        path = a.safe_child(folder, run_["receipt"])
        require(a.seal(path) == run_["seal"], "changed process receipt")
        receipt = a.load(path)
        events = rp.parse_events(receipt["stdout"])
        _, measured = observations(events, module)
        require(measured == {k: v for k, v in receipt["measurement"].items()
                             if k != "extension_absence_enforced"},
                "changed measurement: " + run_["receipt"])
        actual = receipt["actual_selection"]
        require(not (actual == "candidate" and
                     measured["extensions_loaded"]),
                "extension module loaded by candidate: " + run_["receipt"])
        row = dict(receipt, pair=run_["pair"], selection=run_["selection"],
                   rep=run_["rep"], accepted=run_["accepted"])
        by_phase.setdefault(run_["phase"], []).append(row)
    pilots = by_phase.pop("pilot")
    require(len(pilots) == 2, "missing pilots")
    results = {phase: statistics(rows, pairs, report["mode"] == "smoke",
                                 reps)
               for phase, rows in by_phase.items()}
    if not light:
        for metric, data in results["candidate"]["metrics"].items():
            a.apply_control(data, results["control"]["metrics"][metric])
            if data.get("gated", True) and not all(
                    p["measurement"]["calibrated"] for p in pilots):
                data["decision"] = "inconclusive"
                data["reason"] = "uncalibrated pilot import"
    require(json.dumps(results, sort_keys=True) ==
            json.dumps(report["results"], sort_keys=True),
            "recomputed statistics differ from the report")
    status = None if light else exit_status(results["candidate"]["metrics"])
    return {"replayed": len(report["runs"]), "exit": status}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[3])
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--candidate")
    parser.add_argument("--module", choices=MODULES, required=True)
    parser.add_argument("--pairs", type=int, default=PAIRS)
    parser.add_argument("--reps", type=int, default=REPS,
                        help="fresh processes per side of a pair")
    parser.add_argument("--calibrate", action="store_true",
                        help="B/B only: measure jitter, derive pairs")
    parser.add_argument("--replay", type=Path,
                        help="recompute a finished run's decisions")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--api-audit", type=Path)
    parser.add_argument("--timeout", type=float, default=1800)
    parser.add_argument("--smoke", action="store_true")
    parser.add_argument("--authorize-measurements", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.replay:
            print(json.dumps(replay(args.replay)))
            return 0
        if args.calibrate and args.candidate is None:
            args.candidate = args.baseline
        require(args.candidate, "--candidate required")
        report = run(args)
        print(json.dumps({k: report[k] for k in
                          ("success", "mode", "module")}))
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
