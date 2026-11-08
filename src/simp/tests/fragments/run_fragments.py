#!/usr/bin/env python3
"""TASK15 isolated-source fragment probes; not independent repository builds."""
import argparse
import gzip
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import shutil
import statistics
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "compatibility"))
import run_paired as paired

SIZES = (0, 1, 10, 100, 1000, 10000)
LABELS = ("rewrites", "rewrites_with_names", "named_rewrites",
          "named_rewrites_with_names", "SSFRAG", "update", "add_named_rwt",
          "merge", "merge_duplicate", "merge_named", "named_merge",
          "ac_create", "ac_merge", "type_create", "type_lookup")
# Match registry/context state with API-compatible cold dependencies only.
# Cond_rewrExt cannot elaborate against pinned Cond_rewr; do not transform
# that public signature or claim this is a complete matching of loaded code.
MATCHED_MODULES = ("TraverseExt", "simpMarkerTheory",
                   "simpMarkerLib", "SplitData", "splitLib")

EXTRAS = ("empty", "update callback and persistence",
          "update exception identity", "anonymous registration rejects",
          "named registration", "named registration replacement",
          "partition preserves duplicates and order",
          "rewrite name survives update and merge", "missing TypeBase rejects")


def require(ok, message):
    paired.require(ok, message)


def integers(text, count):
    fields = text.split(",")
    require(len(fields) == count and all(f.isdecimal() for f in fields),
            "invalid integer row")
    return list(map(int, fields))


def payload(text):
    return [e for e in paired.parse_events(text)
            if e[0] in ("observation", "check", "exception")]


def behavior(text):
    events = payload(text)
    cursor, graphs = 0, {label: [] for label in LABELS}
    for n in SIZES:
        for label in (*LABELS, "cells"):
            key = "control.cells" if label == "cells" else "graph." + label
            require(cursor + 1 < len(events), "missing graph row")
            event = events[cursor]
            require(event[:2] == ["observation", key] and len(event) == 3,
                    "missing/unordered graph observation")
            size, words = integers(event[2], 2)
            require(size == n, "wrong graph size")
            if label == "cells":
                require(words == 5 * n, "allocation sensitivity control failed")
            else:
                graphs[label].append([n, words])
            require(events[cursor + 1] ==
                    ["check", label + " " + str(n), "pass"],
                    "missing graph proof check")
            cursor += 2
    expected = [["check", name, "pass"] for name in EXTRAS]
    expected += [["observation", "complete", "TASK15-fragments-v1"]]
    require(events[cursor:] == expected, "incomplete behavior observations")
    return events, graphs


def fixed_iterations(values):
    keys = {label + "." + str(n) for n in SIZES for label in LABELS}
    require(isinstance(values, dict) and set(values) == keys,
            "fixed iterations must contain exactly all 90 workload keys")
    require(all(type(v) is int and v > 0 for v in values.values()),
            "fixed iteration counts must be positive integers")
    return {key: values[key] for key in sorted(keys)}


def load_fixed_iterations(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "duplicate fixed iteration key: " + key)
            result[key] = value
        return result

    data = path.read_bytes()
    values = fixed_iterations(json.loads(data, object_pairs_hook=unique))
    seal = dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))
    return values, seal


def timing(text, samples, seconds, fixed=None):
    if fixed is not None:
        fixed = fixed_iterations(fixed)
    events, cursor, total = payload(text), 0, 0

    def take(prefix):
        nonlocal cursor
        require(cursor < len(events), "missing timing event")
        e = events[cursor]
        require(e[:len(prefix)] == prefix, "wrong ordered timing event")
        if prefix[0] == "check":
            require(e == prefix, "invalid timing check")
        cursor += 1
        return e

    def metrics(fields, count):
        nonlocal total
        require(len(fields) == 9, "wrong timing metrics arity")
        try:
            values = [float(v.replace("~", "-")) for v in fields[:8]]
        except ValueError:
            raise paired.InvalidRun("invalid timing metric")
        require(all(math.isfinite(v) and v >= 0 for v in values) and
                values[0] > 0, "invalid timing metric")
        used, = integers(fields[-1], 1)
        require(used == count, "unconsumed timing result")
        total += used
        wall, usr, sys_, gu, gs, cu, cs, gc = values
        require(abs(cu - usr - gu) < .02 and abs(cs - sys_ - gs) < .02
                and abs(gc - gu) < .02, "invalid timer accounting")
        return dict(wall=wall / count, cpu=(usr + sys_ + gu + gs) / count,
                    nongc_cpu=(usr + sys_) / count, gc_cpu=(gu + gs) / count,
                    user_cpu=(usr + gu) / count,
                    system_cpu=(sys_ + gs) / count,
                    iterations=count, raw=values)

    accounting = take(["observation", "timer.accounting"])
    require(len(accounting) == 3, "invalid accounting event")
    metrics(accounting[2].split(","), 5)
    take(["check", "timer accounting", "pass"])
    results = {}
    for n in SIZES:
        for label in LABELS:
            key = label + "." + str(n)
            count = fixed[key] if fixed is not None else 1
            while True:
                e = take(["observation", "calibration." + key])
                require(len(e) == 3, "invalid calibration event")
                fields = e[2].split(",")
                actual, = integers(fields[0], 1)
                require(actual == count and
                        (fixed is not None or count <= 1073741824),
                        "invalid calibration iterations")
                row = metrics(fields[1:], count)
                wall = row["raw"][0]
                if fixed is not None or wall >= seconds:
                    break
                count *= 2
            rows = []
            for i in range(samples):
                e = take(["observation", "batch." + key])
                require(len(e) == 3, "invalid batch event")
                fields = e[2].split(",")
                require(integers(",".join(fields[:2]), 2) == [i, count],
                        "wrong sample/iterations")
                rows.append(metrics(fields[2:], count))
                take(["check", "results " + key, "pass"])
            results[key] = rows
    require(take(["observation", "sink"]) ==
            ["observation", "sink", str(total)], "wrong sink total")
    require(cursor == len(events), "extra timing event")
    return events, results


def graph_comparison(selections):
    result = {}
    for label in LABELS:
        a, b = (selections[s]["graphs"][label]
                for s in ("baseline", "candidate"))
        result[label] = dict(
            candidate_minus_baseline_words=[y[1] - x[1]
                                            for x, y in zip(a, b)],
            adjacent_words_per_input={side: [
                (y[1] - x[1]) / (y[0] - x[0])
                for x, y in zip(rows, rows[1:])]
                for side, rows in (("baseline", a), ("candidate", b))})
    return result


def require_baseline_graphs(comparison):
    for label, data in comparison.items():
        require(all(delta <= 0 for delta in
                    data["candidate_minus_baseline_words"]),
                "increased retained fragment words: " + label)


def timing_comparison(runs):
    """One median per process, then paired ratios; no regression allowance."""
    result = {}
    pairs = sorted({r["pair"] for r in runs})
    for n in SIZES:
        for label in LABELS:
            key = label + "." + str(n)
            result[key] = {}
            for metric in ("cpu", "wall", "nongc_cpu", "gc_cpu",
                           "user_cpu", "system_cpu"):
                ratios, medians = [], []
                for pair in pairs:
                    a, b = [statistics.median(
                        row[metric] for row in next(r for r in runs if
                            r["pair"] == pair and r["selection"] == side)
                        ["measurements"][key])
                        for side in ("baseline", "candidate")]
                    medians.append([a, b])
                    ratios.append(b / a if a else None)
                valid = [r for r in ratios if r is not None]
                result[key][metric] = dict(
                    process_medians=medians, paired_ratios=ratios,
                    median_paired_ratio=(statistics.median(valid)
                                         if valid else None))
    return result


def worktree_sources(repo):
    root = repo / "src/simp/src"
    return sorted(p for p in [*root.glob("*.sml"), *root.glob("*.sig"),
                             *root.glob("poly/*.sml"), *root.glob("poly/*.sig")]
                  if p.name != "selftest.sml")


def snapshot(repo, ref, dst):
    rev = paired.git(repo, "rev-parse", ("HEAD" if ref == "worktree" else ref)
                     + "^{commit}").decode().strip()
    inventory = paired.extract(repo, rev, dst)
    if ref != "worktree":
        return rev, inventory
    # Only a task-owned temporary source tree is changed. No worktree products
    # or production sources are built/edited. Include new root/poly modules.
    for source in inventory:
        (dst / Path(source["git_path"]).name).unlink()
    inventory = []
    for source in worktree_sources(repo):
        target = dst / source.name
        require(not target.exists(), "flattened worktree source collision")
        target.write_bytes(source.read_bytes())
        inventory.append(dict(git_path=str(source.relative_to(repo)),
                              private_path=str(target), git_blob=None,
                              **paired.fingerprint(target)))
    return rev, inventory


def positive_integer(text):
    value = int(text)
    if value <= 0:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return value


def supplement_snapshot(repo, dst):
    """Seal the explicit current dependency closure, including theory data.

    Generated theory files are existing worktree products, not regenerated
    pinned sources. Their provenance is deliberately separate from selections.
    """
    dst.mkdir()
    sources = []
    for module in MATCHED_MODULES:
        generated = module == "simpMarkerTheory"
        base = repo / "src/simp/src"
        if generated:
            base = base / ".hol/objs"
        for suffix in ((".sig", ".sml", ".dat") if generated else
                       (".sig", ".sml")):
            source = base / (module + suffix)
            target = dst / source.name
            target.write_bytes(source.read_bytes())
            sources.append(dict(source_path=str(source),
                source_physical=str(source.resolve(strict=True)),
                snapshot_path=str(target), generated=generated,
                **paired.fingerprint(target)))
    return sources


def install_supplements(dst, sources):
    added = []
    for source in sources:
        original = Path(source["snapshot_path"])
        base = dst / ".hol/objs" if source["generated"] else dst
        target = base / original.name
        if target.exists() or (dst / original.name).exists():
            continue  # A selected baseline/candidate file is NEVER replaced.
        require(paired.fingerprint(original) ==
                {k: source[k] for k in ("sha256", "bytes")},
                "supplement snapshot drift: " + str(original))
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(original.read_bytes())
        added.append(dict(source, private_path=str(target)))
    return added


def verify_supplements(sources, installed):
    for source in sources:
        path = Path(source["source_path"])
        seal = {k: source[k] for k in ("sha256", "bytes")}
        require(str(path.resolve(strict=True)) == source["source_physical"] and
                paired.fingerprint(path) == seal and
                paired.fingerprint(Path(source["snapshot_path"])) == seal,
                "supplement source drift: " + str(path))
    for source in installed:
        path = Path(source["private_path"])
        require(paired.fingerprint(path) ==
                {k: source[k] for k in ("sha256", "bytes")},
                "installed supplement drift: " + str(path))


def install_matched_runner(dst):
    path = dst / "runner.sml"
    text = path.read_text()
    anchor = 'Meta.loadPlan tracedUse "CheckSupport";\n'
    require(text.count(anchor) == 1, "wrong private runner preload anchor")
    loads = "".join('   Meta.loadPlan tracedUse "' + name + '";\n'
                    for name in MATCHED_MODULES)
    path.write_text(text.replace(anchor, anchor + loads))


def validate_matched_trace(events, dst, target):
    used = [e[1] for e in events if e[0] == "use"]
    support, fixture = (str(dst / (name + ".sml"))
                        for name in ("CheckSupport", target))
    require(support in used and fixture in used, "missing matched load bounds")
    for module in MATCHED_MODULES:
        source = str(dst / (module + ".sml"))
        require(used.count(source) == 1 and
                used.index(support) < used.index(source) < used.index(fixture),
                "missing/repeated/late matched preload: " + module)
    require(not any(Path(e[1]).stem == "simpExtLib" for e in events
                    if e[0] in ("use", "used", "loaded", "heapfile")) and
            not any("simpExtLib" in e[1].split(",") for e in events
                    if e[0] == "preloaded"),
            "simpExtLib is forbidden in matched diagnostic")


def private_holmakefile(matched):
    text = ("HOLHEAP = $(HOLDIR)/bin/hol.state0\n"
            "paired.exe: runner.uo CheckSupport.uo selftest.uo "
            "FragmentPerformance.uo" +
            (" " + " ".join(name + ".uo" for name in MATCHED_MODULES)
             if matched else "") + "\n"
            "\t$(HOLMOSMLC) -o $@ $<\n")
    if matched:
        # These are sealed prebuilt inputs, not implicit Script targets.
        text += ("simpMarkerTheory.sml simpMarkerTheory.sig "
                 "simpMarkerTheory.dat:\n\t@test -f $@\n")
    return text


def configure_launcher(dst, repo, heap_mb):
    path = dst / "paired.exe"
    text = path.read_text()
    prefix = str(repo / "bin/hol") + " --gcthreads=1 run "
    require(text.count(prefix) == 1 and
            "--holstate=" + str(repo / "bin/hol.state0") in text,
            "wrong launcher runtime/heap/options")
    options = ["--gcthreads=1"]
    if heap_mb is not None:
        options += ["--minheap=" + str(heap_mb), "--maxheap=" + str(heap_mb)]
        text = text.replace(prefix, str(repo / "bin/hol") + " " +
                            " ".join(options) + " run ")
        path.write_text(text)
    return text, options


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=HERE.parents[3])
    p.add_argument("--baseline", default=paired.BASE)
    p.add_argument("--candidate", default="worktree")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--timeout", type=int, default=600)
    p.add_argument("--require-baseline-graphs", action="store_true",
                   help="fail on increased retained graph rows (no tolerance)")
    p.add_argument("--performance-pairs", type=int, default=0)
    p.add_argument("--samples", type=int, default=3)
    p.add_argument("--seconds", type=float, default=.2)
    p.add_argument("--fixed-iterations", type=Path,
                   help="JSON map of all 90 workload keys to positive counts")
    p.add_argument("--matched-environment", action="store_true",
                   help="mixed-source attribution diagnostic, NOT production")
    p.add_argument("--heap-mb", type=positive_integer,
                   help="identical private Poly/ML min/max heap in MB")
    args = p.parse_args()
    if (args.performance_pairs < 0 or args.samples < 3 or args.timeout <= 0 or
            not math.isfinite(args.seconds) or args.seconds <= 0):
        p.error("invalid pair/sample/batch/timeout options")
    fixed, schedule_seal = None, None
    if args.fixed_iterations is not None:
        args.fixed_iterations = args.fixed_iterations.resolve()
        try:
            fixed, schedule_seal = load_fixed_iterations(args.fixed_iterations)
        except (OSError, ValueError, UnicodeError) as e:
            p.error("invalid fixed iterations: " + str(e))
    repo, output = args.repo.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "PAIR_", "PERF_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    files = [*sorted(HERE.glob("*.sml")), Path(__file__),
             HERE / "test_fragments.py", HERE / "README.md",
             HERE / "Holmakefile",
             Path(paired.__file__),
             *sorted((HERE.parent / "compatibility/paired").glob("*.sml")),
             HERE.parent / "compatibility/paired/Holmakefile"]
    manifest = dict(schema_version=1, success=False,
        evidence_id="TASK15-fragments-v1", repo=str(repo),
        scope="isolated fragment behavior, retained graph words and optional "
              "construction timing; NOT cumulative allocation or "
              "simpset storage",
        machine=platform.machine(), selections={}, runs=[],
        git_status=paired.git(repo, "status", "--porcelain=v1").decode(),
        inputs={str(f.relative_to(repo)): paired.fingerprint(f) for f in files},
        tools={n: paired.fingerprint(repo / n) for n in
               ("bin/hol", "bin/Holmake", "bin/hol.state0")},
        performance=dict(pairs=args.performance_pairs, samples=args.samples,
                         seconds=args.seconds, fixed_iterations=fixed,
                         fixed_iterations_path=(str(args.fixed_iterations)
                             if fixed is not None else None)),
        environment=dict(matched=args.matched_environment,
            heap_mb=args.heap_mb,
            preloads=list(MATCHED_MODULES) if args.matched_environment else [],
            supplement_snapshot=[],
            interpretation=("mixed current dependency diagnostic; NOT pinned "
                "baseline full-source production runtime; mixed imports owned "
                "by TASK16; no overhead-fix or acceptance claim"
                if args.matched_environment else "default isolated sources")),
        shared_products={})
    if fixed is not None:
        manifest["inputs"][str(args.fixed_iterations)] = schedule_seal
    try:
        poly = Path(shutil.which("poly")).resolve()
        manifest["poly"] = dict(path=str(poly), **paired.fingerprint(poly))
        manifest["poly_version"] = paired.execute(
            [str(poly), "--version"], repo, env, args.timeout)
        with tempfile.TemporaryDirectory(prefix="task15-fragments-") as temp:
            root, hashes, inventories = Path(temp), {}, {}
            supplements = (supplement_snapshot(repo, root / "current-deps")
                           if args.matched_environment else [])
            manifest["environment"]["supplement_snapshot"] = supplements
            for side, ref in (("baseline", args.baseline),
                              ("candidate", args.candidate)):
                dst = root / side
                dst.mkdir()
                rev, inventory = snapshot(repo, ref, dst)
                inventories[side] = inventory
                added = install_supplements(dst, supplements)
                paired.install_fixtures(dst)
                for f in HERE.glob("*.sml"):
                    shutil.copyfile(f, dst / f.name)
                if args.matched_environment:
                    install_matched_runner(dst)
                # Only the loader is linked. Dependencies defer elaboration
                # until private-first traced loading in each fresh process.
                (dst / "Holmakefile").write_text(
                    private_holmakefile(args.matched_environment))
                hashes[side] = {str(f): paired.fingerprint(f)
                                for f in dst.iterdir() if f.is_file()}
                hashes[side].update({s["private_path"]:
                    {k: s[k] for k in ("sha256", "bytes")} for s in added})
                selected = dict(revision=rev, reference=ref, sources=inventory,
                    private=str(dst), supplement_sources=added,
                    fixture_products={
                        f.name: paired.fingerprint(f)
                        for f in dst.iterdir() if f.is_file() and f.name not in
                        ({Path(i["git_path"]).name for i in inventory} |
                         {Path(i["private_path"]).name for i in added})})
                manifest["selections"][side] = selected
                build = paired.execute([str(repo / "bin/Holmake"),
                    "--no-project", "--no-cache", "--no_prereqs",
                    "--holstate=" + str(repo / "bin/hol.state0"),
                    "-C", str(dst), "-j1", "paired.exe"],
                    root, env, args.timeout)
                paired.compact(dict(build), output, side + "-build")
                require(build["exit"] == 0 and not build["timed_out"],
                        side + " build failed")
                launcher, options = configure_launcher(dst, repo, args.heap_mb)
                selected.update(launcher=launcher, runtime_options=options,
                    launcher_seal=paired.fingerprint(dst / "paired.exe"))

            def run(side, mode, pair):
                dst = root / side
                target = ("selftest" if mode == "behavior"
                          else "FragmentPerformance")
                runenv = dict(env, PAIR_SELECTION=side, PAIR_FIXTURE=mode,
                    PAIR_CONTROL="none", PAIR_PRIVATE=str(dst),
                    PAIR_TARGET=target,
                    PERF_SAMPLES=str(args.samples),
                    PERF_SECONDS=str(args.seconds))
                if fixed is not None:
                    runenv["PERF_FIXED"] = ",".join(
                        key + "=" + str(count) for key, count in fixed.items())
                selected = manifest["selections"][side]
                verify_supplements(supplements, selected["supplement_sources"])
                require(paired.fingerprint(dst / "paired.exe") ==
                        selected["launcher_seal"], "private launcher drift")
                receipt = paired.execute([str(dst / "paired.exe")], dst,
                                         runenv, args.timeout)
                receipt.update(selection=side, fixture=mode, pair=pair,
                               environment=runenv, accepted=False)
                label = side + "-" + mode + "-" + str(pair)
                try:
                    require(receipt["exit"] == 0 and not receipt["timed_out"],
                            side + " " + mode + " process failed; see " +
                            label + ".json.gz")
                    obs, data = (behavior(receipt["stdout"])
                        if mode == "behavior" else timing(receipt["stdout"],
                            args.samples, args.seconds, fixed))
                    receipt["result"] = paired.validate(receipt,
                        selection=side, fixture=mode, control="none",
                        private=dst,
                        repo=repo, private_names=({Path(s["git_path"]).stem
                            for s in inventories[side]} |
                            {Path(s["private_path"]).stem for s in
                             selected["supplement_sources"]}),
                        flavor="baseline",
                        signature="pass", source_hashes=hashes[side],
                        contract=dict(target=target, observations=obs,
                            red=False, modules=["simpLib", "Traverse"],
                            signatures=[]))
                    if args.matched_environment:
                        validate_matched_trace(receipt["result"]["events"],
                                               dst, target)
                    verify_supplements(supplements,
                                       selected["supplement_sources"])
                    require(paired.fingerprint(dst / "paired.exe") ==
                            selected["launcher_seal"],
                            "private launcher drift")
                    for info in receipt["result"]["paths"].values():
                        path = Path(info["physical"])
                        if not path.is_relative_to(root):
                            manifest["shared_products"].setdefault(str(path),
                                {k: info[k] for k in ("sha256", "bytes")})
                            for product, seal in (
                                    info["related_products"].items()):
                                manifest["shared_products"].setdefault(
                                    product, seal)
                    receipt.update(accepted=True, measurements=data)
                    if mode == "behavior":
                        manifest["selections"][side]["graphs"] = data
                    else:
                        manifest["runs"].append(dict(selection=side, pair=pair,
                            measurements=data, receipt=label + ".json.gz"))
                finally:
                    # Keep complete diagnostics plus structured events, but
                    # not duplicate stdout. Failed probes keep raw protocol.
                    if not receipt["accepted"]:
                        receipt["raw_events"] = paired.parse_events(
                            receipt["stdout"])
                    paired.compact(receipt, output, label)
                return obs

            a = run("baseline", "behavior", -1)
            b = run("candidate", "behavior", -1)
            require([e for e in a if e[0] == "check"] ==
                    [e for e in b if e[0] == "check"], "behavior checks differ")
            manifest["graph_comparison"] = graph_comparison(
                manifest["selections"])
            manifest["require_baseline_graphs"] = args.require_baseline_graphs
            if args.require_baseline_graphs:
                require_baseline_graphs(manifest["graph_comparison"])
            for pair in range(args.performance_pairs):
                order = ("baseline", "candidate") if pair % 2 == 0 else (
                    "candidate", "baseline")
                for side in order:
                    run(side, "performance", pair)
            if args.performance_pairs:
                manifest["timing_comparison"] = timing_comparison(
                    manifest["runs"])
                manifest["timing_decision"] = (
                    "observations only; no acceptance claim")
            for side, ref in (("baseline", args.baseline),
                              ("candidate", args.candidate)):
                if ref == "worktree":
                    require({str(p.relative_to(repo)) for p in
                             worktree_sources(repo)} ==
                            {s["git_path"] for s in inventories[side]},
                            "worktree source inventory changed during probes")
                    for source in inventories[side]:
                        require(paired.fingerprint(repo / source["git_path"]) ==
                            {k: source[k] for k in ("sha256", "bytes")},
                            "worktree source changed during probes")
            for selected in manifest["selections"].values():
                verify_supplements(supplements, selected["supplement_sources"])
            for group in ("inputs", "tools", "shared_products"):
                for name, seal in manifest[group].items():
                    require(paired.fingerprint(repo / name) == seal,
                            "input/tool/shared product changed: " + name)
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
