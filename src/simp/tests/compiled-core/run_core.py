#!/usr/bin/env python3
"""Source-tied fresh paired core probes, NOT independent repository builds."""
import argparse
import json
import math
import os
from pathlib import Path
import shutil
import statistics
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import schema
fragments = schema.routes.fragments
paired, require = schema.paired, schema.require
sys.path.insert(0, str(HERE.parent / "performance"))
import performance_schema as performance
import summarize
sys.path.insert(0, str(HERE.parent / "compatibility"))
from prior_contracts import LIMIT_CHECKS


def options(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=HERE.parents[3])
    p.add_argument("--candidate", default="worktree")
    p.add_argument("--baseline-control", action="store_true",
                   help="use the pinned baseline on BOTH sides")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--timeout", type=int, default=600)
    p.add_argument("--performance-pairs", type=int, choices=(0, 10), default=0)
    p.add_argument("--samples", type=int, default=3)
    p.add_argument("--batch-seconds", type=float, default=.2)
    p.add_argument("--require-baseline-graphs", action="store_true")
    args = p.parse_args(argv)
    if (args.timeout <= 0 or args.samples < 3 or
            not math.isfinite(args.batch_seconds) or
            not .1 <= args.batch_seconds <= 60):
        p.error("require positive timeout, >=3 samples, .1..60 second batches")
    return args


def main(argv=None):
    args = options(argv)
    repo, output = args.repo.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "PAIR_", "PERF_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    fixtures = {"CoreGraph": HERE / "CoreGraph.sml",
                "CoreBehavior": HERE / "CoreBehavior.sml",
                "Routes": schema.routes.HERE / "selftest.sml",
                "PriorLimits": paired.HERE / "paired/PriorLimits.sml",
                "Performance": HERE.parent / "performance/Performance.sml"}
    inputs = [*sorted(HERE.glob("*.py")), *sorted(HERE.glob("*.sml")),
              HERE / "README.md", HERE / "Holmakefile",
              *fixtures.values(), Path(paired.__file__),
              Path(fragments.__file__), Path(schema.routes.__file__),
              paired.HERE / "prior_contracts.py",
              *sorted((paired.HERE / "paired").glob("*.sml")),
              paired.HERE / "paired/Holmakefile",
              HERE.parent / "performance/review-20261021/abicheck.sml",
              Path(performance.__file__), Path(summarize.__file__)]
    manifest = dict(schema_version=1, evidence_id="TASK16-compiled-core-v1",
        success=False, repo=str(repo), command=[sys.executable, *sys.argv],
        scope="isolated sources, shared heap/dependencies; retained graph "
              "words NOT cumulative allocation; timings diagnostic only",
        selections={}, runs=[], shared_products={},
        inputs={str(p.relative_to(repo)): paired.fingerprint(p)
                for p in inputs},
        tools={p: paired.fingerprint(repo / p) for p in (
            "bin/hol", "bin/Holmake", "bin/hol.state0", "holproject.toml")},
        performance=dict(pairs=args.performance_pairs, samples=args.samples,
            batch_seconds=args.batch_seconds, suite="simplifier",
            order="AB,BA alternating; fresh process per selection",
            outliers="none removed"),
        baseline_control=args.baseline_control,
        git_status=paired.git(repo, "status", "--porcelain=v1").decode())
    try:
        poly = shutil.which("poly", path=env["PATH"])
        require(poly is not None, "poly not found")
        manifest["tools"][str(Path(poly).resolve())] = paired.fingerprint(
            Path(poly).resolve())
        manifest["poly_version"] = paired.execute(
            [poly, "-v"], repo, env, args.timeout)
        require(manifest["poly_version"]["exit"] == 0, "poly version failed")
        manifest["machine"] = dict(uname=list(os.uname()),
            cpu_affinity=sorted(os.sched_getaffinity(0)),
            load_before=list(os.getloadavg()))
        with tempfile.TemporaryDirectory(prefix="compiled-core-") as temp:
            root, seals = Path(temp), {}
            for side, ref in (("baseline", paired.BASE),
                    ("candidate", paired.BASE if args.baseline_control else
                     args.candidate)):
                dst = root / side
                dst.mkdir()
                rev, inventory = fragments.snapshot(repo, ref, dst)
                paired.install_fixtures(dst)
                for name, source in fixtures.items():
                    shutil.copyfile(source, dst / (name + ".sml"))
                (dst / "Holmakefile").write_text(
                    "HOLHEAP = $(HOLDIR)/bin/hol.state0\n"
                    "paired.exe: runner.uo CheckSupport.uo " +
                    " ".join(name + ".uo" for name in fixtures) + "\n"
                    "\t$(HOLMOSMLC) -o $@ $<\n")
                selected = dict(reference=ref, revision=rev, sources=inventory,
                    private=str(dst), compiler_matches_pinned={name:
                        (dst / name).read_bytes() == paired.git(repo, "show",
                            paired.BASE + ":src/simp/src/" + name)
                        for name in ("simpLib.sml", "simpLib.sig")})
                manifest["selections"][side] = selected
                selected["fixture_products"] = {
                    f.name: paired.fingerprint(f) for f in dst.iterdir()
                    if f.is_file() and f.name not in
                    {Path(s["git_path"]).name for s in inventory}}
                seals.update({str(f): paired.fingerprint(f)
                              for f in dst.iterdir() if f.is_file()})
                build = paired.execute([str(repo / "bin/Holmake"),
                    "--no-project", "--no-cache", "--no_prereqs",
                    "--holstate=" + str(repo / "bin/hol.state0"),
                    "-C", str(dst), "-j1", "paired.exe"],
                    root, env, args.timeout)
                paired.compact(dict(build), output, side + "-build")
                require(build["exit"] == 0 and not build["timed_out"],
                        side + " private launcher build failed")
                selected["launcher"], selected["runtime_options"] = (
                    fragments.configure_launcher(dst, repo, None))
                for pattern in ("*.exe", ".hol/objs/*", ".hol/make-deps/*"):
                    seals.update({str(f.resolve()): paired.fingerprint(f)
                        for f in dst.glob(pattern) if f.is_file()})
            names = {Path(s["git_path"]).stem
                     for selected in manifest["selections"].values()
                     for s in selected["sources"]}
            observations, nongc = {}, {}

            def run(side, target, pair=-1):
                dst = root / side
                mode = "performance" if target == "Performance" else target
                runenv = dict(env, PAIR_SELECTION=side, PAIR_FIXTURE=mode,
                    PAIR_CONTROL="none", PAIR_PRIVATE=str(dst),
                    PAIR_TARGET=target, PERF_SAMPLES=str(args.samples),
                    PERF_SECONDS=str(args.batch_seconds))
                receipt = paired.execute([str(dst / "paired.exe")], dst,
                                         runenv, args.timeout)
                label = f"{side}-{mode}-{pair}"
                receipt.update(selection=side, fixture=mode, pair=pair,
                    environment={k: v for k, v in runenv.items()
                                 if k.startswith(("PAIR_", "PERF_"))},
                    accepted=False)
                entry = dict(receipt=label + ".json.gz", accepted=False,
                             expected_acceptance=True, exit=receipt["exit"])
                manifest["runs"].append(entry)
                try:
                    text, data = receipt["stdout"], None
                    if target == "CoreGraph":
                        obs, data = schema.graph(text)
                        manifest["selections"][side]["graphs"] = data
                    elif target == "CoreBehavior":
                        obs = schema.behavior(text)
                    elif target == "Routes":
                        obs = schema.routes.behavior(text)
                    elif target == "PriorLimits":
                        obs = [["check", name, "pass"]
                               for name in LIMIT_CHECKS]
                    else:
                        obs, data = performance.validate(
                            paired.parse_events(text), args.samples,
                            args.batch_seconds)
                        receipt["measurements"] = data
                        nongc.setdefault(pair, {})[side] = {key:
                            statistics.median((b["nongc_usr"] + b["nongc_sys"])
                                / b["iterations"] for b in w["batches"])
                            for key, w in data["workloads"].items()}
                    receipt["result"] = paired.validate(receipt,
                        selection=side, fixture=mode, control="none",
                        private=dst, repo=repo, private_names=names,
                        flavor="baseline", signature="pass",
                        source_hashes=seals,
                        contract=dict(target=target, observations=obs,
                            red=False, modules=["simpLib", "Traverse"],
                            signatures=[]))
                    for info in receipt["result"]["paths"].values():
                        if not Path(info["physical"]).is_relative_to(root):
                            manifest["shared_products"].setdefault(
                                info["physical"], {k: info[k] for k in
                                                   ("sha256", "bytes")})
                            for p, seal in info["related_products"].items():
                                manifest["shared_products"].setdefault(p, seal)
                    receipt["accepted"] = entry["accepted"] = True
                    return obs
                except Exception as exc:
                    receipt.update(rejection=str(exc),
                                   raw_stdout=receipt["stdout"])
                    raise
                finally:
                    paired.compact(receipt, output, label)

            targets = ("CoreBehavior", "Routes", "PriorLimits", "CoreGraph")
            for target in targets:
                for side in ("baseline", "candidate"):
                    observations[side] = run(side, target)
                if target != "CoreGraph":
                    schema.routes.same_behavior(observations["baseline"],
                                                observations["candidate"])
            comparison = schema.comparison(manifest["selections"])
            manifest["graph_comparison"] = comparison
            manifest["require_baseline_graphs"] = args.require_baseline_graphs
            if args.require_baseline_graphs or args.baseline_control:
                for label, row in comparison.items():
                    require(all(
                        delta == 0 if args.baseline_control else delta <= 0
                        for delta in row["candidate_minus_baseline_words"]),
                        "retained graph regression: " + label)
            for pair in range(args.performance_pairs):
                for side in (("baseline", "candidate") if pair % 2 == 0 else
                             ("candidate", "baseline")):
                    run(side, "Performance", pair)
            manifest["nongc_seconds_per_operation_by_pair"] = nongc
            for selected in manifest["selections"].values():
                if selected["reference"] == "worktree":
                    require({str(p.relative_to(repo)) for p in
                        fragments.worktree_sources(repo)} ==
                        {s["git_path"] for s in selected["sources"]},
                        "worktree source inventory changed")
                    for source in selected["sources"]:
                        current = paired.fingerprint(repo / source["git_path"])
                        require(current ==
                            {k: source[k] for k in ("sha256", "bytes")},
                            "worktree source changed during probes")
            for p, seal in seals.items():
                require(paired.fingerprint(Path(p)) == seal,
                        "private source/product drift: " + p)
            for group in ("inputs", "tools", "shared_products"):
                for p, seal in manifest[group].items():
                    require(paired.fingerprint(repo / p) == seal,
                            "input/tool/shared product drift: " + p)
        manifest["machine"]["load_after"] = list(os.getloadavg())
        manifest["success"] = True
        (output / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n")
        if args.performance_pairs:
            summary = summarize.summarize(output)
            (output / "performance-summary.json").write_text(
                json.dumps(summary, indent=2) + "\n")
    except Exception as exc:
        manifest.update(success=False, failure=str(exc))
    finally:
        (output / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n")
    print(output / "manifest.json")
    if not manifest["success"]:
        raise SystemExit(manifest["failure"])


if __name__ == "__main__":
    main()
