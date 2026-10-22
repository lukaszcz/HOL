#!/usr/bin/env python3
"""TASK18 isolated-source benchmark; requires explicit main authorization."""
import argparse
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import schema
paired, fragments, require = schema.paired, schema.fragments, schema.require


def options(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=HERE.parents[4])
    p.add_argument("--candidate", default="worktree")
    p.add_argument("--baseline-control", action="store_true")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--fixed-iterations", type=Path, required=True)
    p.add_argument("--rows", help="comma-separated keys in matrix order")
    p.add_argument("--gc-trace", action="store_true",
                   help="separate diagnostic, not timing inference")
    p.add_argument("--samples", type=int, default=3)
    p.add_argument("--pairs", type=int, default=10)
    p.add_argument("--timeout", type=int, default=1800)
    p.add_argument("--authorize-measurements", action="store_true",
                   help="main granted an exclusive build/measurement window")
    args = p.parse_args(argv)
    if (args.samples < 3 or args.pairs < (1 if args.gc_trace else 10)
            or args.timeout <= 0):
        p.error("require >=3 samples, >=10 timing pairs, positive timeout")
    args.rows = schema.selected_keys(
        args.rows.split(",") if args.rows is not None else None)
    if not args.authorize_measurements:
        p.error("require main authorization; no concurrent builds/benchmarks")
    return args


def main(argv=None):
    args = options(argv)
    repo, output = args.repo.resolve(), args.output.resolve()
    fixed_path = args.fixed_iterations.resolve()
    fixed, fixed_seal = schema.load_fixed(fixed_path)
    # Nonblocking advisory lock shared by this candidate/control runner only.
    # It cannot stop other HOL runners; main must coordinate those explicitly.
    import fcntl
    lockpath = repo / ".git"
    if lockpath.is_file():
        lockpath = (repo / lockpath.read_text().strip().split(": ", 1)[1])
    # Lock the existing gitdir inode: no persistent lockfile or unlink race.
    lockfd = os.open(lockpath.resolve(), os.O_RDONLY)
    try:
        fcntl.flock(lockfd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return execute(args, repo, output, fixed_path, fixed, fixed_seal)
    finally:
        os.close(lockfd)


def execute(args, repo, output, fixed_path, fixed, fixed_seal):
    output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "PAIR_", "PERF_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    fixtures = {name: HERE / (name + ".sml") for name in
                ("TacticInputs", "TacticPerformance")}
    if args.gc_trace:
        fixtures["TacticPerformance"] = HERE / "GCTracePerformance.sml"
    inputs = [*sorted(HERE.glob("*.py")), *fixtures.values(),
              HERE / "README.md", HERE / "Holmakefile", fixed_path,
              Path(paired.__file__), Path(fragments.__file__),
              schema.TESTS / "fragments/summarize.py",
              schema.TESTS / "performance/review-20261021/abicheck.sml",
              *sorted((paired.HERE / "paired").glob("*.sml")),
              paired.HERE / "paired/Holmakefile"]
    manifest = dict(schema_version=1, evidence_id=schema.EVIDENCE,
        success=False, repo=str(repo), command=[sys.executable, *sys.argv],
        scope="private selected sources, shared hol.state0/dependencies; NOT "
              "independent repository builds; no numerical parity claim",
        baseline_control=args.baseline_control,
        gc_trace=args.gc_trace,
        performance=dict(pairs=args.pairs, samples=args.samples,
            rows=list(args.rows),
            fixed_iterations=fixed, fixed_iterations_path=str(fixed_path),
            order="AB,BA alternating, fresh processes; no discarded outliers"),
        selections={}, runs=[], shared_products={},
        inputs={str(p.resolve()): paired.fingerprint(p) for p in inputs},
        tools={str(repo / p): paired.fingerprint(repo / p) for p in
            ("bin/hol", "bin/Holmake", "bin/hol.state0", "holproject.toml")},
        git_status=paired.git(repo, "status", "--porcelain=v1").decode())
    try:
        require(manifest["inputs"][str(fixed_path)] == fixed_seal,
                "fixed schedule changed before snapshot")
        poly = shutil.which("poly", path=env["PATH"])
        require(poly is not None, "poly not found")
        manifest["tools"][str(Path(poly).resolve())] = paired.fingerprint(
            Path(poly).resolve())
        manifest["poly_version"] = paired.execute(
            [poly, "--version"], repo, env, args.timeout)
        require(manifest["poly_version"]["exit"] == 0, "poly version failed")
        manifest["machine"] = dict(uname=list(os.uname()),
            cpu_affinity=sorted(os.sched_getaffinity(0)),
            load_before=list(os.getloadavg()))
        with tempfile.TemporaryDirectory(prefix="task18-tactics-") as temp:
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
                    "paired.exe: runner.uo CheckSupport.uo "
                    "TacticPerformance.uo\n\t$(HOLMOSMLC) -o $@ $<\n")
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
                if args.gc_trace:
                    launcher = dst / "paired.exe"
                    prefix = str(repo / "bin/hol") + " --gcthreads=1 run "
                    text = launcher.read_text()
                    require(text.count(prefix) == 1, "wrong trace launcher")
                    text = text.replace(prefix, str(repo / "bin/hol") +
                        " --gcthreads=1 --debug=gc,heapsize run ")
                    launcher.write_text(text)
                    selected["launcher"] = text
                    selected["runtime_options"] += ["--debug=gc,heapsize"]
                for pattern in ("*.exe", ".hol/objs/*", ".hol/make-deps/*"):
                    seals.update({str(f.resolve()): paired.fingerprint(f)
                        for f in dst.glob(pattern) if f.is_file()})
            manifest["ordinary_source_byte_identical"] = {
                name: (root / "baseline" / name).read_bytes() ==
                      (root / "candidate" / name).read_bytes()
                for name in ("simpLib.sml", "simpLib.sig")}
            names = {Path(s["git_path"]).stem
                     for selected in manifest["selections"].values()
                     for s in selected["sources"]}
            # Both launchers finish building BEFORE any measurement process.
            for pair in range(args.pairs):
                for side in (("baseline", "candidate") if pair % 2 == 0 else
                             ("candidate", "baseline")):
                    dst = root / side
                    runenv = dict(env, PAIR_SELECTION=side,
                        PAIR_FIXTURE="tactic-performance",
                        PAIR_CONTROL="none", PAIR_PRIVATE=str(dst),
                        PAIR_TARGET="TacticPerformance",
                        PERF_SAMPLES=str(args.samples),
                        PERF_ROWS=",".join(args.rows), PERF_FIXED=",".join(
                            f"{k}={v}" for k, v in fixed.items()))
                    receipt = paired.execute([str(dst / "paired.exe")], dst,
                                             runenv, args.timeout)
                    label = f"{side}-tactics-{pair}"
                    receipt.update(selection=side,
                        fixture="tactic-performance",
                        pair=pair, accepted=False,
                        environment={k: v for k, v in runenv.items()
                                     if k.startswith(("PAIR_", "PERF_"))})
                    entry = dict(receipt=label + ".json.gz", selection=side,
                                 pair=pair, accepted=False)
                    manifest["runs"].append(entry)
                    try:
                        obs = fragments.payload(receipt["stdout"])
                        if args.gc_trace:
                            from gc_diagnostic import parse_events
                            data, stats = parse_events(obs, args.samples,
                                                       fixed, args.rows)
                            receipt["gc_statistics"] = stats
                        else:
                            _, data = schema.timing_events(
                                obs, args.samples, fixed, args.rows)
                        receipt["measurements"] = data
                        receipt["result"] = paired.validate(receipt,
                            selection=side, fixture="tactic-performance",
                            control="none", private=dst, repo=repo,
                            private_names=names, flavor="baseline",
                            signature="pass", source_hashes=seals,
                            contract=dict(target="TacticPerformance",
                                observations=obs, red=False,
                                modules=["simpLib", "Traverse"],
                                signatures=[]))
                        for info in receipt["result"]["paths"].values():
                            if not Path(info["physical"]).is_relative_to(root):
                                manifest["shared_products"].setdefault(
                                    info["physical"], {k: info[k] for k in
                                                       ("sha256", "bytes")})
                                for p, seal in (
                                        info["related_products"].items()):
                                    manifest["shared_products"].setdefault(p, seal)
                        receipt["accepted"] = entry["accepted"] = True
                    except Exception as exc:
                        receipt.update(rejection=str(exc),
                                       raw_stdout=receipt["stdout"])
                        raise
                    finally:
                        paired.compact(receipt, output, label)
            for selected in manifest["selections"].values():
                if selected["reference"] == "worktree":
                    require({str(p.relative_to(repo)) for p in
                        fragments.worktree_sources(repo)} ==
                        {s["git_path"] for s in selected["sources"]},
                        "worktree source inventory changed")
                    for source in selected["sources"]:
                        require(paired.fingerprint(repo / source["git_path"]) ==
                            {k: source[k] for k in ("sha256", "bytes")},
                            "worktree source drift")
            for p, seal in seals.items():
                require(paired.fingerprint(Path(p)) == seal,
                        "private source/product drift: " + p)
            for group in ("inputs", "tools", "shared_products"):
                for p, seal in manifest[group].items():
                    require(paired.fingerprint(Path(p)) == seal,
                            "input/tool/shared product drift: " + p)
        manifest["machine"]["load_after"] = list(os.getloadavg())
        manifest["success"] = True
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
