#!/usr/bin/env python3
"""Fail-closed paired ordinary tactic contracts; shared HOL heap.

Builds/runs only when explicitly invoked. Never imports/runs the parent main.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

# Importing the parent must not leave caches in another agent's directory.
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "fragments"))
import run_fragments as fragments
paired = fragments.paired
require = paired.require
EVIDENCE = "TASK18-tactics-v1"


def schema():
    """Ordered contract: no missing observations or candidate-only outcomes."""
    names = []
    direct = ("ASM", "asm alias", "SIMP", "simp alias")
    fulls = ("full", "full alias", "reverse", "reverse alias")
    nostrips = ("no-strip full", "no-strip reverse")

    def application(name):
        names.extend(name + " " + part for part in ("goals", "proof"))

    def reused(name):
        for use in ("first", "reused"):
            application(name + " " + use)

    for name in (*direct, "NoAsms", "IgnAsm", "label explicit despite NoAsms"):
        reused(name)
    names.append("ASM missing label is late error")
    for name in (*fulls, *nostrips):
        reused(name + " disjunction")
    for name in (*fulls, *nostrips):
        reused(name + " contradiction")
    for name in ("full", "reverse", *nostrips):
        reused(name + " dependency order")
    for name in ("psr oldest", "psr newest", "allasms oldest", "allasms newest",
                 "psr drops true", "psr strips conjunction",
                 "psr eliminates variable"):
        reused(name)
    names.extend(("conversion preserves rule hypothesis",
                  "rule preserves rule hypothesis",
                  "SIMP_RULE does not import hypotheses",
                  "ASM_SIMP_RULE imports hypotheses", "SIMP_PROVE real proof"))
    names.extend("conversion ignores " + name
                 for name in ("NoAsms", "IgnAsm", "Abbr", "label"))
    for wrapper in ("Req0", "ReqD"):
        names.extend(route + " rejects " + wrapper
                     for route in ("conversion", "rule", "installation"))
    names.append("nested generic payload and hypotheses")
    for name in ("nested ASM payload", "nested SIMP payload"):
        reused(name)
    for name in ("filtered", "NoAsms"):
        for use in ("initial", "new assumption"):
            application("reentry " + name + " " + use)
    for name in (*direct, *fulls, *nostrips):
        for wrapper in ("Req0", "ReqD", "both"):
            names.extend("stage " + name + " " + wrapper + " " + stage
                         for stage in ("construct", "first proof",
                                       "first callbacks", "reuse",
                                       "throwing construction"))
    names.extend(("validator rejects wrong conclusion",
                  "validator rejects foreign hypothesis", "validator rejects oracle",
                  "goal comparator detects reversed branches"))
    return ([["check", n, "pass"] for n in names] +
            [["observation", "validations", "116"],
             ["observation", "complete", EVIDENCE]])


def behavior(text):
    events = fragments.payload(text)
    expected = schema()
    require(len(events) == len(expected),
            "incomplete/extra tactic observations")
    for event, row in zip(events, expected):
        require(len(event) == 3 and event[:2] == row[:2],
                "wrong ordered tactic observation: " + repr(row[:2]))
        require(event == row, "wrong tactic result: " + repr(row[:2]))
    return events


def same_behavior(baseline, candidate):
    # No candidate-specific outcomes, whitespace normalization, field removal,
    # set comparison, tolerance, or golden-regeneration mode.
    require(baseline == candidate,
            "candidate differs from exact ordered baseline observations")


def ordinary_only(paths):
    """Reject extension elaboration, not just forbidden direct imports."""
    names = {Path(p).stem for p in paths}
    forbidden = {n for n in names if n.endswith(("Ext", "ExtLib")) or
                 n.startswith(("simpMarker", "split", "Split"))}
    require(not forbidden, "extension module loaded: " + repr(sorted(forbidden)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[3])
    parser.add_argument("--candidate", default="worktree",
                        help="worktree (default), or a commit for controls")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    repo, output = args.repo.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("HOL", "POLY", "ML", "PAIR_", "PERF_", "LD_"))}
    env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
    manifest = dict(schema_version=1, evidence_id=EVIDENCE, success=False,
        scope="legacy tactics; isolated sources, shared dependencies; "
              "NOT independent repository builds or performance evidence",
        command=[sys.executable, *sys.argv], repo=str(repo),
        selections={}, runs=[], inputs={}, tools={}, shared_products={})
    try:
        manifest["git_status"] = paired.git(
            repo, "status", "--porcelain=v1").decode()
        inputs = [HERE / name for name in (
            "selftest.sml", "run_behavior.py", "test_behavior.py", "README.md",
            "Holmakefile")]
        abi = paired.HERE.parent / "performance/review-20261021/abicheck.sml"
        inputs += [Path(fragments.__file__), Path(paired.__file__), abi,
                   *sorted((paired.HERE / "paired").glob("*.sml")),
                   paired.HERE / "paired/Holmakefile"]
        manifest["inputs"] = {str(f.relative_to(repo)): paired.fingerprint(f)
                              for f in inputs}
        manifest["tools"] = {name: paired.fingerprint(repo / name) for name in
            ("bin/hol", "bin/Holmake", "bin/hol.state0", "holproject.toml")}
        poly = shutil.which("poly", path=env["PATH"])
        require(poly is not None, "poly not found")
        manifest["tools"][str(Path(poly).resolve())] = paired.fingerprint(
            Path(poly).resolve())
        version = paired.execute([poly, "-v"], repo, env, args.timeout)
        manifest["poly_version"] = version
        require(version["exit"] == 0 and not version["timed_out"],
                "poly -v failed")
        with tempfile.TemporaryDirectory(prefix="task18-behavior-") as temp:
            root, inventories, seals = Path(temp), {}, {}
            for side, ref in (("baseline", paired.BASE),
                              ("candidate", args.candidate)):
                dst = root / side
                dst.mkdir()
                rev, inventory = fragments.snapshot(repo, ref, dst)
                inventories[side] = inventory
                paired.install_fixtures(dst)
                shutil.copyfile(HERE / "selftest.sml", dst / "selftest.sml")
                (dst / "Holmakefile").write_text(
                    "HOLHEAP = $(HOLDIR)/bin/hol.state0\n"
                    "paired.exe: runner.uo CheckSupport.uo selftest.uo\n"
                    "\t$(HOLMOSMLC) -o $@ $<\n")
                seals.update({str(f): paired.fingerprint(f)
                              for f in dst.iterdir() if f.is_file()})
                selected = dict(reference=ref, revision=rev, sources=inventory,
                    private=str(dst), fixture_products={
                        f.name: paired.fingerprint(f) for f in dst.iterdir()
                        if f.is_file() and f.name not in
                        {Path(i["git_path"]).name for i in inventory}})
                manifest["selections"][side] = selected
                build = paired.execute([str(repo / "bin/Holmake"),
                    "--no-project", "--no-cache", "--no_prereqs",
                    "--holstate=" + str(repo / "bin/hol.state0"),
                    "-C", str(dst), "-j1", "paired.exe"],
                    root, env, args.timeout)
                paired.compact(dict(build), output, side + "-build")
                require(build["exit"] == 0 and not build["timed_out"],
                        side + " private launcher build failed")
                launcher = (dst / "paired.exe").read_text()
                runtime = str(repo / "bin/hol") + " --gcthreads=1 run "
                heap = "--holstate=" + str(repo / "bin/hol.state0")
                require(runtime in launcher and heap in launcher,
                        "wrong launcher runtime/heap/options")
                selected["launcher"] = launcher
                for pattern in ("*.exe", ".hol/objs/*", ".hol/make-deps/*"):
                    seals.update({str(f.resolve()): paired.fingerprint(f)
                                  for f in dst.glob(pattern) if f.is_file()})
            private_names = {Path(s["git_path"]).stem
                             for inv in inventories.values() for s in inv}
            observations = {}
            for side in ("baseline", "candidate"):
                dst = root / side
                runenv = dict(env, PAIR_SELECTION=side, PAIR_FIXTURE="routes",
                    PAIR_CONTROL="none", PAIR_PRIVATE=str(dst),
                    PAIR_TARGET="selftest")
                receipt = paired.execute([str(dst / "paired.exe")], dst,
                                         runenv, args.timeout)
                receipt.update(
                    selection=side, fixture="routes", accepted=False,
                    environment={k: v for k, v in runenv.items()
                                 if k.startswith("PAIR_")})
                label = side + "-routes"
                manifest["runs"].append(dict(receipt=label + ".json.gz",
                                            accepted=False))
                try:
                    obs = behavior(receipt["stdout"])
                    receipt["result"] = paired.validate(receipt,
                        selection=side, fixture="routes", control="none",
                        private=dst, repo=repo, private_names=private_names,
                        flavor="baseline", signature="pass",
                        source_hashes=seals,
                        contract=dict(target="selftest", observations=obs,
                            red=False, modules=["simpLib", "Traverse"],
                            signatures=[]))
                    ordinary_only(receipt["result"]["paths"])
                    observations[side] = obs
                    # Seal shared inputs and generated dependency products.
                    for info in receipt["result"]["paths"].values():
                        path = Path(info["physical"])
                        if not path.is_relative_to(root):
                            manifest["shared_products"].setdefault(str(path),
                                {k: info[k] for k in ("sha256", "bytes")})
                            for name, seal in info["related_products"].items():
                                manifest["shared_products"].setdefault(
                                    name, seal)
                    receipt["accepted"] = True
                    manifest["runs"][-1]["accepted"] = True
                except Exception as exc:
                    receipt["rejection"] = str(exc)
                    receipt["raw_stdout"] = receipt["stdout"]
                    raise
                finally:
                    paired.compact(receipt, output, label)
            same_behavior(observations["baseline"], observations["candidate"])
            for side, inv in inventories.items():
                if manifest["selections"][side]["reference"] == "worktree":
                    require({str(f.relative_to(repo)) for f in
                             fragments.worktree_sources(repo)} ==
                            {s["git_path"] for s in inv},
                            "worktree source inventory changed during pair")
                    for source in inv:
                        current = paired.fingerprint(repo / source["git_path"])
                        require(current ==
                                {k: source[k] for k in ("sha256", "bytes")},
                                "worktree source changed during pair")
            for name, seal in seals.items():
                require(paired.fingerprint(Path(name)) == seal,
                        "private input/product changed during pair: " + name)
            for group in ("inputs", "tools", "shared_products"):
                for name, seal in manifest[group].items():
                    require(paired.fingerprint(repo / name) == seal,
                            "input/tool/shared product changed: " + name)
        manifest["success"] = True
    except Exception as exc:
        manifest["failure"] = str(exc)
    finally:
        (output / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n")
    print(output / "manifest.json")
    if not manifest["success"]:
        raise SystemExit(manifest["failure"])


if __name__ == "__main__":
    main()
