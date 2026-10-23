#!/usr/bin/env python3
"""Untimed, isolated-source client semantic smoke; NOT performance acceptance.

Compile the unchanged real ClientPerformance/RuntimeMetrics entrypoint, but run
only a source-bound definitions prefix and direct workload calls. Each workload
is verified initially and after each of two runs (including tactic validation).
The small smoke intentionally tests all client cases at 0,1,10, even singleton
and numeral cases: these are semantic edge probes, not ledger timing sizes.
Use the historical configured-root wrapper when the heap embeds that root.
Outputs are new exclusive-created JSON and a sibling raw .log. Private trees
are removed even on failure; no shared source/build product is modified.
"""
import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "compatibility"))
import run_paired as rp
import client_dependencies as cd
import matrix_schema as ms
from acceptance import serial_lock

SIZES = (0, 1, 10, 100, 1000, 10000)
ASSUMPTION_SCALING = (
    "tactic_supplied_reuse", "tactic_asm_reuse", "tactic_full_reuse",
    "tactic_dependency_reverse_reuse",
)


def smoke_cases(matrix, cases=None, sizes=(0, 1, 10)):
    """Validate semantic selections, deliberately not timing-ledger sizes."""
    available = [name for name, row in matrix["cases"].items()
                 if row["fixture"] == "ClientPerformance.sml"]
    rp.require(len(available) == len(set(available)) == 56,
               "expected 56 distinct ledger client cases")
    chosen = available if cases is None else list(cases)
    rp.require(chosen and len(chosen) == len(set(chosen)) and
               set(chosen) <= set(available), "invalid/duplicate client case")
    sizes = list(sizes)
    rp.require(sizes and len(sizes) == len(set(sizes)) and
               all(type(n) is int and n in SIZES for n in sizes),
               "invalid/duplicate semantic smoke size")
    return chosen, sizes


def plan(matrix, scope, cases=None, sizes=None):
    chosen, small = smoke_cases(matrix, cases, sizes or (0, 1, 10))
    groups = [(chosen, small)]
    if scope == "scaling":
        depth = [c for c in chosen if matrix["cases"][c]["sizes"] == "depth"]
        if depth:
            groups.append((depth, [100]))
        # Separate processes bound each potentially quadratic large workload.
        groups.extend(([c], [1000]) for c in ASSUMPTION_SCALING
                      if c in chosen)
        # Full/dependency passes can be quadratic; the 10000 full probe
        # exceeded a 300s semantic-only process budget. Keep large linear
        # supplied/ASM probes, and retain 1000 for the directional passes.
        groups.extend(([c], [10000]) for c in ASSUMPTION_SCALING[:2]
                      if c in chosen)
    return groups


def generate(source, cases, sizes):
    """Keep real definitions/dispatcher; remove only executed timing control."""
    marker = "val {run,verify=check} = choose ()\n"
    rp.require(source.count(marker) == 1, "client entrypoint marker changed")
    prefix = source.split(marker)[0]
    accounting = (
        "val (_,accounting) = measure 5 (fn () => "
        "(PolyML.fullGC (); consume ()))\n"
        'val _ = emit "timer.accounting" accounting\n'
        'val _ = Paired.check "timer accounting" true\n')
    rp.require(prefix.count(accounting) == 1,
               "client accounting control changed")
    prefix = prefix.replace(accounting, "")
    dispatcher = "fun choose () =\n"
    rp.require(prefix.count(dispatcher) == 1, "client dispatcher changed")
    prefix = prefix.replace(dispatcher,
                            "fun smokeChoose (selected,workloadSize) =\n")
    return prefix + '''
(* Generated semantic-only driver. No timing/calibration/sampling executes. *)
val smokeCases = [%s]
val smokeSizes = [%s]
fun smokeOne label n = let
  val _ = print ("client smoke " ^ label ^ " " ^ Int.toString n ^ "\\n")
  val _ = TextIO.flushOut TextIO.stdOut
  val {run,verify} = smokeChoose (label,n)
  val _ = verify ()
  val _ = run ()
  val _ = verify ()
  val _ = run ()
  val _ = verify ()
in Paired.check (label ^ ":" ^ Int.toString n) true end
val _ = List.app (fn n => List.app (fn c => smokeOne c n) smokeCases)
                 smokeSizes
''' % (",".join(json.dumps(c) for c in cases), ",".join(map(str, sizes)))


def summary(receipt):
    return {k: v for k, v in receipt.items() if k != "stdout"}


def seal(stamps):
    for path, stamp in stamps.items():
        rp.require(rp.fingerprint(Path(path)) == stamp,
                   "input/product changed: " + path)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[3])
    parser.add_argument("--baseline", default=rp.BASE)
    parser.add_argument("--candidate", default="HEAD")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--scope", choices=("small", "scaling"),
                        default="scaling")
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--size", type=int, action="append", dest="sizes",
                        help="small-group semantic size; repeatable")
    parser.add_argument("--timeout", type=int, default=300,
                        help="seconds per build or grouped smoke process")
    args = parser.parse_args(argv)
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    repo, output = args.repo.resolve(), args.output.resolve()
    logpath = output.with_suffix(".log")
    if output == logpath or output.exists() or logpath.exists():
        parser.error("JSON and sibling .log must be new, distinct files")
    src = repo / "src/simp/tests/performance"
    try:
        matrix = ms.load_matrix(src / "matrix.json")
        groups = plan(matrix, args.scope, args.cases, args.sizes)
    except (ValueError, KeyError) as error:
        parser.error(str(error))
    output.parent.mkdir(parents=True, exist_ok=True)
    manifest = {
        "schema": 1, "success": False,
        "scope": "semantic smoke only; no performance acceptance",
        "scope_selection": args.scope, "repo": str(repo),
        "command": [sys.executable, *sys.argv],
        "plan": [{"cases": cs, "sizes": ns} for cs, ns in groups],
        "expected_checks": 2 * sum(len(cs) * len(ns) for cs, ns in groups),
        "executed_checks": 0, "selections": {}, "runs": [],
        "inputs": {}, "tools": {},
        "verification": "initially, run once, verify, run once, verify",
        "semantic_size_override": "all clients include 0,1,10 by default; "
                                  "not timing-ledger singleton/numeral grids",
    }
    with output.open("x") as result, logpath.open("x") as log:
        def note(text):
            print(text, flush=True)
            log.write(text + "\n")
            log.flush()

        def record_raw(label, receipt):
            log.write("\n=== " + label + " ===\n" + receipt["stdout"])
            log.flush()

        try:
            with serial_lock(repo):
                source = (src / "ClientPerformance.sml").read_text()
                inputs = [Path(__file__).resolve(), Path(rp.__file__),
                          Path(cd.__file__), Path(ms.__file__),
                          src / "acceptance.py", src / "matrix.json",
                          src / "ClientPerformance.sml",
                          src / "RuntimeMetrics.sml",
                          src / "MatrixSupport.sml",
                          src / "MatrixPerformance.sml",
                          *sorted((rp.HERE / "paired").glob("*.sml")),
                          rp.HERE / "paired/Holmakefile",
                          rp.HERE.parent /
                          "performance/review-20261021/abicheck.sml"]
                manifest["inputs"] = {str(p): rp.fingerprint(p) for p in inputs}
                manifest["client_source"] = rp.fingerprint(
                    src / "ClientPerformance.sml")
                manifest["generator"] = rp.fingerprint(Path(__file__))
                manifest["head"] = rp.git(repo, "rev-parse", "HEAD").decode().strip()
                manifest["working_simplifier_diff"] = rp.git(
                    repo, "diff", "HEAD", "--", "src/simp/src").decode()
                manifest["tools"] = {
                    str(repo / name): rp.fingerprint(repo / name)
                    for name in ("bin/Holmake", "bin/hol", "bin/hol.state0")}
                env = {k: v for k, v in os.environ.items()
                       if not k.startswith(("HOL", "POLY", "ML", "PAIR_",
                                            "PERF_", "LD_"))}
                env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
                manifest["runtime_environment"] = env
                with tempfile.TemporaryDirectory(prefix="client-smoke-") as tmp:
                    root = Path(tmp)
                    for selection, ref in (("baseline", args.baseline),
                                           ("candidate", args.candidate)):
                        dst = root / selection
                        dst.mkdir()
                        rev = rp.git(repo, "rev-parse", ref + "^{commit}")
                        rev = rev.decode().strip()
                        inventory = rp.extract(repo, rev, dst)
                        rp.install_fixtures(dst, performance=True,
                                            matrix_fixture="ClientPerformance.sml")
                        names = {Path(s["git_path"]).stem for s in inventory}
                        installed = cd.install(repo, dst, names)
                        info = {"requested_ref": ref, "revision": rev,
                                "sources": inventory, "dependencies": installed,
                                "builds": [], "loaded_paths": {}}
                        manifest["selections"][selection] = info
                        hashes = {str(p): rp.fingerprint(p)
                                  for p in dst.rglob("*") if p.is_file()}
                        for index, (cases, sizes) in enumerate(groups):
                            driver = dst / "selftest.sml"
                            driver.write_text(generate(source, cases, sizes))
                            hashes[str(driver)] = rp.fingerprint(driver)
                            command = [str(repo / "bin/Holmake"), "--no-project",
                                       "--no-cache", "--no_prereqs",
                                       "--holstate=" + str(repo / "bin/hol.state0"),
                                       "-C", str(dst), "-j1", "paired.exe"]
                            build = rp.execute(command, root, env, args.timeout)
                            info["builds"].append(summary(build))
                            record_raw(selection + " build " + str(index), build)
                            note(f"{selection} group {index} build exit={build['exit']}")
                            rp.require(build["exit"] == 0 and not build["timed_out"],
                                       selection + " private Holmake failed")
                            local = names | set(installed["modules"])
                            for product in (dst / ".hol/objs").iterdir():
                                if product.suffix not in (".uo", ".ui"):
                                    continue
                                for line in product.read_text().splitlines():
                                    if ("$(HOLDIR)/sigobj/" in line or
                                            str(repo / "sigobj") in line):
                                        rp.require(Path(line).name not in local,
                                                   "shared static edge: " + line)
                            runenv = dict(env, PAIR_SELECTION=selection,
                                          PAIR_FIXTURE="selftest", PAIR_CONTROL="none",
                                          PAIR_PRIVATE=str(dst), PAIR_TARGET="selftest",
                                          PERF_CASE="downstream_boss", PERF_SIZE="0",
                                          PERF_SAMPLES="1", PERF_SECONDS="0.001")
                            receipt = rp.execute([str(dst / "paired.exe")], dst,
                                                 runenv, args.timeout)
                            record_raw(selection + " run " + str(index), receipt)
                            record = dict(summary(receipt), selection=selection,
                                          group=index, cases=cases, sizes=sizes,
                                          selftest=hashes[str(driver)],
                                          runtime_options=runenv,
                                          accepted=False)
                            manifest["runs"].append(record)
                            expected = [["check", f"{c}:{n}", "pass"]
                                        for n in sizes for c in cases]
                            try:
                                audit = rp.validate(
                                    receipt, selection=selection, fixture="selftest",
                                    control="none", private=dst, repo=repo,
                                    private_names=local, flavor="baseline",
                                    signature="pass",
                                    source_hashes={**installed["inputs"], **hashes},
                                    expected_observations=expected)
                                for name in ("bossLib", "numLib", "reduceLib",
                                             "simpLib"):
                                    rp.require(str(dst / (name + ".sml")) in
                                               audit["paths"],
                                               "client not private: " + name)
                                record["checks"] = audit["observations"]
                                record["loaded_path_count"] = len(audit["paths"])
                                for raw, stamp in audit["paths"].items():
                                    if raw == str(driver):
                                        continue
                                    previous = info["loaded_paths"].setdefault(raw, stamp)
                                    rp.require(previous == stamp,
                                               "loaded dependency changed: " + raw)
                                record["accepted"] = True
                                manifest["executed_checks"] += len(expected)
                            except Exception as error:
                                record["failure"] = str(error)
                                raise
                            finally:
                                note(f"{selection} group {index} sizes={sizes} "
                                     f"cases={len(cases)} exit={receipt['exit']} "
                                     f"accepted={record['accepted']}")
                        seal(installed["inputs"])
                        for raw, stamp in info["loaded_paths"].items():
                            seal({stamp["physical"]: {k: stamp[k]
                                  for k in ("sha256", "bytes")}})
                            seal(stamp["related_products"])
                    seal(manifest["inputs"])
                    seal(manifest["tools"])
                rp.require(manifest["executed_checks"] ==
                           manifest["expected_checks"], "incomplete checks")
                manifest["success"] = True
        except Exception as error:
            manifest["failure"] = str(error)
            note("FAIL: " + str(error))
        finally:
            manifest["raw_log"] = {"path": str(logpath),
                                   **rp.fingerprint(logpath)}
            result.write(json.dumps(manifest, indent=2) + "\n")
            print(f"checks={manifest['executed_checks']}/"
                  f"{manifest['expected_checks']} success={manifest['success']}",
                  flush=True)
            print(output, flush=True)
    return 0 if manifest["success"] else 1


if __name__ == "__main__":
    sys.exit(main())
