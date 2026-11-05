#!/usr/bin/env python3
"""Non-timing MatrixSupport smoke with private exact-source Holmake launchers.

Run from a configured HOL tree (use the historical root-wrapper on hosts whose
heap embeds that path). This is mixed-source semantic validation, NOT benchmark
acceptance or independent repository builds. --scope grid excludes four costly
10000-rule single-add/AC cases; --scope expensive runs those explicitly.
Outputs are exclusive-created JSON + a compact sibling .log; private trees are
always removed. No source is modified outside the private temporary directory.
"""
import argparse
import json
import os
from pathlib import Path
import re
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "compatibility"))
import run_paired as rp
sys.path.insert(0, str(HERE))
import allocation_schema as sc

SIZES = (0, 1, 10, 100, 1000, 10000)
EXPENSIVE = ("compile_single", "frag_ac", "frag_ac_merge", "compile_ac")
SCALABLE = ("frag_create", "compile_batch", "exclude_matching",
            "history_remove", "storage_graph")

# The retained result is checked initially and after batches of one and two.
# Context restores isolate constants, TypeBase hooks, and theory mutations.
# Use a fresh theory too: sealing a theory is not undone by Context.restore.
# Paired.check uses CheckSupport's testutils tprint/OK/die reporter.
# The work phase of the allocation fixture (structure v1) runs here too,
# twice: its records are printed, and the steady-state counts, the counts of
# the use of the result and the result digest must reproduce within the
# process. The records of the two sides are then compared (compare_sides).
SELFTEST = '''open HolKernel MatrixSupport
val _ = new_theory "matrix_smoke"
val sizes = [%s]
val labels = [%s]
val _ = required (length cases = 51 andalso Lib.mk_set cases = cases)
fun validate label n = let
  val saved = Context.snapshot ()
  fun body () = let
    val _ = new_theory ("matrix_smoke_" ^ label ^ "_" ^ Int.toString n)
    val _ = print ("matrix smoke " ^ label ^ " " ^ Int.toString n ^ "\\n")
    val _ = TextIO.flushOut TextIO.stdOut
    val wl as {run,verify,beforeBatch,afterBatch} = workload label n
      handle e => (print "workload construction failed\\n"; raise e)
    val _ = verify ()
      handle e => (print "initial verification failed\\n"; raise e)
    fun batch count =
      (beforeBatch (); funpow count run (); afterBatch count; verify ())
    val _ = batch 1
    val _ = batch 2
    val _ = if label = "storage_graph" then (!rawStorage) () else ()
    val work = workPhase wl
      handle e => (print "work phase failed\\n"; raise e)
    val again = workPhase wl
    fun field key records = valOf (List.find (fn (k,_) => k = key) records)
    val _ = required (#2 (field "work.second" work) =
                      #2 (field "work.first" again) andalso
                      #2 (field "work.second" work) =
                      #2 (field "work.second" again) andalso
                      #2 (field "work.use" work) =
                      #2 (field "work.use" again) andalso
                      #2 (field "result.digest" work) =
                      #2 (field "result.digest" again))
    val _ = List.app (fn (k,v) => print ("@@MATRIX_WORK\\t" ^ label ^ "\\t" ^
              Int.toString n ^ "\\t" ^ k ^ "\\t" ^ v ^ "\\n")) work
    val _ = TextIO.flushOut TextIO.stdOut
  in Paired.check (label ^ ":" ^ Int.toString n) true end
in Portable.finally (fn () =>
     (rawStorage := (fn () => ()); Context.restore saved)) body () end
val _ = List.app (fn n => List.app (fn label => validate label n) labels) sizes
'''


def plan(scope, cases):
    if scope == "expensive":
        return [([name], [10000]) for name in cases if name in EXPENSIVE]
    small = [(cases, [0, 1, 10])]
    if scope == "small":
        return small
    if scope == "smoke":
        return small + [([c for c in cases if c in SCALABLE], [n])
                        for n in SIZES[3:]]
    return small + [(cases, [100]), (cases, [1000]),
                    ([c for c in cases if c not in EXPENSIVE], [10000])]


def storage_records(text, sizes, labels):
    records = []
    for line in text.splitlines():
        if not line.startswith("@@MATRIX_STORAGE"):
            continue
        fields = line.split("\t")
        rp.require(len(fields) == 3 and fields[1] == "storage_graph",
                   "invalid storage record")
        values = fields[2].split(",")
        rp.require(len(values) == 11 and all(re.fullmatch(r"[0-9]+", v)
                                          for v in values),
                   "invalid storage integers")
        v = list(map(int, values))
        rp.require(v[5] - v[4] == v[6] and v[8] - v[7] == v[9]
                   and v[10] == v[4], "invalid storage graph subtraction")
        records.append(v)
    expected = sizes if "storage_graph" in labels else []
    rp.require([v[0] for v in records] == expected,
               "missing/duplicate/unexpected storage records")
    return records


def work_records(text, sizes, labels):
    """The work records of one process: three per case and size, in order,
    the counts valid by the allocation schema (the digest is the
    fingerprint itself here; the fixture's process publishes it the same)."""
    records = []
    for line in text.splitlines():
        if not line.startswith("@@MATRIX_WORK\t"):
            continue
        fields = line.split("\t")
        rp.require(len(fields) == 5, "invalid work record")
        records.append(fields[1:])
    rp.require([r[:3] for r in records] == [
        [c, str(n), k] for n in sizes for c in labels
        for k in sc.WORK_EVENTS], "missing/duplicate/unexpected work records")
    for _, _, key, value in records:
        if key != "result.digest":
            sc.work_counts(value)
    return [dict(case=c, size=int(n), key=k, value=v)
            for c, n, k, v in records]


def compare_sides(runs):
    """Baseline against candidate, per case, size and work record: the
    differing records (with the differing counts of a count record) and the
    number of records compared. The records of the two sides must be the
    same set. Equal work records on both sides are what an unchanged
    operation shows."""
    sides = {"baseline": {}, "candidate": {}}
    for run in runs:
        if run.get("accepted") and "work" in run:
            seen = sides[run["selection"]]
            for r in run["work"]:
                key = (r["case"], r["size"], r["key"])
                rp.require(key not in seen, "duplicate work record")
                seen[key] = r["value"]
    keys = sorted(set(sides["baseline"]) | set(sides["candidate"]))
    differences = []
    for case, size, key in keys:
        b, c = sides["baseline"].get((case, size, key)), \
            sides["candidate"].get((case, size, key))
        if b == c:
            continue
        entry = dict(case=case, size=size, key=key, baseline=b, candidate=c)
        if b is not None and c is not None and key != "result.digest":
            bc, cc = sc.work_counts(b), sc.work_counts(c)
            entry["counts"] = {
                k: [bc.get(k, 0), cc.get(k, 0)]
                for k in sorted(set(bc) | set(cc))
                if bc.get(k, 0) != cc.get(k, 0)}
        differences.append(entry)
    return dict(compared=len(keys), differences=differences)


def report_sides(cross, note):
    note("cross-side work records: %d compared, %d differ"
         % (cross["compared"], len(cross["differences"])))
    for d in cross["differences"]:
        note("  DIFFERS %s %s %s" % (d["case"], d["size"], d["key"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[3])
    parser.add_argument("--baseline", default=rp.BASE)
    parser.add_argument("--candidate", default="HEAD")
    parser.add_argument("--output", type=Path,
                        help="new JSON path (sibling .log must be absent)")
    parser.add_argument("--compare", type=Path, metavar="MANIFEST",
                        help="only compare the work records of the two "
                        "sides in an earlier manifest (exit 1 on any "
                        "difference or none compared)")
    parser.add_argument("--scope", default="smoke",
                        choices=("small", "smoke", "grid", "expensive"))
    parser.add_argument("--case", action="append", dest="cases",
                        help="restrict cases (repeatable); sizes follow scope")
    parser.add_argument("--timeout", type=int, default=600,
                        help="seconds per build or grouped smoke process")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.compare is not None:
        cross = compare_sides(json.loads(args.compare.read_text())["runs"])
        report_sides(cross, print)
        return 1 if cross["differences"] or not cross["compared"] else 0
    if args.output is None:
        parser.error("--output is required")
    repo, output = args.repo.resolve(), args.output.resolve()
    logpath = output.with_suffix(".log")
    if output == logpath or output.exists() or logpath.exists():
        parser.error("JSON and sibling .log must be new, distinct files")
    output.parent.mkdir(parents=True, exist_ok=True)
    manifest = {"schema": 1, "success": False,
                "scope": "semantic smoke only; no performance acceptance",
                "command": [sys.executable, *sys.argv], "repo": str(repo),
                "scope_selection": args.scope, "selections": {}, "runs": [],
                "inputs": {}, "tools": {}, "expected_checks": 0,
                "executed_checks": 0}
    # Reserve both outputs before any build; never replace old evidence.
    with output.open("x") as result, logpath.open("x") as log:
        def note(text):
            print(text, flush=True)
            log.write(text + "\n")
            log.flush()

        def receipt_summary(receipt):
            return {k: v for k, v in receipt.items() if k != "stdout"}

        try:
            src = repo / "src/simp/tests/performance"
            text = (src / "MatrixSupport.sml").read_text()
            match = re.search(r"val cases =\s*\[(.*?)\]", text, re.S)
            rp.require(match is not None, "missing authoritative case list")
            allcases = re.findall(r'"([a-z_]+)"', match[1])
            rp.require(len(allcases) == len(set(allcases)) == 51,
                       "expected 51 distinct MatrixSupport cases")
            cases = args.cases or allcases
            rp.require(len(cases) == len(set(cases)) and
                       set(cases) <= set(allcases), "invalid/duplicate --case")
            groups = [(cs, ns) for cs, ns in plan(args.scope, cases) if cs]
            rp.require(bool(groups), "empty validation scope")
            manifest["plan"] = [
                {"cases": cs, "sizes": ns} for cs, ns in groups]
            manifest["expected_checks"] = 2 * sum(len(cs) * len(ns)
                                                  for cs, ns in groups)
            manifest["excluded_10000_expensive"] = (
                list(EXPENSIVE) if args.scope != "expensive" else [])
            manifest["head"] = rp.git(
                repo, "rev-parse", "HEAD").decode().strip()
            manifest["working_simplifier_diff"] = rp.git(
                repo, "diff", "HEAD", "--", "src/simp/src").decode()
            input_paths = [
                Path(__file__).resolve(), Path(rp.__file__).resolve(),
                src / "MatrixSupport.sml", src / "MatrixPerformance.sml",
                src / "RuntimeMetrics.sml",
                *sorted((rp.HERE / "paired").glob("*.sml")),
                rp.HERE / "paired/Holmakefile"]
            manifest["inputs"] = {
                str(p): rp.fingerprint(p) for p in input_paths}
            for name in ("bin/Holmake", "bin/hol", "bin/hol.state0"):
                manifest["tools"][str(repo / name)] = rp.fingerprint(
                    repo / name)
            excluded_env = ("HOL", "POLY", "ML", "PAIR_", "PERF_", "LD_")
            env = {k: v for k, v in os.environ.items()
                   if not k.startswith(excluded_env)}
            env.update(HOLDIR=str(repo), TERM="dumb", LC_ALL="C", TZ="UTC")
            with tempfile.TemporaryDirectory(prefix="matrix-smoke-") as tmp:
                root = Path(tmp)
                for selection, ref in (("baseline", args.baseline),
                                       ("candidate", args.candidate)):
                    dst = root / selection
                    dst.mkdir()
                    rev = rp.git(
                        repo, "rev-parse", ref + "^{commit}").decode().strip()
                    inventory = rp.extract(repo, rev, dst)
                    rp.install_fixtures(dst)
                    for name in ("MatrixSupport.sml", "MatrixPerformance.sml",
                                 "RuntimeMetrics.sml"):
                        (dst / name).write_bytes((src / name).read_bytes())
                    # Static compile the real timing entrypoint, but execute
                    # only our untimed selftest via the standard paired runner.
                    with (dst / "Holmakefile").open("a") as f:
                        f.write("\npaired.exe: MatrixPerformance.uo\n")
                    selection_info = {"requested_ref": ref, "revision": rev,
                                      "sources": inventory, "builds": [],
                                      "loaded_paths": {}}
                    manifest["selections"][selection] = selection_info
                    private_names = {
                        Path(s["git_path"]).stem for s in inventory}
                    hashes = {str(p): rp.fingerprint(p) for p in dst.iterdir()
                              if p.is_file()}
                    for index, (labels, sizes) in enumerate(groups):
                        code = SELFTEST % (
                            ",".join(map(str, sizes)),
                            ",".join(json.dumps(c) for c in labels))
                        (dst / "selftest.sml").write_text(code)
                        hashes[str(dst / "selftest.sml")] = rp.fingerprint(
                            dst / "selftest.sml")
                        command = [
                            str(repo / "bin/Holmake"), "--no-project",
                            "--no-cache", "--no_prereqs",
                            "--holstate=" + str(repo / "bin/hol.state0"),
                            "-C", str(dst), "-j1", "paired.exe"]
                        build = rp.execute(command, root, env, args.timeout)
                        selection_info["builds"].append(receipt_summary(build))
                        note(f"{selection} group {index} "
                             f"build exit={build['exit']}")
                        if build["exit"] or build["timed_out"]:
                            log.write(build["stdout"])
                        rp.require(
                            build["exit"] == 0 and not build["timed_out"],
                            selection + " private Holmake failed")
                        runenv = dict(
                            env, PAIR_SELECTION=selection,
                            PAIR_FIXTURE="selftest", PAIR_CONTROL="none",
                            PAIR_PRIVATE=str(dst), PAIR_TARGET="selftest")
                        receipt = rp.execute([str(dst / "paired.exe")], dst,
                                             runenv, args.timeout)
                        record = dict(
                            receipt_summary(receipt), selection=selection,
                            group=index,
                            selftest=hashes[str(dst / "selftest.sml")],
                            expected_checks=len(labels) * len(sizes),
                            accepted=False)
                        manifest["runs"].append(record)
                        expected = [["check", f"{c}:{n}", "pass"]
                                    for n in sizes for c in labels]
                        try:
                            audit = rp.validate(
                                receipt, selection=selection,
                                fixture="selftest",
                                control="none", private=dst, repo=repo,
                                private_names=private_names, flavor="baseline",
                                signature="pass", source_hashes=hashes,
                                expected_observations=expected)
                            record["storage"] = storage_records(
                                receipt["stdout"], sizes, labels)
                            record["work"] = work_records(
                                receipt["stdout"], sizes, labels)
                            record["checks"] = audit["observations"]
                            # Retain repeated path inventories only once;
                            # generated selftests are bound per run above.
                            for raw, info in audit["paths"].items():
                                if raw == str(dst / "selftest.sml"):
                                    continue
                                paths = selection_info["loaded_paths"]
                                old = paths.setdefault(raw, info)
                                rp.require(old == info,
                                           "loaded dependency changed")
                            record["accepted"] = True
                            manifest["executed_checks"] += len(expected)
                        except Exception as error:
                            record["failure"] = str(error)
                            log.write(receipt["stdout"])
                            raise
                        finally:
                            note(f"{selection} group {index} sizes={sizes} "
                                 f"cases={len(labels)} exit={receipt['exit']} "
                                 f"accepted={record['accepted']}")
                for info in manifest["selections"].values():
                    for path, source in info["loaded_paths"].items():
                        rp.require(rp.fingerprint(Path(source["physical"])) ==
                                   {k: source[k] for k in ("sha256", "bytes")},
                                   "loaded source changed: " + path)
                        products = source["related_products"]
                        for p, fingerprint in products.items():
                            rp.require(rp.fingerprint(Path(p)) == fingerprint,
                                       "loaded product changed: " + p)
                for path, fingerprint in {**manifest["inputs"],
                                          **manifest["tools"]}.items():
                    rp.require(rp.fingerprint(Path(path)) == fingerprint,
                               "input/tool changed: " + path)
            rp.require(
                manifest["executed_checks"] == manifest["expected_checks"],
                "incomplete checks")
            manifest["cross_side"] = compare_sides(manifest["runs"])
            report_sides(manifest["cross_side"], note)
            manifest["success"] = True
        except Exception as error:
            manifest["failure"] = str(error)
            note("FAIL: " + str(error))
        finally:
            result.write(json.dumps(manifest, indent=2) + "\n")
            note(f"checks={manifest['executed_checks']}/"
                 f"{manifest['expected_checks']} "
                 f"success={manifest['success']}")
            note(str(output))
    cross = manifest.get("cross_side", {"differences": [1]})
    return 0 if manifest["success"] and not cross["differences"] else 1


if __name__ == "__main__":
    sys.exit(main())
