#!/usr/bin/env python3
"""TASK16 source-tied static compiler inspection; no timing/introspection.

Adapt the existing fail-closed private-source collector, not its production
inputs. Strict code equality is a reported outcome, NOT an acceptance gate:
this inspection must preserve and explain differences, not conceal them.
"""
import argparse
import difflib
import gzip
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
COLLECTOR = HERE.parents[1] / "fragments/assembly/run_assembly.py"
spec = importlib.util.spec_from_file_location("fragment_assembly", COLLECTOR)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
paired, require = audit.paired, audit.require
ROOTS = ("++", "mk_rewr_convdata", "appconv", "USER_CONV", "mk_named_rewrs")
HELPERS = ("net_add_conv", "net_add_convs", "mk_ac", "ac_rewrites",
           "empty_ss", "empty_ss-", "empty_ssfrag", "empty_excluded", "SSFRAG", "SS",
           "SSFRAG_CON", "ADDFRAG", "ssupd_net", "ssf_upd_rewrs",
           "fupdlimit", "limit", "unlimit", "rewrites", "rewrites_with_names",
           "conv_ss", "std_conv_ss", "ac_ss", "name_ss", "merge_ss",
           "split_name", "option_cases")


def selected(name):
    return bool(re.match(r"simpLib\.(?:" + "|".join(
        re.escape(n) for n in ROOTS + HELPERS) + r")(?:\(|$)", name))


def compiler_records(text, private):
    """Exact trees/passes, with original stdout line ranges and hashes.

    Keep library specializations whose printed code names a selected helper,
    plus their immediately following native body. No operand normalization.
    The full simpLib compiler extent is archived separately as a backstop.
    """
    lines, offset = audit.simp_extent(text, private)
    boundaries = [i for i, line in enumerate(lines) if
                  line.startswith("fn(") or re.fullmatch(
                      r"(?:[^\s:]+|<top level>):?[ \t]*\n", line)]
    result, previous = [], None
    for start, end in zip(boundaries, boundaries[1:] + [len(lines)]):
        raw = "".join(lines[start:end])
        if lines[start].startswith("fn("):
            match = re.search(r'\(\*\s*"([^"]+)"', raw)
            require(match is not None, "optimized lambda has no name")
            name, kind = match[1], "optimized-tree"
        else:
            name = lines[start].strip()
            kind = ("assembly" if name.endswith(":") else
                    "backend-tree" if name == "LAMBDA(" else "icode")
            name = name.removesuffix(":")
        referenced = any(selected(n) for n in re.findall(
            r'"(simpLib\.[^"]+)"', raw))
        keep = selected(name) or (not name.startswith("simpLib.") and (
            referenced or (kind == "assembly" and
                           previous == (name, "icode", True))))
        previous = name, kind, keep
        if keep:
            result.append(dict(kind=kind, name=name, text=raw,
                stdout_start_line=offset + start + 1,
                stdout_end_line=offset + end,
                sha256=paired.digest(raw.encode())))
    for root in ROOTS:
        require(any(r["kind"] == "optimized-tree" and
                    re.search(r'\(\*\s*"simpLib\.' + re.escape(root) +
                              r'(?:\(|")', r["text"]) for r in result),
                "missing optimized tree (including nested lambda): " + root)
    return result


def native_records(records):
    result = {}
    for row in records:
        if row["kind"] != "assembly":
            continue
        key, occurrence = row["name"], 1
        while key in result:
            occurrence += 1
            key = row["name"] + "@" + str(occurrence)
        result[key] = row["text"]
    return result


def collection_accepted(manifest):
    expected = ("strict equality rejected: nonrelocation code or "
                "emission-inventory differences (see comparison)")
    return manifest.get("collection_validated", False) and (
        manifest["success"] or manifest.get("failure") == expected)


# Exact pinned source ranges; callers of inlined helpers are linked by the runner.
SOURCE_SPANS = {"appconv": (53, 62), "mk_rewr_convdata": (65, 86),
    "SSFRAG_CON": (94, 103), "SSFRAG": (109, 114),
    "empty_ssfrag": (115, 116), "ssf_upd_rewrs": (117, 124),
    "history_item": (257, 259), "SS": (261, 270),
    "empty_excluded": (272, 272), "ssupd_net": (274, 278),
    "empty_ss": (280, 284), "USER_CONV": (350, 367),
    "net_add_conv": (371, 375), "net_add_convs": (377, 378),
    "mk_ac": (381, 389), "ac_rewrites": (391, 391),
    "fupdlimit": (402, 406), "limit/unlimit": (408, 410),
    "mk_named_rewrs": (629, 639), "++": (646, 682)}


def tree_comparison(a, b):
    """Compare every occurrence, including repeated optimizer/backend passes."""
    def keyed(records):
        result, occurrences = {}, {}
        for row in records:
            key = row["kind"] + ":" + row["name"]
            occurrences[key] = occurrences.get(key, 0) + 1
            result[key + "@" + str(occurrences[key])] = row["text"]
        return result
    aa, bb = keyed(a), keyed(b)
    result = {}
    for key in dict.fromkeys([*aa, *bb]):
        x, y = aa.get(key), bb.get(key)
        result[key] = dict(identical=x is not None and y is not None and x == y,
            baseline_emitted=x is not None, candidate_emitted=y is not None,
            diff=list(difflib.unified_diff((x or "").splitlines(),
                (y or "").splitlines(), fromfile="baseline",
                tofile="candidate", lineterm="")))
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[4])
    parser.add_argument("--candidate", default="worktree")
    parser.add_argument("--baseline-control", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args(argv)
    require(args.timeout > 0, "timeout must be positive")
    output = args.output.resolve()
    original_extract, original_snapshot = audit.extract, audit.fragments.snapshot
    original_collector_seal = paired.fingerprint(COLLECTOR)
    extra_artifacts = {}

    def archive(name, data):
        path = output / name
        path.write_bytes(gzip.compress(data, mtime=0))
        extra_artifacts[name] = dict(**paired.fingerprint(path),
            uncompressed_sha256=paired.digest(data),
            uncompressed_bytes=len(data))

    def snapshot(repo, ref, dst):
        revision, inventory = original_snapshot(repo, ref, dst)
        for name in ("simpLib.sml", "simpLib.sig", "Cond_rewr.sml",
                     "SimpTracking.sml", "SimpTracking.sig"):
            path = dst / name
            if path.exists():
                archive(dst.name + ".source." + name + ".gz", path.read_bytes())
        for name in ("simpLib.sml", "simpLib.sig"):
            require((dst / name).read_bytes() == paired.git(repo, "show",
                paired.BASE + ":src/simp/src/" + name),
                "TASK16 compiler source must match pinned baseline: " + name)
        return revision, inventory

    def extract(text, private):
        lines, offset = audit.simp_extent(text, private)
        archive(private.name + ".compiler-extent.txt.gz",
                "".join(lines).encode())
        extra_artifacts[private.name + ".compiler-extent.txt.gz"].update(
            stdout_start_line=offset + 1,
            stdout_end_line=offset + len(lines))
        return original_extract(text, private)

    audit.HERE, audit.ROOTS, audit.HELPERS = HERE, ROOTS, HELPERS
    audit.CHECKS = ("assembly reset", "empty/updaters", "named rewrite maker",
                    "bounded appconv", "user keyed/unkeyed conversions",
                    "AC compilation", "persistent original")
    audit.OBS = [["check", n, "pass"] for n in audit.CHECKS] + [
        ["observation", "complete", "TASK16-core-assembly-v1"]]
    audit.extract, audit.extract_compiler = extract, compiler_records
    audit.fragments.snapshot = snapshot
    old_argv = sys.argv
    sys.argv = [str(HERE / "run_assembly.py"), "--repo", str(args.repo),
        "--candidate", paired.BASE if args.baseline_control else args.candidate,
        "--output", str(output), "--timeout", str(args.timeout),
        "--optimized-tree"]
    try:
        try:
            audit.main()
        except SystemExit:
            # Only the collector's final strict-equality rejection is allowed.
            # Source/build/provenance/fixture failures remain failures below.
            pass
    finally:
        sys.argv = old_argv
        audit.extract = original_extract
        audit.fragments.snapshot = original_snapshot
    path = output / "manifest.json"
    manifest = json.loads(path.read_text())
    collector_success = manifest["success"]
    valid = collection_accepted(manifest)
    manifest.update(evidence_id="TASK16-core-assembly-v1",
        collector_success=collector_success, inspection_complete=valid,
        success=valid, baseline_control=args.baseline_control,
        compiler_source_matches_pinned=True if valid else None,
        extra_artifacts=extra_artifacts,
        collector=dict(path=str(COLLECTOR), **original_collector_seal),
        acceptance="validated source/load/fixture provenance and complete "
            "comparison; strict equality is an outcome, not a gate")
    if valid:
        require(paired.fingerprint(COLLECTOR) == original_collector_seal,
                "collector drift")
        trees = {side: json.loads(gzip.decompress((output /
            (side + ".optimized-tree.json.gz")).read_bytes()))
            for side in ("baseline", "candidate")}
        manifest["compiler_comparison"] = tree_comparison(
            trees["baseline"], trees["candidate"])
        manifest["extended_native_comparison"] = audit.compare(
            native_records(trees["baseline"]), native_records(trees["candidate"]))
        manifest["collector_strict_equality_accepted"] = manifest[
            "strict_equality_accepted"]
        manifest["strict_equality_accepted"] = all(
            row["identical_after_pool_relocation"] for row in
            manifest["extended_native_comparison"].values())
        source = gzip.decompress((output /
            "baseline.source.simpLib.sml.gz").read_bytes()).decode()
        lines = source.splitlines(keepends=True)
        manifest["source_spans"] = {name: dict(start_line=start,
            end_line=end, text="".join(lines[start - 1:end]))
            for name, (start, end) in SOURCE_SPANS.items()}
        cond = [gzip.decompress((output /
            (side + ".source.Cond_rewr.sml.gz")).read_bytes()).decode()
            for side in ("baseline", "candidate")]
        manifest["cond_rewr_source_diff"] = list(difflib.unified_diff(
            cond[0].splitlines(), cond[1].splitlines(),
            fromfile="baseline/Cond_rewr.sml", tofile="candidate/Cond_rewr.sml",
            lineterm=""))
        if args.baseline_control:
            require(manifest["strict_equality_accepted"],
                    "pinned control emitted different native code")
            require(all(row["identical"] for key, row in
                manifest["compiler_comparison"].items()
                if not key.startswith("assembly:")),
                "pinned control emitted different trees/ICode")
        manifest["difference_notice"] = manifest.pop("failure", None)
    path.write_text(json.dumps(manifest, indent=2) + "\n")
    if not valid:
        raise SystemExit(manifest.get("failure", "inspection incomplete"))


if __name__ == "__main__":
    main()
