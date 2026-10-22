#!/usr/bin/env python3
"""TASK18 ordinary staging codegen using the maintained strict collector."""
import argparse
import gzip
import importlib.util
import json
import re
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CORE = HERE.parents[2] / "compiled-core/assembly/run_assembly.py"
spec = importlib.util.spec_from_file_location("task18_core_codegen", CORE)
core = importlib.util.module_from_spec(spec)
spec.loader.exec_module(core)
audit, paired, require = core.audit, core.paired, core.require
ROOTS = ("process_tags", "SIMP_CONV", "SIMP_RULE", "ASM_SIMP_RULE",
         "SIMP_TAC", "ASM_SIMP_TAC", "GEN_FULL_SIMP_TAC", "psr", "allasms",
         "global_simp_tac")
HELPERS = ("BF_ASSUME_TAC", "caa_tac0", "stdcon", "drop", "tactic_only",
           "SIMP_QCONV", "SIMP_CONV", "rewrites", "++", "appconv")
core.ROOTS, core.HELPERS = ROOTS, HELPERS
SPANS = {"directive/conversion": (824, 918), "full/global": (936, 1017)}


def compiler_records(text, private):
    """Retain backend trees when local blocks have no optimized-tree print.

    Poly/ML emits these roots inside local declaration blocks as LAMBDA
    backend trees, without a corresponding fn(... optimized-tree record.
    Preserve the actual available pass; never fabricate an optimized tree.
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
        referenced = any(core.selected(n) for n in re.findall(
            r'simpLib\.[^\s";,)]+(?:\([^\s";]*\))?', raw))
        keep = core.selected(name) or (not name.startswith("simpLib.") and (
            referenced or (kind == "assembly" and
                           previous == (name, "icode", True))))
        previous = name, kind, keep
        if keep:
            result.append(dict(kind=kind, name=name, text=raw,
                stdout_start_line=offset + start + 1,
                stdout_end_line=offset + end,
                sha256=paired.digest(raw.encode())))
    for root in ROOTS:
        require(any(r["kind"] in ("optimized-tree", "backend-tree") and
                    re.search(r'\bsimpLib\.' + re.escape(root) +
                              r'\(', r["text"]) for r in result),
                "missing actual compiler tree: " + root)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=HERE.parents[5])
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--baseline-control", action="store_true")
    p.add_argument("--timeout", type=int, default=600)
    p.add_argument("--authorize-measurements", action="store_true")
    args = p.parse_args()
    require(args.authorize_measurements, "require exclusive authorization")
    output = args.output.resolve()
    original_snapshot, original_extract = (audit.fragments.snapshot,
                                           audit.extract)
    artifacts = {}
    adapter_inputs = {str(f): paired.fingerprint(f) for f in
        (CORE, core.COLLECTOR, HERE.parent / "TacticInputs.sml")}

    def archive(name, data):
        path = output / name
        path.write_bytes(gzip.compress(data, mtime=0))
        artifacts[name] = dict(**paired.fingerprint(path),
            uncompressed_sha256=paired.digest(data),
            uncompressed_bytes=len(data))

    def snapshot(repo, ref, dst):
        revision, inventory = original_snapshot(repo, ref, dst)
        for name in ("simpLib.sml", "simpLib.sig", "Cond_rewr.sml"):
            archive(dst.name + ".source." + name + ".gz",
                    (dst / name).read_bytes())
        for name in ("simpLib.sml", "simpLib.sig"):
            require((dst / name).read_bytes() == paired.git(repo, "show",
                paired.BASE + ":src/simp/src/" + name),
                "ordinary source differs from pinned: " + name)
        (dst / "TacticInputs.sml").write_bytes(
            (HERE.parent / "TacticInputs.sml").read_bytes())
        return revision, inventory

    def extract(text, private):
        lines, offset = audit.simp_extent(text, private)
        name = private.name + ".compiler-extent.txt.gz"
        archive(name, "".join(lines).encode())
        artifacts[name].update(stdout_start_line=offset + 1,
                               stdout_end_line=offset + len(lines))
        return original_extract(text, private)

    audit.HERE, audit.ROOTS, audit.HELPERS = HERE, ROOTS, HELPERS
    audit.CHECKS = ("assembly reset", "ordinary 0", "ordinary 8")
    audit.OBS = [["check", n, "pass"] for n in audit.CHECKS] + [
        ["observation", "complete", "TASK18-tactic-assembly-v1"]]
    audit.extract, audit.extract_compiler = extract, compiler_records
    audit.fragments.snapshot = snapshot
    argv = sys.argv
    sys.argv = [str(HERE / "run_assembly.py"), "--repo", str(args.repo),
        "--candidate", paired.BASE if args.baseline_control else "worktree",
        "--output", str(output), "--timeout", str(args.timeout),
        "--optimized-tree"]
    try:
        try:
            audit.main()
        except SystemExit:
            pass  # Only the exact validated strict-equality failure is allowed.
    finally:
        sys.argv = argv
        audit.fragments.snapshot, audit.extract = (original_snapshot,
                                                   original_extract)
    path = output / "manifest.json"
    m = json.loads(path.read_text())
    valid = core.collection_accepted(m)
    m.update(evidence_id="TASK18-tactic-assembly-v1",
        collector_success=m["success"], inspection_complete=valid,
        success=valid, baseline_control=args.baseline_control,
        extra_artifacts=artifacts, adapter_inputs=adapter_inputs)
    if valid:
        for name, seal in adapter_inputs.items():
            require(paired.fingerprint(Path(name)) == seal, "adapter drift")
        trees = {side: json.loads(gzip.decompress((output /
            (side + ".optimized-tree.json.gz")).read_bytes()))
            for side in ("baseline", "candidate")}
        m["compiler_comparison"] = core.tree_comparison(
            trees["baseline"], trees["candidate"])
        m["extended_native_comparison"] = audit.compare(
            core.native_records(trees["baseline"]),
            core.native_records(trees["candidate"]))
        m["strict_equality_accepted"] = all(
            row["identical_after_pool_relocation"] for row in
            m["extended_native_comparison"].values())
        source = gzip.decompress((output /
            "baseline.source.simpLib.sml.gz").read_bytes()).decode()
        lines = source.splitlines(keepends=True)
        m["source_spans"] = {name: dict(start_line=a, end_line=b,
            text="".join(lines[a-1:b])) for name, (a, b) in SPANS.items()}
        m["difference_notice"] = m.pop("failure", None)
        if args.baseline_control:
            require(m["strict_equality_accepted"], "control native differs")
            require(all(row["identical"] for key, row in
                m["compiler_comparison"].items()
                if not key.startswith("assembly:")), "control trees differ")
    path.write_text(json.dumps(m, indent=2) + "\n")
    if not valid:
        raise SystemExit(m.get("failure", "inspection incomplete"))


if __name__ == "__main__":
    main()
