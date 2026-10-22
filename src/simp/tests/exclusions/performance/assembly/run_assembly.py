#!/usr/bin/env python3
"""TASK17 source-tied delete/replay codegen; maintained TASK16 collector adapter."""
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CORE = HERE.parents[2] / "compiled-core/assembly/run_assembly.py"
spec = importlib.util.spec_from_file_location("task17_core_codegen", CORE)
core = importlib.util.module_from_spec(spec)
spec.loader.exec_module(core)
audit, paired, require = core.audit, core.paired, core.require
ROOTS = ("-*", "filter_net_by_names", "remove_ssfrags")
# build_from_history is inlined into remove_ssfrags by Poly/ML 5.9.2.
# Keep it optional and retain the caller's exact trees; never invent a body.
HELPERS = ("build_from_history", "name_match", "dphas_name_from",
           "filter_dprocs_by_names",
           "remove_simps", "setexcluded", "fupdlimit", "++", "mk_named_rewrs")
core.ROOTS, core.HELPERS = ROOTS, HELPERS
SPANS = {"history/SS": (257, 284), "delete/parser/filters": (291, 342),
         "replay/addition": (629, 718)}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=HERE.parents[5])
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--baseline-control", action="store_true")
    p.add_argument("--timeout", type=int, default=600)
    args = p.parse_args()
    output = args.output.resolve()
    original_snapshot, original_extract = (audit.fragments.snapshot,
                                           audit.extract)
    artifacts = {}
    adapter_inputs = {str(f): paired.fingerprint(f) for f in
        (CORE, core.COLLECTOR, HERE.parent / "ExclusionInputs.sml")}

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
        (dst / "ExclusionInputs.sml").write_bytes(
            (HERE.parent / "ExclusionInputs.sml").read_bytes())
        return revision, inventory

    def extract(text, private):
        lines, offset = audit.simp_extent(text, private)
        name = private.name + ".compiler-extent.txt.gz"
        archive(name, "".join(lines).encode())
        artifacts[name].update(stdout_start_line=offset + 1,
                               stdout_end_line=offset + len(lines))
        return original_extract(text, private)

    audit.HERE, audit.ROOTS, audit.HELPERS = HERE, ROOTS, HELPERS
    audit.CHECKS = ("assembly reset", "delete/replay 0", "delete/replay 10")
    audit.OBS = [["check", n, "pass"] for n in audit.CHECKS] + [
        ["observation", "complete", "TASK17-exclusion-assembly-v1"]]
    audit.extract, audit.extract_compiler = extract, core.compiler_records
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
            pass  # Only exact strict-equality rejection is promotable below.
    finally:
        sys.argv = argv
        audit.fragments.snapshot, audit.extract = (original_snapshot,
                                                   original_extract)
    path = output / "manifest.json"
    m = json.loads(path.read_text())
    valid = core.collection_accepted(m)
    m.update(evidence_id="TASK17-exclusion-assembly-v1",
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
