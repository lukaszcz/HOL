#!/usr/bin/env python3
"""Offline raw/protocol, lossless archive and exact codegen recheck."""
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tarfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import summarize

ARCHIVED = {}
ALIASES = {}


def seal(data):
    return dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def artifact_bytes(path):
    name = os.path.relpath(path, HERE)
    if name in ALIASES:
        return artifact_bytes(HERE / ALIASES[name]["target"])
    if name in ARCHIVED:
        return ARCHIVED[name]
    return path.read_bytes()


def load(path):
    data = artifact_bytes(path)
    return json.loads(gzip.decompress(data) if path.suffix == ".gz" else data,
                      object_pairs_hook=summarize.schema.unique)


def recheck_compaction():
    c = load(HERE / "archive-compaction.json")
    previous = c["previous_inventories"]
    assert seal((HERE / previous["path"]).read_bytes()) == {
        k: previous[k] for k in ("sha256", "bytes")}
    for name, fingerprint in c["archives"].items():
        assert seal((HERE / name).read_bytes()) == fingerprint, name
        entries = {v["member"]: (k, v) for k, v in c["archived"].items()
                   if v["archive"] == name}
        with tarfile.open(HERE / name, "r:xz") as archive:
            assert sorted(archive.getnames()) == sorted(entries), name
            for member in archive:
                old_name, entry = entries[member.name]
                assert member.isfile() and entry["encoding"] == "gzip-mtime0"
                raw = archive.extractfile(member).read()
                assert seal(raw) == entry["uncompressed"], old_name
                data = gzip.compress(raw, mtime=0)
                assert seal(data) == entry["original"], old_name
                ARCHIVED[old_name] = data
    ALIASES.update(c["aliases"])
    for name, entry in ALIASES.items():
        assert entry["target"] not in ALIASES, "alias chain/cycle"
        assert seal(artifact_bytes(HERE / name)) == entry["original"], name
    for name in (*c["archived"], *ALIASES, *c["removed"]):
        assert not (HERE / name).exists(), "redundant copy: " + name
    failure = load(HERE / "codegen-current/failure.json.gz")
    manifest = load(HERE / "codegen-current/manifest.json.gz")
    assert not manifest["success"] and not manifest["inspection_complete"]
    assert not failure["accepted"] and "diagnostics" not in failure
    assert failure["rejection"] == manifest["failure"] == (
        "missing optimized tree (including nested lambda): build_from_history")
    for name, entry in c["removed"].items():
        assert manifest["artifacts"][Path(name).name] == entry["original"]
        assert seal(artifact_bytes(HERE / entry["replacement"])) == (
            entry["replacement_seal"])
    old = load(HERE / previous["path"])
    prefixes = tuple("evidence/" + name for name in (
        "final-", "codegen-current-final/", "codegen-control-final/",
        "gc-long-", "gc-trace-current/"))
    summaries = {"evidence/compact-summary.json.gz",
                 "evidence/gc-diagnostic-summary.json.gz"}
    for inventory in ("SHA256SUMS", "GC_SHA256SUMS"):
        for line in old[inventory].splitlines():
            digest, name = line.split("  ", 1)
            if name.startswith(prefixes) or name in summaries:
                data = artifact_bytes(HERE.parent / name)
                assert hashlib.sha256(data).hexdigest() == digest, name
    print(f"PASS: {len(ARCHIVED)} lossless relocations, "
          f"{len(ALIASES)} exact aliases, compact failure")
    print("PASS: original final timing/codegen/GC hashes preserved")


def main():
    recheck_compaction()
    # Use the maintained parser on virtual original paths, without extraction.
    summarize.read_json = load
    summarize.load(HERE / "second-current", False)
    expected = load(HERE / "final-analysis.json.gz")
    actual = summarize.summarize(HERE / "final-current",
                                 HERE / "final-control")
    assert actual == expected, "raw receipt / analysis mismatch"
    spec = importlib.util.spec_from_file_location("task17_codegen_recheck",
        HERE.parent / "assembly/run_assembly.py")
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    adapter.audit.ROOTS = adapter.ROOTS
    adapter.audit.HELPERS = adapter.HELPERS
    for campaign in ("codegen-current-final", "codegen-control-final"):
        root = HERE / campaign
        m = load(root / "manifest.json.gz")
        assert m["success"] and m["inspection_complete"]
        assert m["evidence_id"] == "TASK17-exclusion-assembly-v1"
        for name, fingerprint in m["artifacts"].items():
            assert seal(artifact_bytes(root / name)) == fingerprint, name
        for name, fingerprint in m["extra_artifacts"].items():
            data = gzip.decompress(artifact_bytes(root / name))
            assert adapter.paired.digest(data) == (
                fingerprint["uncompressed_sha256"])
            assert len(data) == fingerprint["uncompressed_bytes"]
        records = {side: load(root / (side + ".optimized-tree.json.gz"))
                   for side in ("baseline", "candidate")}
        assert adapter.core.tree_comparison(records["baseline"],
            records["candidate"]) == m["compiler_comparison"]
        assert adapter.audit.compare(
            adapter.core.native_records(records["baseline"]),
            adapter.core.native_records(records["candidate"])) == m[
                "extended_native_comparison"]
        for side in ("baseline", "candidate"):
            source = gzip.decompress(artifact_bytes(root /
                (side + ".source.simpLib.sml.gz")))
            assert adapter.paired.digest(source) == (
                "ee324439ac66cd14858d6ea5dc45a867d"
                "44fa6762298f1cf7df45b13aed6c3cd")
    import gc_summary
    gc_actual = dict(scope=gc_summary.__doc__,
        statistics_fields=list(gc_summary.FIELDS),
        current=gc_summary.diagnostic("gc-long-current"),
        control=gc_summary.diagnostic("gc-long-control"),
        trace=gc_summary.trace())
    assert gc_actual == load(HERE / "gc-diagnostic-summary.json.gz")
    print("PASS: 40 final + 20 exploratory timing receipts, exact analysis")
    print("PASS: both exact codegen archives; 18 GC diagnostic receipts")


if __name__ == "__main__":
    main()
