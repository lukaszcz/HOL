#!/usr/bin/env python3
"""Offline archive, source, raw protocol, inference and codegen checks."""
import gzip
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PERF = HERE.parent
sys.path.insert(0, str(PERF))
import summarize


def seal(data):
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    index = json.loads(gzip.decompress(
        (HERE / "archive-index.json.gz").read_bytes()))
    with tarfile.open(HERE / "sources.tar.xz") as archive:
        blobs = {m.name: archive.extractfile(m).read() for m in archive}
    for ref in index["source_refs"]:
        require(seal(blobs[ref["sha256"]]) ==
                {k: ref[k] for k in ("bytes", "sha256")}, "source drift")
    with tempfile.TemporaryDirectory(prefix="task18-evidence-") as scratch:
        root = Path(scratch)
        with tarfile.open(HERE / "receipts.tar.xz") as archive:
            require(set(archive.getnames()) == set(index["members"]),
                    "archive member inventory drift")
            for m in archive:
                require(m.isfile() and not Path(m.name).is_absolute() and
                        ".." not in Path(m.name).parts, "unsafe member")
                data = archive.extractfile(m).read()
                entry = index["members"][m.name]
                require(seal(data) == entry["stored"], "member drift")
                original = entry.get("original_name", Path(m.name).name)
                if original.endswith(".gz"):
                    data = gzip.compress(data, mtime=0)
                if "original" in entry:
                    require(seal(data) == entry["original"],
                            "original receipt bytes not recovered")
                path = root / Path(m.name).parent / original
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
        result = summarize.summarize(root / "final-current",
                                     root / "final-control")
        stored = json.loads((root / "final-analysis.json").read_text())
        require(result == stored, "analysis drift")
        manifests = {}
        for campaign in ("final-current", "final-control", "codegen-current",
                         "codegen-control"):
            m = json.loads((root / campaign / "manifest.json").read_text())
            manifests[campaign] = m
            for side, selected in m["selections"].items():
                for source in selected["sources"]:
                    wanted = {k: source[k] for k in ("bytes", "sha256")}
                    require(seal(blobs[source["sha256"]]) == wanted,
                            "manifest source not recovered")
        for timing, codegen in (("final-current", "codegen-current"),
                                ("final-control", "codegen-control")):
            for side in ("baseline", "candidate"):
                def inventory(campaign):
                    return {s["git_path"]: s["sha256"] for s in manifests[
                        campaign]["selections"][side]["sources"]}
                require(inventory(timing) == inventory(codegen),
                        "timing/codegen selected sources differ")
        initial = summarize.load(root / "initial-current", False)
        require(len(initial[1]) == 20, "initial campaign incomplete")
        old = initial[0]["performance"]["fixed_iterations"]
        expected = {key: count * max(1, math.ceil(.12 / min(
            value for process in initial[2].values()
            for value in process[key]))) for key, count in old.items()}
        require(expected == manifests["final-current"]["performance"][
                    "fixed_iterations"] == json.loads(
                    (PERF / "final-iterations.json").read_text()),
                "common all-sample calibration schedule drift")
        print("PASS: 60 timing processes; protocols, stages and inference")
        print("PASS: common schedule derived from all initial samples")
        spec = importlib.util.spec_from_file_location("task18_assembly_recheck",
            PERF / "assembly/run_assembly.py")
        assembly = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(assembly)
        audit = assembly.audit
        audit.ROOTS, audit.HELPERS = assembly.ROOTS, assembly.HELPERS
        for campaign in ("codegen-current", "codegen-control"):
            directory = root / campaign
            m = json.loads((directory / "manifest.json").read_text())
            require(m["success"] and m["inspection_complete"],
                    "codegen collection failed")
            trees = {}
            for side in ("baseline", "candidate"):
                name = side + ".compiler-extent.txt.gz"
                extent = gzip.decompress((directory / name).read_bytes())
                meta = m["extra_artifacts"][name]
                require(seal(extent) == dict(bytes=meta["uncompressed_bytes"],
                    sha256=meta["uncompressed_sha256"]), "extent drift")
                private = Path(m["selections"][side]["private"])
                offset = meta["stdout_start_line"] - 1
                text = ("\n" * (offset-1) + "@@PAIR\t0\tuse\t" +
                    str(private / "simpLib.sml") + "\n" + extent.decode() +
                    "@@PAIR\t1\tused\t" + str(private / "simpLib.sml") + "\n")
                trees[side] = assembly.compiler_records(text, private)
                expected = json.loads(gzip.decompress((directory /
                    (side + ".optimized-tree.json.gz")).read_bytes()))
                require(trees[side] == expected, "compiler selection drift")
                bodies = audit.extract(text, private)
                exact = gzip.decompress((directory /
                    (side + ".sml-assembly.txt.gz")).read_bytes())
                require("".join(bodies.values()).encode() == exact,
                        "native selection drift")
            require(assembly.core.tree_comparison(trees["baseline"],
                    trees["candidate"]) == m["compiler_comparison"],
                    "exact compiler comparison drift")
            native = audit.compare(assembly.core.native_records(
                trees["baseline"]), assembly.core.native_records(
                trees["candidate"]))
            require(native == m["extended_native_comparison"],
                    "native comparison drift")
            require(all(r["identical_after_pool_relocation"]
                        for r in native.values()), "native equality changed")
            print("PASS:", campaign, len(native), "selected native bodies")
    print("PASS: unique source blobs and original compressed receipt hashes")


if __name__ == "__main__":
    main()
