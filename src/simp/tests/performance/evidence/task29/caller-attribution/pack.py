#!/usr/bin/env python3
"""Lossless transport using a larger XZ dictionary for repeated compiler dumps.

The maintained evidence_bundle schema and per-file byte/hash checks are
unchanged. This affects transport compression only, never observations.
"""
import argparse
import json
import lzma
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
PERF = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(PERF))
import evidence_bundle as bundle
import caller_codegen as codegen

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("folder", type=Path)
parser.add_argument("archive", type=Path)
parser.add_argument("--report", type=Path, required=True)
parser.add_argument("--replay", action="store_true")
args = parser.parse_args()
original = lzma.compress
try:
    lzma.compress = lambda data: original(data, filters=[
        {"id": lzma.FILTER_LZMA2, "preset": 6, "dict_size": 256 << 20}])
    count = bundle.pack(args.folder, args.archive)
finally:
    lzma.compress = original
result = dict(files=count, archive=codegen.paired.fingerprint(args.archive),
              dictionary_bytes=256 << 20, roundtrip=False)
with tempfile.TemporaryDirectory(prefix="caller-codegen-roundtrip-") as temp:
    dst = Path(temp) / "unpacked"
    assert bundle.unpack(args.archive, dst) == count
    for path in args.folder.rglob("*"):
        if path.is_file():
            assert path.read_bytes() == (dst / path.relative_to(
                args.folder)).read_bytes()
    result["roundtrip"] = True
    if args.replay:
        result["replay"] = {name: codegen.replay_report(
            dst / name, PERF.parents[3]) for name in
            ("baseline-control", "baseline-candidate")}
with args.report.open("x") as stream:
    json.dump(result, stream, indent=2)
    stream.write("\n")
print(json.dumps(result, sort_keys=True))
