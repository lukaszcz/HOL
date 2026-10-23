#!/usr/bin/env python3
"""Lossless compact evidence transport; unpack before running archive audits.

Repeated JSON/path inventories compress together instead of as hundreds of
independent gzip members. Every original byte/hash is verified on round trip.
This is transport only, not a provenance or measurement acceptance validator.
"""
import argparse
import base64
import gzip
import hashlib
import json
import lzma
from pathlib import Path
import shutil


def stamp(data):
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


def pack(folder, output):
    folder, output = Path(folder).resolve(), Path(output).resolve()
    if not folder.is_dir() or output.is_relative_to(folder):
        raise ValueError("require source folder and external output")
    files = {}
    for path in sorted(folder.rglob("*")):
        if path.is_symlink():
            raise ValueError("symlink in evidence")
        if not path.is_file():
            continue
        data = path.read_bytes()
        record = stamp(data)
        decoded = gzip.decompress(data) if path.suffix == ".gz" else data
        try:
            text = decoded.decode("utf-8")
            encoded = gzip.compress(decoded, mtime=0) if \
                path.suffix == ".gz" else decoded
            if encoded != data:
                raise ValueError("gzip header differs")
            record.update(encoding="gzip-text" if path.suffix == ".gz"
                          else "text", content=text)
        except (UnicodeError, ValueError):
            record.update(encoding="base64", content=base64.b64encode(
                data).decode("ascii"))
        files[str(path.relative_to(folder))] = record
    if not files:
        raise ValueError("empty evidence folder")
    payload = dict(schema="task28-lossless-evidence-v1", files=files)
    data = json.dumps(payload, ensure_ascii=True,
                      separators=(",", ":")).encode()
    data = lzma.compress(data) if output.suffix == ".xz" else \
        gzip.compress(data, mtime=0)
    with output.open("xb") as stream:
        stream.write(data)
    return len(files)


def unpack(archive, output):
    data = Path(archive).read_bytes()
    payload = json.loads(lzma.decompress(data) if data.startswith(b"\xfd7zXZ")
                         else gzip.decompress(data))
    if payload["schema"] != "task28-lossless-evidence-v1":
        raise ValueError("unknown evidence transport")
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    try:
        for name, record in payload["files"].items():
            path = Path(name)
            if path.is_absolute() or ".." in path.parts or not path.name:
                raise ValueError("unsafe evidence path")
            encoding = record["encoding"]
            if encoding == "base64":
                data = base64.b64decode(record["content"], validate=True)
            elif encoding in ("text", "gzip-text"):
                data = record["content"].encode("utf-8")
                if encoding == "gzip-text":
                    data = gzip.compress(data, mtime=0)
            else:
                raise ValueError("unknown evidence encoding")
            if stamp(data) != {k: record[k] for k in ("bytes", "sha256")}:
                raise ValueError("evidence transport changed original bytes")
            path = output / path
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("xb") as stream:
                stream.write(data)
    except BaseException:
        shutil.rmtree(output)
        raise
    return len(payload["files"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("pack", "unpack"))
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    count = (pack if args.action == "pack" else unpack)(args.source, args.output)
    print(str(count) + " files; lossless transport")


if __name__ == "__main__":
    main()
