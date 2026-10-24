#!/usr/bin/env python3
"""Static checks only: replay patch hunks in memory, without building Poly/ML.

Run with python3 -B. This is NOT a counter correctness/runtime regression test.
"""
import argparse
import hashlib
import gzip
import json
from pathlib import Path
import re

from prepare_patch import DEFAULT_SOURCE, HERE, transformations


def replay(patch, originals):
    """Strict unified-hunk replay, preserving original CRLF bytes."""
    targets = {}
    chunks = patch.split(b"diff --git ")[1:]
    for chunk in chunks:
        lines = chunk.splitlines(keepends=True)
        name = lines[0].split(b" b/", 1)[1].strip().decode()
        old = originals.get(name, b"").splitlines(keepends=True)
        out = []
        cursor = 0
        i = 1
        while i < len(lines):
            if not lines[i].startswith(b"@@ "):
                i += 1
                continue
            match = re.fullmatch(
                rb"@@ -(\d+),(\d+) \+(\d+),(\d+) @@\n", lines[i]
            )
            assert match, lines[i]
            old_start, old_count, new_start, new_count = map(
                int, match.groups()
            )
            start = max(0, old_start - 1)
            assert start >= cursor
            out.extend(old[cursor:start])
            cursor = start
            assert len(out) == max(0, new_start - 1)
            seen_old = seen_new = 0
            i += 1
            while i < len(lines) and not lines[i].startswith(b"@@ "):
                line = lines[i]
                assert line[:1] in (b" ", b"-", b"+")
                if line[:1] in (b" ", b"-"):
                    assert old[cursor] == line[1:], (name, cursor)
                    cursor += 1
                    seen_old += 1
                if line[:1] in (b" ", b"+"):
                    out.append(line[1:])
                    seen_new += 1
                i += 1
            assert (seen_old, seen_new) == (old_count, new_count)
        out.extend(old[cursor:])
        targets[name] = b"".join(out)
    return targets


def read_patch():
    return gzip.decompress((HERE / "managed-allocation.patch.gz").read_bytes())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    args = parser.parse_args()
    seal = json.loads((HERE / "SOURCE_SHA256.json").read_text())
    originals = {
        name: (args.source / name).read_bytes() for name in seal["files"]
    }
    for name, raw in originals.items():
        assert hashlib.sha256(raw).hexdigest() == seal["files"][name]
    expected = transformations(originals)
    actual = replay(read_patch(), originals)
    assert actual == expected
    after_seal = json.loads((HERE / "PATCHED_SHA256.json").read_text())
    assert {p: hashlib.sha256(b).hexdigest() for p, b in actual.items()} == (
        after_seal
    )
    # Four paths, five success hooks (interpreter has fast and slow returns).
    hooks = {
        "arm64.cpp": 1, "run_time.cpp": 1,
        "bytecode.cpp": 2, "memmgr.cpp": 1,
    }
    for name, count in hooks.items():
        text = actual["libpolyml/" + name].decode()
        # Also exclude the definition of RecordManagedAllocation in run_time.
        assert len(re.findall(
            r"RecordManagedAllocation\("
            r"ManagedAlloc(?:Native|RTS|Interpreter|Code),", text,
        )) == count
    patch_bytes = read_patch()
    assert b"processes.cpp" not in patch_bytes
    assert actual["libpolyml/arm64.cpp"].count(b"\r\n") == (
        actual["libpolyml/arm64.cpp"].count(b"\n")
    )
    print("PASS: seven targets replay byte-exactly; source/output hashes match")
    print("five success hooks; original ARM64 CRLF preserved. STATIC ONLY.")


if __name__ == "__main__":
    main()
