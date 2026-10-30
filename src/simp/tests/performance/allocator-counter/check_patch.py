#!/usr/bin/env python3
"""Static checks only: replay patch hunks in memory, without building Poly/ML.

Run with python3 -B. --source-only checks current transformations without
requiring regenerated patch artifacts. NOT a runtime correctness/coverage test.
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
    parser.add_argument(
        "--source-only", action="store_true",
        help="check transformations in memory, ignoring generated artifacts",
    )
    args = parser.parse_args()
    seal = json.loads((HERE / "SOURCE_SHA256.json").read_text())
    originals = {
        name: (args.source / name).read_bytes() for name in seal["files"]
    }
    for name, raw in originals.items():
        assert hashlib.sha256(raw).hexdigest() == seal["files"][name]
    expected = transformations(originals)
    if args.source_only:
        actual = expected
    else:
        actual = replay(read_patch(), originals)
        assert actual == expected
        after_seal = json.loads((HERE / "PATCHED_SHA256.json").read_text())
        assert {
            p: hashlib.sha256(b).hexdigest() for p, b in actual.items()
        } == after_seal
    # Four paths, five success hooks. Branch diagnostics replace, rather
    # than supplement, the interpreter's two original accounting calls.
    hooks = {
        "arm64.cpp": 1, "run_time.cpp": 1,
        "bytecode.cpp": 0, "memmgr.cpp": 1,
    }
    for name, count in hooks.items():
        text = actual["libpolyml/" + name].decode()
        # Also exclude the definition of RecordManagedAllocation in run_time.
        assert len(re.findall(
            r"RecordManagedAllocation\("
            r"ManagedAlloc(?:Native|RTS|Interpreter|Code),", text,
        )) == count
    bytecode = actual["libpolyml/bytecode.cpp"].decode()
    assert bytecode.count("RecordManagedInterpreterAllocation(") == 2
    assert (
        "taskData->allocPointer -= words;\n"
        "        RecordManagedInterpreterAllocation(false, words);"
    ) in bytecode
    assert (
        "if (space == 0) return 0;\n"
        "    RecordManagedInterpreterAllocation(true,\n"
        "        ManagedHeapReservationWords(words));\n"
        "    return (PolyObject*)(space + 1);"
    ) in bytecode
    # Lower-level path diagnostics: one caller marker at each of the three
    # FindAllocationSpace users, three success outcomes, GC and failure.
    for name, marker in (
            ("arm64.cpp", "ManagedSetFindCaller(ManagedAllocNative);"),
            ("run_time.cpp", "ManagedSetFindCaller(ManagedAllocRTS);"),
            ("bytecode.cpp",
             "ManagedSetFindCaller(ManagedAllocInterpreter);")):
        assert actual["libpolyml/" + name].decode().count(marker) == 1
    processes = actual["libpolyml/processes.cpp"].decode()
    for outcome in ("Segment", "LargeObject", "Refill"):
        assert processes.count(
            "RecordManagedFindSuccess(ManagedFind" + outcome) == 1
    assert processes.count("RecordManagedFindFailure(words);") == 1
    assert processes.count("RecordManagedQuickGC(managedGC);") == 1
    assert processes.count("managedAfterGC = true;") == 2
    assert actual["libpolyml/memmgr.cpp"].decode().count(
        "RecordManagedCodeFailure();") == 1
    # The one place the native backend creates task data for a thread the
    # runtime did not create is counted; the source has no other such site.
    arm64 = actual["libpolyml/arm64.cpp"]
    assert arm64.count(b"RecordManagedForeignThread();") == 1
    assert (
        b"    if (taskData == 0)\r\n    {\r\n"
        b"        RecordManagedForeignThread();\r\n"
        b"        try {\r\n"
        b"            taskData = processes->CreateNewTaskData();"
    ) in arm64
    assert arm64.count(b"CreateNewTaskData()") == 1
    assert arm64.count(b"\r\n") == arm64.count(b"\n")
    if args.source_only:
        print("PASS: pinned source hashes; eight in-memory transformations")
        print("Generated artifacts NOT checked or updated.")
    else:
        print("PASS: eight targets replay byte-exactly; "
              "input/output hashes match")
    print("Five success hooks, interpreter fast/slow and lower-level path")
    print("diagnostics;")
    print("original ARM64 CRLF preserved. STATIC ONLY; not complete coverage.")


if __name__ == "__main__":
    main()
