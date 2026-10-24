"""Fail-closed admission for the narrow managed-allocation control fixture.

Not a validator for arbitrary workloads, allocator coverage, or TASK29 parity.
"""
import re

WORD_SIZES = (0, 1, 2, 127, 1024, 1048576)
BYTE_SIZES = (0, 1, 7, 8, 9, 15, 16, 17, 8192, 8388608)
REF_SIZES = (0, 1, 256, 512)
LABELS = (
    "noop-warmup-1", "noop-warmup-2", "noop-baseline", "noop-repeat-1",
    "noop-repeat-2", "gc-warmup", "gc-before-retained",
    "gc-before-retained-repeat",
    *(f"word-array-{n}" for n in WORD_SIZES),
    *(f"byte-array-{n}" for n in BYTE_SIZES),
    *(f"ref-list-{n}" for n in REF_SIZES),
    "rts-bignum-multiply", "gc-with-retained-arrays-1",
    "gc-with-retained-arrays-2", "compile-retained-entry-closure",
    "noop-final-1", "noop-final-2")


def require(yes, why):
    if not yes:
        raise ValueError(why)


def numbers(fields, count):
    require(len(fields) == count and all(
        re.fullmatch(r"0|[1-9][0-9]*", n) for n in fields),
        "malformed numeric control record")
    result = list(map(int, fields))
    require(all(n <= 2**64 - 1 for n in result), "uint64 out of range")
    return result


def observations(text):
    endpoints, deltas, layouts, singleton = [], [], [], {}
    known = {"SCOPE", "RUNTIME", "ABI", "NOOP", "UNCLAIMED"}
    completed = False
    for line in text.splitlines():
        if not line.startswith("@@TASK29_ALLOC_"):
            continue
        require(not completed, "control data after completion")
        parts = line.split("\t")
        kind = parts[0].removeprefix("@@TASK29_ALLOC_")
        if kind == "MAP_V1":
            require(len(parts) == 2, "malformed maps record")
        elif kind == "ENDPOINT_V1":
            require(len(parts) == 11 and parts[2] in ("start", "end"),
                    "malformed endpoint")
            s = numbers(parts[3:], 8)
            require(s[:3] == [1, 8, 0], "ABI/word-size/overflow mismatch")
            require(s[3] == sum(s[4:]), "endpoint category sum mismatch")
            endpoints.append((parts[1], parts[2], s))
        elif kind == "DELTA_V1":
            require(len(parts) == 7, "malformed delta")
            deltas.append((parts[1], numbers(parts[2:], 5)))
        elif kind == "LAYOUT_V1":
            require(len(parts) == 7, "malformed layout")
            layouts.append((parts[1], numbers(parts[2:], 5)))
        elif kind == "CONTROLS_COMPLETE_V1":
            require(kind not in singleton and parts == [parts[0], str(len(LABELS))],
                    "missing/duplicate/wrong completion count")
            singleton[kind] = parts[1:]
            completed = True
        else:
            require(kind.endswith("_V1") and kind[:-3] in known and
                    kind not in singleton, "unknown/duplicate control record")
            singleton[kind] = parts[1:]
    require(set(singleton) == {n + "_V1" for n in known} |
            {"CONTROLS_COMPLETE_V1"}, "missing control summary")
    require(singleton["ABI_V1"] == ["15"], "C ABI controls did not pass")
    require(singleton["SCOPE_V1"] == ["controls-only; not full runtime validation"]
            and len(singleton["UNCLAIMED_V1"]) == 1 and
            "TASK29B matrix" in singleton["UNCLAIMED_V1"][0],
            "scope/limitations record changed")
    require([(n, s) for n, s, _ in endpoints] == [
        (n, s) for n in LABELS for s in ("start", "end")],
        "missing/duplicate/reordered endpoints")
    require([n for n, _ in deltas] == list(LABELS),
            "missing/duplicate/reordered deltas")
    previous = [0] * 5
    for i, (_, delta) in enumerate(deltas):
        start, end = endpoints[2*i][2][3:], endpoints[2*i+1][2][3:]
        require(all(a <= b <= c for a, b, c in zip(previous, start, end)),
                "counter is not process-monotonic")
        require(delta == [b-a for a, b in zip(start, end)],
                "delta does not match endpoints")
        previous = end
    data = dict(deltas)
    idle = data["noop-baseline"]
    require(numbers(singleton["NOOP_V1"], 5) == idle,
            "no-op summary mismatch")
    require(all(data[n] == idle for n in (
        "noop-repeat-1", "noop-repeat-2", "noop-final-1", "noop-final-2")),
        "no-op controls do not repeat")
    gc = data["gc-before-retained"]
    require(all(data[n] == gc for n in (
        "gc-before-retained-repeat", "gc-with-retained-arrays-1",
        "gc-with-retained-arrays-2")), "GC recounts retained-data/unknown activity")
    expected = []
    for prefix, sizes, physical in (
        ("word-array", WORD_SIZES, lambda n: n + 1),
        ("byte-array", BYTE_SIZES, lambda n: 4 + (n+7)//8),
        ("ref-list", REF_SIZES, lambda n: 5*n)):
        zero = data[prefix + "-0"][0]
        for n in sizes:
            label, words = f"{prefix}-{n}", physical(n)
            total = data[label][0]
            require(total >= words and
                    total - zero == words - physical(0),
                    "physical allocation slope mismatch: " + label)
            expected.append((label, [n, words, total, total-words, 8*total]))
    require(layouts == expected, "layout/raw-byte evidence mismatch")
    require(data["ref-list-512"][1] > data["ref-list-0"][1],
            "no native allocation coverage")
    require(data["rts-bignum-multiply"][2] > idle[2], "no RTS coverage")
    require(data["compile-retained-entry-closure"][4] > idle[4],
            "no code-space coverage")
    return dict(brackets=len(LABELS), endpoints=endpoints, deltas=data,
                layouts=dict(layouts), no_op_words=idle,
                scope="controls only; interpreter/failures/full matrix unverified")
