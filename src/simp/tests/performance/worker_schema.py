"""Fail-closed V1 protocol for allocating ML worker/retirement controls.

Admission is not runtime identity/provenance validation or TASK29B acceptance.
The execution driver must independently seal the launcher, shim and mapped DSO.
No synthetic fixture here is evidence of executed worker allocation.
"""
import re

PREFIX = "@@TASK29_WORKER_"
SCOPE = "allocating-ML-workers-only; not full runtime validation"
UNCLAIMED = ("compact32; foreign-created threads; interpreter coverage; "
             "failures/overflow; full runtime completeness; TASK29B matrix")
CONFIG = [4, 8, 2, 0, 256, 512, 5]
LABELS = (
    "noop-warmup-1", "noop-warmup-2", "noop-before", "gc-warmup",
    "gc-empty-1", "gc-empty-2", "workers-warmup-1", "workers-warmup-2",
    "workers-0-1", "workers-256-1", "workers-512-1",
    "workers-0-2", "workers-256-2", "workers-512-2",
    "gc-live-1", "gc-live-2", "noop-parked", "retirement",
    "noop-retired-1", "noop-retired-2", "gc-retired-1", "gc-retired-2")
WORK_LABELS = tuple(n for n in LABELS if n.startswith("workers-"))
RESULT_LABELS = (*WORK_LABELS, "before-retirement", "after-retired-gc")
RAW_FIELDS = ("n", "parked_before", "parked_after", "active_before",
              "active_after", "failures", "total", "native", "rts",
              "interpreter", "code")
UINT64_MAX = 2**64 - 1


def require(yes, why):
    if not yes:
        raise ValueError(why)


def numbers(fields, count):
    require(len(fields) == count and all(
        re.fullmatch(r"0|[1-9][0-9]*", n) for n in fields),
        "malformed worker numeric record")
    # Bound decimal length before int() too (no giant untrusted integers).
    require(all(len(n) <= 20 for n in fields), "uint64 out of range")
    result = list(map(int, fields))
    require(all(n <= UINT64_MAX for n in result), "uint64 out of range")
    return result


def observations(text):
    records = [line.split("\t") for line in text.splitlines()
               if line.startswith("@@TASK29")]
    cursor = 0

    def take(kind):
        nonlocal cursor
        require(cursor < len(records), "missing worker " + kind)
        p = records[cursor]
        require(p[0] == PREFIX + kind + "_V1",
                "missing/reordered/unknown worker record: " + kind)
        cursor += 1
        return p[1:]

    require(take("SCOPE") == [SCOPE], "changed worker scope")
    runtime = take("RUNTIME")
    require(len(runtime) == 1 and runtime[0].startswith("/") and
            not any(c.isspace() for c in runtime[0]),
            "malformed worker runtime identity")
    maps = []
    while cursor < len(records) and records[cursor][0] == PREFIX + "MAP_V1":
        p = take("MAP")
        require(len(p) == 1 and re.fullmatch(
            r"[0-9a-f]+-[0-9a-f]+ [r-][w-][x-][ps] [0-9a-f]+ "
            r"[0-9a-f]+:[0-9a-f]+ [0-9]+(?: +[^\t]*)?", p[0]),
            "malformed worker process map")
        require(p[0] not in maps, "duplicate worker process map")
        maps.append(p[0])
    require(maps, "missing worker process maps")
    require(take("ABI") == ["15"], "worker C ABI controls failed")
    require(numbers(take("CONFIG"), 7) == CONFIG,
            "changed worker configuration")
    endpoints, raw, results, retired = [], {}, [], []
    previous = [0] * 5
    n = 0

    def result_records(label, count):
        for worker in range(4):
            p = take("RESULT")
            require(len(p) == 4 and p[0] == label,
                    "missing/reordered worker retained-result evidence")
            values = numbers(p[1:], 3)
            require(values == [worker, count, count*(count+1)//2],
                    "worker retained result changed")
            results.append((label, *values))

    for label in LABELS:
        if label == "retirement":
            result_records("before-retirement", 512)
        if label.startswith("workers-"):
            n = (0 if "warmup" in label else int(label.split("-")[1]))
        pair = []
        for side in ("start", "end"):
            p = take("ENDPOINT")
            require(len(p) == 10 and p[:2] == [label, side],
                    "missing/reordered worker endpoint")
            snapshot = numbers(p[2:], 8)
            require(snapshot[:3] == [1, 8, 0],
                    "worker ABI/word-size/overflow mismatch")
            require(snapshot[3] == sum(snapshot[4:]),
                    "worker endpoint category sum mismatch")
            endpoints.append((label, side, snapshot))
            pair.append(snapshot[3:])
        start, end = pair
        require(all(a <= b <= c for a, b, c in zip(previous, start, end)),
                "worker counter not process-monotonic (including retirement)")
        previous = end
        p = take("RAW")
        require(len(p) == 12 and p[0] == label,
                "missing/reordered worker raw evidence")
        values = numbers(p[1:], 11)
        if label == "retirement":
            state = [512, 4, 0, 4, 0, 0]
        elif label in LABELS[LABELS.index("retirement")+1:]:
            state = [512, 0, 0, 0, 0, 0]
        else:
            state = [n, 4, 4, 4, 4, 0]
        require(values[:6] == state,
                "worker count/parking/activity/exception state changed")
        delta = [b-a for a, b in zip(start, end)]
        require(values[6:] == delta and delta[0] == sum(delta[1:]),
                "worker raw delta/endpoint mismatch")
        raw[label] = dict(zip(RAW_FIELDS, values))
        if label in WORK_LABELS:
            result_records(label, n)
        if label == "retirement":
            for worker in range(4):
                values = numbers(take("RETIRED"), 2)
                require(values == [worker, 0],
                        "worker did not actually retire/isActive still true")
                retired.append(values)
    result_records("after-retired-gc", 512)
    require(take("UNCLAIMED") == [UNCLAIMED], "changed worker limitations")
    require(take("COMPLETE") == [str(len(LABELS))],
            "wrong worker completion count")
    require(cursor == len(records), "worker data after completion")

    deltas = {label: [raw[label][f] for f in RAW_FIELDS[6:]]
              for label in LABELS}
    idle = deltas["noop-before"]
    require(all(deltas[label] == idle for label in
                ("noop-parked", "noop-retired-1", "noop-retired-2")),
            "worker no-op costs do not repeat")
    gc = deltas["gc-empty-1"]
    require(all(deltas[label] == gc for label in (
        "gc-empty-2", "gc-live-1", "gc-live-2", "gc-retired-1",
        "gc-retired-2")), "GC recounts retained worker data/unknown activity")
    zero = deltas["workers-0-1"]
    for repeat in (1, 2):
        for count in (0, 256, 512):
            delta = deltas[f"workers-{count}-{repeat}"]
            words = 4 * 5 * count
            require([a-b for a, b in zip(delta, zero)] ==
                    [words, words, 0, 0, 0],
                    "worker exact native ref/cons slope or repeat mismatch")
            require(delta[0] >= words,
                    "worker count below retained physical storage")
    return dict(brackets=len(LABELS), endpoints=endpoints, raw=raw,
                deltas=deltas, results=results, retired=retired,
                runtime=runtime[0], maps=maps, no_op_words=idle,
                scope=SCOPE, unclaimed=UNCLAIMED)
