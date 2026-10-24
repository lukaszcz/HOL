"""Fail-closed raw protocol for the hybrid bytecode allocator controls.

Not runtime/source/image identity verification or TASK29B acceptance. The
execution driver must separately seal all sources, fixture products, shim and
mapped DSO. Synthetic tests are protocol tests, never execution evidence.
No native-FFI baseline, tolerance, or native-only positivity is admitted.
"""
import re

PREFIX = "@@TASK29_INTERPRETER_"
SCOPE = "hybrid-bytecode-controls-only; not full runtime validation"
BOOTSTRAP = ["RootInterpreted.ML", "Make.makeGEnv",
             "Initialise.initGlobalEnv:false", "mlsource/BuildBasis.sml"]
CONFIG = [8, 2, 0, 1, 16, 32, 5, 1]
UNCLAIMED = ("compact32; pure-interpreter runtime; threads; "
             "failed allocations; overflow injection; image lineage; "
             "full runtime completeness; "
             "TASK29B matrix")
SIZES = (0, 1, 16, 32)
KINDS = ("refs", "words")
LABELS = ("noop-warmup-1", "noop-warmup-2", "noop-before-1", "noop-before-2",
          "gc-warmup", "gc-empty-1", "gc-empty-2", *(
              label for kind in KINDS for label in (
                  f"{kind}-warmup-1", f"{kind}-warmup-2", *(
                      f"{kind}-{n}-{repeat}" for repeat in (1, 2)
                      for n in SIZES))),
          "gc-live-1", "gc-live-2", "noop-final-1", "noop-final-2")
WORK = {label: (kind, 0 if "warmup" in label else int(label.split("-")[1]))
        for label in LABELS for kind in KINDS if label.startswith(kind + "-")}
RAW_FIELDS = ("total", "native", "rts", "interpreter", "code")
UINT64_MAX = 2**64 - 1


def require(yes, why):
    if not yes:
        raise ValueError(why)


def numbers(fields, count):
    require(len(fields) == count and all(
        re.fullmatch(r"0|[1-9][0-9]*", n) for n in fields),
        "malformed interpreter numeric record")
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
        require(cursor < len(records), "missing interpreter " + kind)
        p = records[cursor]
        require(p[0] == PREFIX + kind + "_V1",
                "missing/reordered/unknown interpreter record: " + kind)
        cursor += 1
        return p[1:]

    require(take("SCOPE") == [SCOPE], "changed interpreter scope")
    require(take("BOOTSTRAP") == BOOTSTRAP, "changed interpreter recipe")
    runtime = take("RUNTIME")
    require(len(runtime) == 1 and runtime[0].startswith("/") and
            not any(c.isspace() for c in runtime[0]),
            "malformed interpreter runtime identity")
    maps = []
    while cursor < len(records) and records[cursor][0] == PREFIX + "MAP_V1":
        p = take("MAP")
        require(len(p) == 1 and re.fullmatch(
            r"[0-9a-f]+-[0-9a-f]+ [r-][w-][x-][ps] [0-9a-f]+ "
            r"[0-9a-f]+:[0-9a-f]+ [0-9]+(?: +[^\t]*)?", p[0]),
            "malformed interpreter process map")
        require(p[0] not in maps, "duplicate interpreter process map")
        maps.append(p[0])
    require(maps, "missing interpreter process maps")
    require(take("ABI") == ["15"], "interpreter C ABI controls failed")
    require(numbers(take("CONFIG"), 8) == CONFIG,
            "changed interpreter configuration")
    previous = [0] * 5
    endpoints, deltas, results = [], {}, []

    def result_record(label, kind, n):
        p = take("RESULT")
        require(len(p) == 4 and p[:2] == [label, kind],
                "missing/reordered interpreter retained-result evidence")
        checksum = n*(n+1)//2 if kind == "refs" else 37*n
        values = numbers(p[2:], 2)
        require(values == [n, checksum], "changed interpreter retained result")
        results.append((label, kind, *values))

    for label in LABELS:
        pair = []
        for side in ("start", "end"):
            p = take("ENDPOINT")
            require(len(p) == 10 and p[:2] == [label, side],
                    "missing/reordered interpreter endpoint")
            snapshot = numbers(p[2:], 8)
            require(snapshot[:3] == [1, 8, 0],
                    "interpreter ABI/word-size/overflow mismatch")
            require(snapshot[3] == sum(snapshot[4:]),
                    "interpreter endpoint category sum mismatch")
            endpoints.append((label, side, snapshot))
            pair.append(snapshot[3:])
        start, end = pair
        require(all(a <= b <= c for a, b, c in zip(previous, start, end)),
                "interpreter counter not process-monotonic")
        previous = end
        p = take("RAW")
        require(len(p) == 6 and p[0] == label,
                "missing/reordered interpreter raw evidence")
        delta = numbers(p[1:], 5)
        require(delta == [b-a for a, b in zip(start, end)] and
                delta[0] == sum(delta[1:]),
                "interpreter raw delta/endpoint mismatch")
        deltas[label] = delta
        if label in WORK:
            kind, n = WORK[label]
            physical = 5*n if kind == "refs" else 1+n
            require(delta[3] >= physical,
                    "interpreter count below retained physical storage")
            result_record(label, kind, n)
        if label == "gc-live-2":
            for kind in KINDS:
                result_record("after-live-gc", kind, 32)
    require(take("UNCLAIMED") == [UNCLAIMED],
            "changed interpreter limitations")
    require(take("COMPLETE") == [str(len(LABELS))],
            "wrong interpreter completion count")
    require(cursor == len(records), "interpreter data after completion")

    idle = deltas["noop-before-1"]
    require(all(deltas[label] == idle for label in (
        "noop-before-2", "noop-final-1", "noop-final-2")),
        "interpreted no-op costs do not repeat")
    gc = deltas["gc-empty-1"]
    require(all(deltas[label] == gc for label in (
        "gc-empty-2", "gc-live-1", "gc-live-2")),
        "GC recounts retained interpreter data/unknown activity")
    for kind in KINDS:
        zero = deltas[f"{kind}-0-1"]
        for repeat in (1, 2):
            for n in SIZES:
                d = deltas[f"{kind}-{n}-{repeat}"]
                words = (5 if kind == "refs" else 1)*n
                require([a-b for a, b in zip(d, zero)] ==
                        [words, 0, 0, words, 0],
                        "exact interpreter slope/category/repeat mismatch")
        small, large = (deltas[f"{kind}-{n}-1"] for n in (16, 32))
        words = (5 if kind == "refs" else 1)*16
        require([a-b for a, b in zip(large, small)] ==
                [words, 0, 0, words, 0], "interpreter doubling slope mismatch")
    return dict(brackets=len(LABELS), endpoints=endpoints, deltas=deltas,
                raw={label: dict(zip(RAW_FIELDS, delta))
                     for label, delta in deltas.items()},
                results=results, runtime=runtime[0], maps=maps,
                bootstrap=BOOTSTRAP.copy(), no_op_words=idle,
                scope=SCOPE, unclaimed=UNCLAIMED)
