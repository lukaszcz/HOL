"""Private successful-bytecode fast/slow diagnostic protocol.

This is NOT TASK29 numerical acceptance or runtime/source/image verification.
It covers a single native controller without workers, not refill, GC retry,
failed allocations, or lineage closure. Synthetic tests are not run evidence.
Branch scheduling may vary even when original allocation vectors repeat.
"""
import re

PREFIX = "@@TASK29_IBRANCH_"
SCOPE = ("successful-bytecode-fast-slow-controls; "
         "not refill/failure/lineage closure")
CONFIG = [8, 2, 65536, 131072, 5, 1]
UNCLAIMED = ("refill; GC retry; failed allocations; native compiler/image "
             "lineage; TASK29B matrix")
SIZES = (65536, 131072)
KINDS = ("refs", "words")
LABELS = ("noop-before-1", "noop-before-2", "gc-empty-1", "gc-empty-2", *(
    f"{kind}-{n}-{repeat}" for kind in KINDS for repeat in (1, 2)
    for n in SIZES), "gc-live-1", "gc-live-2", "noop-final-1", "noop-final-2")
WORK = {f"{kind}-{n}-{repeat}": (kind, n) for kind in KINDS
        for repeat in (1, 2) for n in SIZES}
RAW_FIELDS = ("total", "native", "rts", "interpreter", "code")
SPLIT_FIELDS = ("fast_count", "fast_words", "slow_count", "slow_words")
UINT64_MAX = 2**64 - 1


def require(yes, why):
    if not yes:
        raise ValueError(why)


def numbers(fields, count):
    require(len(fields) == count and all(
        re.fullmatch(r"0|[1-9][0-9]*", n) for n in fields),
        "malformed interpreter branch numeric record")
    require(all(len(n) <= 20 for n in fields), "uint64 out of range")
    values = list(map(int, fields))
    require(all(n <= UINT64_MAX for n in values), "uint64 out of range")
    return values


def observations(text):
    """Validate ordered V1 records; ignore only unrelated output lines."""
    require(isinstance(text, str), "interpreter branch output must be text")
    records = []
    for line in text.splitlines():
        if line.startswith("@@TASK29_IBRANCH"):
            require(line.startswith(PREFIX),
                    "malformed interpreter branch prefix")
            records.append(line.split("\t"))
    cursor = 0

    def take(kind):
        nonlocal cursor
        require(cursor < len(records), "missing interpreter branch " + kind)
        p = records[cursor]
        require(p[0] == PREFIX + kind + "_V1",
                "missing/reordered/unknown interpreter branch record: " + kind)
        cursor += 1
        return p[1:]

    def result_record(label, kind, n):
        p = take("RESULT")
        require(len(p) == 4 and p[:2] == [label, kind],
                "missing/reordered interpreter branch retained result")
        values = numbers(p[2:], 2)
        checksum = n*(n+1)//2 if kind == "refs" else 37*n
        require(values == [n, checksum], "changed retained result")
        results.append((label, kind, *values))

    require(take("SCOPE") == [SCOPE], "changed interpreter branch scope")
    require(take("ABI") == ["15"], "interpreter branch C ABI controls failed")
    require(numbers(take("CONFIG"), 6) == CONFIG,
            "changed interpreter branch configuration")
    previous, previous_branch = [0]*5, [0]*4
    endpoints, branches, deltas, splits, results = [], [], {}, {}, []
    for label in LABELS:
        pair, branch_pair = [], []
        for side in ("start", "end"):
            p = take("ENDPOINT")
            require(len(p) == 10 and p[:2] == [label, side],
                    "missing/reordered interpreter branch endpoint")
            snapshot = numbers(p[2:], 8)
            require(snapshot[:3] == [1, 8, 0],
                    "original ABI/word-size/overflow mismatch")
            require(snapshot[3] == sum(snapshot[4:]),
                    "original endpoint category sum mismatch")
            endpoints.append((label, side, snapshot))
            pair.append(snapshot[3:])
        for side, original in zip(("start", "end"), pair):
            p = take("BRANCH")
            require(len(p) == 10 and p[:2] == [label, side],
                    "missing/reordered interpreter branch snapshot")
            snapshot = numbers(p[2:], 8)
            require(snapshot[:3] == [1, 8, 0] and snapshot[7] == 0,
                    "diagnostic ABI/word-size/overflow/reserved mismatch")
            require(original[3] == snapshot[4] + snapshot[6],
                    "original/diagnostic interpreter words mismatch")
            branches.append((label, side, snapshot))
            branch_pair.append(snapshot[3:7])
        start, end = pair
        branch_start, branch_end = branch_pair
        require(all(a <= b <= c for a, b, c in zip(previous, start, end)),
                "original counter not process-monotonic")
        require(all(a <= b <= c for a, b, c in zip(
            previous_branch, branch_start, branch_end)),
            "diagnostic counter not process-monotonic")
        previous, previous_branch = end, branch_end
        p = take("RAW")
        require(len(p) == 6 and p[0] == label,
                "missing/reordered interpreter branch raw evidence")
        delta = numbers(p[1:], 5)
        require(delta == [b-a for a, b in zip(start, end)] and
                delta[0] == sum(delta[1:]),
                "raw delta/endpoint/category sum mismatch")
        deltas[label] = delta
        p = take("SPLIT")
        require(len(p) == 5 and p[0] == label,
                "missing/reordered interpreter branch split evidence")
        split = numbers(p[1:], 4)
        require(split == [b-a for a, b in zip(branch_start, branch_end)] and
                split[1] + split[3] == delta[3],
                "split delta/endpoint/interpreter sum mismatch")
        for count, words in (split[:2], split[2:]):
            require((count > 0) == (words > 0) and words >= count,
                    "branch count/words inconsistent")
        splits[label] = split
        if label in WORK:
            kind, n = WORK[label]
            physical = 5*n if kind == "refs" else 1+n
            require(delta[3] >= physical,
                    "interpreter below retained physical minimum")
            if kind == "refs":
                require(split[0] > 0, "missing fast refs branch coverage")
            result_record(label, kind, n)
        else:
            require(delta[3] == 0,
                    "no-op/GC interpreter allocation or recount")
        if label == "gc-live-2":
            for kind in KINDS:
                result_record("after-live-gc", kind, SIZES[-1])
    require(take("UNCLAIMED") == [UNCLAIMED],
            "changed interpreter branch limitations")
    require(take("COMPLETE") == [str(len(LABELS))],
            "wrong interpreter branch completion count")
    require(cursor == len(records), "interpreter branch data after completion")

    idle = deltas["noop-before-1"]
    require(all(deltas[label] == idle for label in (
        "noop-before-2", "noop-final-1", "noop-final-2")),
        "original no-op costs do not repeat")
    gc = deltas["gc-empty-1"]
    require(all(deltas[label] == gc for label in (
        "gc-empty-2", "gc-live-1", "gc-live-2")),
        "GC recounts retained data/unknown activity")
    for kind in KINDS:
        for n in SIZES:
            require(deltas[f"{kind}-{n}-1"] == deltas[f"{kind}-{n}-2"],
                    "original work allocation vector does not repeat")
        small, large = (deltas[f"{kind}-{n}-1"] for n in SIZES)
        words = (5 if kind == "refs" else 1)*(SIZES[1] - SIZES[0])
        require([b-a for a, b in zip(small, large)] ==
                [words, 0, 0, words, 0],
                "exact interpreter doubling slope/category mismatch")
    # Request size alone does not identify the branch: available segment
    # space can satisfy even a large array directly. Require EXECUTED fast
    # and slow successes in each complete kind-series, not an assumed branch
    # per request. No individual observation is dropped or reclassified.
    for kind in KINDS:
        require(all(sum(splits[label][index] for label, (k, _) in
                        WORK.items() if k == kind) > 0 for index in (0, 2)),
                kind + " series missing fast/slow branch coverage")
    return dict(brackets=len(LABELS), endpoints=endpoints, branches=branches,
                deltas=deltas, splits=splits,
                raw={label: dict(zip(RAW_FIELDS, delta))
                     for label, delta in deltas.items()},
                split={label: dict(zip(SPLIT_FIELDS, delta))
                       for label, delta in splits.items()},
                results=results, no_op_words=idle,
                scope=SCOPE, unclaimed=UNCLAIMED)
