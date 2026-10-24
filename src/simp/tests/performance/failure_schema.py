"""Fail-closed protocol for actual failed NATIVE reservation controls.

observations takes the COMPLETE, ordered process output with stderr merged
into stdout (loading.execute does this). It requires the RTS's own diagnostic
between each failed request and its frozen endpoints. Do not strip stderr or
replace it with a fixture-generated status. validate_receipt additionally
checks the dedicated capped-process command, exit, timeout and output seal.
--maxheap is soft and permits oversized objects: LIMIT_V1 must attest a
verified RLIMIT_AS soft bound of current virtual bytes plus exactly 64 MiB.
The driver must use a finite process-group timeout and seal sources/products,
shim, mapped runtime and launcher independently. No timing tolerance, baseline
subtraction, or RTS/interpreter/code failure-completeness claim is made here.
Synthetic unit tests are protocol tests, NEVER execution evidence.
"""
import hashlib
import math
import re

PREFIX = "@@TASK29_FAILURE_"
SCOPE = "failed-native-reservations-only; not full runtime validation"
UNCLAIMED = ("RTS allocation failures; interpreter allocation failures; "
             "code allocation failures; compact32; overflow injection; "
             "foreign-thread callbacks; image lineage; "
             "full runtime completeness; TASK29B matrix")
CONFIG = [8, 32, 96, 2, 16777216, 25165824, 1024, 90, 37]
FLAGS = ("-H", "32", "--maxheap=96", "--gcthreads=1")
EXHAUSTION = "Run out of store - interrupting threads"
SIZES = (16777216, 25165824)
RECOVERY_SIZES = (0, 256, 512)
RAW_FIELDS = ("total", "native", "rts", "interpreter", "code")
UINT64_MAX = 2**64 - 1
LIMIT_HEADROOM = 67108864

# Ordered recipe: label, kind, dynamic array length (zero for controls).
RECIPE = (
    *((f"noop-{phase}-{r}", "noop", 0)
      for phase in ("warmup", "before") for r in (1, 2)),
    *((f"manual-{phase}-{r}", "manual", 0)
      for phase in ("warmup", "before") for r in (1, 2)),
    *((f"array-before-{n}", "success", n) for n in RECOVERY_SIZES),
    *(request for r in (1, 2) for n in SIZES for request in (
        (f"manual-{n}-{r}", "manual", 0),
        (f"fail-{n}-{r}", "failure", n),
        *((f"recover-{n}-{r}-{m}", "success", m)
          for m in RECOVERY_SIZES))),
    *((f"manual-final-{r}", "manual", 0) for r in (1, 2)),
    *((f"noop-final-{r}", "noop", 0) for r in (1, 2)))
LABELS = tuple(label for label, _, _ in RECIPE)


def require(yes, why):
    if not yes:
        raise ValueError(why)


def numbers(fields, count):
    require(len(fields) == count and all(
        re.fullmatch(r"0|[1-9][0-9]*", n) for n in fields),
        "malformed failure numeric record")
    require(all(len(n) <= 20 for n in fields), "uint64 out of range")
    result = list(map(int, fields))
    require(all(n <= UINT64_MAX for n in result), "uint64 out of range")
    return result


def observations(text):
    require(isinstance(text, str), "failure output must be merged text")
    records = []
    for line in text.splitlines():
        # These are genuine unprefixed RTS stderr lines, NOT ML status tags.
        if "Run out of store" in line or "Failed to recover" in line:
            require(line == EXHAUSTION,
                    "unexpected/malformed runtime exhaustion diagnostic")
            records.append([EXHAUSTION])
        elif line.startswith("@@TASK29"):
            # Do not silently discard another protocol, version or typo.
            records.append(line.split("\t"))
    cursor = 0

    def take(kind):
        nonlocal cursor
        require(cursor < len(records), "missing failure " + kind)
        p = records[cursor]
        require(p[0] == PREFIX + kind + "_V1",
                "missing/reordered/unknown failure record: " + kind)
        cursor += 1
        return p[1:]

    require(take("SCOPE") == [SCOPE], "changed failure scope")
    runtime = take("RUNTIME")
    require(len(runtime) == 1 and runtime[0].startswith("/") and
            not any(c.isspace() for c in runtime[0]),
            "malformed failure runtime identity")
    maps = []
    while cursor < len(records) and records[cursor][0] == PREFIX + "MAP_V1":
        p = take("MAP")
        require(len(p) == 1 and re.fullmatch(
            r"[0-9a-f]+-[0-9a-f]+ [r-][w-][x-][ps] [0-9a-f]+ "
            r"[0-9a-f]+:[0-9a-f]+ [0-9]+(?: +[^\t]*)?", p[0]),
            "malformed failure process map")
        require(p[0] not in maps, "duplicate failure process map")
        maps.append(p[0])
    require(maps, "missing failure process maps")
    require(take("ABI") == ["15"], "failure C ABI controls failed")
    require(numbers(take("CONFIG"), 9) == CONFIG,
            "changed failure configuration")
    limit_values = numbers(take("LIMIT"), 5)
    success, vsize_before, applied_soft, hard, headroom = limit_values
    require(success == 1 and vsize_before > 0 and
            headroom == LIMIT_HEADROOM and
            vsize_before <= UINT64_MAX - headroom and
            applied_soft == vsize_before + headroom and hard >= applied_soft,
            "OS address-space limit failed/unverified or wrong bound")
    limit = dict(zip(("success", "vsize_before", "applied_soft", "hard",
                      "headroom"), limit_values))
    previous = [0] * 5
    endpoints, deltas, results, failures = [], {}, [], []
    for label, kind, n in RECIPE:
        p = take("REQUEST")
        require(len(p) == 3 and p[:2] == [label, kind] and
                numbers(p[2:], 1) == [n],
                "changed/reordered failure request")
        if kind == "failure":
            require(cursor < len(records) and
                    records[cursor] == [EXHAUSTION],
                    "missing actual RTS exhaustion output in process receipt")
            cursor += 1
            failures.append(label)
        pair = []
        for side in ("start", "end"):
            p = take("ENDPOINT")
            require(len(p) == 10 and p[:2] == [label, side],
                    "missing/reordered failure endpoint")
            snapshot = numbers(p[2:], 8)
            require(snapshot[:3] == [1, 8, 0],
                    "failure ABI/word-size/overflow mismatch")
            require(snapshot[3] == sum(snapshot[4:]),
                    "failure endpoint category sum mismatch")
            endpoints.append((label, side, snapshot))
            pair.append(snapshot[3:])
        start, end = pair
        require(all(a <= b <= c for a, b, c in zip(previous, start, end)),
                "failure counter not process-monotonic")
        previous = end
        p = take("RAW")
        require(len(p) == 6 and p[0] == label,
                "missing/reordered failure raw evidence")
        delta = numbers(p[1:], 5)
        require(delta == [b-a for a, b in zip(start, end)] and
                delta[0] == sum(delta[1:]),
                "failure raw delta/endpoint mismatch")
        deltas[label] = delta
        p = take("RESULT")
        require(len(p) == 9 and p[0] == label,
                "missing/reordered failure result")
        outcome = ([1, 0, 1, 1] if kind in ("manual", "failure")
                   else [1, 1, 0, 1])
        # Every record establishes entry, exact outcome, attribute restoration,
        # intact rooted sentinel, and the entire escaped result's checksum.
        result = [n, 37*n] if kind == "success" else [1024, 92160]
        values = numbers(p[1:], 8)
        require(values == outcome + [1024, 92160] + result,
                "wrong failure outcome/entry/restoration/sentinel/result")
        results.append((label, *values))
    require(take("UNCLAIMED") == [UNCLAIMED], "changed failure limitations")
    require(take("COMPLETE") == [str(len(LABELS))],
            "wrong failure completion count")
    require(cursor == len(records), "failure data after completion")

    idle = deltas["noop-before-1"]
    manual = deltas["manual-before-1"]
    for label, kind, n in RECIPE:
        if kind == "noop" and "warmup" not in label:
            require(deltas[label] == idle, "raw native no-op costs differ")
        elif kind in ("manual", "failure") and "warmup" not in label:
            require(deltas[label] == manual,
                    "failed reservation/prebuilt interrupt raw costs differ")
        if kind == "failure":
            require(deltas[label][0] < n,
                    "requested failed reservation charged/unknown activity")
        if kind == "success":
            require([a-b for a, b in zip(deltas[label],
                                        deltas["array-before-0"])] ==
                    [n, n, 0, 0, 0],
                    "exact successful native payload/recovery slope mismatch")
    require(all(a >= b for a, b in zip(manual, idle)),
            "manual interrupt wrapper below native no-op baseline")
    return dict(brackets=len(LABELS), endpoints=endpoints, deltas=deltas,
                raw={label: dict(zip(RAW_FIELDS, delta))
                     for label, delta in deltas.items()},
                results=results, failures=failures,
                exhaustion_messages=len(failures),
                runtime=runtime[0], maps=maps, limit=limit,
                no_op_words=idle, manual_interrupt_words=manual,
                wrapper_difference=[a-b for a, b in zip(manual, idle)],
                scope=SCOPE, unclaimed=UNCLAIMED)


def validate_receipt(receipt, *, timeout):
    """Validate a loading.execute receipt from the SEPARATE capped process.

    The caller must actually pass timeout to its subprocess runner (which
    must kill the process group on expiry); this function cannot enforce a
    timeout retrospectively. A complete-looking transcript from a timed-out
    or unsuccessful process is never accepted. Source/map identity is the
    driver's separate provenance check, as with the other control schemas.
    """
    require(type(timeout) in (int, float) and math.isfinite(timeout) and
            timeout > 0, "finite positive failure-process timeout required")
    require(isinstance(receipt, dict), "missing failure process receipt")
    command = receipt.get("command")
    require(isinstance(command, list) and len(command) == 1 + len(FLAGS) and
            isinstance(command[0], str) and command[0].startswith("/") and
            command[1:] == list(FLAGS),
            "failure process needs exactly -H 32 --maxheap=96 --gcthreads=1")
    require(type(receipt.get("exit")) is int and receipt["exit"] == 0 and
            receipt.get("timed_out") is False,
            "failed/timed-out failure process")
    text = receipt.get("stdout")
    require(isinstance(text, str), "missing merged failure process output")
    raw = text.encode()
    require(type(receipt.get("stdout_bytes")) is int and
            receipt["stdout_bytes"] == len(raw) and
            receipt.get("stdout_sha256") == hashlib.sha256(raw).hexdigest(),
            "failure process output seal mismatch")
    return observations(text)
