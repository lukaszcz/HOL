"""Strict protocol for one TASK29B allocation process (MatrixAllocation.sml).

Pure functions over parsed protocol events and stdout text; no filesystem
access, so archived receipts replay offline. Counts are exact Python
integers; floats are rejected wherever an exact value is required.
"""
from fractions import Fraction
import re

U64 = 2 ** 64
PHASES = ("setup", "operation_first", "operation_steady", "apply")
PUBLISHED = ("startup", "empty", "canary")
METRICS = ("total", "native", "rts", "interpreter", "code", "heap")
# Snapshot layout: ABI, word bytes, overflow mask, total, then categories.
FIELDS = ("abi", "word_bytes", "overflow", "total", "native", "rts",
          "interpreter", "code")
COUNTS = FIELDS[3:]
WORD_BYTES = 8
# Known-size canary: Array.array (CANARY_ARRAY, 0) stored in a ref inside the
# bracket. Its words beyond the no-op `empty` bracket are exact per category
# (a dead or under-reporting counter cannot produce them): the array's
# CANARY_ARRAY words and header plus the two-word SOME, all native storage.
CANARY_ARRAY = 1000
CANARY = dict(native=1003, rts=0, interpreter=0, code=0)
ABI = 15
FOREIGN = "0,0"  # foreign-thread counter, reserved word: both zero


class InvalidAllocation(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise InvalidAllocation(message)


def exact(value):
    """Counts and rates are integers or Fractions; never floats or text."""
    require(isinstance(value, (int, Fraction)) and
            not isinstance(value, bool), "inexact value: " + repr(value))
    return Fraction(value)


def names(repeats):
    return (list(PUBLISHED) + ["setup", "operation_first"] +
            ["operation_steady"] * repeats + ["apply"])


def numbers(text, count):
    fields = text.split(",")
    require(len(fields) == count and
            all(re.fullmatch(r"0|[1-9][0-9]*", f) for f in fields),
            "malformed endpoint: " + text)
    values = [int(f) for f in fields]
    require(all(v < U64 for v in values), "endpoint exceeds uint64")
    return values


def endpoint(text):
    values = numbers(text, len(FIELDS))
    point = dict(zip(FIELDS, values))
    require(point["abi"] == 1, "wrong snapshot ABI")
    require(point["word_bytes"] == WORD_BYTES,
            "unsupported word size (compact32 is rejected)")
    require(point["overflow"] == 0, "counter overflow mask set")
    require(point["total"] == sum(point[k] for k in COUNTS[1:]),
            "total differs from category sum")
    return point


def ordered(low, high):
    return all(low[k] <= high[k] for k in COUNTS)


def parse(events, *, case, size, steady, repeats):
    """Return (bracket records, observation events) of one valid process."""
    require(repeats >= 3, "need at least three steady repeats")
    es = [e for e in events if e[0] in ("observation", "check", "exception")]
    require(all(e[0] != "exception" for e in es), "fixture exception")
    require(len(es) == len(names(repeats)) + 3, "wrong observation count")
    require(es[0][:2] == ["observation", "alloc.config"] and len(es[0]) == 3,
            "missing configuration record")
    config = es[0][2].split(",")
    require(config == [case, str(size), str(steady), str(repeats),
                       str(ABI), str(CANARY_ARRAY)],
            "wrong case/size/count binding")
    require(es[-1] == ["check", "allocation brackets", "pass"],
            "missing completion check")
    # Path counter 27 (a thread the runtime did not create entered it) and
    # the reserved path word, read after the last bracket: both are zero.
    require(es[-2] == ["observation", "alloc.foreign", FOREIGN],
            "foreign-thread counter is not zero at process end")
    brackets, steady_index, previous = [], 0, None
    for name, event in zip(names(repeats), es[1:-2]):
        require(len(event) == 3 and event[:2] ==
                ["observation", "alloc." + name], "wrong bracket order")
        parts = event[2].split(";")
        require(len(parts) == 3, "malformed bracket record")
        index, start, end = parts
        want = steady_index if name == "operation_steady" else 0
        require(index == str(want), "wrong bracket index")
        steady_index += name == "operation_steady"
        start, end = endpoint(start), endpoint(end)
        require(ordered(start, end), "non-monotonic bracket endpoints")
        if previous is not None:
            require(ordered(previous, start), "non-monotonic across brackets")
        previous = end
        brackets.append(dict(name=name, index=want, start=start, end=end))
    check_canary(brackets)
    return brackets, es


def check_canary(brackets):
    """Startup is nonzero and the canary costs exactly its known words."""
    by = {b["name"]: deltas(b) for b in brackets
          if b["name"] in PUBLISHED}
    require(by["startup"]["total"] > 0, "counter reported no startup words")
    for key in COUNTS[1:]:
        got = by["canary"][key] - by["empty"][key]
        require(got == CANARY[key],
                "canary %s words %d, expected %d (counter dead or "
                "under-reporting)" % (key, got, CANARY[key]))
    require(by["canary"]["total"] - by["empty"]["total"] ==
            sum(CANARY.values()), "canary total differs from categories")


def deltas(bracket):
    """Words per metric. startup is the absolute counter at the first probe
    (counters are zero when the runtime DSO initializes)."""
    s, e = bracket["start"], bracket["end"]
    if bracket["name"] == "startup":
        e, s = s, dict.fromkeys(FIELDS, 0)
    out = {k: e[k] - s[k] for k in COUNTS}
    out["heap"] = out["total"] - out["code"]
    require(all(v >= 0 for v in out.values()), "negative delta")
    return out


def to_bytes(words, word_bytes=WORD_BYTES):
    value = exact(words) * word_bytes
    require(value < U64, "byte count overflow")
    return value


def observation(brackets, steady):
    """Raw word deltas by phase (operation_steady: one per repeat)."""
    result = {}
    for b in brackets:
        result.setdefault(b["name"], []).append(deltas(b))
    require(all(len(v) == 1 for k, v in result.items()
                if k != "operation_steady"), "duplicated bracket")
    return dict(steady=steady, phases=result)


def check_runtime(stdout, library, aliases=()):
    """One runtime symbol/mapping, the sealed library (the symbol may be
    reported under a symlink that resolved to it when the grid started)."""
    rows = [l.split("\t", 1)[1] for l in stdout.splitlines()
            if l.startswith("@@TASK29_ALLOC_RUNTIME_V1\t")]
    require(len(rows) == 1 and rows[0] in (library, *aliases),
            "snapshot symbol bound to wrong runtime")
    maps = [l.split("\t", 1)[1] for l in stdout.splitlines()
            if l.startswith("@@TASK29_ALLOC_MAP_V1\t")]
    paths = set()
    for line in maps:
        fields = line.split(maxsplit=5)
        if len(fields) == 6 and "libpolyml" in fields[5]:
            paths.add(fields[5].strip())
    require(paths == {library}, "missing/multiple runtime mappings")
    return dict(symbol=rows[0], maps=sorted(paths))


def per_run(phase, value, steady):
    return exact(value) / (steady if phase == "operation_steady" else 1)
