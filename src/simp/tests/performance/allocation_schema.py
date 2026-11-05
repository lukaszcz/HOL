"""Strict protocol for one TASK29B allocation process (MatrixAllocation.sml).

Pure functions over parsed protocol events and stdout text; no filesystem
access, so archived receipts replay offline. Counts are exact Python
integers; floats are rejected wherever an exact value is required.
"""
from fractions import Fraction
import hashlib
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
# Structural evidence: a grid header that says `structure: "v1"` has, after
# the foreign-thread record of every process, the three records of the
# untimed work phase of MatrixAllocation.sml. A header without the key has
# none (every archive made before it replays unchanged).
STRUCTURE = "v1"
WORK_EVENTS = ("work.first", "work.second", "result.digest")
TRACE_ACTIONS = (
    "IGNORE", "LZ_TEXT", "MORE_CONTEXT", "OPENING", "PRODUCE", "REDUCE",
    "REWRITING", "SIDECOND_ATTEMPT", "SIDECOND_NOT_SOLVED",
    "SIDECOND_SOLVED", "TEXT")
TRACE_LEVELS = 16
KERNEL_RULES = (
    "ABS", "ALPHA", "AP_TERM", "AP_THM", "ASSUME", "BETA_CONV", "CCONTR",
    "CHOOSE", "COMPUTE", "CONJ", "CONJUNCT1", "CONJUNCT2", "DISCH", "DISJ1",
    "DISJ2", "DISJ_CASES", "EQ_IMP_RULE", "EQ_MP", "EXISTS", "GEN",
    "GEN_ABS", "INST", "INST_TYPE", "MK_COMB", "MP", "NOT_ELIM",
    "NOT_INTRO", "REFL", "SPEC", "SUBST", "SYM", "TRANS", "axiom",
    "definition", "from_disk", "oracle", "total")
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


def parse(events, *, case, size, steady, repeats, structure=None):
    """Return (bracket records, observation events) of one valid process.
    `structure` is the header's structure key: None (no work records) or
    STRUCTURE (three, between the foreign-thread record and the check)."""
    require(repeats >= 3, "need at least three steady repeats")
    require(structure in (None, STRUCTURE), "unknown structure version")
    extra = len(WORK_EVENTS) if structure else 0
    es = [e for e in events if e[0] in ("observation", "check", "exception")]
    require(all(e[0] != "exception" for e in es), "fixture exception")
    require(len(es) == len(names(repeats)) + 3 + extra,
            "wrong observation count")
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
    foreign = -2 - extra
    require(es[foreign] == ["observation", "alloc.foreign", FOREIGN],
            "foreign-thread counter is not zero at process end")
    require([e[:2] for e in es[foreign + 1:-1]] ==
            [["observation", k] for k in WORK_EVENTS[:extra]] and
            all(len(e) == 3 for e in es[foreign + 1:-1]),
            "missing or misplaced work records")
    brackets, steady_index, previous = [], 0, None
    for name, event in zip(names(repeats), es[1:foreign]):
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
    work(es, structure)  # the records are well formed, or the process is not
    return brackets, es


def work_counts(text):
    """The counts of one `work.first`/`work.second` record as a flat dict
    (`trace.L.ACTION`, `kernel.RULE`, `maker`, `collector`), nonzero counts
    only, in the canonical order of the fixture, each key once."""
    parts = text.split(";")
    require(len(parts) == 4 and
            [p.split("=", 1)[0] for p in parts] ==
            ["trace", "kernel", "maker", "collector"],
            "malformed work record")
    out = {}
    for part, order in ((parts[0], None), (parts[1], KERNEL_RULES)):
        body = part.split("=", 1)[1]
        last = -1
        for item in (body.split(",") if body else []):
            key, _, number = item.rpartition("=")
            if order is None:
                level, _, action = key.partition(".")
                require(re.fullmatch(r"0|[1-9][0-9]*", level) and
                        int(level) < TRACE_LEVELS and
                        action in TRACE_ACTIONS, "bad trace key: " + key)
                rank = int(level) * len(TRACE_ACTIONS) + \
                    TRACE_ACTIONS.index(action)
                name = "trace." + key
            else:
                require(key in order, "bad kernel key: " + key)
                rank, name = order.index(key), "kernel." + key
            require(rank > last, "work keys out of order or repeated")
            require(re.fullmatch(r"[1-9][0-9]*", number),
                    "malformed work count: " + item)
            last = rank
            out[name] = int(number)
    for part in parts[2:]:
        key, _, number = part.partition("=")
        require(re.fullmatch(r"0|[1-9][0-9]*", number),
                "malformed work count: " + part)
        if int(number):
            out[key] = int(number)
    return out


def work(es, structure):
    """The structural record of one process (None without structure): the
    counts of both runs and the SHA-256 of the result fingerprint."""
    if structure is None:
        return None
    first, second, digest = es[-4:-1]
    require([first[1], second[1], digest[1]] == list(WORK_EVENTS),
            "missing or misplaced work records")
    return dict(first=work_counts(first[2]), second=work_counts(second[2]),
                digest=hashlib.sha256(digest[2].encode()).hexdigest())


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


def observation(brackets, steady, structural=None):
    """Raw word deltas by phase (operation_steady: one per repeat), and
    under a structure header the work record (see work())."""
    result = {}
    for b in brackets:
        result.setdefault(b["name"], []).append(deltas(b))
    require(all(len(v) == 1 for k, v in result.items()
                if k != "operation_steady"), "duplicated bracket")
    out = dict(steady=steady, phases=result)
    if structural is not None:
        out["work"] = structural
    return out


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
