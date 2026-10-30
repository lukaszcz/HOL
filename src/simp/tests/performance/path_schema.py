"""Fail-closed protocol for lower-level allocator PATH controls.

Three dedicated, separately executed launcher processes, each validated by
profile:

  native-rts   successful native and RTS reservations that take the refill,
               large-object and success-after-GC branches of
               Processes::FindAllocationSpace (the lower-level boundary
               tests that the bytecode and native fast paths do not share)
  interpreter  the same for the bytecode interpreter, plus a real
               interpreter reservation failure under RLIMIT_AS
  failure      real RTS and native reservation failures (RLIMIT_AS) and real
               code-space allocation failures (a request larger than the
               reserved code region), each followed by exact recovery
               controls; a failed code request is compared with a control
               that raises an exception packet of the same size

observations takes the COMPLETE, ordered process output with stderr merged
into stdout (loading.execute does this). Every measured interval has the
original eight-word counters, the separate 32-word path counters (version 1,
bytes/word 8, overflow mask 0, 28 counters, one reserved zero word) and, for
the interpreter profile, the original branch counters. Failed requests must
leave the exact RTS exhaustion diagnostic (or Fail "Insufficient memory" for
code space) AND a path failure counter; they must not be charged. Retry
successes must be counted exactly once. Neither is inferred from a requested
size. The path counters are diagnostics: they are checked here for exact
structural identities and for the presence of each branch, never for exact
GC schedules (those legitimately differ between rounds).

Counter 27 counts entries of a thread the runtime did not create into
PolyArm64GetThreadData (the only place the native backend creates task data
for such a thread); it must be zero at every endpoint. The native and
bytecode callers pass alwaysInSeg, so their large-object-area cells must be
zero as well.

validate_receipt additionally checks the capped-process command, exit,
timeout and output seal. Synthetic unit tests are protocol tests, NEVER
execution evidence. Compact32 and foreign-created-thread callbacks are out
of scope: reject_compact32 refuses any compact32 configuration and the
THREADS records pin the process's OS thread inventory.
"""
import hashlib
import math
import re

PREFIX = "@@TASK29_PATH_"
EXHAUSTION = "Run out of store - interrupting threads"
UINT64_MAX = 2**64 - 1
RAW_FIELDS = ("total", "native", "rts", "interpreter", "code")
LIMIT_HEADROOM = 67108864
PATH_COUNTERS = 28
PATH_WORDS = 32

# Path counter indexes (see managed_alloc_counter.h): 6*caller + 2*outcome +
# after_gc with caller 0 native, 1 RTS, 2 interpreter and outcome 0 within
# segment, 1 large-object area, 2 refill/new segment.
NATIVE_FAIL, RTS_FAIL, INTERP_FAIL = FAIL_COUNTER = (18, 19, 20)
QUICKGC_TRUE, QUICKGC_FALSE, CODE_FAIL = 21, 22, 23
WORDS = (24, 25, 26)
FOREIGN_THREAD = 27
FAILURE_INDEXES = (18, 19, 20, 22, 23)


def success_counters(caller):
    return range(6 * caller, 6 * caller + 6)


def counter(caller, outcome, after_gc):
    return 6 * caller + 2 * outcome + after_gc


# FindAllocationSpace is called with alwaysInSeg for the native and bytecode
# callers, so those callers can never take its large-object-area branch.
LARGE_UNREACHABLE = tuple(counter(c, 1, g) for c in (0, 2) for g in (0, 1))


UNCLAIMED = dict(
    {"native-rts": ("compact32; foreign-created-thread callbacks; image "
                    "lineage; failure paths; code-space reuse; TASK29B "
                    "matrix"),
     "interpreter": ("compact32; foreign-created-thread callbacks; "
                     "pure-interpreter runtime; code-space failures here; "
                     "image lineage; TASK29B matrix"),
     "failure": ("compact32; foreign-created-thread callbacks; interpreter "
                 "reservation failures here; code-space success after a "
                 "GC; image lineage; TASK29B matrix")})
SCOPE = {
    "native-rts": "lower-level-success-paths-only; not full runtime "
                  "validation",
    "interpreter": "hybrid-bytecode-path-controls-only; not full runtime "
                   "validation",
    "failure": "rts-native-and-code-failure-paths-only; not full runtime "
               "validation"}
FLAGS = {"native-rts": ("--gcthreads=1",),
         "interpreter": ("--gcthreads=1",),
         "failure": ("-H", "32", "--gcthreads=1")}
CONFIG = {"native-rts": [8, 4096, 32768, 1024, 262144, 1, 101, 8, 64,
                         1048576],
          "interpreter": [8, 2, 16777216, 25165824, 1000],
          "failure": [8, 1073741824, 1610612736, 16777216, 335544320, 1,
                      128]}
LIMIT_MARK = "@LIMIT"
OK_SIZE = 1000
FAIL_WORDS = (16777216, 25165824)
FAIL_BITS = (1073741824, 1610612736)
NATIVE_FAIL_WORDS = (16777216,)
# One size: a request beyond the reserved code region fails whatever its
# size, so a second size would exercise the same branch.
CODE_WORDS = (335544320,)
RECOVERY_LIMBS = (1, 128)
NATIVE_LOOPS = tuple((k, s) for k in (4096, 32768) for s in (0, 1024))
RTS_LOOPS = tuple((262144, s) for s in (1, 101))
LARGE_LOOPS = tuple((k, 1048576) for k in (8, 64))
INTERPRETER_LOOPS = ((4096, 0), (4096, 1000), (32768, 1000), (1, 100000),
                     (1, 200000), (64, 2097152))


def _recipe_native_rts():
    rows = [(f"noop-{p}-{r}", "noop", 0, 0)
            for p in ("warmup", "before") for r in (1, 2)]
    for kind, loops in (("native", NATIVE_LOOPS), ("rts", RTS_LOOPS),
                        ("large", LARGE_LOOPS)):
        for r in (1, 2):
            rows += [(f"{kind}-{k}-{s}-{r}", kind, k, s) for k, s in loops]
    rows += [(f"noop-final-{r}", "noop", 0, 0) for r in (1, 2)]
    return tuple(rows)


def _recipe_interpreter():
    rows = [(f"noop-{p}-{r}", "noop", 0, 0)
            for p in ("warmup", "before") for r in (1, 2)]
    rows += [(f"loop-{k}-{s}-{r}", "loop", k, s)
             for r in (1, 2) for k, s in INTERPRETER_LOOPS]
    rows.append((LIMIT_MARK,))
    rows += [(f"noop-limited-{r}", "noop", 0, 0) for r in (1, 2)]
    rows += [(f"attempt-noop-{r}", "attempt-noop", 0, 0) for r in (1, 2)]
    rows += [(f"ok-before-{r}", "ok", 1, OK_SIZE) for r in (1, 2)]
    for r in (1, 2):
        for n in FAIL_WORDS:
            rows += [(f"fail-{n}-{r}", "fail", 1, n),
                     (f"recover-{n}-{r}", "ok", 1, OK_SIZE)]
    rows += [(f"noop-final-{r}", "noop", 0, 0) for r in (1, 2)]
    rows.append(("attempt-noop-final", "attempt-noop", 0, 0))
    return tuple(rows)


def _recipe_failure():
    rows = [(f"noop-{p}-{r}", "noop", 0, 0)
            for p in ("warmup", "before") for r in (1, 2)]
    rows += [(f"manual-{p}-{r}", "manual", 0, 0)
             for p in ("warmup", "before") for r in (1, 2)]
    rows += [("compile-warmup-1", "compile", 0, 0),
             ("compile-before-1", "compile", 0, 0),
             ("compile-before-2", "compile", 0, 0)]
    rows += [(f"code-ctl-before-{r}", "code-ctl", 0, r) for r in (1, 2)]
    rows += [(f"rts-ok-before-{m}", "rts-ok", 64, m)
             for m in RECOVERY_LIMBS]
    rows.append((LIMIT_MARK,))
    rows += [(f"code-ctl-limited-{r}", "code-ctl", 0, r) for r in (1, 2)]
    for r in (1, 2):
        for bits in FAIL_BITS:
            rows.append((f"rts-fail-{bits}-{r}", "rts-fail", 1, bits))
            rows += [(f"rts-ok-{bits}-{r}-{m}", "rts-ok", 64, m)
                     for m in RECOVERY_LIMBS]
        for n in NATIVE_FAIL_WORDS:
            rows += [(f"native-fail-{n}-{r}", "native-fail", 1, n),
                     (f"native-ok-{n}-{r}", "native-ok", 1, OK_SIZE)]
        for n in CODE_WORDS:
            rows += [(f"code-fail-{n}-{r}", "code-fail", n, r),
                     (f"compile-after-{n}-{r}", "compile", 0, 0)]
    rows.append(("compile-final", "compile", 0, 0))
    rows += [(f"noop-final-{r}", "noop", 0, 0) for r in (1, 2)]
    return tuple(rows)


RECIPE = {"native-rts": _recipe_native_rts(),
          "interpreter": _recipe_interpreter(),
          "failure": _recipe_failure()}
EXHAUSTION_KINDS = {"native-rts": (), "interpreter": ("fail",),
                    "failure": ("rts-fail", "native-fail")}


def labels(profile):
    return tuple(r[0] for r in RECIPE[profile] if r[0] != LIMIT_MARK)


def require(yes, why):
    if not yes:
        raise ValueError(why)


def numbers(fields, count):
    require(len(fields) == count and all(
        re.fullmatch(r"0|[1-9][0-9]{0,19}", n) for n in fields),
        "malformed path numeric record")
    result = list(map(int, fields))
    require(all(n <= UINT64_MAX for n in result), "uint64 out of range")
    return result


def reject_compact32(configuration, configure_arguments, word_bytes=8):
    """Refuse a compact32 runtime: out of scope for every path control."""
    require(isinstance(configuration, str) and
            isinstance(configure_arguments, (list, tuple)),
            "malformed compact32 guard input")
    require("--disable-compact32bit" in configure_arguments and
            not any("enable-compact32bit" in a for a in configure_arguments)
            and word_bytes == 8, "compact32 configuration rejected")
    require(not re.search(r"^[ \t]*#[ \t]*define[ \t]+POLYML32IN64\b",
                          configuration, re.M),
            "compact32 runtime configuration rejected")


def observations(text, profile):
    require(profile in RECIPE, "unknown path profile")
    require(isinstance(text, str), "path output must be merged text")
    records = []
    for line in text.splitlines():
        if "Run out of store" in line or "Failed to recover" in line:
            require(line == EXHAUSTION,
                    "unexpected/malformed runtime exhaustion diagnostic")
            records.append([EXHAUSTION])
        elif line.startswith("@@TASK29"):
            records.append(line.split("\t"))
    cursor = 0

    def take(kind):
        nonlocal cursor
        require(cursor < len(records), "missing path " + kind)
        p = records[cursor]
        require(p[0] == PREFIX + kind + "_V1",
                "missing/reordered/unknown path record: " + kind)
        cursor += 1
        return p[1:]

    require(take("SCOPE") == [SCOPE[profile]], "changed path scope")
    require(take("PROFILE") == [profile], "changed path profile")
    runtime = take("RUNTIME")
    require(len(runtime) == 1 and runtime[0].startswith("/") and
            not any(c.isspace() for c in runtime[0]),
            "malformed path runtime identity")
    maps = []
    while cursor < len(records) and records[cursor][0] == PREFIX + "MAP_V1":
        p = take("MAP")
        require(len(p) == 1 and re.fullmatch(
            r"[0-9a-f]+-[0-9a-f]+ [r-][w-][x-][ps] [0-9a-f]+ "
            r"[0-9a-f]+:[0-9a-f]+ [0-9]+(?: +[^\t]*)?", p[0]),
            "malformed path process map")
        require(p[0] not in maps, "duplicate path process map")
        maps.append(p[0])
    require(maps, "missing path process maps")

    def thread_inventory(side):
        p = take("THREADS")
        require(len(p) >= 3 and p[0] == side and
                re.fullmatch(r"[1-9][0-9]*", p[1]) and
                len(p) - 2 == int(p[1]) and
                all(re.fullmatch(r"[A-Za-z0-9_./:-]{1,15}", n)
                    for n in p[2:]) and p[2:] == sorted(p[2:]),
                "malformed OS thread inventory")
        return p[1:]

    threads_start = thread_inventory("start")
    require(take("ABI") == ["15"], "path C ABI controls failed")
    require(numbers(take("CONFIG"), len(CONFIG[profile])) ==
            CONFIG[profile], "changed path configuration")
    limit = None
    previous_raw = [0] * 5
    previous_path = [0] * PATH_COUNTERS
    rows = {}
    order = []
    for entry in RECIPE[profile]:
        if entry[0] == LIMIT_MARK:
            values = numbers(take("LIMIT"), 5)
            success, vsize, soft, hard, headroom = values
            require(success == 1 and vsize > 0 and
                    headroom == LIMIT_HEADROOM and
                    soft == vsize + headroom and hard >= soft,
                    "OS address-space limit failed/unverified or wrong bound")
            limit = dict(zip(("success", "vsize_before", "applied_soft",
                              "hard", "headroom"), values))
            continue
        label, kind, a, b = entry
        p = take("REQUEST")
        require(p[:2] == [label, kind] and numbers(p[2:], 2) == [a, b],
                "changed/reordered path request")
        if kind in EXHAUSTION_KINDS[profile]:
            require(cursor < len(records) and records[cursor] == [EXHAUSTION],
                    "missing actual RTS exhaustion output in process receipt")
            cursor += 1
        endpoints = []
        for side in ("start", "end"):
            p = take("ENDPOINT")
            require(p[:2] == [label, side],
                    "missing/reordered path endpoint")
            s = numbers(p[2:], 8)
            require(s[:3] == [1, 8, 0], "path ABI/word-size/overflow mismatch")
            require(s[3] == sum(s[4:]), "path endpoint category sum mismatch")
            endpoints.append(s)
        path_endpoints = []
        for side in ("start", "end"):
            p = take("PENDPOINT")
            require(p[:2] == [label, side],
                    "missing/reordered path-counter endpoint")
            s = numbers(p[2:], PATH_WORDS)
            require(s[:3] == [1, 8, 0] and s[PATH_WORDS - 1] == 0,
                    "path ABI/overflow/reserved mismatch")
            require(s[3 + FOREIGN_THREAD] == 0,
                    "a thread not created by the runtime entered it")
            path_endpoints.append(s)
        branch_endpoints = []
        if profile == "interpreter":
            for side in ("start", "end"):
                p = take("BENDPOINT")
                require(p[:2] == [label, side],
                        "missing/reordered branch endpoint")
                s = numbers(p[2:], 8)
                require(s[:3] == [1, 8, 0] and s[7] == 0,
                        "branch ABI/overflow/reserved mismatch")
                branch_endpoints.append(s)
        start, end = (e[3:] for e in endpoints)
        pstart, pend = (e[3:3 + PATH_COUNTERS] for e in path_endpoints)
        require(all(x <= y <= z for x, y, z in zip(previous_raw, start, end)),
                "path raw counter not process-monotonic")
        require(all(x <= y <= z for x, y, z in
                    zip(previous_path, pstart, pend)),
                "path counter not process-monotonic")
        previous_raw, previous_path = end, pend
        p = take("RAW")
        require(p[:1] == [label], "missing/reordered path raw")
        raw = numbers(p[1:], 5)
        # Each endpoint's total is the sum of its categories, so the
        # delta's is.
        require(raw == [y - x for x, y in zip(start, end)],
                "path raw delta/endpoint mismatch")
        p = take("PATH")
        require(p[:1] == [label], "missing/reordered path counter delta")
        path = numbers(p[1:], PATH_COUNTERS)
        require(path == [y - x for x, y in zip(pstart, pend)],
                "path delta/endpoint mismatch")
        branch = None
        if profile == "interpreter":
            p = take("BRANCH")
            require(p[:1] == [label], "missing/reordered branch delta")
            branch = numbers(p[1:], 4)
            bs, be = (e[3:7] for e in branch_endpoints)
            require(branch == [y - x for x, y in zip(bs, be)],
                    "branch delta/endpoint mismatch")
        p = take("RESULT")
        n = 4 if profile != "native-rts" else 5
        require(p[:1] == [label], "missing/reordered result")
        result = numbers(p[1:], n - 1)
        # Structural identities for EVERY bracket, success or failure.
        require(path[WORDS[1]] == raw[2],
                "RTS path words differ from raw RTS words")
        require(path[WORDS[0]] <= raw[1],
                "native path words exceed raw native words")
        require(not any(path[i] for i in LARGE_UNREACHABLE),
                "large-object area used by an alwaysInSeg caller")
        if branch is not None:
            require(branch[3] == path[WORDS[2]],
                    "interpreter path words differ from branch slow words")
            require(sum(path[i] for i in success_counters(2)) == branch[2],
                    "interpreter path events differ from branch slow count")
            require(raw[3] == branch[1] + branch[3],
                    "interpreter raw words differ from branch words")
            require(raw[3] >= branch[0] + branch[2],
                    "interpreter raw words below branch event count")
        else:
            require(not any(path[i] for i in success_counters(2)),
                    "unexpected interpreter path success events")
            require(path[INTERP_FAIL] == 0 and path[WORDS[2]] == 0,
                    "unexpected interpreter path failure or words")
        order.append(label)
        rows[label] = dict(kind=kind, a=a, b=b, raw=raw, path=path,
                           branch=branch, result=result)
    require(thread_inventory("end") == threads_start,
            "OS thread inventory changed during the measured process")
    require(take("UNCLAIMED") == [UNCLAIMED[profile]],
            "changed path limitations")
    require(take("COMPLETE") == [str(len(order))],
            "wrong path completion count")
    require(cursor == len(records), "path data after completion")
    check = dict(zip(("native-rts", "interpreter", "failure"),
                     (_check_native_rts, _check_interpreter,
                      _check_failure)))[profile]
    check(rows)
    return dict(profile=profile, brackets=len(order), rows=rows,
                runtime=runtime[0], maps=maps, limit=limit,
                threads=threads_start, scope=SCOPE[profile],
                unclaimed=UNCLAIMED[profile])


def _sub(x, y):
    return [p - q for p, q in zip(x, y)]


def _no_failures(row, why):
    require(all(row["path"][i] == 0 for i in FAILURE_INDEXES), why)


def _check_native_rts(rows):
    idle = rows["noop-before-1"]["raw"]
    require(idle[0] > 0 and idle[1:] == [idle[0], 0, 0, 0],
            "native no-op wrapper is not purely native")
    large_first = 0
    for label, row in rows.items():
        kind, k, s = row["kind"], row["a"], row["b"]
        path, raw = row["path"], row["raw"]
        _no_failures(row, "failure path counter in a successful control")
        word_result = {"noop": [1, 0, 1, 1], "native": [1, s, 1, 1],
                       "rts": [1, 64 * s, 1, 1],
                       "large": [1, 64 * s, 1, 1]}[kind]
        require(row["result"] == word_result,
                "wrong path outcome/payload/sentinel")
        delta = _sub(raw, idle)
        if kind == "noop":
            if "warmup" not in label:
                require(raw == idle and not any(path),
                        "no-op path/raw costs differ")
            continue
        if kind == "native":
            n = k * (s + 1)
            require(delta == [n, n, 0, 0, 0],
                    "exact native payload slope mismatch")
            require(not any(path[i] for i in success_counters(1)),
                    "RTS path event in native control")
            if s:
                require(path[counter(0, 2, 0)] >= 1,
                        "native control missed the refill branch")
                if k == 32768:
                    require(path[counter(0, 2, 1)] >= 1 and
                            path[QUICKGC_TRUE] >= 1,
                            "native control missed success-after-GC")
        else:
            w = k * (s + 2)
            require(delta == [w, 0, w, 0, 0],
                    "exact RTS payload slope mismatch")
            require(sum(path[i] for i in success_counters(1)) == k,
                    "retry successes not counted exactly once")
            large = path[counter(1, 1, 0)] + path[counter(1, 1, 1)]
            require(large == (k if kind == "large" else 0),
                    "wrong large-object area count")
            if kind == "rts" and s == 101:
                require(path[counter(1, 2, 0)] >= 1 and
                        path[counter(1, 2, 1)] >= 1 and
                        path[QUICKGC_TRUE] >= 1,
                        "RTS control missed refill/after-GC branches")
            elif kind == "rts":
                require(path[counter(1, 2, 0)] >= 1,
                        "RTS control missed the refill branch")
            else:
                large_first += path[counter(1, 1, 0)]
                if k == 64:
                    require(path[counter(1, 1, 1)] >= 1 and
                            path[QUICKGC_TRUE] >= 1,
                            "large-object control missed success-after-GC")
        if any(path[i] for i in (counter(0, 2, 1), counter(1, 2, 1),
                                 counter(1, 1, 1))):
            require(path[QUICKGC_TRUE] >= 1,
                    "success-after-GC without a successful QuickGC")
    # Every other branch is required of each of its rows above; this one
    # could otherwise be reached only through the retry cell.
    require(large_first, "missing first-attempt large-object coverage")


def _check_interpreter(rows):
    idle = rows["noop-before-1"]["raw"]
    require(idle[0] > 0 and idle[1:] == [idle[0], 0, 0, 0],
            "interpreter entry no-op is not purely native")
    wrapper_row = rows["attempt-noop-1"]
    wrapper = wrapper_row["raw"]
    require(_sub(wrapper, idle)[1:3] == [0, 0] and wrapper[3] > 0 and
            wrapper[4] == 0,
            "interpreted attempt wrapper is not purely interpreter")
    single = 0
    for label, row in rows.items():
        kind, k, s = row["kind"], row["a"], row["b"]
        path, raw, branch = row["path"], row["raw"], row["branch"]
        require("warmup" in label or
                (raw[1] == idle[1] and raw[2] == 0 and raw[4] == 0),
                "native/RTS/code words in interpreter control")
        if kind == "noop":
            require(row["result"] == [0, 0, 1], "wrong no-op result")
            if "warmup" not in label:
                require(raw == idle and not any(path),
                        "no-op path/raw costs differ")
            _no_failures(row, "failure counter in a no-op")
        elif kind == "loop":
            require(raw[3] == k * (s + 1) and row["result"] == [1, s, 1],
                    "exact interpreter payload slope mismatch")
            _no_failures(row, "failure counter in a successful control")
            slow = branch[2]
            if (k, s) == (4096, 0):
                require(slow == 0, "unexpected slow events")
            elif k > 1:
                require(path[counter(2, 2, 0)] >= 1,
                        "interpreter control missed the refill branch")
            else:
                # A single large array may fit the current segment: the
                # schedule decides, so only the aggregate is required.
                require(slow <= k, "more slow events than requests")
                single += slow
            if (k, s) in ((32768, 1000), (64, 2097152)):
                require(path[counter(2, 2, 1)] >= 1 and
                        path[QUICKGC_TRUE] >= 1,
                        "interpreter control missed success-after-GC")
            require(path[counter(2, 2, 1)] == 0 or path[QUICKGC_TRUE] >= 1,
                    "success-after-GC without a successful QuickGC")
        elif kind == "attempt-noop":
            require(raw == wrapper and branch == wrapper_row["branch"] and
                    not any(path) and row["result"] == [1, 0, 1],
                    "attempt wrapper costs differ")
        elif kind == "ok":
            require(_sub(raw, wrapper) == [s + 1, 0, 0, s + 1, 0] and
                    row["result"] == [1, s, 1],
                    "exact recovery/slope mismatch")
            _no_failures(row, "failure counter in a successful control")
        elif kind == "fail":
            unit = [0] * PATH_COUNTERS
            unit[INTERP_FAIL] = unit[QUICKGC_FALSE] = 1
            require(path == unit, "failure is not exactly one interpreter "
                    "FindAllocationSpace failure with a failed QuickGC")
            require(raw == wrapper and branch == wrapper_row["branch"],
                    "failed request charged/changed raw or branch costs")
            require(row["result"] == [2, 0, 1],
                    "wrong failed outcome/entry")
    require(single, "missing single-array slow-path coverage")


def _check_failure(rows):
    idle = rows["noop-before-1"]["raw"]
    manual = rows["manual-before-1"]["raw"]
    require(idle[0] > 0 and idle[1:] == [idle[0], 0, 0, 0],
            "native no-op wrapper is not purely native")
    require(all(x >= y for x, y in zip(manual, idle)),
            "manual interrupt wrapper below native no-op baseline")
    compile_raw = rows["compile-before-1"]["raw"]
    require(compile_raw[1] > 0 and compile_raw[4] > 0 and
            compile_raw[2] == compile_raw[3] == 0,
            "compiler control does not allocate native and code words")
    # The control raises an exception packet of the same size through the
    # same RTS call as a failed code request, without asking for code space.
    packet = rows["code-ctl-before-1"]["raw"]
    require(packet[2] > 0 and packet[3] == 0 and packet[4] == 0,
            "same-packet control does not allocate only native/RTS words")
    for label, row in rows.items():
        kind, a, b = row["kind"], row["a"], row["b"]
        path, raw = row["path"], row["raw"]
        require(raw[3] == 0, "interpreter event in failure control")
        warm = "warmup" in label
        if kind == "noop":
            require(row["result"] == [1, 0, 1], "wrong no-op result")
            if not warm:
                require(raw == idle and not any(path),
                        "raw native no-op costs differ")
        elif kind == "manual":
            require(row["result"] == [3, 0, 1], "wrong manual outcome")
            if not warm:
                require(raw == manual and not any(path),
                        "prebuilt interrupt raw costs differ")
        elif kind == "compile":
            require(raw == compile_raw and row["result"] == [1, 0, 1],
                    "compiler raw costs differ before/after failures")
            _no_failures(row, "failure counter in a successful compile")
        elif kind == "rts-ok":
            w = b + 2
            require(_sub(raw, idle) == [w, 0, w, 0, 0],
                    "exact RTS recovery slope mismatch")
            require(row["result"] == [1, 64 * b, 1],
                    "wrong RTS recovery outcome")
            require(sum(path[i] for i in success_counters(1)) == 1,
                    "RTS recovery is not exactly one reservation")
            _no_failures(row, "failure counter in a successful RTS control")
        elif kind == "native-ok":
            require(_sub(raw, idle) == [b + 1, b + 1, 0, 0, 0],
                    "exact native recovery slope mismatch")
            require(row["result"] == [1, b, 1],
                    "wrong native recovery outcome")
            _no_failures(row,
                         "failure counter in a successful native control")
        elif kind == "rts-fail":
            unit = [0] * PATH_COUNTERS
            unit[RTS_FAIL] = unit[QUICKGC_FALSE] = 1
            require(path == unit, "failure is not exactly one RTS "
                    "FindAllocationSpace failure with a failed QuickGC")
            require(raw == manual and row["result"] == [2, 0, 1],
                    "failed RTS request charged/changed raw costs")
        elif kind == "native-fail":
            # One failed request and a failed QuickGC. The thread's next
            # small native allocation may then need one segment refill,
            # which is charged like any other native reservation.
            refills = path[counter(0, 2, 0)]
            unit = [0] * PATH_COUNTERS
            unit[NATIVE_FAIL] = unit[QUICKGC_FALSE] = 1
            unit[counter(0, 2, 0)] = refills
            unit[WORDS[0]] = path[WORDS[0]]
            require(path == unit and refills <= 1 and
                    (path[WORDS[0]] > 0) == (refills == 1),
                    "failure is not exactly one native "
                    "FindAllocationSpace failure with a failed QuickGC")
            require(raw == manual and row["result"] == [2, 0, 1],
                    "failed native request charged/changed raw costs")
        elif kind == "code-ctl":
            require(row["result"] == [4, 0, 1], "wrong same-packet outcome")
            require(raw == packet, "same-packet control costs differ")
            require(not any(path[i] for i in FAILURE_INDEXES),
                    "failure counter in the same-packet control")
        elif kind == "code-fail":
            # One failed AllocCodeSpace hook per failed attempt, and nothing
            # else: the QuickGC that ends the retry loop is outside the
            # hooked FindAllocationSpace.
            require(path[CODE_FAIL] == 1 and all(
                path[i] == 0 for i in (*FAIL_COUNTER, QUICKGC_TRUE,
                                       QUICKGC_FALSE)),
                "failure is not exactly one code-space allocation failure")
            require(row["result"] == [3, 0, 1], "wrong code failure outcome")
            # packet has no code words (checked above), so equality also
            # means the failed request was charged none.
            require(raw == packet, "failed code request is not charged as "
                    "the same-size exception packet alone")


def validate_receipt(receipt, profile, *, timeout):
    """Validate a loading.execute receipt from one capped control process.

    The caller must actually pass timeout to its subprocess runner (which
    must kill the process group on expiry); this function cannot enforce a
    timeout retrospectively. A complete-looking transcript from a timed-out
    or unsuccessful process is never accepted.
    """
    require(profile in RECIPE, "unknown path profile")
    require(type(timeout) in (int, float) and math.isfinite(timeout) and
            timeout > 0, "finite positive path-process timeout required")
    require(isinstance(receipt, dict), "missing path process receipt")
    flags = FLAGS[profile]
    command = receipt.get("command")
    require(isinstance(command, list) and len(command) == 1 + len(flags) and
            isinstance(command[0], str) and command[0].startswith("/") and
            command[1:] == list(flags),
            "path process needs exactly " + " ".join(flags))
    require(type(receipt.get("exit")) is int and receipt["exit"] == 0 and
            receipt.get("timed_out") is False,
            "failed/timed-out path process")
    text = receipt.get("stdout")
    require(isinstance(text, str), "missing merged path process output")
    raw = text.encode()
    require(type(receipt.get("stdout_bytes")) is int and
            receipt["stdout_bytes"] == len(raw) and
            receipt.get("stdout_sha256") == hashlib.sha256(raw).hexdigest(),
            "path process output seal mismatch")
    return observations(text, profile)
