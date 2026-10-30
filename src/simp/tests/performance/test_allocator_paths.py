"""SYNTHETIC path-protocol tests; NOT executed allocator-path evidence.

No allocator, subprocess, OS limit, build or benchmark is run. All counters,
diagnostics and thread names below are invented parser-test data (fixtures
are generated in this file; no committed receipt is read). Only the
separate driver's sealed, timed, successful process receipts are evidence.
"""
import copy
import hashlib
import unittest

import path_schema as s

PROFILES = ("native-rts", "interpreter", "failure")
TOTALS = {"native-rts": 22, "interpreter": 33, "failure": 40}
THREADS = ["4", "hol", "hol", "hol", "hol"]
PACKET = [28, 4, 24, 0, 0]


def unit(*indexes):
    v = [0] * s.PATH_COUNTERS
    for i in indexes:
        v[i] = 1
    return v


def model(profile, label, kind, a, b):
    """Invent a self-consistent row; returns raw, path, branch, result."""
    path = [0] * s.PATH_COUNTERS
    branch = [0, 0, 0, 0] if profile == "interpreter" else None
    if profile == "native-rts":
        raw = [4, 4, 0, 0, 0]
        result = [1, 0, 1, 1]
        if kind == "native":
            n = a * (b + 1)
            raw = [4 + n, 4 + n, 0, 0, 0]
            result = [1, b, 1, 1]
            if b:
                path[4] = 3
                path[5] = 2 if a == 32768 else 0
                path[21] = path[5]
                path[24] = n // 100
        elif kind in ("rts", "large"):
            w = a * (b + 2)
            raw = [4 + w, 4, w, 0, 0]
            result = [1, 64 * b, 1, 1]
            path[25] = w
            if kind == "large":
                path[9] = 2
                path[8] = a - 2
                path[21] = 2
            elif b == 101:
                path[10], path[11], path[21] = 211, 5, 5
                path[6] = a - 216
            else:
                path[10] = 6
                path[6] = a - 6
    elif profile == "interpreter":
        raw = [31, 31, 0, 0, 0]
        result = [0, 0, 1]
        wrapper = [6, 18, 0, 0]
        if kind == "loop":
            n = a * (b + 1)
            raw = [31 + n, 31, 0, n, 0]
            result = [1, b, 1]
            slow = (a if b >= 100000 else
                    0 if (a, b) == (4096, 0) else a // 128)
            sw = slow * (b + 1)
            branch = [a - slow, n - sw, slow, sw]
            after = 2 if (a, b) in ((32768, 1000), (64, 2097152)) else 0
            path[17], path[21] = after, after
            path[16] = slow - after
            path[26] = sw
        elif kind == "attempt-noop":
            raw = [49, 31, 0, 18, 0]
            result = [1, 0, 1]
            branch = wrapper
        elif kind == "ok":
            raw = [49 + b + 1, 31, 0, 18 + b + 1, 0]
            result = [1, b, 1]
            branch = [6, 18, 1, b + 1]
            path[16], path[26] = 1, b + 1
        elif kind == "fail":
            raw = [49, 31, 0, 18, 0]
            result = [2, 0, 1]
            branch = wrapper
            path = unit(20, 22)
    else:
        raw = [4, 4, 0, 0, 0]
        result = [1, 0, 1]
        if kind == "manual":
            result = [3, 0, 1]
        elif kind == "compile":
            raw = [29898, 29860, 0, 0, 38]
        elif kind == "rts-ok":
            w = b + 2
            raw = [4 + w, 4, w, 0, 0]
            result = [1, 64 * b, 1]
            path[6], path[25] = 1, w
        elif kind == "rts-fail":
            result = [2, 0, 1]
            path = unit(19, 22)
        elif kind == "native-ok":
            raw = [4 + b + 1, 4 + b + 1, 0, 0, 0]
            result = [1, b, 1]
        elif kind == "native-fail":
            result = [2, 0, 1]
            path = unit(18, 22)
            path[4], path[24] = 1, 2  # the next small allocation refills
        elif kind in ("code-ctl", "code-fail"):
            # The same exception packet: 24 RTS words through five RTS
            # reservations; only the failed request also hits counter 23,
            # and a refill happens to fall inside the failed request's.
            raw = list(PACKET)
            path[6], path[25] = 5, 24
            if kind == "code-ctl":
                result = [4, 0, 1]
            else:
                result = [3, 0, 1]
                path[6], path[10], path[23] = 4, 1, 1
    return dict(raw=raw, path=path, branch=branch, result=result)


def synthetic(profile, mutate=None, limit=None, threads_end=None,
              config=None, drop=None, threads=None):
    """Invent consistent counters/results/diagnostics for parser tests ONLY.

    mutate maps label -> function(row) editing the invented row in place.
    """
    mutate = mutate or {}
    lines = []

    def emit(kind, *values):
        lines.append("\t".join([s.PREFIX + kind + "_V1", *map(str, values)]))

    emit("SCOPE", s.SCOPE[profile])
    emit("PROFILE", profile)
    emit("RUNTIME", "/synthetic/libpolyml.so.16")
    emit("MAP", "100-200 r-xp 0000 00:00 1 /synthetic/libpolyml.so.16")
    emit("THREADS", "start", *(threads if threads is not None else THREADS))
    emit("ABI", 15)
    emit("CONFIG", *(config or s.CONFIG[profile]))
    cumulative = [1000, 700, 100, 100, 100]
    pathc = [5] * s.PATH_COUNTERS
    pathc[s.FOREIGN_THREAD] = 0
    br = [50, 500, 5, 50]
    for entry in s.RECIPE[profile]:
        if entry[0] == s.LIMIT_MARK:
            emit("LIMIT", *(limit if limit is not None else
                            [1, 268435456, 335544320, s.UINT64_MAX,
                             s.LIMIT_HEADROOM]))
            continue
        label, kind, a, b = entry
        row = model(profile, label, kind, a, b)
        if label in mutate:
            mutate[label](row)
        emit("REQUEST", label, kind, a, b)
        if kind in s.EXHAUSTION_KINDS[profile]:
            lines.append(s.EXHAUSTION)  # Fabricated, NOT execution evidence.
        raw, path, branch = row["raw"], row["path"], row["branch"]
        raw[0] = sum(raw[1:])  # The ABI sums categories; mutations keep it.
        end = [x + y for x, y in zip(cumulative, raw)]
        pend = [x + y for x, y in zip(pathc, path)]
        for side, values in (("start", cumulative), ("end", end)):
            emit("ENDPOINT", label, side, 1, 8, 0, *values)
        for side, values in (("start", pathc), ("end", pend)):
            emit("PENDPOINT", label, side, 1, 8, 0, *values, 0)
        if branch is not None:
            bend = [x + y for x, y in zip(br, branch)]
            for side, values in (("start", br), ("end", bend)):
                emit("BENDPOINT", label, side, 1, 8, 0, *values, 0)
            br = bend
        emit("RAW", label, *raw)
        emit("PATH", label, *path)
        if branch is not None:
            emit("BRANCH", label, *branch)
        emit("RESULT", label, *row["result"])
        cumulative = [end[0] + 3] + [x + (3 if i == 0 else 0) for i, x in
                                     enumerate(end[1:])]
        pathc = pend
    emit("THREADS", "end", *(threads_end or (threads if threads is not None
                                             else THREADS)))
    emit("UNCLAIMED", s.UNCLAIMED[profile])
    emit("COMPLETE", TOTALS[profile])
    out = lines
    if drop is not None:
        out = lines[:drop] + lines[drop + 1:]
    return "\n".join(out) + "\n"


def receipt(profile):
    text = synthetic(profile)
    return dict(command=["/synthetic/controls.exe", *s.FLAGS[profile]],
                exit=0, timed_out=False, stdout=text,
                stdout_bytes=len(text.encode()),
                stdout_sha256=hashlib.sha256(text.encode()).hexdigest())


def edit(**fields):
    def apply(row):
        for key, value in fields.items():
            if callable(value):
                value(row[key])
            else:
                row[key] = value
    return apply


def reject(test, profile, why, **kwargs):
    """The mutated protocol must be rejected, and for the stated reason."""
    if not why:
        raise TypeError("reject needs the expected rejection reason")
    with test.assertRaisesRegex(ValueError, why):
        s.observations(synthetic(profile, **kwargs), profile)


class PathSchemaTests(unittest.TestCase):
    def test_recipes_are_stable_and_unique(self):
        for profile in PROFILES:
            self.assertEqual(len(s.labels(profile)), TOTALS[profile])
            self.assertEqual(len(set(s.labels(profile))), TOTALS[profile])

    def test_complete_synthetic_protocols(self):
        for profile in PROFILES:
            with self.subTest(profile=profile):
                result = s.observations(synthetic(profile), profile)
                self.assertEqual(result["brackets"], TOTALS[profile])
                self.assertEqual(result["threads"], THREADS)
                self.assertEqual(
                    s.validate_receipt(receipt(profile), profile, timeout=60),
                    result)
        # The synthetic limit is the only invented OS limit.
        result = s.observations(synthetic("failure"), "failure")
        self.assertEqual(result["limit"], dict(
            success=1, vsize_before=268435456, applied_soft=335544320,
            hard=s.UINT64_MAX, headroom=s.LIMIT_HEADROOM))
        self.assertEqual(result["rows"]["code-fail-335544320-1"]["raw"],
                         PACKET)

    def test_wrong_profile_is_rejected(self):
        for profile in PROFILES:
            for other in PROFILES:
                if other != profile:
                    with self.assertRaises(ValueError):
                        s.observations(synthetic(profile), other)
        with self.assertRaises(ValueError):
            s.observations(synthetic("failure"), "native")

    def test_every_record_and_diagnostic_required_unique_and_ordered(self):
        for profile in PROFILES:
            lines = synthetic(profile).splitlines()
            for i, line in enumerate(lines):
                variants = [lines[:i] + lines[i+1:],
                            lines[:i] + [line] + lines[i:]]
                if i + 1 < len(lines) and lines[i+1] != line:
                    swapped = lines.copy()
                    swapped[i], swapped[i+1] = swapped[i+1], swapped[i]
                    variants.append(swapped)
                for variant in variants:
                    with self.subTest(profile=profile, i=i), \
                            self.assertRaises(ValueError):
                        s.observations("\n".join(variant), profile)

    def test_unknown_versions_protocols_and_records_rejected(self):
        for profile in PROFILES:
            text = synthetic(profile)
            for changed in (
                    text.replace("_V1", "_V2", 1),
                    text.replace(s.PREFIX + "RAW", s.PREFIX + "DELTA", 1),
                    text.replace(s.PREFIX + "PATH_V1", s.PREFIX + "PATHS_V1",
                                 1),
                    text.replace(s.PREFIX + "ENDPOINT",
                                 "@@TASK29_FAILURE_ENDPOINT"),
                    text.replace(s.PREFIX + "RESULT",
                                 "@@TASK29_ALLOC_RESULT", 1),
                    text + s.PREFIX + "EXCEPTION_V1\tInterrupt\n",
                    text + s.PREFIX + "FUTURE_V1\t1\n",
                    text + "@@TASK29_PATHbroken\n"):
                with self.subTest(profile=profile, changed=changed[:60]), \
                        self.assertRaises(ValueError):
                    s.observations(changed, profile)
            self.assertEqual(
                s.observations("ordinary testutils output\n" + text,
                               profile),
                s.observations(text, profile))

    def test_runtime_exhaustion_output_is_actual_and_exact(self):
        for profile in ("interpreter", "failure"):
            text = synthetic(profile)
            for changed in (
                    text.replace(s.EXHAUSTION + "\n", ""),
                    text.replace(s.EXHAUSTION, "fixture says exhausted"),
                    text.replace(s.EXHAUSTION, s.PREFIX + "EXHAUSTED_V1\t1"),
                    text.replace(s.EXHAUSTION, s.EXHAUSTION + " ", 1),
                    text.replace(s.EXHAUSTION, "prefix " + s.EXHAUSTION, 1),
                    text + s.EXHAUSTION + "\n",
                    text + "Failed to recover - exiting\n",
                    s.EXHAUSTION + "\n" + text):
                with self.subTest(profile=profile, changed=changed[:70]), \
                        self.assertRaises(ValueError):
                    s.observations(changed, profile)
        # A success control must not be accompanied by an exhaustion line.
        text = synthetic("native-rts")
        marker = s.PREFIX + "REQUEST_V1\tnative-4096-0-1"
        with self.assertRaises(ValueError):
            s.observations(text.replace(marker, s.EXHAUSTION + "\n" + marker,
                                        1), "native-rts")

    def test_every_numeric_field_is_canonical_bounded_uint64(self):
        for profile in PROFILES:
            lines = synthetic(profile).splitlines()
            first = {"ABI_V1": 1, "CONFIG_V1": 1, "LIMIT_V1": 1,
                     "REQUEST_V1": 3, "ENDPOINT_V1": 3, "PENDPOINT_V1": 3,
                     "BENDPOINT_V1": 3, "RAW_V1": 2, "PATH_V1": 2,
                     "BRANCH_V1": 2, "RESULT_V1": 2, "COMPLETE_V1": 1}
            seen = set()
            for i, line in enumerate(lines):
                p = line.split("\t")
                start = first.get(p[0].removeprefix(s.PREFIX))
                if start is None:
                    continue
                # One line of each record type, every field, is enough
                # structure for the shared parser and keeps this test fast.
                if p[0] in seen and p[1] not in ("rts-fail-1073741824-1",
                                                 "fail-16777216-1"):
                    continue
                seen.add(p[0])
                for j in range(start, len(p)):
                    for value in ("-1", "+1", "01", "1.0", "", " 1", "1 ",
                                  str(2**64), "9" * 100):
                        changed = lines.copy()
                        q = p.copy()
                        q[j] = value
                        changed[i] = "\t".join(q)
                        with self.subTest(profile=profile, i=i, j=j,
                                          value=value), \
                                self.assertRaises(ValueError):
                            s.observations("\n".join(changed), profile)

    def test_changed_numeric_fields_and_shapes_rejected(self):
        for profile in PROFILES:
            lines = synthetic(profile).splitlines()
            for i, line in enumerate(lines):
                p = line.split("\t")
                if not p[0].endswith(("_V1",)):
                    continue
                for j in range(2, len(p)):
                    if not p[j].isdigit() or p[0].endswith("THREADS_V1"):
                        continue
                    changed = lines.copy()
                    q = p.copy()
                    q[j] = str(int(q[j]) + 1)
                    changed[i] = "\t".join(q)
                    try:
                        s.observations("\n".join(changed), profile)
                    except ValueError:
                        continue
                    # An arbitrary +1 may by chance stay a valid invented
                    # measurement; only identity-defining records must fail.
                    kind = p[0].removeprefix(s.PREFIX)
                    self.assertNotIn(kind, (
                        "ABI_V1", "CONFIG_V1", "REQUEST_V1", "RAW_V1",
                        "RESULT_V1", "COMPLETE_V1", "LIMIT_V1"), line)
            text = synthetic(profile)
            for old, new in (
                    (s.SCOPE[profile], "all paths covered"),
                    (s.UNCLAIMED[profile], "nothing unverified"),
                    ("RUNTIME_V1\t/", "RUNTIME_V1\t"),
                    ("MAP_V1\t100-200", "MAP_V1\tbad-map"),
                    ("ENDPOINT_V1\t", "ENDPOINT_V1\tx\t"),
                    ("1\t8\t0", "1\t4\t0"),
                    ("1\t8\t0", "1\t8\t1"),
                    ("1\t8\t0", "2\t8\t0"),
                    ("PROFILE_V1\t" + profile, "PROFILE_V1\tother"),
                    ("ABI_V1\t15", "ABI_V1\t7")):
                self.assertIn(old, text)
                with self.subTest(profile=profile, old=old), \
                        self.assertRaises(ValueError):
                    s.observations(text.replace(old, new, 1), profile)
            reject(self, profile, "configuration",
                   config=s.CONFIG[profile][:-1] + [
                       s.CONFIG[profile][-1] + 1])

    def test_path_abi_reserved_words_overflow_and_monotonicity(self):
        for profile in PROFILES:
            lines = synthetic(profile).splitlines()
            index = next(i for i, l in enumerate(lines)
                         if l.startswith(s.PREFIX + "PENDPOINT_V1"))
            p = lines[index].split("\t")
            # fields: label side ver bytes mask counters... r1 r2
            for position, value in ((4, "2"), (5, "9"), (6, "1"),
                                    (-1, "1"), (-2, "1")):
                q = p.copy()
                q[position] = value
                changed = lines.copy()
                changed[index] = "\t".join(q)
                with self.subTest(profile=profile, position=position), \
                        self.assertRaises(ValueError):
                    s.observations("\n".join(changed), profile)
            q = p[:-1]
            changed = lines.copy()
            changed[index] = "\t".join(q)
            with self.assertRaises(ValueError):
                s.observations("\n".join(changed), profile)

    def test_process_counter_reset_and_raw_path_inconsistency(self):
        for profile in PROFILES:
            lines = synthetic(profile).splitlines()
            for record, position in (("ENDPOINT_V1", 6),
                                     ("PENDPOINT_V1", 8)):
                last = max(i for i, l in enumerate(lines)
                           if l.startswith(s.PREFIX + record)
                           and "\tstart\t" in l)
                p = lines[last].split("\t")
                p[position] = "0"
                changed = lines.copy()
                changed[last] = "\t".join(p)
                with self.subTest(profile=profile, record=record), \
                        self.assertRaises(ValueError):
                    s.observations("\n".join(changed), profile)
            lines = synthetic(profile).splitlines()
            for record in ("RAW_V1", "PATH_V1"):
                i = next(i for i, l in enumerate(lines) if
                         l.startswith(s.PREFIX + record + "\tnoop-before-1"))
                p = lines[i].split("\t")
                p[3] = str(int(p[3]) + 1)
                changed = lines.copy()
                changed[i] = "\t".join(p)
                with self.subTest(profile=profile, record=record), \
                        self.assertRaises(ValueError):
                    s.observations("\n".join(changed), profile)

    def test_thread_inventory_pinned_and_unchanged(self):
        for profile in PROFILES:
            for end in (THREADS + ["hol"], ["3", "hol", "hol", "hol"],
                        ["4", "hol", "hol", "hol", "other"],
                        ["4", "hol", "hol", "hol"],
                        ["5", "hol", "hol", "hol", "hol", "hol"]):
                with self.subTest(profile=profile, end=end):
                    reject(self, profile, "OS thread inventory",
                           threads_end=end)
        text = synthetic("native-rts")
        for old, new in (("start\t4\thol\thol\thol\thol",
                          "start\t4\thol\thol\thol"),
                         ("start\t4\thol\thol\thol\thol",
                          "start\t0"),
                         ("start\t4\thol\thol\thol\thol",
                          "start\t4\thol\thol\thol\tz hol"),
                         ("start\t4\thol\thol\thol\thol",
                          "start\t4\thol\thol\thol\tabcdefghijklmnop"),
                         ("start\t4\thol\thol\thol\thol",
                          "start\t4\tz\thol\thol\thol")):
            with self.subTest(new=new), self.assertRaises(ValueError):
                s.observations(text.replace(old, new, 1), "native-rts")

    def test_os_limit_arithmetic_and_hard_bound(self):
        for profile in ("interpreter", "failure"):
            for before in (4096, 536870912, 2**40):
                soft = before + s.LIMIT_HEADROOM
                for hard in (soft, soft + 4096, s.UINT64_MAX):
                    limit = [1, before, soft, hard, s.LIMIT_HEADROOM]
                    parsed = s.observations(
                        synthetic(profile, limit=limit), profile)["limit"]
                    self.assertEqual(parsed["applied_soft"], soft)
            valid = [1, 268435456, 335544320, s.UINT64_MAX, s.LIMIT_HEADROOM]
            for index, replacements in {
                    0: (0, 2), 1: (0, 268435457, s.UINT64_MAX),
                    2: (335544319, 335544321), 3: (0, 335544319),
                    4: (0, s.LIMIT_HEADROOM - 1,
                        s.LIMIT_HEADROOM + 1)}.items():
                for value in replacements:
                    invalid = valid.copy()
                    invalid[index] = value
                    with self.subTest(profile=profile, limit=invalid), \
                            self.assertRaises(ValueError):
                        s.observations(synthetic(profile, limit=invalid),
                                       profile)
            for invalid in (valid[:-1], valid + [0]):
                with self.assertRaises(ValueError):
                    s.observations(synthetic(profile, limit=invalid), profile)
        # No LIMIT record is admitted where no limit was applied.
        text = synthetic("native-rts").splitlines()
        text.insert(7, s.PREFIX + "LIMIT_V1\t1\t1\t1\t1\t1")
        with self.assertRaises(ValueError):
            s.observations("\n".join(text), "native-rts")

    def test_native_rts_exact_slopes_branches_and_retry_counting(self):
        p = "native-rts"
        for label, change, why in (
                ("native-4096-1024-1", edit(raw=[4198405, 4198405, 0, 0, 0]),
                 "native payload"),
                ("native-4096-1024-1", edit(raw=[4198404, 4198400, 4, 0, 0]),
                 "native payload|RTS path words"),
                ("rts-262144-1-1", edit(raw=[786437, 5, 786432, 0, 0]),
                 "RTS payload"),
                ("rts-262144-1-1", edit(raw=[786435, 4, 786431, 0, 0]),
                 "RTS payload|RTS path words"),
                ("large-8-1048576-1",
                 edit(raw=[8388627, 4, 8388623, 0, 0]),
                 "RTS payload|RTS path words"),
                ("noop-before-2", edit(raw=[5, 5, 0, 0, 0]),
                 "no-op path/raw"),
                ("noop-final-1", edit(path=lambda v: v.__setitem__(6, 1)),
                 "no-op path/raw")):
            with self.subTest(label=label, why=why):
                reject(self, p, why, mutate={label: change})
        # Retry successes counted exactly once: one more or fewer success.
        for label, index in (("rts-262144-101-1", 6), ("rts-262144-1-2", 6),
                             ("large-64-1048576-1", 8)):
            for delta in (-1, 1):
                def tweak(row, i=index, d=delta):
                    row["path"][i] += d
                with self.subTest(label=label, delta=delta):
                    reject(self, p, "retry successes|large-object",
                           mutate={label: tweak})
        # Large objects misclassified as ordinary refills, or the reverse.
        reject(self, p, "large-object", mutate={
            "rts-262144-1-1": lambda r: (r["path"].__setitem__(8, 1),
                                         r["path"].__setitem__(6, r["path"][6]
                                                               - 1))})
        reject(self, p, "large-object", mutate={
            "large-8-1048576-2": lambda r: (r["path"].__setitem__(10, 2),
                                            r["path"].__setitem__(8, 6),
                                            r["path"].__setitem__(9, 0))})
        # Missing branches: refill, success-after-GC, large-after-GC.
        for label, index, why in (
                ("native-4096-1024-1", 4, "refill"),
                ("native-32768-1024-2", 5, "success-after-GC"),
                ("rts-262144-101-1", 10, "refill"),
                ("rts-262144-101-2", 11, "refill/after-GC"),
                ("rts-262144-1-1", 10, "refill"),
                ("large-64-1048576-1", 9, "success-after-GC")):
            def zero(row, i=index):
                if i == 10:
                    row["path"][6] += row["path"][10]
                elif i == 9:
                    row["path"][8] += row["path"][9]
                elif i == 5:
                    row["path"][4] += row["path"][5]
                elif i == 11:
                    row["path"][10] += row["path"][11]
                row["path"][i] = 0
                row["path"][21] = 0
            with self.subTest(label=label):
                reject(self, p, why, mutate={label: zero})
        reject(self, p, "QuickGC|success-after-GC", mutate={
            "native-32768-1024-1": lambda r: r["path"].__setitem__(21, 0)})
        # Aggregate coverage cannot be satisfied by other rounds' rows.
        def no_after(row):
            row["path"][4] += row["path"][5]
            row["path"][5] = row["path"][21] = 0
        reject(self, p, "success-after-GC|path coverage", mutate={
            l: no_after for l in ("native-32768-1024-1",
                                  "native-32768-1024-2")})

    def test_native_rts_foreign_events_failures_and_outcomes_rejected(self):
        p = "native-rts"
        for index, why in ((12, "interpreter path"), (16, "interpreter path"),
                           (20, "failure|interpreter"), (26, "interpreter"),
                           (18, "failure"), (19, "failure"), (22, "failure"),
                           (23, "failure")):
            def poke(row, i=index):
                row["path"][i] += 1
            with self.subTest(index=index):
                reject(self, p, why, mutate={"native-4096-1024-1": poke})
        reject(self, p, "RTS path event", mutate={
            "native-4096-1024-1": lambda r: r["path"].__setitem__(7, 1)})
        for label, wrong in (("native-4096-1024-1", [1, 1023, 1, 1]),
                             ("native-4096-1024-1", [1, 1024, 0, 1]),
                             ("native-4096-1024-1", [1, 1024, 1, 0]),
                             ("native-4096-1024-1", [0, 1024, 1, 1]),
                             ("rts-262144-1-1", [1, 63, 1, 1]),
                             ("large-8-1048576-1", [1, 1, 1, 1]),
                             ("noop-final-1", [1, 0, 1, 0])):
            with self.subTest(label=label, wrong=wrong):
                reject(self, p, "outcome", mutate={label: edit(result=wrong)})

    def test_interpreter_exact_slopes_branch_identities_and_failures(self):
        p = "interpreter"
        wrapper = [49, 31, 0, 18, 0]
        for label, change, why in (
                ("loop-4096-1000-1", edit(raw=[31 + 4100097, 31, 0,
                                               4100097, 0]), "branch"),
                ("loop-64-2097152-2", edit(raw=[1, 31, 0, 0, 0]),
                 "interpreter"),
                ("attempt-noop-2", edit(raw=[50, 31, 0, 19, 0]), "branch"),
                ("ok-before-1", edit(raw=[1051, 31, 0, 1020, 0]),
                 "branch"),
                ("recover-16777216-2", edit(raw=[1049, 31, 0, 1018, 0]),
                 "branch"),
                ("noop-limited-2", edit(raw=[32, 32, 0, 0, 0]),
                 "no-op path/raw|native"),
                ("fail-16777216-1", edit(raw=[50, 31, 0, 19, 0]),
                 "branch"),
                ("fail-25165824-2", edit(raw=wrapper[:3] + [18, 1]),
                 "native/RTS/code|charged"),
                ("fail-25165824-1", edit(raw=[4, 4, 0, 0, 0],
                                         branch=[0, 0, 0, 0]),
                 "charged|native"),
                ("fail-16777216-2", edit(raw=[50, 31, 0, 19, 0],
                                         branch=[6, 19, 0, 0]),
                 "charged"),
                ("ok-before-2", edit(raw=[1051, 31, 0, 1020, 0],
                                     branch=[7, 1020, 0, 0],
                                     path=[0] * s.PATH_COUNTERS),
                 "recovery"),
                ("attempt-noop-1", edit(raw=[50, 31, 0, 19, 0],
                                        branch=[6, 19, 0, 0]), "wrapper"),
                ("loop-4096-1000-2", edit(raw=[31 + 4100097, 31, 0, 4100097,
                                               0],
                                         branch=[4064, 4068065, 32, 32032]),
                 "slope"),
                ("fail-25165824-1", edit(branch=[7, 19, 0, 0]),
                 "branch|charged")):
            with self.subTest(label=label, why=why):
                reject(self, p, why, mutate={label: change})
        # Requested size charged to a failure in every category.
        for category in (1, 2, 3, 4):
            def charge(row, c=category):
                row["raw"][0] += 16777216
                row["raw"][c] += 16777216
            with self.subTest(category=category):
                reject(self, p, "interpreter raw words differ|native/RTS/code"
                       "|RTS path words differ", mutate={
                           "fail-16777216-1": charge})
        # Failure counters: exact unit vector with a failed QuickGC.
        exact = "failure is not exactly one interpreter"
        for path, why in ((unit(20), exact), (unit(22), exact),
                          (unit(19, 22), exact), (unit(18, 22), exact),
                          (unit(23, 22), exact), (unit(20, 21), exact),
                          (unit(20, 22, 16), "interpreter path events"),
                          (unit(20, 22, 25), "RTS path words"),
                          ([0] * s.PATH_COUNTERS, exact),
                          ([0, 0, 0, 0, 2] + [0] * 23, exact),
                          ([2 if i in (20, 22) else 0
                            for i in range(s.PATH_COUNTERS)], exact)):
            with self.subTest(path=path):
                reject(self, p, why, mutate={
                    "fail-25165824-1": edit(path=path)})
        # Outcomes: a failed request must be an exact caught Interrupt.
        for label, wrong in (("fail-16777216-1", [1, 0, 1]),
                             ("fail-16777216-1", [2, 1, 1]),
                             ("fail-16777216-1", [2, 0, 0]),
                             ("fail-16777216-1", [0, 0, 1]),
                             ("recover-16777216-1", [2, 1000, 1]),
                             ("recover-16777216-1", [1, 999, 1]),
                             ("recover-16777216-1", [1, 1000, 0])):
            with self.subTest(label=label, wrong=wrong):
                reject(self, p, "outcome|recovery|entry",
                       mutate={label: edit(result=wrong)})
        # Failure vectors must repeat exactly, across both sizes and repeats.
        reject(self, p, "branch|charged|repeat|differ", mutate={
            "fail-25165824-2": edit(raw=[49, 31, 0, 18, 0],
                                    branch=[6, 17, 0, 1])})

    def test_interpreter_branch_and_path_counters_must_agree(self):
        p = "interpreter"
        for label in ("loop-4096-1000-1", "loop-64-2097152-1",
                      "loop-1-100000-2", "ok-before-1"):
            for index, delta in ((16, 1), (16, -1), (17, 1), (26, 1),
                                 (26, -1)):
                def poke(row, i=index, d=delta):
                    row["path"][i] = max(0, row["path"][i] + d)
                with self.subTest(label=label, index=index, delta=delta):
                    reject(self, p, "interpreter path|interpreter raw",
                           mutate={label: poke})
        for label in ("loop-4096-1000-1", "loop-32768-1000-2"):
            for position in (1, 2, 3):
                def poke(row, k=position):
                    row["branch"][k] += 1
                with self.subTest(label=label, position=position):
                    reject(self, p, "interpreter (path|raw)",
                           mutate={label: poke})
        reject(self, p, "interpreter control missed", mutate={
            "loop-64-2097152-1": lambda r: (
                r["path"].__setitem__(16, r["path"][16] + r["path"][17]),
                r["path"].__setitem__(17, 0),
                r["path"].__setitem__(21, 0))})
        reject(self, p, "path coverage|missed", mutate={
            l: lambda r: (r["path"].__setitem__(16, r["path"][16]
                                                + r["path"][17]),
                          r["path"].__setitem__(17, 0),
                          r["path"].__setitem__(21, 0))
            for l in ("loop-32768-1000-1", "loop-32768-1000-2",
                      "loop-64-2097152-1", "loop-64-2097152-2")})
        # Single large arrays may legitimately stay in the current segment
        # (the fast path), but not all of them, and never more slow events
        # than requests.
        reject(self, p, "more slow events", mutate={
            "loop-1-200000-1": lambda r: (
                r.__setitem__("branch", [0, 0, 2, 200001]),
                r["path"].__setitem__(16, 2))})
        none = lambda r: (r.__setitem__("branch", [1, r["raw"][3], 0, 0]),
                          r["path"].__setitem__(16, 0),
                          r["path"].__setitem__(26, 0))
        reject(self, p, "path coverage", mutate={
            l: none for l in ("loop-1-100000-1", "loop-1-100000-2",
                              "loop-1-200000-1", "loop-1-200000-2")})
        s.observations(synthetic(p, mutate={"loop-1-200000-1": none}), p)
        for index in (20, 22, 18, 19, 23):
            def poke(row, i=index):
                row["path"][i] += 1
            with self.subTest(index=index):
                reject(self, p, "failure counter in a successful control",
                       mutate={"loop-4096-1000-1": poke})

    def test_failure_exact_recovery_slopes_and_unchanged_compile(self):
        p = "failure"
        base = s.observations(synthetic(p), p)["rows"]
        self.assertEqual(base["rts-ok-before-128"]["raw"][2], 130)
        for label, change, why in (
                ("rts-ok-before-1", edit(raw=[8, 4, 4, 0, 0]),
                 "recovery slope|RTS path words"),
                ("rts-ok-1073741824-1-128", edit(raw=[133, 4, 129, 0, 0]),
                 "recovery slope|RTS path words"),
                ("rts-ok-1610612736-2-1", edit(result=[1, 64, 0]),
                 "wrong RTS recovery outcome"),
                ("rts-ok-1610612736-2-1",
                 lambda row: row["path"].__setitem__(6, 2),
                 "exactly one reservation"),
                ("compile-after-335544320-1",
                 edit(raw=[29899, 29861, 0, 0, 38]), "compiler raw costs"),
                ("compile-after-335544320-2",
                 edit(raw=[29898, 29860, 0, 0, 37]),
                 "compiler raw costs|category"),
                ("compile-final", edit(result=[1, 0, 0]),
                 "compiler raw costs"),
                ("compile-before-2", edit(raw=[29898, 29862, 0, 0, 36]),
                 "compiler raw costs"),
                ("noop-final-2", edit(raw=[5, 5, 0, 0, 0]),
                 "no-op costs"),
                ("manual-before-2", edit(raw=[5, 5, 0, 0, 0]),
                 "prebuilt interrupt"),
                ("noop-before-1", edit(raw=[0, 0, 0, 0, 0]),
                 "native no-op wrapper")):
            with self.subTest(label=label, why=why):
                reject(self, p, why, mutate={label: change})
        def failed(row):
            row["path"][19] += 1
        reject(self, p, "failure counter", mutate={
            "compile-after-335544320-2": failed})

    def test_failure_real_rts_and_code_failures_not_charged(self):
        p = "failure"
        rts_labels = [l for l in s.labels(p) if l.startswith("rts-fail-")]
        native_labels = [l for l in s.labels(p)
                         if l.startswith("native-fail-")]
        code_labels = [l for l in s.labels(p) if l.startswith("code-fail-")]
        self.assertEqual((len(rts_labels), len(native_labels),
                          len(code_labels)), (4, 2, 2))
        for kind, labels, index, size in (
                ("RTS", rts_labels, s.RTS_FAIL, 1073741824),
                ("native", native_labels, s.NATIVE_FAIL, 16777216)):
            exact = f"failure is not exactly one {kind}"
            charged = f"failed {kind} request charged"
            for label in labels:
                for path, why in ((unit(19), exact), (unit(22), exact),
                                  (unit(18, 22), exact),
                                  (unit(20, 22), "unexpected interpreter"),
                                  (unit(19, 22, 6), exact),
                                  (unit(19, 22, 23), exact),
                                  (unit(19, 21), exact),
                                  ([0] * s.PATH_COUNTERS, exact)):
                    if path == unit(index, s.QUICKGC_FALSE):
                        continue
                    with self.subTest(label=label, path=path):
                        reject(self, p, why, mutate={
                            label: edit(path=path)})
                for category, why in ((1, charged), (2, "RTS path words"),
                                      (3, "interpreter event"),
                                      (4, charged)):
                    def charge(row, c=category, n=size):
                        row["raw"][0] += n
                        row["raw"][c] += n
                    with self.subTest(label=label, category=category):
                        reject(self, p, why, mutate={label: charge})
                for result in ([1, 0, 1], [2, 1, 1], [2, 0, 0], [3, 0, 1]):
                    with self.subTest(label=label, result=result):
                        reject(self, p, charged, mutate={
                            label: edit(result=result)})
        # A native failure may not be recorded as an RTS one or vice versa.
        reject(self, p, "failure is not exactly one RTS", mutate={
            rts_labels[0]: edit(path=unit(18, 22))})
        reject(self, p, "failure is not exactly one native", mutate={
            native_labels[0]: edit(path=unit(19, 22))})
        only = "same-size exception packet alone"
        for label in code_labels:
            for index, why in ((18, "one code-space"), (19, "one code-space"),
                               (20, "unexpected interpreter"),
                               (21, "one code-space"),
                               (22, "one code-space")):
                def poke(row, i=index):
                    row["path"][i] += 1
                with self.subTest(label=label, index=index):
                    reject(self, p, why, mutate={label: poke})
            for value in (0, 2):
                with self.subTest(label=label, value=value):
                    reject(self, p, "one code-space", mutate={
                        label: lambda r, v=value: r["path"].__setitem__(23,
                                                                         v)})
            # Raw costs must equal the same-size packet exactly; a code
            # allocation inside the bracket (word 4) is rejected on its own.
            for raw, why in (([PACKET[0] + 1, 5, 24, 0, 0], only),
                             ([PACKET[0] + 1, 4, 24, 0, 1], only),
                             ([PACKET[0] + 16, 4, 24, 0, 16], only),
                             ([PACKET[0] + 335544320, 4 + 335544320, 24, 0,
                               0], only),
                             ([PACKET[0] + 30, 4, 54, 0, 0],
                              "RTS path words")):
                with self.subTest(label=label, raw=raw):
                    reject(self, p, why, mutate={label: edit(raw=raw)})
            for result in ([1, 0, 1], [2, 0, 1], [3, 1, 1], [3, 0, 0],
                           [4, 0, 1]):
                with self.subTest(label=label, result=result):
                    reject(self, p, "wrong code failure outcome",
                           mutate={label: edit(result=result)})

    def test_failure_same_packet_control(self):
        p = "failure"
        labels = [l for l in s.labels(p) if l.startswith("code-ctl-")]
        self.assertEqual(len(labels), 4)
        rows = s.observations(synthetic(p), p)["rows"]
        self.assertTrue(all(rows[l]["raw"] == rows["code-fail-335544320-1"]
                            ["raw"] for l in labels))
        for label in labels:
            for result in ([3, 0, 1], [1, 0, 1], [4, 1, 1], [4, 0, 0]):
                with self.subTest(label=label, result=result):
                    reject(self, p, "wrong same-packet outcome",
                           mutate={label: edit(result=result)})
            for index, why in ((s.NATIVE_FAIL, "failure counter in the"),
                               (s.RTS_FAIL, "failure counter in the"),
                               (s.INTERP_FAIL, "unexpected interpreter"),
                               (s.QUICKGC_FALSE, "failure counter in the"),
                               (s.CODE_FAIL, "failure counter in the")):
                def poke(row, i=index):
                    row["path"][i] += 1
                with self.subTest(label=label, index=index):
                    reject(self, p, why, mutate={label: poke})
            def dearer(row):
                row["raw"][0] += 1
                row["raw"][1] += 1
            reject(self, p, "same-packet control costs differ",
                   mutate={label: dearer} if label != "code-ctl-before-1"
                   else {"code-ctl-before-2": dearer})
        # A control that allocated code, or no RTS words, is not a control.
        label = "code-ctl-before-1"
        for raw in ([44, 4, 24, 0, 16], [31, 4, 24, 3, 0]):
            reject(self, p, "same-packet control does not allocate only",
                   mutate={label: edit(raw=raw)})
        reject(self, p, "RTS path words", mutate={
            label: edit(raw=[4, 4, 0, 0, 0])})
        # The first control fixes the packet cost: a later control (also
        # one measured under the limit) that differs is rejected.
        for label in ("code-ctl-limited-2", "code-fail-335544320-2"):
            reject(self, p, "same-packet control costs differ|same-size",
                   mutate={label: edit(raw=[29, 5, 24, 0, 0])})

    def test_failure_native_recovery_and_sizes(self):
        p = "failure"
        for label in ("native-ok-16777216-1", "native-ok-16777216-2"):
            for raw, why in (([1006, 1006, 0, 0, 0], "native recovery slope"),
                             ([1004, 1004, 0, 0, 0], "native recovery slope"),
                             ([1006, 1005, 0, 1, 0], "interpreter event"),
                             ([1005, 1004, 1, 0, 0], "RTS path words")):
                with self.subTest(label=label, raw=raw):
                    reject(self, p, why, mutate={label: edit(raw=raw)})
            for result in ([1, 999, 1], [2, 1000, 1], [1, 1000, 0]):
                with self.subTest(label=label, result=result):
                    reject(self, p, "wrong native recovery outcome",
                           mutate={label: edit(result=result)})
            reject(self, p, "failure counter in a successful native", mutate={
                label: edit(path=unit(18, 22))})
        # Declared request sizes: each failing kind must ask for its size.
        text = synthetic(p)
        for old, new in (
                ("native-fail-16777216-1\tnative-fail\t1\t16777216",
                 "native-fail-16777216-1\tnative-fail\t1\t25165824"),
                ("code-fail-335544320-1\tcode-fail\t335544320",
                 "code-fail-335544320-1\tcode-fail\t301989888")):
            self.assertIn(old, text)
            with self.assertRaisesRegex(ValueError, "changed/reordered"):
                s.observations(text.replace(old, new), p)

    def test_receipt_rejects_exit_timeout_flags_output_tampering(self):
        for profile in PROFILES:
            original = receipt(profile)
            flags = list(s.FLAGS[profile])
            for key, values in {
                    "exit": (1, -9, None, False),
                    "timed_out": (True, None, 0),
                    "stdout": (None, original["stdout"] + "tampered\n"),
                    "stdout_bytes": (0, True),
                    "stdout_sha256": ("0" * 64, None),
                    "command": (
                        [], ["relative.exe", *flags],
                        [original["command"][0]],
                        [*original["command"], "--maxheap=512"],
                        [original["command"][0], *flags[:-1]],
                        [original["command"][0], "--maxheap=96", *flags],
                        [original["command"][0], "-H", "128",
                         "--gcthreads=1"])}.items():
                for value in values:
                    changed = copy.deepcopy(original)
                    changed[key] = value
                    with self.subTest(profile=profile, key=key,
                                      value=str(value)[:80]), \
                            self.assertRaises(ValueError):
                        s.validate_receipt(changed, profile, timeout=60)
            for timeout in (0, -1, True, None, float("inf"), float("nan")):
                with self.subTest(timeout=timeout), \
                        self.assertRaises(ValueError):
                    s.validate_receipt(original, profile, timeout=timeout)
            for key in original:
                changed = original.copy()
                del changed[key]
                with self.subTest(profile=profile, missing=key), \
                        self.assertRaises(ValueError):
                    s.validate_receipt(changed, profile, timeout=60)
            # A diverted run (valid-looking output from a different profile's
            # command line) is not accepted either.
            for other in PROFILES:
                if s.FLAGS[other] != s.FLAGS[profile]:
                    changed = copy.deepcopy(original)
                    changed["command"] = [changed["command"][0],
                                          *s.FLAGS[other]]
                    with self.assertRaises(ValueError):
                        s.validate_receipt(changed, profile, timeout=60)

    def test_compact32_is_rejected_and_normal_configuration_accepted(self):
        good = "#define HOSTARCHITECTURE_AARCH64 1\n"
        args = ["./configure", "--without-x", "--disable-compact32bit",
                "--enable-shared"]
        s.reject_compact32(good, args)
        s.reject_compact32(good + "/* #undef POLYML32IN64 */\n", args)
        for configuration, arguments, word_bytes in (
                (good + "#define POLYML32IN64 1\n", args, 8),
                (good + "  # define POLYML32IN64\n", args, 8),
                (good, ["./configure", "--enable-compact32bit"], 8),
                (good, ["./configure", "--without-x"], 8),
                (good, args + ["--enable-compact32bit"], 8),
                (good, args, 4), (good, "not a list", 8),
                (None, args, 8)):
            with self.subTest(configuration=configuration,
                              arguments=arguments), \
                    self.assertRaises(ValueError):
                s.reject_compact32(configuration, arguments, word_bytes)


if __name__ == "__main__":
    unittest.main()
