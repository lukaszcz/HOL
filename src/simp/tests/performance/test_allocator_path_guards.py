"""SYNTHETIC guard-by-guard tests of path_schema; NOT execution evidence.

test_allocator_paths.py corrupts whole protocols and mostly asks only that
something rejects. Here each corruption is built to be caught by ONE named
guard and the test pins that guard's message: weakening or deleting the
guard either lets the corruption through or sends it to a different guard
with a different message. All data is invented here; no allocator, process
or receipt is involved.
"""
import re
import unittest

import path_schema as s
from test_allocator_paths import PROFILES, receipt, synthetic

TAG = s.PREFIX
INTERP = "interpreter"
NATIVE = "native-rts"
FAILURE = "failure"
# Native words of one no-op bracket in each profile.
NOOP = {NATIVE: 4, INTERP: 31, FAILURE: 4}


def expect(test, profile, text, why):
    with test.assertRaisesRegex(ValueError, re.escape(why)):
        s.observations(text, profile)


def tamper(profile, kind, label, edit, side=None, **kwargs):
    """Synthetic text with edit(fields) applied to each record of the
    given kind (and side) for label; fields[0] is the record tag."""
    lines = synthetic(profile, **kwargs).splitlines()
    hits = 0
    for i, line in enumerate(lines):
        f = line.split("\t")
        if (f[0] == TAG + kind + "_V1" and len(f) > 1 and f[1] == label
                and (side is None or f[2] == side)):
            edit(f)
            lines[i] = "\t".join(f)
            hits += 1
    assert hits, (kind, label, side)
    return "\n".join(lines) + "\n"


def replace_line(profile, old, new, **kwargs):
    lines = synthetic(profile, **kwargs).splitlines()
    assert lines.count(old) == 1, old
    return "\n".join(new if x == old else x for x in lines) + "\n"


def change(raw=None, branch=None, result=None, path=()):
    """A row edit: replace the given vectors and set path[i] = v."""
    def apply(row):
        if raw is not None:
            row["raw"][:] = raw
        if branch is not None:
            row["branch"][:] = branch
        if result is not None:
            row["result"][:] = result
        for i, v in path:
            row["path"][i] = v
    return apply


def reject(test, profile, why, mutate):
    with test.subTest(profile=profile, why=why, labels=sorted(mutate)):
        expect(test, profile, synthetic(profile, mutate=mutate), why)


def accept(profile, mutate):
    return s.observations(synthetic(profile, mutate=mutate), profile)


def move(source, target):
    """Move one row's whole count from path[source] to path[target]."""
    def apply(row):
        row["path"][target] += row["path"][source]
        row["path"][source] = 0
    return apply


def only(rows, edit):
    return {label: edit for label in rows}


class RecordShapeGuards(unittest.TestCase):
    def test_numbers_helper(self):
        top = str(s.UINT64_MAX)
        self.assertEqual(s.numbers(["0", top], 2), [0, s.UINT64_MAX])
        for fields, count, why in (
                (["1"], 2, "malformed path numeric"),
                (["1", "2", "3"], 2, "malformed path numeric"),
                (["01"], 1, "malformed path numeric"),
                (["-1"], 1, "malformed path numeric"),
                ([""], 1, "malformed path numeric"),
                (["1" * 21], 1, "malformed path numeric"),
                (["18446744073709551616"], 1, "uint64 out of range")):
            with self.subTest(fields=fields), \
                    self.assertRaisesRegex(ValueError, why):
                s.numbers(fields, count)

    def test_compact32_guard(self):
        plain = "#define HOSTARCHITECTURE_AARCH64 1\n"
        off = ["--disable-compact32bit"]
        s.reject_compact32(plain, off)
        s.reject_compact32(plain, tuple(off))
        s.reject_compact32(plain + "#define POLYML32IN64X 1\n", off)
        s.reject_compact32(plain + "x #define POLYML32IN64 1\n", off)
        for configuration, arguments, kwargs, why in (
                (plain, "--disable-compact32bit", {}, "malformed compact32"),
                (plain.encode(), off, {}, "malformed compact32"),
                (plain, [], {}, "compact32 configuration rejected"),
                (plain, off + ["--enable-compact32bit"], {},
                 "compact32 configuration rejected"),
                (plain, off, dict(word_bytes=4),
                 "compact32 configuration rejected"),
                (plain + "#define POLYML32IN64 1\n", off, {},
                 "compact32 runtime configuration rejected"),
                (plain + "  #  define\tPOLYML32IN64\n", off, {},
                 "compact32 runtime configuration rejected")):
            with self.subTest(arguments=arguments, why=why), \
                    self.assertRaisesRegex(ValueError, why):
                s.reject_compact32(configuration, arguments, **kwargs)

    def test_unknown_profile_and_non_text_output(self):
        text = synthetic(FAILURE)
        with self.assertRaisesRegex(ValueError, "unknown path profile"):
            s.observations(text, "native")
        with self.assertRaisesRegex(ValueError, "merged text"):
            s.observations(text.encode(), FAILURE)

    def test_exhaustion_diagnostic_is_exact(self):
        for profile in (INTERP, FAILURE):
            for new in (s.EXHAUSTION + " ", " " + s.EXHAUSTION,
                        "Failed to recover", s.EXHAUSTION + "x"):
                lines = synthetic(profile).splitlines()
                lines[lines.index(s.EXHAUSTION)] = new
                expect(self, profile, "\n".join(lines) + "\n",
                       "malformed runtime exhaustion diagnostic")

    def test_scope_profile_abi_and_configuration_are_exact(self):
        for profile in PROFILES:
            lines = synthetic(profile).splitlines()
            for old, new, why in (
                    (lines[0], lines[0] + "x", "changed path scope"),
                    (lines[1], lines[1] + "x", "changed path profile"),
                    (TAG + "ABI_V1\t15", TAG + "ABI_V1\t16",
                     "path C ABI controls failed")):
                expect(self, profile,
                       "\n".join(new if x == old else x for x in lines)
                       + "\n", why)
            config = [x for x in lines if x.startswith(TAG + "CONFIG")][0]
            fields = config.split("\t")
            fields[2] = str(int(fields[2]) + 1)
            expect(self, profile,
                   "\n".join("\t".join(fields) if x == config else x
                             for x in lines) + "\n",
                   "changed path configuration")

    def test_runtime_identity_is_one_absolute_path_without_spaces(self):
        old = TAG + "RUNTIME_V1\t/synthetic/libpolyml.so.16"
        for profile in PROFILES:
            for new in (old + "\t/second",
                        old.replace("/synthetic/", "/syn thetic/"),
                        old.replace("/synthetic/", "/syn\u00a0thetic/"),
                        old.replace("\t/", "\t"),
                        TAG + "RUNTIME_V1"):
                with self.subTest(profile=profile, new=new):
                    expect(self, profile, replace_line(profile, old, new),
                           "malformed path runtime identity")

    def test_process_maps(self):
        old = (TAG + "MAP_V1\t100-200 r-xp 0000 00:00 1 "
               "/synthetic/libpolyml.so.16")
        for profile in PROFILES:
            for new in (old + "\textra",
                        old.replace("100-200", "zz-200"),
                        old.replace("r-xp", "r-xq"),
                        old.replace("00:00 1", "00:00 x"),
                        old.replace("00:00 1 /", "00:00 1x/")):
                with self.subTest(profile=profile, new=new):
                    expect(self, profile, replace_line(profile, old, new),
                           "malformed path process map")
            expect(self, profile, replace_line(profile, old, old + "\n" +
                                               old),
                   "duplicate path process map")
            expect(self, profile, replace_line(profile, old, ""),
                   "missing path process maps")
            # Two distinct maps and a map without a path are both fine.
            other = TAG + "MAP_V1\t300-400 rw-p 0000 00:00 0"
            self.assertEqual(s.observations(
                replace_line(profile, old, old + "\n" + other),
                profile)["maps"][1], other.split("\t")[1])

    def test_thread_inventory_shape_on_both_sides(self):
        # Start and end agree, so only the shape guard can reject these.
        for profile in PROFILES:
            for threads in (
                    [],
                    ["1"],
                    ["4", "a", "b", "c"],
                    ["3", "a", "b", "c", "d"],
                    ["04", "a", "b", "c", "d"],
                    ["0", "a"],
                    ["4", "d", "c", "b", "a"],
                    ["4", "a", "b", "c", "d e"],
                    ["4", "", "a", "b", "c"],
                    ["4", "a", "b", "c", "d" * 16]):
                with self.subTest(profile=profile, threads=threads):
                    expect(self, profile, synthetic(profile, threads=threads),
                           "malformed OS thread inventory")
            for text in (synthetic(profile).replace(
                    "THREADS_V1\tstart", "THREADS_V1\tbegin"),
                    synthetic(profile).replace(
                        "THREADS_V1\tend", "THREADS_V1\tstart")):
                expect(self, profile, text, "malformed OS thread inventory")
            names = ["4", "a", "b", "c", "d" * 15]
            self.assertEqual(s.observations(
                synthetic(profile, threads=names), profile)["threads"],
                names)
            expect(self, profile, synthetic(
                profile, threads_end=["4", "a", "b", "c", "e"]),
                "inventory changed")

    def test_limit_arithmetic_pinned_independently(self):
        h = s.LIMIT_HEADROOM
        top = s.UINT64_MAX
        good = [1, 4096, 4096 + h, top, h]
        for profile in (INTERP, FAILURE):
            self.assertEqual(s.observations(
                synthetic(profile, limit=good), profile)["limit"]["hard"],
                top)
            self.assertEqual(s.observations(synthetic(
                profile, limit=[1, 4096, 4096 + h, 4096 + h, h]),
                profile)["limit"]["hard"], 4096 + h)
            for limit in ([0, 4096, 4096 + h, top, h],
                          [1, 0, h, top, h],
                          [1, 4096, 4096 + h + 1, top, h],
                          [1, 4096, 4096 + h - 1, top, h],
                          [1, 4096, 4096 + h, 4096 + h - 1, h],
                          [1, 4096, 4097 + h, top, h + 1],
                          [1, 4096, 4095 + h, top, h - 1]):
                with self.subTest(profile=profile, limit=limit):
                    expect(self, profile, synthetic(profile, limit=limit),
                           "OS address-space limit")

    def test_request_record_is_the_recipe_entry(self):
        for profile in PROFILES:
            label = s.labels(profile)[5]
            for position in (1, 2, 3, 4):
                def poke(f, i=position):
                    f[i] = str(int(f[i]) + 1) if f[i].isdigit() else f[i] + "x"
                with self.subTest(profile=profile, position=position):
                    expect(self, profile,
                           tamper(profile, "REQUEST", label, poke),
                           "changed/reordered path request")
            expect(self, profile, tamper(
                profile, "REQUEST", label,
                lambda f: f.__delitem__(slice(1, None))),
                "changed/reordered path request")

    def test_truncation_after_the_request_of_an_exhausting_bracket(self):
        for profile, label in ((INTERP, "fail-16777216-1"),
                               (FAILURE, "rts-fail-1073741824-1")):
            text = synthetic(profile)
            at = text.index(TAG + "REQUEST_V1\t" + label)
            cut = text.index("\n", at) + 1
            expect(self, profile, text[:cut], "missing actual RTS exhaustion")
            without = text.replace(s.EXHAUSTION + "\n", "", 1)
            expect(self, profile, without, "missing actual RTS exhaustion")


class EndpointGuards(unittest.TestCase):
    def labels(self, profile):
        return s.labels(profile)[1]

    def test_record_labels_sides_and_arity(self):
        for profile in PROFILES:
            label = self.labels(profile)
            other = s.labels(profile)[2]
            records = [("ENDPOINT", "missing/reordered path endpoint"),
                       ("PENDPOINT",
                        "missing/reordered path-counter endpoint"),
                       ("RAW", "missing/reordered path raw"),
                       ("PATH", "missing/reordered path counter delta"),
                       ("RESULT", "missing/reordered result")]
            if profile == INTERP:
                records += [("BENDPOINT",
                             "missing/reordered branch endpoint"),
                            ("BRANCH", "missing/reordered branch delta")]
            for kind, why in records:
                two = kind in ("ENDPOINT", "PENDPOINT", "BENDPOINT")

                def relabel(f):
                    f[1] = other
                with self.subTest(profile=profile, kind=kind, field="label"):
                    expect(self, profile,
                           tamper(profile, kind, label, relabel), why)
                if two:
                    def reside(f):
                        f[2] = "middle"
                    with self.subTest(profile=profile, kind=kind,
                                      field="side"):
                        expect(self, profile,
                               tamper(profile, kind, label, reside), why)
                with self.subTest(profile=profile, kind=kind, field="empty"):
                    expect(self, profile, tamper(
                        profile, kind, label,
                        lambda f: f.__delitem__(slice(1, None))), why)

    def test_endpoint_abi_and_category_sum(self):
        for profile in PROFILES:
            label = self.labels(profile)
            for position in (3, 4, 5):
                def poke(f, i=position):
                    f[i] = str(int(f[i]) + 1)
                for side in ("start", "end"):
                    with self.subTest(profile=profile, i=position,
                                      side=side):
                        expect(self, profile, tamper(
                            profile, "ENDPOINT", label, poke, side),
                            "path ABI/word-size/overflow mismatch")

            def total(f):
                f[6] = str(int(f[6]) + 1)
            for side in ("start", "end"):
                expect(self, profile, tamper(
                    profile, "ENDPOINT", label, total, side),
                    "category sum mismatch")

    def test_path_endpoint_abi_reserved_and_foreign_thread(self):
        for profile in PROFILES:
            label = self.labels(profile)
            for position in (3, 4, 5, -1):
                def poke(f, i=position):
                    f[i] = str(int(f[i]) + 1)
                for side in ("start", "end"):
                    with self.subTest(profile=profile, i=position,
                                      side=side):
                        expect(self, profile, tamper(
                            profile, "PENDPOINT", label, poke, side),
                            "path ABI/overflow/reserved mismatch")

            def foreign(f):
                f[6 + s.FOREIGN_THREAD] = "1"
            for side in ("start", "end", None):
                with self.subTest(profile=profile, side=side):
                    expect(self, profile, tamper(
                        profile, "PENDPOINT", label, foreign, side),
                        "not created by the runtime")

    def test_branch_endpoint_abi(self):
        label = s.labels(INTERP)[1]
        for position in (3, 4, 5, -1):
            def poke(f, i=position):
                f[i] = str(int(f[i]) + 1)
            for side in ("start", "end"):
                with self.subTest(i=position, side=side):
                    expect(self, INTERP, tamper(
                        INTERP, "BENDPOINT", label, poke, side),
                        "branch ABI/overflow/reserved mismatch")

    def test_raw_counters_are_monotonic_across_and_within_brackets(self):
        for profile in PROFILES:
            label = self.labels(profile)

            def below_previous(f):
                for i in (6, 7):
                    f[i] = str(int(f[i]) - 4)
            expect(self, profile,
                   tamper(profile, "ENDPOINT", label, below_previous),
                   "path raw counter not process-monotonic")

            def end_below_start(f):
                for i in (6, 7):
                    f[i] = str(int(f[i]) - NOOP[profile] - 1)
            expect(self, profile,
                   tamper(profile, "ENDPOINT", label, end_below_start,
                          "end"),
                   "path raw counter not process-monotonic")

    def test_path_counters_are_monotonic_across_and_within_brackets(self):
        for profile in PROFILES:
            label = self.labels(profile)

            def below(f):
                f[6] = str(int(f[6]) - 1)
            expect(self, profile,
                   tamper(profile, "PENDPOINT", label, below),
                   "path counter not process-monotonic")
            expect(self, profile,
                   tamper(profile, "PENDPOINT", label, below, "end"),
                   "path counter not process-monotonic")

    def test_deltas_equal_their_endpoints(self):
        def swap(f):
            f[3], f[4] = f[4], f[3]
        for profile in PROFILES:
            label = s.labels(profile)[5]
            row = {NATIVE: "native-4096-0-1", INTERP: "loop-4096-1000-1",
                   FAILURE: "rts-ok-before-1"}[profile]
            expect(self, profile, tamper(profile, "RAW", row, swap),
                   "path raw delta/endpoint mismatch")

            def bump(f):
                f[2] = str(int(f[2]) + 1)
            expect(self, profile, tamper(profile, "PATH", label, bump),
                   "path delta/endpoint mismatch")
        expect(self, INTERP, tamper(
            INTERP, "BRANCH", "loop-4096-1000-1",
            lambda f: f.__setitem__(2, str(int(f[2]) + 1))),
            "branch delta/endpoint mismatch")

    def test_numeric_arity_of_deltas_and_results(self):
        for profile in PROFILES:
            label = s.labels(profile)[5]
            for kind in ("RAW", "PATH", "RESULT"):
                with self.subTest(profile=profile, kind=kind):
                    expect(self, profile, tamper(
                        profile, kind, label, lambda f: f.append("0")),
                        "malformed path numeric")
                    expect(self, profile, tamper(
                        profile, kind, label, lambda f: f.pop()),
                        "malformed path numeric")

    def test_trailer_records(self):
        for profile in PROFILES:
            lines = synthetic(profile).splitlines()
            for prefix, why in ((TAG + "UNCLAIMED", "changed path limit"),
                                (TAG + "COMPLETE", "wrong path completion")):
                text = "\n".join(x + "x" if x.startswith(prefix) else x
                                for x in lines) + "\n"
                expect(self, profile, text, why)
            expect(self, profile, "\n".join(lines) + "\n" + lines[0] + "\n",
                   "path data after completion")


class StructuralGuards(unittest.TestCase):
    def test_rts_path_words_equal_raw_rts_words(self):
        for profile in PROFILES:
            reject(self, profile, "RTS path words differ", {
                "noop-before-2": change(path=[(s.WORDS[1], 1)])})

    def test_native_path_words_cannot_exceed_raw_native_words(self):
        for profile in PROFILES:
            reject(self, profile, "native path words exceed", {
                "noop-before-2": change(path=[(s.WORDS[0],
                                               NOOP[profile] + 1)])})

    def test_large_object_cells_of_alwaysinseg_callers_are_zero(self):
        for profile in PROFILES:
            for index in s.LARGE_UNREACHABLE:
                reject(self, profile, "alwaysInSeg caller", {
                    "noop-before-2": change(path=[(index, 1)])})
        self.assertEqual(s.LARGE_UNREACHABLE, (2, 3, 14, 15))

    def test_interpreter_branch_identities(self):
        for edit, why in (
                (change(path=[(s.WORDS[2], 1)]),
                 "path words differ from branch slow words"),
                (change(path=[(12, 1)]),
                 "path events differ from branch slow count"),
                (change(path=[(17, 1)]),
                 "path events differ from branch slow count"),
                (lambda row: row["branch"].__setitem__(
                    1, row["branch"][1] + 1),
                 "raw words differ from branch words"),
                (lambda row: row["branch"].__setitem__(0, 10**6),
                 "below branch event count")):
            reject(self, INTERP, why, {"noop-before-2": edit})

    def test_non_interpreter_profiles_have_no_interpreter_events(self):
        for profile in (NATIVE, FAILURE):
            # 14 and 15 are the alwaysInSeg cells, rejected earlier.
            for index in (12, 13, 16, 17):
                reject(self, profile, "unexpected interpreter path success",
                       {"noop-before-2": change(path=[(index, 1)])})
            for index in (s.INTERP_FAIL, s.WORDS[2]):
                reject(self, profile, "unexpected interpreter path failure",
                       {"noop-before-2": change(path=[(index, 1)])})


class NativeRtsControlGuards(unittest.TestCase):
    def test_idle_baseline_is_purely_native_and_nonzero(self):
        for raw in ([0, 0, 0, 0, 0], [0, 0, 5, 0, 0], [0, 0, 0, 0, 5],
                    [0, 0, 0, 5, 0]):
            path = [(s.WORDS[1], raw[2])]
            reject(self, NATIVE, "native no-op wrapper is not purely native",
                   {"noop-before-1": change(raw=raw, path=path)})

    def test_failure_counters_in_successful_controls(self):
        for index in (18, 19, 22, 23):
            for label in ("noop-before-2", "native-4096-0-1",
                          "rts-262144-1-1", "large-8-1048576-1"):
                reject(self, NATIVE, "failure path counter in a success",
                       {label: change(path=[(index, 1)])})

    def test_outcomes_and_slopes(self):
        for label, result in (("noop-before-2", [1, 0, 1, 2]),
                              ("native-4096-0-1", [1, 1, 1, 1]),
                              ("rts-262144-1-1", [1, 1, 1, 1]),
                              ("large-8-1048576-1", [1, 1, 1, 1])):
            reject(self, NATIVE, "wrong path outcome",
                   {label: change(result=result)})
        base = 4 + 4096
        for raw, path in (
                ([base + 1, base + 1, 0, 0, 0], []),
                ([base, base - 1, 0, 0, 1], []),
                ([base + 1, base, 0, 1, 0], []),
                ([base + 1, base, 1, 0, 0], [(s.WORDS[1], 1)])):
            reject(self, NATIVE, "exact native payload slope", {
                "native-4096-0-1": change(raw=raw, path=path)})
        w = 262144 * 3
        reject(self, NATIVE, "exact RTS payload slope", {
            "rts-262144-1-1": change(raw=[4 + w + 1, 4, w + 1, 0, 0],
                                     path=[(s.WORDS[1], w + 1)])})
        reject(self, NATIVE, "RTS path event in native control", {
            "native-4096-0-1": change(path=[(6, 1)])})
        reject(self, NATIVE, "retry successes not counted exactly once", {
            "rts-262144-1-1": lambda row: row["path"].__setitem__(
                6, row["path"][6] - 1)})

    def test_noop_brackets_cost_exactly_the_baseline(self):
        reject(self, NATIVE, "no-op path/raw costs differ", {
            "noop-before-2": change(path=[(0, 1)])})
        reject(self, NATIVE, "no-op path/raw costs differ", {
            "noop-final-1": change(raw=[5, 5, 0, 0, 0])})
        # Warm-up brackets are exempt.
        accept(NATIVE, {"noop-warmup-2": change(raw=[9, 9, 0, 0, 0])})
        accept(NATIVE, {"noop-warmup-1": change(path=[(0, 1)])})

    def test_branch_requirements_one_condition_at_a_time(self):
        for label, edit, why in (
                ("native-4096-1024-1", change(path=[(4, 0)]),
                 "native control missed the refill branch"),
                ("native-32768-1024-1", change(path=[(4, 0)]),
                 "native control missed the refill branch"),
                ("native-32768-1024-1", move(5, 4),
                 "native control missed success-after-GC"),
                ("native-32768-1024-1", change(path=[(21, 0)]),
                 "native control missed success-after-GC"),
                ("native-4096-1024-1", change(path=[(5, 1), (21, 0)]),
                 "success-after-GC without a successful QuickGC"),
                ("rts-262144-1-1", move(10, 6),
                 "RTS control missed the refill branch"),
                ("rts-262144-101-1", move(10, 6),
                 "RTS control missed refill/after-GC"),
                ("rts-262144-101-1", move(11, 6),
                 "RTS control missed refill/after-GC"),
                ("rts-262144-101-1", change(path=[(21, 0)]),
                 "RTS control missed refill/after-GC"),
                ("rts-262144-1-1", lambda row: (
                    move(6, 11)(row), row["path"].__setitem__(21, 0)),
                 "success-after-GC without a successful QuickGC"),
                ("large-64-1048576-1", move(9, 8),
                 "large-object control missed success-after-GC"),
                ("large-64-1048576-1", change(path=[(21, 0)]),
                 "large-object control missed success-after-GC"),
                ("large-8-1048576-1", change(path=[(21, 0)]),
                 "success-after-GC without a successful QuickGC"),
                ("large-8-1048576-1", move(8, 6),
                 "wrong large-object area count"),
                ("rts-262144-1-1", move(6, 8),
                 "wrong large-object area count")):
            reject(self, NATIVE, why, {label: edit})

    def test_a_large_object_is_requested_on_a_first_attempt_somewhere(self):
        def after_only(row):
            total = row["path"][8] + row["path"][9]
            row["path"][8], row["path"][9], row["path"][21] = 0, total, 1
        labels = [x for x in s.labels(NATIVE) if x.startswith("large-")]
        self.assertEqual(len(labels), 4)
        reject(self, NATIVE, "missing first-attempt large-object",
               only(labels, after_only))
        # One first-attempt row is enough.
        accept(NATIVE, only(labels[1:], after_only))


class InterpreterControlGuards(unittest.TestCase):
    def test_idle_baseline_and_attempt_wrapper(self):
        for raw in ([0, 0, 0, 0, 0], [0, 0, 5, 0, 0], [0, 0, 0, 0, 5]):
            reject(self, INTERP,
                   "interpreter entry no-op is not purely native", {
                       "noop-before-1": change(
                           raw=raw, path=[(s.WORDS[1], raw[2])])})
        why = "interpreted attempt wrapper is not purely interpreter"
        for raw, branch, path in (
                ([50, 32, 0, 18, 0], None, []),
                ([50, 31, 1, 18, 0], None, [(s.WORDS[1], 1)]),
                ([31, 31, 0, 0, 0], [0, 0, 0, 0], []),
                ([50, 31, 0, 18, 1], None, [])):
            reject(self, INTERP, why, {"attempt-noop-1": change(
                raw=raw, branch=branch, path=path)})

    def test_non_warmup_brackets_allocate_interpreter_words_only(self):
        why = "native/RTS/code words in interpreter control"
        for raw, path in (([35, 35, 0, 0, 0], []),
                          ([35, 31, 4, 0, 0], [(s.WORDS[1], 4)]),
                          ([35, 31, 0, 0, 4], [])):
            reject(self, INTERP, why,
                   {"noop-before-2": change(raw=raw, path=path)})
        accept(INTERP, {"noop-warmup-1": change(raw=[35, 35, 0, 0, 0])})
        accept(INTERP, {"noop-warmup-2": change(raw=[35, 31, 4, 0, 0],
                                                path=[(s.WORDS[1], 4)])})

    def test_noop_brackets(self):
        reject(self, INTERP, "wrong no-op result", {
            "noop-before-2": change(result=[1, 0, 1])})
        reject(self, INTERP, "no-op path/raw costs differ", {
            "noop-before-2": change(path=[(0, 1)])})
        reject(self, INTERP, "no-op path/raw costs differ", {
            "noop-before-2": change(raw=[32, 31, 0, 1, 0],
                                    branch=[1, 1, 0, 0])})
        accept(INTERP, {"noop-warmup-1": change(path=[(0, 1)])})
        for index in (18, 19, 20, 22, 23):
            reject(self, INTERP, "failure counter in a no-op", {
                "noop-warmup-1": change(path=[(index, 1)])})

    def test_loop_payload_and_failure_counters(self):
        reject(self, INTERP, "exact interpreter payload slope", {
            "loop-4096-1000-1": lambda row: (
                row["raw"].__setitem__(3, row["raw"][3] + 1),
                row["branch"].__setitem__(1, row["branch"][1] + 1))})
        reject(self, INTERP, "exact interpreter payload slope", {
            "loop-4096-1000-1": change(result=[1, 1001, 1])})
        for index in (18, 19, 20, 22, 23):
            for label in ("loop-4096-0-1", "ok-before-1",
                          "recover-16777216-1"):
                reject(self, INTERP, "failure counter in a successful", {
                    label: change(path=[(index, 1)])})

    def test_slow_path_requirements_one_condition_at_a_time(self):
        def one_slow(row):
            row["branch"][:] = [4095, 4095, 1, 1]
            row["path"][16] = row["path"][s.WORDS[2]] = 1
        reject(self, INTERP, "unexpected slow events",
               {"loop-4096-0-1": one_slow})
        reject(self, INTERP, "interpreter control missed the refill", {
            "loop-4096-1000-1": move(16, 12)})
        reject(self, INTERP, "missed success-after-GC", {
            "loop-32768-1000-1": move(17, 16)})
        reject(self, INTERP, "missed success-after-GC", {
            "loop-32768-1000-1": change(path=[(21, 0)])})
        reject(self, INTERP, "missed success-after-GC", {
            "loop-64-2097152-1": move(17, 16)})
        reject(self, INTERP, "missed success-after-GC", {
            "loop-64-2097152-1": change(path=[(21, 0)])})
        reject(self, INTERP, "without a successful QuickGC", {
            "loop-4096-1000-1": lambda row: (
                row["path"].__setitem__(17, 1),
                row["path"].__setitem__(16, row["path"][16] - 1),
                row["path"].__setitem__(21, 0))})

    def test_single_array_loops(self):
        def two_slow(row):
            row["branch"][2] = 2
            row["path"][16] = 2
        reject(self, INTERP, "more slow events than requests", {
            "loop-1-100000-1": two_slow})

        def no_slow(row):
            n = row["raw"][3]
            row["branch"][:] = [1, n, 0, 0]
            row["path"][16] = row["path"][s.WORDS[2]] = 0
        singles = [x for x in s.labels(INTERP)
                   if x.startswith(("loop-1-100000", "loop-1-200000"))]
        self.assertEqual(len(singles), 4)
        reject(self, INTERP, "missing single-array slow-path coverage",
               only(singles, no_slow))
        accept(INTERP, only(singles[1:], no_slow))

    def test_attempt_wrapper_repeats_exactly(self):
        for label in ("attempt-noop-2", "attempt-noop-final"):
            for edit in (change(raw=[50, 31, 0, 19, 0],
                                branch=[6, 19, 0, 0]),
                         change(branch=[5, 18, 0, 0]),
                         change(path=[(0, 1)]),
                         change(result=[1, 1, 1])):
                reject(self, INTERP, "attempt wrapper costs differ",
                       {label: edit})

    def test_recovery_rows_are_exactly_one_slope(self):
        reject(self, INTERP, "exact recovery/slope mismatch", {
            "ok-before-1": lambda row: (
                row["raw"].__setitem__(3, row["raw"][3] + 1),
                row["branch"].__setitem__(1, row["branch"][1] + 1))})
        reject(self, INTERP, "exact recovery/slope mismatch", {
            "recover-16777216-1": change(result=[1, 1001, 1])})

    def test_failed_request_is_exactly_one_failure(self):
        why = "failure is not exactly one interpreter"
        for path in ([(22, 0)], [(20, 0)], [(0, 1)]):
            reject(self, INTERP, why, {
                "fail-16777216-1": change(path=path)})
        why = "failed request charged/changed raw or branch costs"
        reject(self, INTERP, why, {"fail-16777216-1": change(
            raw=[50, 31, 0, 19, 0], branch=[6, 19, 0, 0])})
        reject(self, INTERP, why, {
            "fail-16777216-1": change(branch=[5, 18, 0, 0])})
        reject(self, INTERP, "wrong failed outcome/entry", {
            "fail-16777216-1": change(result=[3, 0, 1])})


class FailureControlGuards(unittest.TestCase):
    def test_baselines(self):
        why = "native no-op wrapper is not purely native"
        for raw in ([0, 0, 0, 0, 0], [0, 0, 5, 0, 0], [0, 0, 0, 0, 5]):
            reject(self, FAILURE, why, {"noop-before-1": change(
                raw=raw, path=[(s.WORDS[1], raw[2])])})
        reject(self, FAILURE, "manual interrupt wrapper below native", {
            "manual-before-1": change(raw=[3, 3, 0, 0, 0])})
        reject(self, FAILURE, "manual interrupt wrapper below native", {
            "manual-before-1": change(raw=[4, 3, 1, 0, 0],
                                      path=[(s.WORDS[1], 1)])})

    def test_compiler_control_allocates_native_and_code_words_only(self):
        why = "compiler control does not allocate native and code words"
        for raw, path in (([38, 0, 0, 0, 38], []),
                          ([29860, 29860, 0, 0, 0], []),
                          ([29903, 29860, 5, 0, 38], [(s.WORDS[1], 5)]),
                          ([29899, 29860, 0, 1, 38], [])):
            reject(self, FAILURE, why, {"compile-before-1": change(
                raw=raw, path=path)})

    def test_same_packet_control_allocates_rts_words_only(self):
        why = "same-packet control does not allocate only"
        for raw, path in (([4, 4, 0, 0, 0], [(s.WORDS[1], 0)]),
                          ([29, 4, 24, 1, 0], []),
                          ([29, 4, 24, 0, 1], [])):
            reject(self, FAILURE, why, {"code-ctl-before-1": change(
                raw=raw, path=path)})

    def test_every_row_is_free_of_interpreter_words(self):
        reject(self, FAILURE, "interpreter event in failure control", {
            "noop-warmup-1": change(raw=[5, 4, 0, 1, 0])})

    def test_noop_manual_and_compile_rows(self):
        reject(self, FAILURE, "wrong no-op result", {
            "noop-before-2": change(result=[1, 0, 2])})
        reject(self, FAILURE, "raw native no-op costs differ", {
            "noop-before-2": change(path=[(0, 1)])})
        reject(self, FAILURE, "raw native no-op costs differ", {
            "noop-final-1": change(raw=[5, 5, 0, 0, 0])})
        accept(FAILURE, {"noop-warmup-1": change(path=[(0, 1)])})
        reject(self, FAILURE, "wrong manual outcome", {
            "manual-before-2": change(result=[1, 0, 1])})
        reject(self, FAILURE, "prebuilt interrupt raw costs differ", {
            "manual-before-2": change(path=[(0, 1)])})
        reject(self, FAILURE, "prebuilt interrupt raw costs differ", {
            "manual-before-2": change(raw=[5, 5, 0, 0, 0])})
        accept(FAILURE, {"manual-warmup-1": change(raw=[9, 9, 0, 0, 0])})
        reject(self, FAILURE, "compiler raw costs differ", {
            "compile-after-335544320-1": change(
                raw=[29899, 29861, 0, 0, 38])})
        reject(self, FAILURE, "compiler raw costs differ", {
            "compile-final": change(result=[1, 0, 2])})
        for index in (18, 19, 22, 23):
            reject(self, FAILURE, "failure counter in a successful compile",
                   {"compile-final": change(path=[(index, 1)])})

    def test_rts_recovery_rows(self):
        reject(self, FAILURE, "exact RTS recovery slope mismatch", {
            "rts-ok-before-1": change(raw=[8, 4, 4, 0, 0],
                                      path=[(s.WORDS[1], 4)])})
        reject(self, FAILURE, "wrong RTS recovery outcome", {
            "rts-ok-before-1": change(result=[1, 64 * 3, 1])})
        reject(self, FAILURE, "not exactly one reservation", {
            "rts-ok-before-1": change(path=[(6, 2)])})
        reject(self, FAILURE, "not exactly one reservation", {
            "rts-ok-before-1": change(path=[(6, 0)])})
        for index in (18, 19, 22, 23):
            reject(self, FAILURE, "failure counter in a successful RTS", {
                "rts-ok-before-1": change(path=[(index, 1)])})

    def test_native_recovery_rows(self):
        label = "native-ok-16777216-1"
        reject(self, FAILURE, "exact native recovery slope", {
            label: change(raw=[1006, 1006, 0, 0, 0])})
        reject(self, FAILURE, "wrong native recovery outcome", {
            label: change(result=[1, 1001, 1])})
        for index in (18, 19, 22, 23):
            reject(self, FAILURE, "failure counter in a successful native", {
                label: change(path=[(index, 1)])})

    def test_failed_requests_are_exactly_one_failure(self):
        for label, why in (
                ("rts-fail-1073741824-1", "failure is not exactly one RTS"),
                ("native-fail-16777216-1",
                 "failure is not exactly one native")):
            reject(self, FAILURE, why, {label: change(path=[(0, 1)])})
        reject(self, FAILURE, "failure is not exactly one RTS", {
            "rts-fail-1073741824-1": change(path=[(22, 0)])})
        reject(self, FAILURE, "failed RTS request charged", {
            "rts-fail-1073741824-1": change(raw=[5, 5, 0, 0, 0])})
        reject(self, FAILURE, "failed RTS request charged", {
            "rts-fail-1073741824-1": change(result=[3, 0, 1])})
        reject(self, FAILURE, "failed native request charged", {
            "native-fail-16777216-1": change(raw=[5, 5, 0, 0, 0])})
        reject(self, FAILURE, "failed native request charged", {
            "native-fail-16777216-1": change(result=[3, 0, 1])})

    def test_native_failure_admits_at_most_one_refill(self):
        why = "failure is not exactly one native"
        label = "native-fail-16777216-1"
        for refills, words in ((2, 2), (1, 0), (0, 2)):
            reject(self, FAILURE, why, {label: change(
                path=[(4, refills), (s.WORDS[0], words)])})
        for refills, words in ((0, 0), (1, 2), (1, 4)):
            accept(FAILURE, {label: change(
                path=[(4, refills), (s.WORDS[0], words)])})

    def test_code_space_rows(self):
        for label in ("code-ctl-limited-1", "code-ctl-before-2"):
            reject(self, FAILURE, "wrong same-packet outcome", {
                label: change(result=[3, 0, 1])})
            reject(self, FAILURE, "same-packet control costs differ", {
                label: change(raw=[29, 4, 25, 0, 0],
                              path=[(s.WORDS[1], 25)])})
            for index in (18, 19, 22, 23):
                reject(self, FAILURE, "failure counter in the same-packet", {
                    label: change(path=[(index, 1)])})
        label = "code-fail-335544320-1"
        for path in ([(23, 0)], [(23, 2)], [(18, 1)], [(19, 1)],
                     [(21, 1)], [(22, 1)]):
            reject(self, FAILURE, "not exactly one code-space allocation", {
                label: change(path=path)})
        reject(self, FAILURE, "wrong code failure outcome", {
            label: change(result=[4, 0, 1])})
        reject(self, FAILURE, "not charged as the same-size exception", {
            label: change(raw=[33, 4, 24, 0, 5])})
        reject(self, FAILURE, "not charged as the same-size exception", {
            label: change(raw=[29, 4, 25, 0, 0],
                          path=[(s.WORDS[1], 25)])})


class ReceiptInputGuards(unittest.TestCase):
    def test_unknown_profile(self):
        with self.assertRaisesRegex(ValueError, "unknown path profile"):
            s.validate_receipt(receipt(FAILURE), "native", timeout=60)

    def test_timeout_must_be_finite_and_positive(self):
        for timeout in (0, -1, float("inf"), float("nan"), "60", None):
            with self.subTest(timeout=timeout), self.assertRaisesRegex(
                    ValueError, "finite positive"):
                s.validate_receipt(receipt(FAILURE), FAILURE,
                                   timeout=timeout)

    def test_receipt_must_be_a_mapping(self):
        for value in (None, [], "text"):
            with self.assertRaisesRegex(ValueError,
                                        "missing path process receipt"):
                s.validate_receipt(value, FAILURE, timeout=60)

    def test_command_is_one_absolute_executable_and_exact_flags(self):
        base = receipt(FAILURE)
        flags = list(s.FLAGS[FAILURE])
        for command in ([5] + flags, [None] + flags, ["rel/exe"] + flags,
                        ["/x"] + flags[:-1], ["/x"] + flags + ["--more"],
                        ["/x"] + flags[::-1], "/x -H 32 --gcthreads=1",
                        None):
            with self.subTest(command=command), self.assertRaisesRegex(
                    ValueError, "path process needs exactly"):
                s.validate_receipt(dict(base, command=command), FAILURE,
                                   timeout=60)

    def test_process_must_have_succeeded(self):
        base = receipt(FAILURE)
        for edit in (dict(exit=1), dict(exit=None), dict(exit=True),
                     dict(exit=0.0), dict(timed_out=True),
                     dict(timed_out=None), dict(timed_out=0)):
            with self.subTest(edit=edit), self.assertRaisesRegex(
                    ValueError, "failed/timed-out"):
                s.validate_receipt(dict(base, **edit), FAILURE, timeout=60)

    def test_output_is_text_and_sealed(self):
        base = receipt(FAILURE)
        with self.assertRaisesRegex(ValueError, "missing merged"):
            s.validate_receipt(dict(base, stdout=None), FAILURE, timeout=60)
        for edit in (dict(stdout_bytes=base["stdout_bytes"] + 1),
                     dict(stdout_bytes=str(base["stdout_bytes"])),
                     dict(stdout_bytes=True),
                     dict(stdout_sha256="0" * 64),
                     dict(stdout_sha256=None)):
            with self.subTest(edit=edit), self.assertRaisesRegex(
                    ValueError, "seal mismatch"):
                s.validate_receipt(dict(base, **edit), FAILURE, timeout=60)


if __name__ == "__main__":
    unittest.main()
