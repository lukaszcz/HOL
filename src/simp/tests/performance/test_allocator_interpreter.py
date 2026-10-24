"""Synthetic interpreter-protocol tests, NOT executed allocation evidence.

No build, compiler bootstrap, runtime invocation or benchmark is launched.
These made-up counters intentionally give interpreted FFI a nonzero overhead
that differs from work's zero-size overhead. Only real separately sealed runs
can establish that the pinned hybrid runtime actually passes this protocol.
"""
import unittest

import interpreter_schema as s


def synthetic(overrides=None):
    """Invent consistent endpoint records for validator tests ONLY."""
    overrides = overrides or {}
    lines = []

    def emit(kind, *values):
        lines.append("\t".join([s.PREFIX + kind + "_V1", *map(str, values)]))

    def result(label, kind, n):
        checksum = n*(n+1)//2 if kind == "refs" else 37*n
        emit("RESULT", label, kind, n, checksum)

    emit("SCOPE", s.SCOPE)
    emit("BOOTSTRAP", *s.BOOTSTRAP)
    emit("RUNTIME", "/synthetic/libpolyml.so.16")
    emit("MAP", "100-200 r-xp 0000 00:00 1 /synthetic/libpolyml.so.16")
    emit("ABI", 15)
    emit("CONFIG", *s.CONFIG)
    counter = [1000, 100, 200, 600, 100]
    for label in s.LABELS:
        delta = [17, 3, 2, 12, 0]
        if label.startswith("gc-"):
            delta = [29, 5, 3, 21, 0]
        if label in s.WORK:
            kind, n = s.WORK[label]
            delta = ([41+5*n, 7, 4, 30+5*n, 0] if kind == "refs"
                     else [43+n, 9, 3, 31+n, 0])
        delta = overrides.get(label, delta)
        end = [a+b for a, b in zip(counter, delta)]
        for side, values in (("start", counter), ("end", end)):
            emit("ENDPOINT", label, side, 1, 8, 0, *values)
        emit("RAW", label, *delta)
        # Formatting/decoding/consumption outside the bracket also allocate.
        counter = [a+b for a, b in zip(end, [21, 6, 4, 9, 2])]
        if label in s.WORK:
            result(label, *s.WORK[label])
        if label == "gc-live-2":
            for kind in s.KINDS:
                result("after-live-gc", kind, 32)
    emit("UNCLAIMED", s.UNCLAIMED)
    emit("COMPLETE", len(s.LABELS))
    return "\n".join(lines) + "\n"


class InterpreterSchemaTests(unittest.TestCase):
    def test_complete_synthetic_protocol(self):
        result = s.observations(synthetic())
        self.assertEqual(result["brackets"], 31)
        self.assertEqual(len(result["endpoints"]), 62)
        self.assertEqual(len(result["results"]), 22)
        self.assertEqual(result["bootstrap"], s.BOOTSTRAP)
        self.assertEqual(result["no_op_words"], [17, 3, 2, 12, 0])
        self.assertEqual(result["deltas"]["refs-32-1"], [201, 7, 4, 190, 0])
        self.assertEqual(result["deltas"]["words-32-1"], [75, 9, 3, 63, 0])
        self.assertEqual(result["results"][-2:], [
            ("after-live-gc", "refs", 32, 528),
            ("after-live-gc", "words", 32, 1184)])

    def test_every_record_is_required_and_unique(self):
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            for changed in (lines[:i]+lines[i+1:],
                            lines[:i]+[line]+lines[i:]):
                with self.subTest(i=i, line=line), \
                        self.assertRaises(ValueError):
                    s.observations("\n".join(changed))

    def test_every_adjacent_reordering_is_rejected(self):
        lines = synthetic().splitlines()
        for i in range(len(lines)-1):
            changed = lines.copy()
            changed[i], changed[i+1] = changed[i+1], changed[i]
            with self.subTest(i=i), self.assertRaises(ValueError):
                s.observations("\n".join(changed))

    def test_unknown_exception_version_and_cross_protocol_rejected(self):
        text = synthetic()
        bad = [text.replace("_V1", "_V2", 1),
               text.replace(s.PREFIX + "RAW", s.PREFIX + "DELTA", 1),
               text + s.PREFIX + "FUTURE_V1\t1\n",
               s.PREFIX + "EXCEPTION_V1\tfailed\n" + text,
               text.replace(s.PREFIX + "ENDPOINT", "@@TASK29_ALLOC_ENDPOINT"),
               text.replace(s.PREFIX + "ENDPOINT", "@@TASK29_WORKER_ENDPOINT"),
               text + "@@TASK29_INTERPRETERbroken\n"]
        for value in bad:
            with self.subTest(value=value[:100]), \
                    self.assertRaises(ValueError):
                s.observations(value)
        self.assertEqual(s.observations("ordinary testutils chatter\n" + text),
                         s.observations(text))

    def test_every_numeric_field_is_canonical_bounded_uint64(self):
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            p = line.split("\t")
            kind = p[0].removeprefix(s.PREFIX)
            first = {"ABI_V1": 1, "CONFIG_V1": 1, "ENDPOINT_V1": 3,
                     "RAW_V1": 2, "RESULT_V1": 3,
                     "COMPLETE_V1": 1}.get(kind)
            if first is None:
                continue
            for j in range(first, len(p)):
                for value in ("-1", "+1", "01", "1.0", "", " 1", "1 ",
                              str(2**64), "9"*100):
                    changed = lines.copy()
                    q = p.copy()
                    q[j] = value
                    changed[i] = "\t".join(q)
                    with self.subTest(i=i, j=j, value=value), \
                            self.assertRaises(ValueError):
                        s.observations("\n".join(changed))

    def test_each_numeric_field_change_is_rejected(self):
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            p = line.split("\t")
            for j in range(1, len(p)):
                if not p[j].isdigit():
                    continue
                changed = lines.copy()
                q = p.copy()
                q[j] = str(int(q[j])+1)
                changed[i] = "\t".join(q)
                with self.subTest(i=i, j=j), self.assertRaises(ValueError):
                    s.observations("\n".join(changed))

    def test_changed_scope_recipe_identity_limits_and_shapes(self):
        text = synthetic()
        for old, new in ((s.SCOPE, "full allocator validation"),
                         (s.UNCLAIMED, "nothing unverified"),
                         ("RootInterpreted.ML", "RootArm64.ML"),
                         ("initGlobalEnv:false", "initGlobalEnv:true"),
                         ("BuildBasis.sml", "NotBuildBasis.sml"),
                         ("1\t8\t0", "1\t4\t0"),
                         ("1\t8\t0", "1\t8\t1"),
                         ("1\t8\t0", "2\t8\t0"),
                         ("RUNTIME_V1\t/", "RUNTIME_V1\t"),
                         ("MAP_V1\t100-200", "MAP_V1\tbad-map"),
                         ("COMPLETE_V1\t31", "COMPLETE_V1\t31\textra"),
                         ("RAW_V1\trefs-0-1", "RAW_V1\trefs-0-1\textra"),
                         ("RESULT_V1\trefs-1-1\trefs",
                          "RESULT_V1\trefs-1-1\twords")):
            self.assertIn(old, text)
            with self.subTest(old=old), self.assertRaises(ValueError):
                s.observations(text.replace(old, new, 1))

    def test_coherent_positive_wrong_slope_and_category_rejected(self):
        base = s.observations(synthetic())["deltas"]
        for kind in s.KINDS:
            for n in (1, 16, 32):
                for repeats in ((1,), (1, 2)):
                    label = f"{kind}-{n}-1"
                    d = base[label]
                    words = (5 if kind == "refs" else 1)*n
                    for category in (1, 2, 4):
                        # Preserve total and all endpoint sums; misattribute
                        # exactly the real workload slope to another category.
                        wrong = d.copy()
                        wrong[3] -= words
                        wrong[category] += words
                        changes = {f"{kind}-{n}-{r}": wrong for r in repeats}
                        with self.subTest(changes=changes), \
                                self.assertRaises(ValueError):
                            s.observations(synthetic(changes))
                    for adjustment in (-1, 1, words):
                        wrong = d.copy()
                        wrong[0] += adjustment
                        wrong[3] += adjustment
                        changes = {f"{kind}-{n}-{r}": wrong for r in repeats}
                        with self.subTest(changes=changes), \
                                self.assertRaises(ValueError):
                            s.observations(synthetic(changes))

    def test_coherent_native_only_positivity_is_not_interpreter_evidence(self):
        # High total/native counts and correct numerical total slopes alone
        # must fail, even when all records and retained checksums are present.
        base = s.observations(synthetic())["deltas"]
        changes = {}
        for label in s.WORK:
            d = base[label].copy()
            d[1] += d[3]
            d[3] = 0
            changes[label] = d
        with self.assertRaisesRegex(ValueError, "physical|interpreter"):
            s.observations(synthetic(changes))

    def test_coherent_repeat_noise_and_gc_recount_rejected(self):
        base = s.observations(synthetic())["deltas"]
        for label in ("noop-before-2", "noop-final-1", "noop-final-2",
                      "gc-empty-2", "gc-live-1", "gc-live-2", *(
                          f"{kind}-{n}-2" for kind in s.KINDS
                          for n in s.SIZES)):
            for category in (1, 2, 3, 4):
                wrong = base[label].copy()
                wrong[0] += 1
                wrong[category] += 1
                with self.subTest(label=label, category=category), \
                        self.assertRaises(ValueError):
                    s.observations(synthetic({label: wrong}))

    def test_zero_work_not_assumed_equal_to_noop(self):
        result = s.observations(synthetic())
        idle = result["no_op_words"]
        self.assertNotEqual(result["deltas"]["refs-0-1"], idle)
        self.assertNotEqual(result["deltas"]["words-0-1"], idle)
        # Nonzero overhead in arbitrary categories is retained, not calibrated
        # away; changing ALL baselines consistently is permitted.
        shifted = {}
        for label, delta in result["deltas"].items():
            shifted[label] = [delta[0]+13, delta[1]+7, delta[2]+1,
                              delta[3]+3, delta[4]+2]
        admitted = s.observations(synthetic(shifted))
        self.assertEqual(admitted["no_op_words"], [30, 10, 3, 15, 2])

    def test_coherent_process_counter_reset_rejected(self):
        lines = synthetic().splitlines()
        # Shift BOTH endpoints equally, leaving every bracket delta valid.
        # Last bracket then falls below the preceding end in all categories.
        for i, line in enumerate(lines):
            p = line.split("\t")
            if p[0] == s.PREFIX + "ENDPOINT_V1" and p[1] == "noop-final-2":
                if p[2] == "start":
                    p[6:] = ["0"]*5
                else:
                    p[6:] = ["17", "3", "2", "12", "0"]
                lines[i] = "\t".join(p)
        with self.assertRaisesRegex(ValueError, "monotonic"):
            s.observations("\n".join(lines))


if __name__ == "__main__":
    unittest.main()
