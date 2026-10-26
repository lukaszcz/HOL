"""Synthetic private branch protocol tests, NOT executed allocation evidence.

No runtime, compiler, benchmark, or TASK29 acceptance gate is invoked.
"""
import unittest

import interpreter_branch_schema as s


def synthetic(deltas=None, splits=None, gaps=None):
    """Invent consistent snapshots, including allocations between brackets."""
    deltas, splits, gaps = deltas or {}, splits or {}, gaps or {}
    lines = []

    def emit(kind, *values):
        lines.append("\t".join([s.PREFIX + kind + "_V1", *map(str, values)]))

    def result(label, kind, n):
        emit("RESULT", label, kind, n,
             n*(n+1)//2 if kind == "refs" else 37*n)

    emit("SCOPE", s.SCOPE)
    emit("ABI", 15)
    emit("CONFIG", *s.CONFIG)
    counter, branch = [1000, 100, 200, 600, 100], [10, 400, 5, 200]
    for label in s.LABELS:
        delta = [7, 3, 2, 0, 2]
        if label.startswith("gc-"):
            delta = [11, 5, 3, 0, 3]
        if label in s.WORK:
            kind, n = s.WORK[label]
            delta = ([41+5*n, 7, 4, 30+5*n, 0] if kind == "refs"
                     else [43+n, 9, 3, 31+n, 0])
        delta = deltas.get(label, delta)
        split = [0]*4 if delta[3] == 0 else [1, delta[3], 0, 0]
        if label in s.WORK and delta[3] > 10:
            kind, n = s.WORK[label]
            split = ([n, delta[3]-10, 1, 10] if kind == "refs"
                     else [1, 10, 1, delta[3]-10])
        split = splits.get(label, split)
        end = [a+b for a, b in zip(counter, delta)]
        branch_end = [a+b for a, b in zip(branch, split)]
        for side, values in (("start", counter), ("end", end)):
            emit("ENDPOINT", label, side, 1, 8, 0, *values)
        for side, values in (("start", branch), ("end", branch_end)):
            emit("BRANCH", label, side, 1, 8, 0, *values, 0)
        emit("RAW", label, *delta)
        emit("SPLIT", label, *split)
        if label in s.WORK:
            result(label, *s.WORK[label])
        if label == "gc-live-2":
            for kind in s.KINDS:
                result("after-live-gc", kind, 131072)
        gap, branch_gap = gaps.get(label, ([21, 6, 4, 9, 2], [1, 6, 1, 3]))
        counter = [a+b for a, b in zip(end, gap)]
        branch = [a+b for a, b in zip(branch_end, branch_gap)]
    emit("UNCLAIMED", s.UNCLAIMED)
    emit("COMPLETE", 16)
    return "\n".join(lines) + "\n"


def replace_field(text, kind, label, side, index, value):
    """Change a selected record without regenerating dependent evidence."""
    lines = text.splitlines()
    found = 0
    for i, line in enumerate(lines):
        p = line.split("\t")
        if (p[0] == s.PREFIX + kind + "_V1" and p[1] == label and
                (side is None or p[2] == side)):
            p[index] = str(value)
            lines[i] = "\t".join(p)
            found += 1
    assert found == 1
    return "\n".join(lines)


class InterpreterBranchTests(unittest.TestCase):
    def test_complete_private_synthetic_protocol(self):
        result = s.observations(synthetic())
        self.assertEqual(s.LABELS, (
            "noop-before-1", "noop-before-2", "gc-empty-1", "gc-empty-2",
            "refs-65536-1", "refs-131072-1", "refs-65536-2", "refs-131072-2",
            "words-65536-1", "words-131072-1", "words-65536-2",
            "words-131072-2", "gc-live-1", "gc-live-2", "noop-final-1",
            "noop-final-2"))
        self.assertEqual(result["brackets"], 16)
        self.assertEqual(len(result["endpoints"]), 32)
        self.assertEqual(len(result["branches"]), 32)
        self.assertEqual(len(result["results"]), 10)
        self.assertEqual(result["no_op_words"], [7, 3, 2, 0, 2])
        self.assertEqual(result["raw"]["refs-131072-1"]["interpreter"],
                         30 + 5*131072)
        self.assertEqual(result["results"][-2:], [
            ("after-live-gc", "refs", 131072, 8590000128),
            ("after-live-gc", "words", 131072, 4849664)])
        self.assertEqual(result["scope"], s.SCOPE)
        self.assertEqual(result["unclaimed"], s.UNCLAIMED)

    def test_every_record_required_unique_and_ordered(self):
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            changes = [lines[:i] + lines[i+1:],
                       lines[:i] + [line] + lines[i:]]
            if i+1 < len(lines):
                changes.append(lines[:i] + [lines[i+1], line] + lines[i+2:])
            for changed in changes:
                with self.subTest(i=i, line=line), \
                        self.assertRaises(ValueError):
                    s.observations("\n".join(changed))

    def test_only_own_namespace_is_parsed(self):
        text = synthetic()
        chatter = ("ordinary testutils chatter\n"
                   "@@TASK29_INTERPRETER_broken\n@@TASK29_ALLOC_RAW_V1\t-1\n"
                   " @@TASK29_IBRANCH_bad-but-not-at-line-start\n")
        self.assertEqual(s.observations(chatter + text + chatter),
                         s.observations(text))
        for bad in ("@@TASK29_IBRANCH", "@@TASK29_IBRANCHbroken",
                    "@@TASK29_IBRANCH\t1", "@@TASK29_IBRANCH ",
                    s.PREFIX + "FUTURE_V1\t1",
                    s.PREFIX + "EXCEPTION_V1\tfailed",
                    s.PREFIX + "COMPLETE_V1\t16"):
            for changed in (bad + "\n" + text, text + bad + "\n"):
                with self.subTest(bad=bad), self.assertRaises(ValueError):
                    s.observations(changed)
        for changed in (text.replace("_V1", "_V2", 1),
                        text.replace(s.PREFIX + "RAW", s.PREFIX + "DELTA"),
                        text.replace(s.PREFIX, "@@TASK29_INTERPRETER_")):
            with self.assertRaises(ValueError):
                s.observations(changed)
        with self.assertRaises(ValueError):
            s.observations(None)

    def test_every_record_shape_is_exact(self):
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            for changed_line in (line + "\textra", line.rsplit("\t", 1)[0]):
                changed = lines.copy()
                changed[i] = changed_line
                with self.subTest(i=i), self.assertRaises(ValueError):
                    s.observations("\n".join(changed))

    def test_all_numbers_are_canonical_uint64(self):
        self.assertEqual(s.numbers([str(s.UINT64_MAX)], 1), [s.UINT64_MAX])
        lines = synthetic().splitlines()
        first_numeric = {"ABI": 1, "CONFIG": 1, "ENDPOINT": 3,
                         "BRANCH": 3, "RAW": 2, "SPLIT": 2,
                         "RESULT": 3, "COMPLETE": 1}
        for i, line in enumerate(lines):
            p = line.split("\t")
            kind = p[0][len(s.PREFIX):-3]
            for j in range(first_numeric.get(kind, len(p)), len(p)):
                for value in ("-1", "+1", "01", "1.0", "", " 1", "1 ",
                              "\u0661", str(2**64), "9"*100):
                    changed, q = lines.copy(), p.copy()
                    q[j] = value
                    changed[i] = "\t".join(q)
                    with self.subTest(i=i, j=j, value=value), \
                            self.assertRaises(ValueError):
                        s.observations("\n".join(changed))

    def test_scope_abi_config_limitations_and_completion_fixed(self):
        text = synthetic()
        for old, new in ((s.SCOPE, "full runtime validation"),
                         (s.UNCLAIMED, "nothing unverified"),
                         ("ABI_V1\t15", "ABI_V1\t14"),
                         ("COMPLETE_V1\t16", "COMPLETE_V1\t15")):
            with self.subTest(old=old), self.assertRaises(ValueError):
                s.observations(text.replace(old, new, 1))
        for i in range(len(s.CONFIG)):
            wrong = s.CONFIG.copy()
            wrong[i] += 1
            with self.subTest(config=i), self.assertRaises(ValueError):
                s.observations(text.replace(
                    "\t".join(map(str, s.CONFIG)),
                    "\t".join(map(str, wrong)), 1))

    def test_snapshot_headers_reserved_overflow_and_endpoint_sums(self):
        text = synthetic()
        for kind in ("ENDPOINT", "BRANCH"):
            for side in ("start", "end"):
                for index, value in ((3, 2), (4, 4), (5, 1), (5, 2**64-1)):
                    with self.subTest(kind=kind, side=side, index=index), \
                            self.assertRaises(ValueError):
                        s.observations(replace_field(
                            text, kind, "refs-65536-1", side, index, value))
                with self.assertRaises(ValueError):
                    s.observations(replace_field(
                        text, kind, "refs-65536-1", side, 10, 1))
        # Original total must sum; diagnostic words must match at BOTH ends,
        # not merely have equal per-bracket differences.
        for side in ("start", "end"):
            with self.assertRaisesRegex(ValueError, "category sum"):
                s.observations(replace_field(
                    text, "ENDPOINT", "noop-before-1", side, 6, 1001))
        lines = text.splitlines()
        for i, line in enumerate(lines):
            p = line.split("\t")
            if p[0] == s.PREFIX + "BRANCH_V1":
                p[7] = str(int(p[7])+1)
                lines[i] = "\t".join(p)
        with self.assertRaisesRegex(ValueError, "interpreter words mismatch"):
            s.observations("\n".join(lines))

    def test_raw_split_and_results_cannot_disagree_with_snapshots(self):
        text = synthetic()
        for kind, label, indices in (
                ("RAW", "refs-65536-1", range(2, 7)),
                ("SPLIT", "refs-65536-1", range(2, 6)),
                ("RESULT", "refs-65536-1", (3, 4)),
                ("RESULT", "words-65536-1", (3, 4))):
            record = next(line.split("\t") for line in text.splitlines()
                          if line.startswith(s.PREFIX + kind + "_V1\t" +
                                             label + "\t"))
            for index in indices:
                with self.subTest(kind=kind, index=index), \
                        self.assertRaises(ValueError):
                    s.observations(replace_field(
                        text, kind, label, None, index, int(record[index])+1))
        for kind in s.KINDS:
            # There are two after-live records, so select by kind explicitly.
            for value in ("131071\t0", "131072\t0"):
                old = (s.PREFIX + "RESULT_V1\tafter-live-gc\t" + kind +
                       "\t131072\t" + str(8590000128 if kind == "refs"
                                           else 4849664))
                with self.assertRaises(ValueError):
                    s.observations(text.replace(
                        old, s.PREFIX + "RESULT_V1\tafter-live-gc\t" +
                        kind + "\t" + value))
        with self.assertRaises(ValueError):
            s.observations(text.replace("refs-65536-1\trefs",
                                        "refs-65536-1\twords"))

    def test_both_counter_sets_are_process_monotonic(self):
        for gap in (([-1, -1, 0, 0, 0], [0, 0, 0, 0]),
                    ([0, 0, 0, 0, 0], [-1, 0, 0, 0]),
                    ([0, 0, 0, 0, 0], [0, -1, 0, 1]),
                    ([0, 0, 0, 0, 0], [0, 0, -1, 0])):
            with self.subTest(gap=gap), \
                    self.assertRaisesRegex(ValueError, "monotonic"):
                s.observations(synthetic(gaps={"gc-empty-2": gap}))
        # A within-bracket reset also fails before unsigned delta comparison.
        text = synthetic()
        for kind, index in (("ENDPOINT", 7), ("BRANCH", 6)):
            with self.assertRaisesRegex(ValueError, "sum|monotonic"):
                s.observations(replace_field(
                    text, kind, "noop-before-1", "end", index, 0))

    def test_branch_count_word_consistency_and_coverage(self):
        base = s.observations(synthetic())
        for label in ("refs-65536-1", "words-131072-2"):
            words = base["deltas"][label][3]
            for split in ([0, words-1, 1, 1], [1, 0, 1, words],
                          [1, 1, 0, words-1], [1, words, 1, 0],
                          [words, words-1, 1, 1],
                          [1, 1, words, words-1]):
                with self.subTest(label=label, split=split), \
                        self.assertRaisesRegex(ValueError, "count/words"):
                    s.observations(synthetic(splits={label: split}))
        for label, (kind, _) in s.WORK.items():
            words = base["deltas"][label][3]
            split = [0, 0, 1, words] if kind == "refs" else [1, words, 0, 0]
            if kind == "refs":
                with self.subTest(label=label), \
                        self.assertRaisesRegex(ValueError, "coverage"):
                    s.observations(synthetic(splits={label: split}))
            else:
                # A single array can fit the current segment. Its actual
                # fast observation is valid if this series still covers slow.
                s.observations(synthetic(splits={label: split}))
        for kind in s.KINDS:
            for index in (0, 2):
                changes = {}
                for label, (k, _) in s.WORK.items():
                    if k != kind:
                        continue
                    words = base["deltas"][label][3]
                    changes[label] = ([1, words, 0, 0] if index == 0
                                      else [0, 0, 1, words])
                with self.assertRaisesRegex(ValueError, "coverage"):
                    s.observations(synthetic(splits=changes))

    def test_physical_minimum_and_exact_doubling_categories(self):
        base = s.observations(synthetic())["deltas"]
        for kind in s.KINDS:
            # Coherent slopes and repeats do not excuse undercounted storage.
            changes = {}
            for label, (k, n) in s.WORK.items():
                if k == kind:
                    physical = 5*n if kind == "refs" else 1+n
                    changes[label] = [physical-1, 0, 0, physical-1, 0]
            with self.assertRaisesRegex(ValueError, "physical minimum"):
                s.observations(synthetic(deltas=changes))
            for adjustment in (-1, 1, 65536):
                changes = {}
                for repeat in (1, 2):
                    label = f"{kind}-131072-{repeat}"
                    wrong = base[label].copy()
                    wrong[0] += adjustment
                    wrong[3] += adjustment
                    changes[label] = wrong
                with self.assertRaisesRegex(ValueError, "doubling"):
                    s.observations(synthetic(deltas=changes))
            for category in (1, 2, 4):
                for preserve_total in (False, True):
                    changes = {}
                    for repeat in (1, 2):
                        label = f"{kind}-131072-{repeat}"
                        wrong = base[label].copy()
                        wrong[category] += 1
                        if preserve_total:
                            wrong[3] -= 1
                        else:
                            wrong[0] += 1
                        changes[label] = wrong
                    with self.assertRaisesRegex(ValueError, "category"):
                        s.observations(synthetic(deltas=changes))

    def test_original_work_noop_and_gc_vectors_must_repeat(self):
        base = s.observations(synthetic())["deltas"]
        labels = ("noop-before-2", "noop-final-1", "noop-final-2",
                  "gc-empty-2", "gc-live-1", "gc-live-2", *(
                      f"{kind}-{n}-2" for kind in s.KINDS for n in s.SIZES))
        for label in labels:
            for category in (1, 2, 3, 4):
                wrong = base[label].copy()
                wrong[0] += 1
                wrong[category] += 1
                with self.subTest(label=label, category=category), \
                        self.assertRaises(ValueError):
                    s.observations(synthetic(deltas={label: wrong}))

    def test_noop_and_gc_never_charge_interpreter_even_if_repeatable(self):
        base = s.observations(synthetic())["deltas"]
        for prefix in ("noop-", "gc-"):
            changes = {}
            for label, delta in base.items():
                if label.startswith(prefix):
                    wrong = delta.copy()
                    wrong[0] += 1
                    wrong[3] += 1
                    changes[label] = wrong
            with self.assertRaisesRegex(ValueError, "no-op/GC"):
                s.observations(synthetic(deltas=changes))

    def test_branch_schedule_may_change_with_exact_original_allocations(self):
        original = s.observations(synthetic())
        changes = {}
        for label, (kind, _) in s.WORK.items():
            words = original["deltas"][label][3]
            # Deliberately change counts AND the word distribution on repeat.
            if label.endswith("-1"):
                changes[label] = ([2, words, 0, 0] if kind == "refs" else
                                  [0, 0, 2, words])
            else:
                changes[label] = ([3, words-7, 1, 7] if kind == "refs" else
                                  [1, 7, 3, words-7])
        changed = s.observations(synthetic(splits=changes))
        self.assertEqual(changed["deltas"], original["deltas"])
        self.assertEqual(changed["endpoints"], original["endpoints"])
        self.assertNotEqual(changed["splits"], original["splits"])
        # No-op/GC packaging in native/RTS/code is retained, not calibrated
        # away, and need not equal work overhead or each other.
        shifted = {label: [d[0]+13, d[1]+7, d[2]+4, d[3], d[4]+2]
                   for label, d in original["deltas"].items()}
        self.assertEqual(s.observations(synthetic(deltas=shifted))[
            "no_op_words"], [20, 10, 6, 0, 4])


if __name__ == "__main__":
    unittest.main()
