"""Synthetic worker-protocol rejection tests, NOT executed runtime evidence.

The main authorized driver separately builds worker_selftest.sml, records its
raw output even on failure, checks DSO identity, then calls observations().
No runtime build or benchmark is launched by this test module.
"""
import unittest

import worker_schema as s


def synthetic(overrides=None):
    """Consistent endpoints/raw deltas; overrides exercise semantic guards."""
    overrides = overrides or {}
    lines = [s.PREFIX + "SCOPE_V1\t" + s.SCOPE,
             s.PREFIX + "RUNTIME_V1\t/synthetic/libpolyml.so.16",
             s.PREFIX + "MAP_V1\t100-200 r-xp 0000 00:00 1 "
             "/synthetic/libpolyml.so.16",
             s.PREFIX + "ABI_V1\t15",
             s.PREFIX + "CONFIG_V1\t4\t8\t2\t0\t256\t512\t5"]
    counter = [100, 100, 0, 0, 0]
    n = 0

    def emit(kind, *values):
        lines.append("\t".join([s.PREFIX + kind + "_V1", *map(str, values)]))

    def results(label, count):
        for worker in range(4):
            emit("RESULT", label, worker, count, count*(count+1)//2)

    for label in s.LABELS:
        if label == "retirement":
            results("before-retirement", 512)
        if label.startswith("workers-"):
            n = 0 if "warmup" in label else int(label.split("-")[1])
        delta = [4, 4, 0, 0, 0]
        if label.startswith("workers-"):
            delta = [24+20*n, 24+20*n, 0, 0, 0]
        if label == "retirement":
            # Intentionally NOT constrained to a deterministic retirement cost.
            delta = [37, 31, 6, 0, 0]
        delta = overrides.get(label, delta)
        end = [a+b for a, b in zip(counter, delta)]
        for side, value in (("start", counter), ("end", end)):
            emit("ENDPOINT", label, side, 1, 8, 0, *value)
        counter = end
        if label == "retirement":
            state = [512, 4, 0, 4, 0, 0]
        elif label in s.LABELS[s.LABELS.index("retirement")+1:]:
            state = [512, 0, 0, 0, 0, 0]
        else:
            state = [n, 4, 4, 4, 4, 0]
        emit("RAW", label, *state, *delta)
        if label.startswith("workers-"):
            results(label, n)
        if label == "retirement":
            for worker in range(4):
                emit("RETIRED", worker, 0)
    results("after-retired-gc", 512)
    emit("UNCLAIMED", s.UNCLAIMED)
    emit("COMPLETE", len(s.LABELS))
    return "\n".join(lines) + "\n"


class WorkerSchemaTests(unittest.TestCase):
    def test_complete_synthetic_protocol(self):
        result = s.observations(synthetic())
        self.assertEqual(result["brackets"], 22)
        self.assertEqual(len(result["endpoints"]), 44)
        self.assertEqual(len(result["results"]), 40)
        self.assertEqual(result["retired"], [[i, 0] for i in range(4)])
        self.assertEqual(result["no_op_words"], [4, 4, 0, 0, 0])
        self.assertEqual(result["deltas"]["workers-256-1"][0], 5144)
        self.assertEqual(result["deltas"]["workers-512-1"][0], 10264)
        self.assertEqual(result["raw"]["retirement"]["active_after"], 0)

    def test_every_record_is_required_and_unique(self):
        lines = synthetic().splitlines()
        # Includes EVERY endpoint, per-worker result, raw state, retirement,
        # identity, scope and completion record, not just representative kinds.
        for i, line in enumerate(lines):
            for change in (lines[:i]+lines[i+1:],
                           lines[:i]+[line]+lines[i:]):
                with self.subTest(i=i, line=line), \
                        self.assertRaises(ValueError):
                    s.observations("\n".join(change))

    def test_every_adjacent_reordering_is_rejected(self):
        lines = synthetic().splitlines()
        for i in range(len(lines)-1):
            changed = lines.copy()
            changed[i], changed[i+1] = changed[i+1], changed[i]
            with self.subTest(i=i), self.assertRaises(ValueError):
                s.observations("\n".join(changed))

    def test_protocol_version_unknown_exception_and_post_completion(self):
        text = synthetic()
        bad = [text.replace("_V1", "_V2", 1),
               text.replace(s.PREFIX + "RAW", s.PREFIX + "DELTA", 1),
               text + s.PREFIX + "FUTURE_V1\t1\n",
               s.PREFIX + "EXCEPTION_V1\tstartup\t0\tfailure\n" + text,
               text.replace(s.PREFIX + "RAW_V1\tworkers-256-1",
                            s.PREFIX + "EXCEPTION_V1\tworkers-256-1", 1)]
        for value in bad:
            with self.subTest(value=value[:80]), self.assertRaises(ValueError):
                s.observations(value)
        # Ordinary testutils output and the separate old protocol are not
        # worker evidence and cannot fill any worker record's absence.
        self.assertEqual(s.observations("testutils chatter\n" + text),
                         s.observations(text))
        with self.assertRaises(ValueError):
            s.observations(text.replace("@@TASK29_WORKER_ENDPOINT_V1",
                                        "@@TASK29_ALLOC_ENDPOINT_V1"))

    def test_every_numeric_field_is_canonical_bounded_uint64(self):
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            p = line.split("\t")
            kind = p[0].removeprefix(s.PREFIX)
            first = {"ABI_V1": 1, "CONFIG_V1": 1, "ENDPOINT_V1": 3,
                     "RAW_V1": 2, "RESULT_V1": 2, "RETIRED_V1": 1,
                     "COMPLETE_V1": 1}.get(kind)
            if first is None:
                continue
            for j in range(first, len(p)):
                for value in ("-1", "+1", "01", "1.0", "", " 1",
                              str(2**64), "9"*100):
                    q = p.copy()
                    q[j] = value
                    changed = lines.copy()
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
                q = p.copy()
                q[j] = str(int(q[j])+1)
                changed = lines.copy()
                changed[i] = "\t".join(q)
                with self.subTest(i=i, j=j), self.assertRaises(ValueError):
                    s.observations("\n".join(changed))

    def test_changed_scope_limits_metadata_and_record_shape(self):
        text = synthetic()
        for old, new in ((s.SCOPE, "full allocator acceptance"),
                         (s.UNCLAIMED, "nothing unverified"),
                         ("1\t8\t0", "1\t4\t0"),
                         ("1\t8\t0", "1\t8\t1"),
                         ("1\t8\t0", "2\t8\t0"),
                         ("RUNTIME_V1\t/", "RUNTIME_V1\t"),
                         ("MAP_V1\t100-200", "MAP_V1\tbad-map"),
                         ("COMPLETE_V1\t22", "COMPLETE_V1\t22\textra")):
            self.assertIn(old, text)
            with self.subTest(old=old), self.assertRaises(ValueError):
                s.observations(text.replace(old, new, 1))

    def test_coherent_positive_wrong_slope_and_category_fail(self):
        for count in (256, 512):
            words = 20*count
            for delta in ([24+words+1, 24+words+1, 0, 0, 0],
                          [24+2*words, 24+2*words, 0, 0, 0],
                          [24+words, 24, words, 0, 0]):
                for repeats in ((1,), (1, 2)):
                    overrides = {f"workers-{count}-{r}": delta
                                 for r in repeats}
                    with self.subTest(overrides=overrides), \
                            self.assertRaisesRegex(ValueError, "slope|repeat"):
                        s.observations(synthetic(overrides))

    def test_coherent_gc_recounts_and_coordination_noise_fail(self):
        for label in ("workers-0-2", "workers-256-2", "workers-512-2",
                      "noop-parked", "noop-retired-1", "noop-retired-2",
                      "gc-empty-2", "gc-live-1", "gc-live-2",
                      "gc-retired-1", "gc-retired-2"):
            base = s.observations(synthetic())["deltas"][label].copy()
            base[0] += 1
            base[1] += 1
            with self.subTest(label=label), self.assertRaises(ValueError):
                s.observations(synthetic({label: base}))

    def test_retirement_not_allowed_to_drop_process_counter(self):
        # All raw differences/category sums remain internally consistent;
        # subtracting retired workers is caught at global monotonicity.
        text = synthetic()
        lines = text.splitlines()
        for i, line in enumerate(lines):
            p = line.split("\t")
            if (p[0] == s.PREFIX + "ENDPOINT_V1" and
                    p[1] == "retirement" and p[2] == "end"):
                p[6] = "1"
                p[7:] = ["1", "0", "0", "0"]
                lines[i] = "\t".join(p)
        with self.assertRaisesRegex(ValueError, "monotonic"):
            s.observations("\n".join(lines))

    def test_retirement_cost_is_raw_not_a_guessed_layout(self):
        # Retirement scheduling/RTS cleanup has no claimed exact slope.
        result = s.observations(synthetic({"retirement": [99, 80, 19, 0, 0]}))
        self.assertEqual(result["deltas"]["retirement"], [99, 80, 19, 0, 0])


if __name__ == "__main__":
    unittest.main()
