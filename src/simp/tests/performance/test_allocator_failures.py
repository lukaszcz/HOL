"""SYNTHETIC failure-protocol tests; NOT executed reservation evidence.

No allocator, subprocess, capped heap, OS limit, build or benchmark is run.
Even the unprefixed RTS diagnostic below is invented test data. Only the
separate driver's sealed, timed, successful process receipt is real evidence.
"""
import copy
import hashlib
import unittest

import failure_schema as s


def synthetic(overrides=None, result_overrides=None, limit=None):
    """Invent consistent counters/results/diagnostics for parser tests ONLY."""
    overrides = overrides or {}
    result_overrides = result_overrides or {}
    lines = []

    def emit(kind, *values):
        lines.append("\t".join([s.PREFIX + kind + "_V1", *map(str, values)]))

    emit("SCOPE", s.SCOPE)
    emit("RUNTIME", "/synthetic/libpolyml.so.16")
    emit("MAP", "100-200 r-xp 0000 00:00 1 /synthetic/libpolyml.so.16")
    emit("ABI", 15)
    emit("CONFIG", *s.CONFIG)
    # Invented dynamic virtual size and verified OS limit, NOT execution.
    emit("LIMIT", *(limit if limit is not None else
                    [1, 268435456, 335544320, s.UINT64_MAX, s.LIMIT_HEADROOM]))
    counter = [1000, 700, 100, 100, 100]
    for label, kind, n in s.RECIPE:
        emit("REQUEST", label, kind, n)
        if kind == "failure":
            lines.append(s.EXHAUSTION)  # Fabricated, NOT execution evidence.
        delta = ([17, 11, 3, 2, 1] if kind in ("manual", "failure") else
                 [23+n, 15+n, 4, 3, 1] if kind == "success" else
                 [11, 7, 2, 1, 1])
        delta = overrides.get(label, delta)
        end = [a+b for a, b in zip(counter, delta)]
        for side, values in (("start", counter), ("end", end)):
            emit("ENDPOINT", label, side, 1, 8, 0, *values)
        emit("RAW", label, *delta)
        outcome = ([1, 0, 1, 1] if kind in ("manual", "failure")
                   else [1, 1, 0, 1])
        result = [n, 37*n] if kind == "success" else [1024, 92160]
        values = outcome + [1024, 92160] + result
        emit("RESULT", label, *result_overrides.get(label, values))
        # Real outside-bracket decoding/checksum/printing may also allocate.
        counter = [a+b for a, b in zip(end, [13, 7, 2, 3, 1])]
    emit("UNCLAIMED", s.UNCLAIMED)
    emit("COMPLETE", len(s.LABELS))
    return "\n".join(lines) + "\n"


def receipt():
    text = synthetic()
    return dict(command=["/synthetic/failure-controls.exe", *s.FLAGS],
                exit=0, timed_out=False, stdout=text,
                stdout_bytes=len(text.encode()),
                stdout_sha256=hashlib.sha256(text.encode()).hexdigest())


class FailureSchemaTests(unittest.TestCase):
    def test_complete_synthetic_protocol(self):
        result = s.observations(synthetic())
        self.assertEqual(result["limit"], dict(
            success=1, vsize_before=268435456, applied_soft=335544320,
            hard=s.UINT64_MAX, headroom=s.LIMIT_HEADROOM))
        self.assertEqual(result["brackets"], 35)
        self.assertEqual(len(result["endpoints"]), 70)
        self.assertEqual(len(result["results"]), 35)
        self.assertEqual(result["exhaustion_messages"], 4)
        self.assertEqual(result["failures"], [
            "fail-16777216-1", "fail-25165824-1",
            "fail-16777216-2", "fail-25165824-2"])
        self.assertEqual(result["no_op_words"], [11, 7, 2, 1, 1])
        self.assertEqual(result["manual_interrupt_words"], [17, 11, 3, 2, 1])
        self.assertEqual(result["wrapper_difference"], [6, 4, 1, 1, 0])
        self.assertEqual(result["deltas"]["recover-25165824-2-512"],
                         [535, 527, 4, 3, 1])
        self.assertEqual(s.validate_receipt(receipt(), timeout=60), result)

    def test_dynamic_os_limit_success_arithmetic_and_hard_bound(self):
        for before in (4096, 536870912, 2**40):
            soft = before + s.LIMIT_HEADROOM
            for hard in (soft, soft + 4096, s.UINT64_MAX):
                limit = [1, before, soft, hard, s.LIMIT_HEADROOM]
                with self.subTest(limit=limit):
                    parsed = s.observations(synthetic(limit=limit))["limit"]
                    self.assertEqual(parsed["vsize_before"], before)
                    self.assertEqual(parsed["applied_soft"], soft)
                    self.assertEqual(parsed["hard"], hard)
        valid = [1, 268435456, 335544320, s.UINT64_MAX, s.LIMIT_HEADROOM]
        for index, replacements in {
                0: (0, 2), 1: (0, 268435457, s.UINT64_MAX),
                2: (335544319, 335544321), 3: (0, 335544319),
                4: (0, s.LIMIT_HEADROOM - 1, s.LIMIT_HEADROOM + 1)}.items():
            for value in replacements:
                invalid = valid.copy()
                invalid[index] = value
                with self.subTest(limit=invalid), self.assertRaises(ValueError):
                    s.observations(synthetic(limit=invalid))
        for invalid in (valid[:-1], valid + [0]):
            with self.assertRaises(ValueError):
                s.observations(synthetic(limit=invalid))
        # A self-consistent but larger/smaller budget is not the agreed cap.
        for budget in (s.LIMIT_HEADROOM - 1, s.LIMIT_HEADROOM + 1, 2**27):
            with self.assertRaises(ValueError):
                s.observations(synthetic(limit=[
                    1, 268435456, 268435456 + budget, s.UINT64_MAX, budget]))
        # Canonical uint64 fields individually fitting cannot hide overflow
        # in the required before + headroom arithmetic.
        with self.assertRaises(ValueError):
            s.observations(synthetic(limit=[
                1, s.UINT64_MAX, s.LIMIT_HEADROOM - 1,
                s.UINT64_MAX, s.LIMIT_HEADROOM]))

    def test_every_record_and_diagnostic_required_unique_and_ordered(self):
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            variants = [lines[:i]+lines[i+1:], lines[:i]+[line]+lines[i:]]
            if i+1 < len(lines):
                swapped = lines.copy()
                swapped[i], swapped[i+1] = swapped[i+1], swapped[i]
                variants.append(swapped)
            for variant in variants:
                with self.subTest(i=i), self.assertRaises(ValueError):
                    s.observations("\n".join(variant))

    def test_unknown_versions_protocols_and_records_rejected(self):
        text = synthetic()
        for changed in (
                text.replace("_V1", "_V2", 1),
                text.replace(s.PREFIX + "RAW", s.PREFIX + "DELTA", 1),
                text.replace(s.PREFIX + "ENDPOINT", "@@TASK29_ALLOC_ENDPOINT"),
                text.replace(s.PREFIX + "RESULT", "@@TASK29_WORKER_RESULT", 1),
                text + s.PREFIX + "EXCEPTION_V1\tInterrupt\n",
                text + s.PREFIX + "FUTURE_V1\t1\n",
                text + "@@TASK29_FAILUREbroken\n",
                text + "@@TASK29_INTERPRETER_COMPLETE_V1\t31\n"):
            with self.subTest(changed=changed[:80]), \
                    self.assertRaises(ValueError):
                s.observations(changed)
        self.assertEqual(s.observations("ordinary testutils output\n" + text),
                         s.observations(text))

    def test_actual_rts_output_required_not_just_claimed_interrupts(self):
        text = synthetic()
        # All endpoints/outcomes are left consistent in these attacks.
        for changed in (
                text.replace(s.EXHAUSTION + "\n", ""),
                text.replace(s.EXHAUSTION, "fixture says heap exhausted"),
                text.replace(s.EXHAUSTION, s.PREFIX + "EXHAUSTED_V1\t1"),
                text.replace(s.EXHAUSTION, s.EXHAUSTION + " ", 1),
                text.replace(s.EXHAUSTION, "prefix " + s.EXHAUSTION, 1),
                text + s.EXHAUSTION + "\n",
                text + "Failed to recover - exiting\n",
                s.EXHAUSTION + "\n" + text):
            with self.subTest(changed=changed[:80]), \
                    self.assertRaises(ValueError):
                s.observations(changed)

    def test_every_numeric_field_is_canonical_bounded_uint64(self):
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            p = line.split("\t")
            first = {"ABI_V1": 1, "CONFIG_V1": 1, "LIMIT_V1": 1,
                     "REQUEST_V1": 3,
                     "ENDPOINT_V1": 3, "RAW_V1": 2, "RESULT_V1": 2,
                     "COMPLETE_V1": 1}.get(p[0].removeprefix(s.PREFIX))
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

    def test_changed_numeric_fields_shapes_scope_and_identity(self):
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
        text = synthetic()
        for old, new in (
                (s.SCOPE, "all failures covered"),
                (s.UNCLAIMED, "nothing unverified"),
                ("RUNTIME_V1\t/", "RUNTIME_V1\t"),
                ("MAP_V1\t100-200", "MAP_V1\tbad-map"),
                ("1\t8\t0", "1\t4\t0"),
                ("1\t8\t0", "1\t8\t1"),
                ("1\t8\t0", "2\t8\t0"),
                ("COMPLETE_V1\t35", "COMPLETE_V1\t35\textra"),
                ("REQUEST_V1\tfail-16777216-1\tfailure",
                 "REQUEST_V1\tfail-16777216-1\tmanual")):
            self.assertIn(old, text)
            with self.subTest(old=old), self.assertRaises(ValueError):
                s.observations(text.replace(old, new, 1))

    def test_immediate_interrupt_wrong_exception_and_missing_recovery(self):
        result = s.observations(synthetic())
        for label, *values in result["results"]:
            # Entry, return, exact Interrupt outcome, attribute restoration,
            # sentinel length/content and destination are each mandatory.
            for i in range(len(values)):
                wrong = values.copy()
                wrong[i] += 1
                if i in (0, 3):
                    wrong[i] = 0  # Interrupt before entry / not restored.
                with self.subTest(label=label, i=i), \
                        self.assertRaises(ValueError):
                    s.observations(synthetic(result_overrides={label: wrong}))
        text = synthetic()
        for changed in (
                text.replace("\tfailure\t16777216", "\tSize\t16777216", 1),
                text.replace("\tmanual\t0", "\tFail\t0", 1),
                text.replace("recover-25165824-2-512", "no-recovery")):
            with self.assertRaises(ValueError):
                s.observations(changed)

    def test_soft_maxheap_oversized_success_is_not_failed_reservation(self):
        # Regression for a 128 MiB allocation that actually returned under
        # --maxheap=96. These counters/results are SYNTHETIC protocol data;
        # the 16777221-word total must never be admitted as a failed request.
        label, n = "fail-16777216-1", 16777216
        text = synthetic(
            overrides={label: [16777221, 16777215, 3, 2, 1]},
            result_overrides={label: [1, 1, 0, 1, 1024, 92160, n, 37*n]})
        with self.assertRaisesRegex(ValueError, "missing actual RTS"):
            s.observations(text.replace(s.EXHAUSTION + "\n", "", 1))
        # Even a purported diagnostic cannot make a returned assignment a
        # failure. The unchanged sentinel and exact Interrupt are mandatory.
        with self.assertRaisesRegex(ValueError, "wrong failure outcome"):
            s.observations(text)

    def test_requested_size_charges_and_failure_noise_rejected(self):
        base = s.observations(synthetic())["deltas"]
        for label, kind, n in s.RECIPE:
            if kind != "failure":
                continue
            for words in (1, n, n+1):
                for category in range(1, 5):
                    wrong = base[label].copy()
                    wrong[0] += words
                    wrong[category] += words
                    with self.subTest(label=label, words=words,
                                      category=category), \
                            self.assertRaisesRegex(ValueError, "raw costs"):
                        s.observations(synthetic({label: wrong}))
        # Inflating EVERY manual and failure baseline identically does not
        # allow a whole requested allocation to hide in 'wrapper overhead'.
        changes = {}
        for label, kind, _ in s.RECIPE:
            if kind in ("manual", "failure"):
                d = base[label].copy()
                d[0] += s.SIZES[0]
                d[1] += s.SIZES[0]
                changes[label] = d
        with self.assertRaisesRegex(ValueError, "requested failed"):
            s.observations(synthetic(changes))

    def test_exact_wrapper_baselines_not_tolerance_or_noop_subtraction(self):
        base = s.observations(synthetic())["deltas"]
        for label, kind, _ in s.RECIPE:
            if "warmup" in label or kind == "success":
                continue
            for category in range(1, 5):
                wrong = base[label].copy()
                wrong[0] += 1
                wrong[category] += 1
                with self.subTest(label=label, category=category), \
                        self.assertRaises(ValueError):
                    s.observations(synthetic({label: wrong}))
        for label, kind, _ in s.RECIPE:
            if kind == "failure":
                with self.assertRaisesRegex(ValueError, "raw costs"):
                    s.observations(synthetic({label: base["noop-before-1"]}))
        changes = {label: [0]*5 for label, kind, _ in s.RECIPE
                   if kind in ("manual", "failure")}
        with self.assertRaisesRegex(ValueError, "below native no-op"):
            s.observations(synthetic(changes))
        # Nonzero shared wrapper costs in every category are retained RAW,
        # not silently rounded to zero or subtracted from published counters.
        shifted = {label: [d[0]+13, d[1]+7, d[2]+1, d[3]+3, d[4]+2]
                   for label, d in base.items()}
        admitted = s.observations(synthetic(shifted))
        self.assertEqual(admitted["manual_interrupt_words"], [30, 18, 4, 5, 3])
        self.assertEqual(admitted["wrapper_difference"], [6, 4, 1, 1, 0])

    def test_successful_recovery_requires_native_exact_slopes(self):
        base = s.observations(synthetic())["deltas"]
        for label, kind, n in s.RECIPE:
            if kind != "success" or n == 0:
                continue
            for category in (2, 3, 4):
                wrong = base[label].copy()
                wrong[1] -= n
                wrong[category] += n
                with self.subTest(label=label, category=category), \
                        self.assertRaisesRegex(ValueError, "native payload"):
                    s.observations(synthetic({label: wrong}))
            for adjustment in (-1, 1, n):
                wrong = base[label].copy()
                wrong[0] += adjustment
                wrong[1] += adjustment
                with self.subTest(label=label, adjustment=adjustment), \
                        self.assertRaisesRegex(ValueError, "native payload"):
                    s.observations(synthetic({label: wrong}))

    def test_coherent_process_counter_reset_rejected(self):
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            p = line.split("\t")
            if p[0] == s.PREFIX + "ENDPOINT_V1" and p[1] == "noop-final-2":
                p[6:] = (["0"]*5 if p[2] == "start" else
                         ["11", "7", "2", "1", "1"])
                lines[i] = "\t".join(p)
        with self.assertRaisesRegex(ValueError, "process-monotonic"):
            s.observations("\n".join(lines))

    def test_receipt_rejects_exit_timeout_flags_output_tampering(self):
        original = receipt()
        for key, values in {
                "exit": (1, -9, None, False),
                "timed_out": (True, None, 0),
                "stdout": (None, original["stdout"] + "tampered\n"),
                "stdout_bytes": (0, True),
                "stdout_sha256": ("0"*64, None),
                "command": (
                    [], ["relative.exe", *s.FLAGS],
                    [original["command"][0], "--maxheap=96"],
                    [*original["command"], "--maxheap=512"],
                    [original["command"][0], "-H", "128",
                     "--maxheap=96", "--gcthreads=1"],
                    [original["command"][0], "-H", "32",
                     "--maxheap=192", "--gcthreads=1"])}.items():
            for value in values:
                changed = copy.deepcopy(original)
                changed[key] = value
                with self.subTest(key=key, value=str(value)[:80]), \
                        self.assertRaises(ValueError):
                    s.validate_receipt(changed, timeout=60)
        for timeout in (0, -1, True, None, float("inf"), float("nan")):
            with self.subTest(timeout=timeout), self.assertRaises(ValueError):
                s.validate_receipt(original, timeout=timeout)
        for key in original:
            changed = original.copy()
            del changed[key]
            with self.subTest(missing=key), self.assertRaises(ValueError):
                s.validate_receipt(changed, timeout=60)


if __name__ == "__main__":
    unittest.main()
