"""Controls are synthetic except the separately authorized runtime driver."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
COUNTER = HERE / "allocator-counter"
sys.path.insert(0, str(COUNTER))
import control_schema as s
import run_controls as driver


def synthetic():
    lines = ["@@TASK29_ALLOC_SCOPE_V1\tcontrols-only; not full runtime validation",
             "@@TASK29_ALLOC_RUNTIME_V1\t/synthetic/libpolyml.so.16",
             "@@TASK29_ALLOC_ABI_V1\t15"]
    count = [100, 100, 0, 0, 0]
    layouts = []
    for label in s.LABELS:
        d = [4, 4, 0, 0, 0]
        if label.startswith(("word-array-", "byte-array-", "ref-list-")):
            n = int(label.rsplit("-", 1)[1])
            words = (n+1 if label.startswith("word-array-") else
                     4+(n+7)//8 if label.startswith("byte-array-") else 5*n)
            d = [4+words, 4+words, 0, 0, 0]
            layouts.append(f"@@TASK29_ALLOC_LAYOUT_V1\t{label}\t{n}\t"
                           f"{words}\t{d[0]}\t4\t{8*d[0]}")
        if label == "rts-bignum-multiply":
            d = [14, 4, 10, 0, 0]
        if label == "compile-retained-entry-closure":
            d = [14, 4, 0, 0, 10]
        for side, c in (("start", count),
                        ("end", [a+b for a, b in zip(count, d)])):
            lines.append("\t".join(["@@TASK29_ALLOC_ENDPOINT_V1", label,
                                   side, *map(str, [1, 8, 0, *c])]))
        count = [a+b for a, b in zip(count, d)]
        lines.append("\t".join(["@@TASK29_ALLOC_DELTA_V1", label, *map(str, d)]))
    lines += layouts
    lines += ["@@TASK29_ALLOC_NOOP_V1\t4\t4\t0\t0\t0",
              "@@TASK29_ALLOC_UNCLAIMED_V1\tfull runtime; TASK29B matrix",
              "@@TASK29_ALLOC_CONTROLS_COMPLETE_V1\t34"]
    return "\n".join(lines) + "\n"


class ControlSchemaTests(unittest.TestCase):
    def test_complete_synthetic_protocol(self):
        result = s.observations(synthetic())
        self.assertEqual(result["brackets"], 34)
        self.assertEqual(result["no_op_words"], [4, 4, 0, 0, 0])

    def test_missing_duplicate_and_reordered_records(self):
        lines = synthetic().splitlines()
        for prefix in ("ENDPOINT", "DELTA", "LAYOUT", "ABI", "NOOP",
                       "CONTROLS_COMPLETE"):
            i = next(i for i, line in enumerate(lines)
                     if line.startswith("@@TASK29_ALLOC_" + prefix))
            for changed in (lines[:i]+lines[i+1:],
                            lines[:i]+[lines[i]]+lines[i:]):
                with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                    s.observations("\n".join(changed))
        i = next(i for i, line in enumerate(lines)
                 if line.startswith("@@TASK29_ALLOC_ENDPOINT"))
        lines[i], lines[i+1] = lines[i+1], lines[i]
        with self.assertRaises(ValueError):
            s.observations("\n".join(lines))

    def test_uint64_and_metadata(self):
        text = synthetic()
        for bad in ("1\t4\t0", "1\t8\t1", "2\t8\t0",
                    "1\t8\t-1", "1\t8\t01", f"1\t8\t{2**64}"):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                s.observations(text.replace("1\t8\t0", bad, 1))

    def test_changed_delta_endpoint_and_layout(self):
        text = synthetic()
        for old, new in (
            ("noop-warmup-1\t4\t4\t0\t0\t0", "noop-warmup-1\t5\t5\t0\t0\t0"),
            ("start\t1\t8\t0\t100\t100", "start\t1\t8\t0\t101\t100"),
            ("word-array-0\t0\t1\t5\t4\t40", "word-array-0\t0\t1\t5\t4\t41"),
            ("CONTROLS_COMPLETE_V1\t34", "CONTROLS_COMPLETE_V1\t33"),
            ("ABI_V1\t15", "ABI_V1\t7")):
            self.assertIn(old, text)
            with self.subTest(old=old), self.assertRaises(ValueError):
                s.observations(text.replace(old, new, 1))

    def test_no_unknown_or_unscoped_record(self):
        for text in (synthetic()+"@@TASK29_ALLOC_FUTURE_V1\t1\n",
                     synthetic().replace("controls-only", "acceptance"),
                     synthetic().replace("TASK29B matrix", "all passed")):
            with self.assertRaises(ValueError):
                s.observations(text)

    def test_completion_cannot_precede_observations(self):
        lines = synthetic().splitlines()
        lines.insert(0, lines.pop())
        with self.assertRaisesRegex(ValueError, "after completion"):
            s.observations("\n".join(lines))

    def test_physical_slope_not_just_positive_counts(self):
        # Consistently multiply every endpoint/delta by 2. Sums, positivity and
        # monotonicity survive; exact physical allocation semantics must not.
        lines = synthetic().splitlines()
        for i, line in enumerate(lines):
            p = line.split("\t")
            if p[0].endswith("ENDPOINT_V1"):
                p[6:] = [str(2*int(n)) for n in p[6:]]
            elif p[0].endswith("DELTA_V1"):
                p[2:] = [str(2*int(n)) for n in p[2:]]
            elif p[0].endswith("NOOP_V1"):
                p[1:] = [str(2*int(n)) for n in p[1:]]
            lines[i] = "\t".join(p)
        with self.assertRaises(ValueError):
            s.observations("\n".join(lines))

    def test_gc_and_noop_repeat_are_strict(self):
        text = synthetic()
        for label in ("noop-repeat-1", "gc-with-retained-arrays-1"):
            # Changing just a delta is already rejected at the endpoint guard.
            with self.subTest(label=label), self.assertRaises(ValueError):
                s.observations(text.replace(label+"\t4\t4\t0\t0\t0",
                                            label+"\t5\t5\t0\t0\t0"))


class IdentityTests(unittest.TestCase):
    def test_actual_symbol_and_single_process_mapping(self):
        with tempfile.TemporaryDirectory() as tmp:
            lib = Path(tmp) / "libpolyml.so.16.0.0"
            lib.write_bytes(b"synthetic, not executable")
            text = (f"@@TASK29_ALLOC_RUNTIME_V1\t{lib}\n"
                    f"@@TASK29_ALLOC_MAP_V1\t100-200 r-xp 0 00:00 1 {lib}\n")
            self.assertEqual(driver.runtime_identity(text, lib)["symbol"], str(lib))
            for changed in ("", text+text,
                text+"@@TASK29_ALLOC_MAP_V1\t200-300 r-xp 0 00:00 2 /other/libpolyml.so\n",
                text.replace("@@TASK29_ALLOC_MAP_V1", "unrecorded")):
                with self.subTest(changed=changed), self.assertRaises(Exception):
                    driver.runtime_identity(changed, lib)

    def test_authorization_required_before_build(self):
        with self.assertRaises(SystemExit):
            driver.main(["--output", "/nonexistent/forbidden.json"])

    def test_pinned_source_and_patch(self):
        # Optional source availability; the authorized driver always runs it.
        if not driver.DEFAULT_SOURCE.is_dir():
            self.skipTest("local pristine Poly/ML distribution unavailable")
        patched = driver.verify_source(driver.DEFAULT_SOURCE)
        self.assertEqual(len(patched), 7)
        self.assertNotIn("libpolyml/processes.cpp", patched)


if __name__ == "__main__":
    unittest.main()
