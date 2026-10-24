"""Fail-closed controls for TASK29's synthetic profiler-loss reproducer."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import allocation_profiler_probe as p


def transcript():
    return "\n".join(
        ["@@TASK29_PROFILER\t%s\t%d\t%d" % (name, events, events+12)
         for name, _, events in p.CASES] +
        ["@@TASK29_PROFILER_COMPLETE\t6", ""])


class ProfilerProbeTests(unittest.TestCase):
    def test_exact_library_pin(self):
        libs = {"/usr/local/lib/libpolyml.so.16":
                {"sha256": p.LIB_SHA256}}
        self.assertEqual(p.admit_library(libs), next(iter(libs)))
        bad = copy.deepcopy(libs)
        bad[next(iter(bad))]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "private ABI probe forbidden"):
            p.admit_library(bad)

    def test_missing_or_multiple_libraries(self):
        for libs in ({}, {"/a/libpolyml.so.16": {"sha256": p.LIB_SHA256},
                         "/b/libpolyml.so.16": {"sha256": p.LIB_SHA256}}):
            with self.subTest(libs=libs), self.assertRaises(ValueError):
                p.admit_library(libs)

    def test_known_word_counts_are_not_allocations(self):
        rows = p.observations(transcript())
        self.assertEqual(rows[1]["unknown_count"], 1)
        self.assertEqual(rows[2]["unknown_count"], 1)
        self.assertEqual(rows[2]["synthetic_requested_word_sum"], 1048576)
        self.assertEqual(rows[3]["synthetic_requested_word_sum"], 7340032)
        self.assertTrue(all("allocated_words" not in row for row in rows))

    def test_missing_duplicate_reordered_cases(self):
        lines = transcript().splitlines()
        for changed in (lines[1:], [lines[0]] + lines,
                        [lines[1], lines[0]] + lines[2:],
                        lines[:-1], lines + [lines[-1]]):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                p.observations("\n".join(changed))

    def test_reject_bad_counts(self):
        text = transcript()
        for bad in ("-1", "1.0", "true", "", "NaN"):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                p.observations(text.replace("one-word\t1\t13",
                                            "one-word\t" + bad + "\t13"))

    def test_reject_wrong_profiler_semantics(self):
        for old, new in (("million-words\t1", "million-words\t1048576"),
                         ("reset\t0", "reset\t1"),
                         ("collected\t7", "collected\t0"),
                         ("seven-events\t7\t19", "seven-events\t7\t0")):
            with self.subTest(new=new), self.assertRaises(ValueError):
                p.observations(transcript().replace(old, new))

    def test_unknown_marker_is_not_ignored(self):
        with self.assertRaises(ValueError):
            p.observations(transcript() + "@@TASK29_PROFILER_OTHER\t0\t0\n")

    def test_explicit_authorization_before_any_runtime_call(self):
        with self.assertRaises(SystemExit) as raised:
            p.main(["--output", "/must-not-be-created.json"])
        self.assertEqual(raised.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
