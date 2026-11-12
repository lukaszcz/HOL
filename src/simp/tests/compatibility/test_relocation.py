"""Fail-closed relocation controls; never regenerate the frozen oracle."""
import copy
import unittest

import coverage_ledger as coverage
import task10_relocation as relocation
from run_paired import InvalidRun


class RelocationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ledger = coverage.receipt(relocation.LEDGER)
        cls.supplement = relocation.load()

    def changed(self):
        return copy.deepcopy(self.supplement)

    def reject(self, supplement, message):
        with self.assertRaisesRegex(InvalidRun, message):
            relocation.verify(self.ledger, supplement)

    def test_source_and_all_occurrences(self):
        relocation.verify(self.ledger, self.supplement)
        self.assertEqual(630, len(self.supplement["native"]["cases"]))
        self.assertEqual(12, len(self.supplement["native"]["additions"]))

    def test_fresh_syntax_explicit_load_relocation(self):
        path = "src/simp/tests/fresh-load/syntax.ML"
        record = self.supplement["sources"][path]
        self.assertEqual(record["old"], self.ledger["sources"][path])
        rows = [r for r in self.supplement["anchors"]
                if r["old"]["path"] == path]
        self.assertEqual([4, 9], [r["old"]["line"] for r in rows])
        self.assertEqual([16, 21], [r["current"]["line"] for r in rows])
        self.assertEqual([r["old"]["literal"] for r in rows],
                         [r["current"]["literal"] for r in rows])
        changed = self.changed()
        del changed["sources"][path]
        self.reject(changed, "unexpected TASK_10 relocation source")
        changed = self.changed()
        changed["sources"][path]["current"]["sha256"] = "wrong"
        self.reject(changed, "destination")

    # TASK34: the four sources below carry the split_attribute_now helper
    # (3 lines) at or after their header, so later case anchors move by
    # that many lines (4 where the file also gained a blank separator).
    TASK34_SOURCES = {
        "src/simp/tests/fresh-load/identity-before.ML": 0,
        "src/simp/tests/fresh-load/identity-after.ML": 3,
        "src/simp/tests/split-persistence/heapSave.ML": 4,
        "src/simp/tests/split-persistence/heapVerify.ML": 4}

    def test_task34_sources_old_records_and_anchor_offsets(self):
        for path, offset in self.TASK34_SOURCES.items():
            with self.subTest(path=path):
                record = self.supplement["sources"][path]
                self.assertEqual(record["old"], self.ledger["sources"][path])
                rows = [r for r in self.supplement["anchors"]
                        if r["old"]["path"] == path]
                self.assertEqual(bool(rows), offset != 0)
                for row in rows:
                    self.assertEqual(row["old"]["literal"],
                                     row["current"]["literal"])
                    self.assertEqual(
                        row["current"]["line"] - row["old"]["line"], offset)

    def test_task34_sources_cannot_be_dropped(self):
        for path in self.TASK34_SOURCES:
            with self.subTest(path=path):
                changed = self.changed()
                del changed["sources"][path]
                self.reject(changed, "unexpected TASK_10 relocation source")

    def test_task34_shifted_anchor_is_not_a_wildcard(self):
        changed = self.changed()
        path = "src/simp/tests/split-persistence/heapVerify.ML"
        row = next(r for r in changed["anchors"]
                   if r["current"]["path"] == path)
        row["current"]["line"] -= 1
        self.reject(changed, "literal anchor")

    def test_fresh_syntax_anchor_is_not_a_wildcard(self):
        changed = self.changed()
        row = next(r for r in changed["anchors"]
                   if r["current"]["path"].endswith("/syntax.ML"))
        row["current"]["line"] -= 1
        self.reject(changed, "literal anchor")

    def test_old_source_hash(self):
        changed = self.changed()
        changed["sources"][relocation.NATIVE]["old"]["sha256"] = "wrong"
        self.reject(changed, "origin")

    def test_current_source_hash(self):
        changed = self.changed()
        changed["sources"][relocation.NATIVE]["current"]["sha256"] = "wrong"
        self.reject(changed, "destination")

    def test_old_git_revision(self):
        changed = self.changed()
        # A real but unrelated blob cannot supply the frozen source.
        changed["sources"][relocation.NATIVE]["old_revision"] = \
            "cccaa27d7099cbadc886983020cbe745db7793f3"
        self.reject(changed, "relocation history")

    def test_missing_anchor(self):
        changed = self.changed()
        changed["anchors"].pop()
        self.reject(changed, "case anchor")

    def test_stale_current_anchor(self):
        changed = self.changed()
        changed["anchors"][0]["current"]["line"] = 1
        self.reject(changed, "anchor")

    def test_same_count_different_stream(self):
        stream = self.supplement["native"]["stream"].copy()
        stream[0] = "replacement ... OK"
        with self.assertRaisesRegex(InvalidRun, "current native cases"):
            relocation.validate_stream(self.ledger, "native", stream,
                                       self.supplement)

    def test_extra_assertion_is_not_a_wildcard(self):
        changed = self.changed()
        row = changed["native"]["additions"][0]
        checks = [i for i, s in enumerate(changed["native"]["stream"])
                  if s.endswith(" ... OK") and not s.startswith("OBS ")]
        changed["native"]["stream"][checks[row["current_check"] - 1]] = \
            "extension registry: R4 invented ... OK"
        self.reject(changed, "assertion label")

    def test_warning_is_not_filtered(self):
        changed = self.changed()
        stream = changed["native"]["stream"]
        index = next(i for i, s in enumerate(stream)
                     if s.startswith("<<HOL warning:"))
        stream[index] = "<<HOL warning: replacement>>"
        self.reject(changed, "frozen native subsequence")

    def test_reordered_frozen_subsequence(self):
        changed = self.changed()
        changed["native"]["original_event_positions"][:2] = [2, 1]
        self.reject(changed, "ordered frozen")

    def test_lost_original_case(self):
        changed = self.changed()
        changed["native"]["cases"].pop()
        self.reject(changed, "original native case")

    def test_reordered_duplicate_case_ids(self):
        changed = self.changed()
        rows = changed["native"]["cases"]
        rows[-3], rows[-2] = rows[-2], rows[-3]
        self.reject(changed, "relocation ID")

    def test_no_unclassified_body_change(self):
        changed = self.changed()
        changed["native"]["cases"][-1]["decision"] = "unknown"
        self.reject(changed, "typed body decision")

    def test_ordinary_and_unchanged_suites_stay_exact(self):
        for label, suite in self.ledger["suites"].items():
            if label == "native":
                continue
            with self.subTest(suite=label):
                relocation.validate_stream(self.ledger, label, suite["stream"],
                                           self.supplement)
                changed = suite["stream"].copy()
                changed[0] += " replacement"
                with self.assertRaisesRegex(InvalidRun, "current native cases"):
                    relocation.validate_stream(self.ledger, label, changed,
                                               self.supplement)


if __name__ == "__main__":
    unittest.main()
