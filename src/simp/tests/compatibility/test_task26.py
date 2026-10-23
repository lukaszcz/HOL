"""Physical relocation and complete-output failure controls."""
import gzip
import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import normal_integration
import task10_relocation as typed
import task26_relocation as physical
from run_paired import HERE, InvalidRun

spec = importlib.util.spec_from_file_location(
    "native_legacy_runner", HERE.parent / "legacy-contracts/run.py")
legacy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(legacy)


class PhysicalTests(unittest.TestCase):
    def test_exact_move_and_original(self):
        original = json.loads(typed.SUPPLEMENT.read_text())
        moved = physical.apply(original)
        self.assertNotIn("current_path", original["sources"][typed.NATIVE])
        self.assertEqual(physical.DESTINATION,
                         moved["sources"][typed.NATIVE]["current_path"])
        self.assertEqual(original["native"]["stream"],
                         moved["native"]["stream"])

    def test_physical_seals_are_not_optional(self):
        original = json.loads(typed.SUPPLEMENT.read_text())
        for name in ("source", "typed_mapping", "original"):
            changed = json.loads(physical.SUPPLEMENT.read_text())
            changed[name]["sha256"] = "wrong"
            with self.subTest(seal=name), patch.object(
                Path, "read_text", autospec=True,
                return_value=json.dumps(changed)):
                with self.assertRaises(InvalidRun):
                    physical.apply(original)

    def test_vectors_cannot_be_truncated_or_replaced(self):
        text = gzip.decompress((HERE.parent /
            "performance/review-20261021/native-selftest.log.gz").read_bytes()
            ).decode()
        physical.validate_vectors(text)
        for changed in (text.replace("POLICY_RESULTS ", "MISSING_RESULTS "),
                        text.replace("POLICY_RESULTS true",
                                     "POLICY_RESULTS false"), text[:-1]):
            with self.assertRaises(InvalidRun):
                physical.validate_vectors(changed)

    def test_missing_later_theory_checks_fail(self):
        supplement = typed.load()
        ledger = json.loads(gzip.decompress(typed.LEDGER.read_bytes()))
        stream = [s for s in supplement["native"]["stream"]
                  if not s.startswith("splitter: option case ...")]
        with self.assertRaises(InvalidRun):
            typed.validate_stream(ledger, "native", stream, supplement)


class FocusedOutputTests(unittest.TestCase):
    def test_counts_and_completions_are_mandatory(self):
        count, footers = normal_integration.SUITES["traverse-ext"]
        text = "pin ... OK\n" * count + "\n".join(footers) + "\n"
        normal_integration.validate("traverse-ext", text)
        for changed in (text.replace("pin ... OK\n", "", 1),
                        text.replace(footers[0], "wrong footer"), text[:-1]):
            with self.assertRaises(InvalidRun):
                normal_integration.validate("traverse-ext", changed)


class LegacyOutputTests(unittest.TestCase):
    def receipt(self):
        return {"exit": 0, "timed_out": False, "stdout":
                "pin ... OK\nOBS legacy.path=" + str(
                    legacy.REPO / "src/simp/src/Traverse.sml") +
                "\nOBS legacy.path=" + str(
                    legacy.REPO / "src/simp/src/simpLib.sml") +
                "\nOBS legacy.complete=PriorLimits:1\n"}

    def test_complete_output(self):
        legacy.validate(self.receipt(), "PriorLimits", ["pin"])

    def test_reject_wrong_label_missing_footer_path_or_exit(self):
        for old, new in (("pin ... OK", "other ... OK"),
                         ("OBS legacy.complete=PriorLimits:1\n", ""),
                         ("Traverse.sml", "Other.sml"),
                         (str(legacy.REPO / "src/simp/src"), "/foreign")):
            changed = self.receipt()
            changed["stdout"] = changed["stdout"].replace(old, new)
            with self.subTest(change=old), self.assertRaises(InvalidRun):
                legacy.validate(changed, "PriorLimits", ["pin"])
        changed = self.receipt()
        changed["exit"] = 1
        with self.assertRaises(InvalidRun):
            legacy.validate(changed, "PriorLimits", ["pin"])


if __name__ == "__main__":
    unittest.main()
