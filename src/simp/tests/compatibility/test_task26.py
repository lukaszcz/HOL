"""Physical relocation and complete-output failure controls."""
import gzip
import importlib.util
import json
import re
from pathlib import Path
import unittest
from unittest.mock import patch

import normal_integration
import task10_relocation as typed
import task26_relocation as physical
from run_paired import BASE, HERE, InvalidRun, require_revisions

spec = importlib.util.spec_from_file_location(
    "native_legacy_runner", HERE.parent / "legacy-contracts/run.py")
legacy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(legacy)


def _strip_sml(text):
    """Drop SML comments; keep string contents with punctuation masked."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("*)", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif text[i] == '"':
            j = i + 1
            while text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(re.sub(r"[^A-Za-z0-9_ ]", "_", text[i:j + 1]))
            i = j + 1
        elif text.startswith("``", i):
            i = text.index("``", i + 2) + 2
            out.append("``")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def _list_length(text, start):
    """Top-level element count of the list literal opening at text[start]."""
    depth, count = 0, 1
    for j in range(start, len(text)):
        ch = text[j]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth == 0:
                return count
        elif ch == "," and depth == 1:
            count += 1
    raise ValueError("unterminated list")


def printed_vector_sizes(sml):
    """Map each `NAME_RESULTS` print of the native selftest to its length.

    Each print is `print ("NAME_RESULTS " ^ concatWith " " (map Bool.toString
    L) ...)` where L is a list literal or the nearest preceding `val L = [..]`.
    """
    text = _strip_sml(sml)
    pattern = (r'print \(\s*_([A-Z_]+_RESULTS) _ \^\s*String\.concatWith _ _'
               r'\s*\(map Bool\.toString\s*(\[|\w+)')
    sizes = {}
    for m in re.finditer(pattern, text):
        name, arg = m.groups()
        if arg == "[":
            start = m.end() - 1
        else:
            start = [d for d in re.finditer(
                r"val " + arg + r"\s*=\s*\[", text[:m.start()])][-1].end() - 1
        sizes[name] = _list_length(text, start)
    return sizes


class PhysicalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        require_revisions(BASE)

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

    def test_vectors_match_native_selftest_source(self):
        sml = (HERE.parent / "native-extension/selftest.sml").read_text()
        self.assertEqual(list(physical.VECTORS.items()),
                         list(printed_vector_sizes(sml).items()))

    def test_vectors_cannot_be_truncated_or_replaced(self):
        text = "".join(
            "pin ... OK\n" + name + " " + " ".join(["true"] * count) + "\n"
            for name, count in physical.VECTORS.items())
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
