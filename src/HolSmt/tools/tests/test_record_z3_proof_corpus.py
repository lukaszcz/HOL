#!/usr/bin/env python3

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from record_z3_proof_corpus import extract_rule_report


class ProofRuleExtractionTests(unittest.TestCase):
    def test_extracts_histogram_from_z3_v4_wrapper(self):
        proof = """((set-logic QF_UF)
(proof
(let (($x25 (not a)))
 (let ((@x26 (asserted $x25)))
 (let ((@x24 (asserted a)))
 (unit-resolution @x24 @x26 false))))))
"""
        report = extract_rule_report(proof)
        self.assertEqual(report["rule_histogram"]["asserted"], 2)
        self.assertEqual(report["rule_histogram"]["unit-resolution"], 1)
        self.assertEqual(report["unknown_rules"], [])
        self.assertEqual(report["malformed_fragments"], [])

    def test_unknown_rule_is_reported_with_context(self):
        proof = """(proof
(let ((@x1 (mystery-rule false)))
  (unit-resolution @x1 false)))
"""
        report = extract_rule_report(proof)
        self.assertEqual(report["rule_histogram"]["mystery-rule"], 1)
        self.assertEqual(report["rule_histogram"]["unit-resolution"], 1)
        self.assertEqual(report["unknown_rules"][0]["rule"], "mystery-rule")
        self.assertIn("mystery-rule", report["unknown_rules"][0]["contexts"][0]["context"])

    def test_indexed_th_lemma_is_normalized_by_theory(self):
        proof = """(proof ((_ th-lemma arith farkas 1 1) @x1 @x2 false))"""
        report = extract_rule_report(proof)
        self.assertEqual(report["rule_histogram"], {"th-lemma-arith": 1})

    def test_malformed_fragment_is_recorded(self):
        report = extract_rule_report("(proof (asserted false)")
        self.assertEqual(report["rule_histogram"], {})
        self.assertEqual(len(report["malformed_fragments"]), 1)
        self.assertIn("missing", report["malformed_fragments"][0]["message"])


if __name__ == "__main__":
    unittest.main()
