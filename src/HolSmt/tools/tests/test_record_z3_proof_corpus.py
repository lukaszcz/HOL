#!/usr/bin/env python3

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from record_z3_proof_corpus import (
    build_rule_gate_report,
    build_summary,
    expected_rules_for_version,
    extract_rule_report,
)


def entry(path, version, proof):
    return {
        "input": {"path": path},
        "z3": {"version": version},
        "proof": {"available": True, **proof},
    }


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
        self.assertEqual(sorted(report["rule_contexts"]), ["asserted", "unit-resolution"])
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

    def test_summary_records_stable_rule_lists_by_z3_version(self):
        proof_a = extract_rule_report("(proof (unit-resolution (asserted a) false))")
        proof_b = extract_rule_report("(proof (asserted false))")
        summary = build_summary(
            [
                entry("a.smt2", "4.13.0", proof_a),
                entry("b.smt2", "2.19.1", proof_b),
            ]
        )
        self.assertEqual(summary["discovered_rules"], ["asserted", "unit-resolution"])
        self.assertEqual(
            summary["rules_by_version"],
            [
                {
                    "z3_version": "2.19.1",
                    "rules": ["asserted"],
                    "rule_histogram": {"asserted": 1},
                },
                {
                    "z3_version": "4.13.0",
                    "rules": ["asserted", "unit-resolution"],
                    "rule_histogram": {"asserted": 1, "unit-resolution": 1},
                },
            ],
        )

    def test_expected_rules_are_version_aware(self):
        manifest = {
            "default": ["asserted"],
            "versions": {
                "4.*": ["unit-resolution"],
                "4.13.0": ["rewrite"],
            },
        }
        self.assertEqual(
            expected_rules_for_version(manifest, "4.13.0"),
            {"asserted", "unit-resolution", "rewrite"},
        )
        self.assertEqual(expected_rules_for_version(manifest, "2.19.1"), {"asserted"})

    def test_gate_flags_unseen_rule_with_version_input_and_context(self):
        proof = extract_rule_report("(proof (unit-resolution (asserted a) false))")
        report = build_rule_gate_report(
            [entry("minimal.smt2", "4.13.0", proof)],
            {"default": ["asserted"]},
        )
        self.assertFalse(report["passed"])
        self.assertEqual(report["unseen_rules"][0]["z3_version"], "4.13.0")
        self.assertEqual(report["unseen_rules"][0]["input"], "minimal.smt2")
        self.assertEqual(report["unseen_rules"][0]["rule"], "unit-resolution")
        self.assertIn(
            "unit-resolution",
            report["unseen_rules"][0]["contexts"][0]["context"],
        )

    def test_gate_flags_replay_unknown_rule_with_context(self):
        proof = extract_rule_report("(proof (mystery-rule false))")
        report = build_rule_gate_report(
            [entry("synthetic.smt2", "4.13.0", proof)],
            {"default": ["mystery-rule"]},
        )
        self.assertFalse(report["passed"])
        self.assertEqual(report["unseen_rules"], [])
        self.assertEqual(report["replay_unknown_rules"][0]["rule"], "mystery-rule")
        self.assertEqual(report["replay_unknown_rules"][0]["input"], "synthetic.smt2")
        self.assertIn(
            "mystery-rule",
            report["replay_unknown_rules"][0]["contexts"][0]["context"],
        )


if __name__ == "__main__":
    unittest.main()
