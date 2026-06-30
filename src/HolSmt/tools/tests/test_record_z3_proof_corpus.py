#!/usr/bin/env python3

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from record_z3_proof_corpus import (
    DEFAULT_SUPPORTED_VERSION_MANIFEST,
    PARSE_ONLY_RULES,
    REPLAY_SUPPORTED_RULES,
    RULE_PREMISE_KIND,
    build_rule_gate_report,
    build_summary,
    expected_rules_for_version,
    extract_rule_report,
    validate_corpus_manifest,
)


def entry(path, version, proof):
    return {
        "input": {"path": path},
        "z3": {"version": version},
        "proof": {"available": True, **proof},
    }


class ProofRuleExtractionTests(unittest.TestCase):
    def proof_fragment_for_rule(self, rule):
        if rule.startswith("th-lemma-"):
            theory = rule.removeprefix("th-lemma-")
            return f"((_ th-lemma {theory}) (asserted a) false)"
        if rule == "rewrite":
            return "((_ rewrite) false)"

        premise_kind = RULE_PREMISE_KIND[rule]
        if premise_kind == "zero":
            return f"({rule} false)"
        if premise_kind == "one":
            return f"({rule} (asserted a) false)"
        if premise_kind == "two":
            return f"({rule} (asserted a) (asserted b) false)"
        if premise_kind == "list":
            return f"({rule} (asserted a) (asserted b) false)"
        self.fail(f"unsupported synthetic premise kind for {rule}: {premise_kind}")

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

    def test_all_core_replay_rules_have_raw_proof_extraction_coverage(self):
        core_rules = sorted(
            rule for rule in REPLAY_SUPPORTED_RULES if not rule.startswith("th-lemma-")
        )
        proof = "(proof\n  " + "\n  ".join(
            self.proof_fragment_for_rule(rule) for rule in core_rules
        ) + "\n)"

        report = extract_rule_report(proof)

        for rule in core_rules:
            self.assertIn(rule, report["rule_histogram"])
        self.assertEqual(report["unknown_rules"], [])
        self.assertEqual(report["malformed_fragments"], [])

    def test_parse_only_rule_is_recorded_but_not_replay_unknown(self):
        proof = "(proof (proof-bind (asserted false)))"
        report = extract_rule_report(proof)
        gate = build_rule_gate_report(
            [entry("proof-bind.smt2", "4.12.4", report)],
            {"default": ["asserted", "proof-bind"]},
        )

        self.assertEqual(PARSE_ONLY_RULES, {"proof-bind"})
        self.assertEqual(report["rule_histogram"]["proof-bind"], 1)
        self.assertEqual(report["unknown_rules"], [])
        self.assertTrue(gate["passed"])
        self.assertEqual(gate["replay_unknown_rules"], [])
        self.assertEqual(gate["parse_only_rules"][0]["rule"], "proof-bind")

    def test_parse_only_rule_is_reported_without_expected_manifest(self):
        proof = extract_rule_report("(proof (proof-bind (asserted false)))")
        gate = build_rule_gate_report(
            [entry("proof-bind.smt2", "4.12.4", proof)],
            None,
        )

        self.assertTrue(gate["passed"])
        self.assertEqual(gate["unseen_rules"], [])
        self.assertEqual(gate["replay_unknown_rules"], [])
        self.assertEqual(gate["parse_only_rules"][0]["rule"], "proof-bind")

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
        self.assertEqual(summary["proof_rule_support"]["parse_only"], ["proof-bind"])
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

    def test_checked_in_supported_version_manifest_validates(self):
        self.assertEqual(validate_corpus_manifest(DEFAULT_SUPPORTED_VERSION_MANIFEST), [])

    def test_supported_version_manifest_requires_all_supported_versions(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest = pathlib.Path(tmp) / "manifest.json"
            manifest.write_text(
                """{
  "schema": "holsmt-z3-proof-corpus-matrix-v1",
  "supported_z3_versions": ["4.13.0"],
  "expected_rules": "expected.json",
  "expected_summary": "summary.json",
  "expected_gate": "rule-gate.json",
  "inputs": [],
  "versions": [],
  "missing_replay_supported_justifications": {},
  "missing_parse_only_justifications": {}
}
""",
                encoding="utf-8",
            )

            errors = validate_corpus_manifest(manifest)

        self.assertTrue(
            any("supported_z3_versions mismatch" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("versions must contain exactly" in error for error in errors),
            errors,
        )


if __name__ == "__main__":
    unittest.main()
