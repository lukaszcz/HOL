#!/usr/bin/env python3

import json
import pathlib
import sys
import tempfile
import unittest


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import audit_proof_completeness as audit


def write(path, text):
    path.write_text(text, encoding="utf-8")


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def proof_source_text():
    return """
structure Z3_Proof =
struct
  datatype proofterm = ASSERTED of Term.term
                     | MP of proofterm * proofterm * Term.term
                     | TH_LEMMA_BASIC of th_lemma_metadata * proofterm list *
                         Term.term
                     | TH_LEMMA_ADVANCED of th_lemma_metadata * proofterm list *
                         Term.term

  val proof_rule_registry : proof_rule list = [
    mk_rule ("asserted", [], ZeroPremises, "asserted"),
    mk_rule ("mp", [], TwoPremises, "mp"),
    mk_rule ("th-lemma-basic", ["th-lemma[basic]"], ListPremises,
      "th_lemma[basic]"),
    mk_rule ("th-lemma-fp", ["th-lemma[fp]"], ListPremises,
      "th_lemma[advanced]")
  ]

  fun rule_names rule = []
end
"""


def unittest_source_text(*, include_mp=True):
    mp_case = (
        '    ("mp",\n'
        '      "((proof (mp (asserted true) (asserted (implies true false)) false)))",\n'
        "      ``F``),\n"
        if include_mp
        else ""
    )
    return f"""
structure Unittest =
struct
fun z3_core_proof_rule_replay_minimal_raw_success () =
let
  val cases = [
    ("asserted",
      "((proof (asserted false)))",
      ``F``),
{mp_case}    ("unit-resolution",
      "((proof (unit-resolution (asserted (or false true)) false)))",
      ``F``)
  ]
in
  ()
end

fun z3_th_lemma_existing_theory_replay_minimal_success () =
let
  val cases = []
in
  ()
end

fun z3_th_lemma_basic_unsupported_diagnostic () =
  replay_z3_proof_string "((proof ((_ th-lemma basic eq-propagate 7) false)))"

fun z3_th_lemma_advanced_unsupported_diagnostic () =
  replay_z3_proof_string "((proof ((_ th-lemma fp eq-propagate 1) false)))"
end
"""


def manifest_with_red_basic_and_fp():
    def row(rule):
        return {
            "id": f"proof-rule:{rule}",
            "file": f"cases/proof_rules/proof_rule_{rule.replace('-', '_')}.smt2",
            "logic": "QF_UF",
            "standard": "Z3-extension",
            "class": "proof-rule",
            "features": [f"proof-rule:{rule}"],
            "modes": ["proof-parse", "proof-replay"],
            "versions": ["4.13.0"],
            "expected": {
                "proof-parse": {
                    "status": "red",
                    "diagnostic": "diagnostic-only proof-rule obligation",
                    "failure_phase": "proof-parse",
                },
                "proof-replay": {
                    "status": "red",
                    "diagnostic": "diagnostic-only proof-rule obligation",
                    "failure_phase": "proof-replay",
                },
            },
            "implementation_obligation": {
                "files": ["src/HolSmt/Z3_ProofReplay.sml"],
                "feature": f"proof-rule:{rule}",
                "test_ids": [f"proof-rule:{rule}"],
                "failure_phase": "proof-replay",
            },
            "source": {
                "kind": "Z3-proof",
                "reference": f"Z3 proof rule {rule}",
            },
        }

    return {"schema_version": "2", "cases": [row("th-lemma-basic"), row("th-lemma-fp")]}


class ProofCompletenessAuditTests(unittest.TestCase):
    def build_fixture(self, include_mp=True, manifest=None, summary=None):
        tmp = tempfile.TemporaryDirectory()
        root = pathlib.Path(tmp.name)
        proof_source = root / "Z3_Proof.sml"
        unittest_source = root / "Unittest.sml"
        manifest_path = root / "manifest.json"
        summary_path = root / "summary.json"
        write(proof_source, proof_source_text())
        write(unittest_source, unittest_source_text(include_mp=include_mp))
        write_json(manifest_path, manifest if manifest is not None else manifest_with_red_basic_and_fp())
        write_json(
            summary_path,
            summary
            if summary is not None
            else {
                "schema": "holsmt-z3-proof-corpus-v1",
                "discovered_rules": ["asserted"],
                "aggregate_rule_histogram": {"asserted": 1},
            },
        )
        return tmp, proof_source, unittest_source, manifest_path, summary_path

    def test_parses_registry_and_th_lemma_classes(self):
        tmp, proof_source, *_ = self.build_fixture()
        self.addCleanup(tmp.cleanup)

        rules = audit.parse_proof_rules(proof_source)
        self.assertEqual([rule.name for rule in rules], ["asserted", "mp", "th-lemma-basic", "th-lemma-fp"])
        self.assertEqual(
            audit.parse_th_lemma_classes(proof_source, rules),
            ["th-lemma-basic", "th-lemma-fp"],
        )

    def test_reports_missing_synthetic_replay_test_as_blocking(self):
        tmp, proof_source, unittest_source, manifest_path, summary_path = self.build_fixture(include_mp=False)
        self.addCleanup(tmp.cleanup)

        report = audit.build_report(
            proof_source=proof_source,
            unittest_source=unittest_source,
            manifest_path=manifest_path,
            proof_summary_path=summary_path,
        )

        issues = report["issues"]
        self.assertTrue(
            any(issue["code"] == "missing_synthetic_replay_test" and issue["subject"] == "mp" for issue in issues),
            issues,
        )
        self.assertFalse(report["summary"]["passed"])

    def test_missing_real_occurrence_is_reported_but_nonblocking(self):
        tmp, proof_source, unittest_source, manifest_path, summary_path = self.build_fixture()
        self.addCleanup(tmp.cleanup)

        report = audit.build_report(
            proof_source=proof_source,
            unittest_source=unittest_source,
            manifest_path=manifest_path,
            proof_summary_path=summary_path,
        )

        real_issues = [issue for issue in report["issues"] if issue["code"] == "missing_real_proof_occurrence"]
        self.assertTrue(any(issue["subject"] == "mp" and not issue["blocking"] for issue in real_issues), real_issues)
        self.assertTrue(report["summary"]["passed"], report["issues"])

    def test_diagnostic_th_lemma_families_require_red_obligations(self):
        tmp, proof_source, unittest_source, manifest_path, summary_path = self.build_fixture(
            manifest={"schema_version": "2", "cases": []}
        )
        self.addCleanup(tmp.cleanup)

        report = audit.build_report(
            proof_source=proof_source,
            unittest_source=unittest_source,
            manifest_path=manifest_path,
            proof_summary_path=summary_path,
        )

        missing = {
            issue["subject"]
            for issue in report["issues"]
            if issue["code"] == "missing_th_lemma_red_obligation"
        }
        self.assertEqual(missing, {"th-lemma-basic", "th-lemma-fp"})
        self.assertFalse(report["summary"]["passed"])

    def test_checked_in_sources_have_synthetic_mapping_for_every_registry_rule(self):
        report = audit.build_report(
            proof_source=audit.DEFAULT_PROOF_SOURCE,
            unittest_source=audit.DEFAULT_UNITTEST_SOURCE,
            manifest_path=audit.DEFAULT_MANIFEST,
            proof_summary_path=audit.DEFAULT_PROOF_SUMMARY,
        )
        self.assertFalse(
            [issue for issue in report["issues"] if issue["code"] == "missing_synthetic_replay_test"],
            report["issues"],
        )


if __name__ == "__main__":
    unittest.main()
