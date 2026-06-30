#!/usr/bin/env python3

import copy
import contextlib
import io
import json
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "coverage"))

import audit_coverage_manifest as audit
import generate_smtlib_coverage as generator


def minimal_coverage(row):
    return {
        "metadata": {},
        "status_legend": {
            "implemented": "Implemented.",
            "parse_only": "Parse only.",
            "unsupported_diagnostic": "Unsupported diagnostic.",
            "untested": "Untested.",
            "unknown": "Unknown.",
            "not_applicable": "Not applicable.",
        },
        "source_classes": {
            "SMT-LIB 2.7": "Official surface.",
            "Z3 extension": "Z3-specific surface.",
        },
        "commands": [row],
    }


def generation_coverage(command_row, unsupported_row):
    status_row = {
        "item": "synthetic",
        "class": "SMT-LIB 2.7",
        "parsed": "not_applicable",
        "translated": "not_applicable",
        "solved": "not_applicable",
        "reconstructed": "not_applicable",
        "tested": "not_applicable",
    }
    return {
        "metadata": {
            "title": "Synthetic SMT-LIB Coverage",
            "smtlib_target": "2.7",
            "last_reviewed": "test",
            "generator": "test",
            "scope_note": "Synthetic generation policy fixture.",
        },
        "status_legend": {
            "implemented": "Implemented.",
            "parse_only": "Parse only.",
            "unsupported_diagnostic": "Unsupported diagnostic.",
            "untested": "Untested.",
            "unknown": "Unknown.",
            "not_applicable": "Not applicable.",
        },
        "source_classes": {
            "SMT-LIB 2.7": "Official surface.",
            "Z3 extension": "Z3-specific surface.",
        },
        "version_targets": [
            {
                **status_row,
                "item": "synthetic version",
                "parsed": "parse_only",
                "tested": "unknown",
            }
        ],
        "commands": [command_row],
        "theories": [{**status_row, "item": "synthetic theory", "tested": "unknown"}],
        "logics": [{**status_row, "item": "synthetic logic", "tested": "untested"}],
        "z3_proof_rules": [unsupported_row],
        "selftest_categories": [{**status_row, "item": "synthetic selftest"}],
        "soundness_audit": [{**status_row, "item": "synthetic audit"}],
    }


def implemented_row():
    return {
        "item": "set-logic",
        "class": "SMT-LIB 2.7",
        "parsed": "implemented",
        "translated": "not_applicable",
        "solved": "not_applicable",
        "reconstructed": "not_applicable",
        "tested": "implemented",
        "test_ids": [],
        "diagnostic_test_ids": [],
        "last_verified_by": "coverage_manifest.json",
    }


def command_coverage_row():
    return {
        "item": "SMT-LIB 2.7 command surface",
        "class": "SMT-LIB 2.7",
        "commands": sorted(generator.OFFICIAL_SMTLIB_27_COMMANDS),
        "parsed": "implemented",
        "translated": "not_applicable",
        "solved": "not_applicable",
        "reconstructed": "not_applicable",
        "tested": "implemented",
    }


def unsupported_rule_row():
    return {
        "item": "synthetic unsupported rule",
        "class": "Z3 extension",
        "parsed": "not_applicable",
        "translated": "not_applicable",
        "solved": "not_applicable",
        "reconstructed": "unsupported_diagnostic",
        "tested": "not_applicable",
    }


def manifest_entry(
    row,
    phases,
    expected_status,
    positive_tests=None,
    negative_tests=None,
    section="commands",
):
    return {
        "section": section,
        "item": row["item"],
        "class": row["class"],
        "phases": phases,
        "expected_status": expected_status,
        "positive_tests": [] if positive_tests is None else positive_tests,
        "negative_tests": [] if negative_tests is None else negative_tests,
        "z3_versions": [],
        "artifacts": [],
    }


def source_evidence():
    return {
        "kind": "source",
        "path": "src/HolSmt/tools/tests/test_generate_smtlib_coverage.py",
        "match": "CoverageGenerationPolicyTests",
    }


def manual_evidence(description):
    return {"kind": "manual", "description": description}


class CoverageGenerationPolicyTests(unittest.TestCase):
    def run_generation(self, coverage, manifest):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            coverage_path = root / "coverage.json"
            manifest_path = root / "manifest.json"
            report_path = root / "coverage.md"
            coverage_path.write_text(json.dumps(coverage, indent=2) + "\n", encoding="utf-8")
            manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
            stderr = io.StringIO()

            with contextlib.redirect_stderr(stderr):
                code = generator.main(
                    [
                        "--coverage",
                        str(coverage_path),
                        "--manifest",
                        str(manifest_path),
                        "--report",
                        str(report_path),
                    ]
                )

        return code, stderr.getvalue()

    def test_tested_implemented_rejects_manual_only_positive_evidence(self):
        row = implemented_row()
        coverage = minimal_coverage(row)
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                manifest_entry(
                    row,
                    ["parsed", "tested"],
                    "implemented",
                    positive_tests=[
                        {"kind": "manual", "description": "synthetic prose claim"}
                    ],
                )
            ],
        }

        with self.assertRaisesRegex(SystemExit, "executable positive evidence"):
            generator.validate_claim_discipline(coverage, manifest)

    def test_unsupported_diagnostic_rejects_manual_only_negative_evidence(self):
        row = implemented_row()
        row.update(
            {
                "parsed": "not_applicable",
                "reconstructed": "unsupported_diagnostic",
                "tested": "not_applicable",
            }
        )
        coverage = minimal_coverage(row)
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                manifest_entry(
                    row,
                    ["reconstructed"],
                    "unsupported_diagnostic",
                    negative_tests=[
                        {"kind": "manual", "description": "synthetic diagnostic claim"}
                    ],
                )
            ],
        }

        with self.assertRaisesRegex(SystemExit, "executable diagnostic evidence"):
            generator.validate_claim_discipline(coverage, manifest)

    def test_release_mode_rejects_unknown_rows(self):
        row = implemented_row()
        for phase in generator.STATUS_COLUMNS:
            row[phase] = "unknown"
        coverage = minimal_coverage(row)

        with self.assertRaisesRegex(SystemExit, "unknown status in release mode"):
            generator.validate_release_unknowns(coverage)

    def test_enrichment_adds_test_and_diagnostic_ids(self):
        row = implemented_row()
        row["reconstructed"] = "unsupported_diagnostic"
        coverage = minimal_coverage(copy.deepcopy(row))
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                manifest_entry(
                    row,
                    ["parsed", "tested"],
                    "implemented",
                    positive_tests=[
                        {
                            "kind": "source",
                            "path": "src/HolSmt/Unittest.sml",
                            "match": "script_ast_metadata_decls_success",
                        }
                    ],
                ),
                manifest_entry(
                    row,
                    ["reconstructed"],
                    "unsupported_diagnostic",
                    negative_tests=[
                        {
                            "kind": "source",
                            "path": "src/HolSmt/Unittest.sml",
                            "match": "smtlib_command_malformed_diagnostics",
                        }
                    ],
                ),
            ],
        }

        enriched = generator.enrich_rows_with_manifest_evidence(coverage, manifest, [], [])
        enriched_row = enriched["commands"][0]
        self.assertEqual(
            enriched_row["test_ids"],
            [
                "source:src/HolSmt/Unittest.sml#script_ast_metadata_decls_success"
            ],
        )
        self.assertEqual(
            enriched_row["diagnostic_test_ids"],
            [
                "source:src/HolSmt/Unittest.sml#smtlib_command_malformed_diagnostics"
            ],
        )
        self.assertEqual(enriched_row["last_verified_by"], "coverage_manifest.json")

    def test_generation_rejects_manual_only_implemented_claim(self):
        command_row = command_coverage_row()
        unsupported_row = unsupported_rule_row()
        coverage = generation_coverage(command_row, unsupported_row)
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                manifest_entry(
                    command_row,
                    ["parsed", "tested"],
                    "implemented",
                    positive_tests=[manual_evidence("synthetic prose claim")],
                ),
                manifest_entry(
                    unsupported_row,
                    ["reconstructed"],
                    "unsupported_diagnostic",
                    negative_tests=[source_evidence()],
                    section="z3_proof_rules",
                ),
            ],
        }

        code, stderr = self.run_generation(coverage, manifest)
        self.assertEqual(code, 1)
        self.assertIn("executable positive evidence", stderr)

    def test_generation_rejects_manual_only_unsupported_diagnostic(self):
        command_row = command_coverage_row()
        unsupported_row = unsupported_rule_row()
        coverage = generation_coverage(command_row, unsupported_row)
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                manifest_entry(
                    command_row,
                    ["parsed", "tested"],
                    "implemented",
                    positive_tests=[source_evidence()],
                ),
                manifest_entry(
                    unsupported_row,
                    ["reconstructed"],
                    "unsupported_diagnostic",
                    negative_tests=[manual_evidence("synthetic prose diagnostic")],
                    section="z3_proof_rules",
                ),
            ],
        }

        code, stderr = self.run_generation(coverage, manifest)
        self.assertEqual(code, 1)
        self.assertIn("executable diagnostic evidence", stderr)


if __name__ == "__main__":
    unittest.main()
