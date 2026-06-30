#!/usr/bin/env python3

import copy
import pathlib
import sys
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


def manifest_entry(row, phases, expected_status, positive_tests=None, negative_tests=None):
    return {
        "section": "commands",
        "item": row["item"],
        "class": row["class"],
        "phases": phases,
        "expected_status": expected_status,
        "positive_tests": [] if positive_tests is None else positive_tests,
        "negative_tests": [] if negative_tests is None else negative_tests,
        "z3_versions": [],
        "artifacts": [],
    }


class CoverageGenerationPolicyTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
