#!/usr/bin/env python3

import contextlib
import io
import json
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "coverage"))

import audit_coverage_manifest as audit


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def minimal_coverage(rows):
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
        "commands": rows,
    }


def row(item, tested):
    return {
        "item": item,
        "class": "SMT-LIB 2.7",
        "parsed": "implemented",
        "translated": "implemented",
        "solved": "implemented",
        "reconstructed": "implemented",
        "tested": tested,
    }


def manifest_entry(item, phases, expected_status, *, positive=None, negative=None, artifacts=None, z3_versions=None):
    return {
        "section": "commands",
        "item": item,
        "class": "SMT-LIB 2.7",
        "phases": phases,
        "expected_status": expected_status,
        "positive_tests": positive or [],
        "negative_tests": negative or [],
        "z3_versions": z3_versions or [],
        "artifacts": artifacts or [],
    }


class CoverageManifestAuditTests(unittest.TestCase):
    def test_validation_rejects_malformed_manifest_entry(self):
        coverage = minimal_coverage([row("set-logic", "implemented")])
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                {
                    "section": "commands",
                    "item": "set-logic",
                    "class": "SMT-LIB 2.7",
                    "phases": ["parsed"],
                    "expected_status": "implemented",
                    "positive_tests": [],
                    "negative_tests": [],
                    "z3_versions": [],
                }
            ],
        }

        with self.assertRaisesRegex(audit.ManifestError, "artifacts"):
            audit.validate_manifest(manifest, coverage)

    def test_report_only_prints_untested_and_unknown_rows_without_failing(self):
        coverage = minimal_coverage(
            [
                row("set-logic", "implemented"),
                row("future-command", "untested"),
                row("smtlib3-command", "unknown"),
            ]
        )
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                {
                    "section": "commands",
                    "item": "set-logic",
                    "class": "SMT-LIB 2.7",
                    "phases": ["parsed", "translated", "solved", "reconstructed", "tested"],
                    "expected_status": "implemented",
                    "positive_tests": [{"kind": "manual", "description": "synthetic test"}],
                    "negative_tests": [],
                    "z3_versions": [],
                    "artifacts": [],
                }
            ],
        }

        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            coverage_path = root / "coverage.json"
            manifest_path = root / "manifest.json"
            write_json(coverage_path, coverage)
            write_json(manifest_path, manifest)
            stdout = io.StringIO()

            with contextlib.redirect_stdout(stdout):
                code = audit.main(
                    [
                        "--coverage",
                        str(coverage_path),
                        "--manifest",
                        str(manifest_path),
                    ]
                )

        output = stdout.getvalue()
        self.assertEqual(code, 0)
        self.assertIn("report-only mode", output)
        self.assertIn("missing_manifest_entry: commands/future-command", output)
        self.assertIn("tested=untested", output)
        self.assertIn("missing_manifest_entry: commands/smtlib3-command", output)
        self.assertIn("tested=unknown", output)

    def test_enforce_rejects_untested_and_unknown_rows(self):
        coverage = minimal_coverage(
            [
                row("future-command", "untested"),
                row("smtlib3-command", "unknown"),
            ]
        )
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                manifest_entry(
                    "future-command",
                    ["parsed", "translated", "solved", "reconstructed", "tested"],
                    "untested",
                    positive=[{"kind": "manual", "description": "placeholder"}],
                ),
                manifest_entry(
                    "smtlib3-command",
                    ["parsed", "translated", "solved", "reconstructed", "tested"],
                    "unknown",
                    positive=[{"kind": "manual", "description": "placeholder"}],
                ),
            ],
        }

        issues = audit.audit(coverage, manifest, [], [], pathlib.Path.cwd())

        self.assertTrue(
            any(issue.code == "unresolved_expected_status" for issue in issues),
            [issue.render() for issue in issues],
        )

    def test_enforce_rejects_missing_implemented_and_unsupported_evidence(self):
        coverage = minimal_coverage(
            [
                row("implemented-command", "implemented"),
                {
                    **row("unsupported-command", "unsupported_diagnostic"),
                    "parsed": "unsupported_diagnostic",
                    "translated": "unsupported_diagnostic",
                    "solved": "unsupported_diagnostic",
                    "reconstructed": "unsupported_diagnostic",
                },
            ]
        )
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                manifest_entry(
                    "implemented-command",
                    ["parsed", "translated", "solved", "reconstructed", "tested"],
                    "implemented",
                ),
                manifest_entry(
                    "unsupported-command",
                    ["parsed", "translated", "solved", "reconstructed", "tested"],
                    "unsupported_diagnostic",
                ),
            ],
        }

        issue_codes = {
            issue.code
            for issue in audit.audit(coverage, manifest, [], [], pathlib.Path.cwd())
        }

        self.assertIn("missing_positive_tests", issue_codes)
        self.assertIn("missing_negative_tests", issue_codes)

    def test_conformance_result_and_z3_version_evidence_must_match_reports(self):
        coverage = minimal_coverage([row("set-logic", "implemented")])
        manifest = {
            "schema": audit.SCHEMA,
            "entries": [
                manifest_entry(
                    "set-logic",
                    ["parsed", "translated", "solved", "reconstructed", "tested"],
                    "implemented",
                    positive=[
                        {
                            "kind": "conformance_result",
                            "logic": "QF_UF",
                            "mode": "parser-only",
                            "status": "pass",
                        }
                    ],
                    z3_versions=["4.13.0"],
                )
            ],
        }
        conformance_report = {
            "results": [
                {
                    "logic": "QF_UF",
                    "mode": "parser-only",
                    "status": "pass",
                }
            ],
            "proof_corpus_summary": {
                "z3_versions": [
                    {
                        "version": "4.13.0",
                        "entry_count": 1,
                        "proof_count": 1,
                    }
                ],
            },
        }

        self.assertEqual(
            audit.audit(coverage, manifest, [conformance_report], [], pathlib.Path.cwd()),
            [],
        )

        missing_report_issues = audit.audit(coverage, manifest, [], [], pathlib.Path.cwd())
        self.assertTrue(
            any(issue.code == "invalid_positive_tests" for issue in missing_report_issues),
            [issue.render() for issue in missing_report_issues],
        )
        self.assertTrue(
            any(issue.code == "missing_z3_version_evidence" for issue in missing_report_issues),
            [issue.render() for issue in missing_report_issues],
        )


if __name__ == "__main__":
    unittest.main()
