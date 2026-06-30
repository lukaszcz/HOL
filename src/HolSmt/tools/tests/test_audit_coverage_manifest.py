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


if __name__ == "__main__":
    unittest.main()
