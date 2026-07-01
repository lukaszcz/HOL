#!/usr/bin/env python3

import contextlib
import io
import json
import pathlib
import sys
import tempfile
import unittest


TOOLS_DIR = pathlib.Path(__file__).resolve().parents[1]
CORPUS_DIR = TOOLS_DIR / "conformance-corpus" / "v2"
sys.path.insert(0, str(TOOLS_DIR))
sys.path.insert(0, str(CORPUS_DIR))

import audit_complete_conformance as audit
import generate_complete_corpus as generator


class CompleteCorpusGeneratorTests(unittest.TestCase):
    def test_sample_manifest_has_one_valid_red_entry_for_each_class(self):
        manifest = generator.manifest_for_cases(generator.sample_cases())
        cases = audit.validate_v2_manifest(manifest)

        self.assertEqual(
            {case["class"] for case in cases},
            set(generator.CASE_CLASSES),
        )
        for case in cases:
            self.assertEqual(case["versions"], list(generator.SUPPORTED_Z3_VERSIONS))
            self.assertTrue(case["implementation_obligation"])
            self.assertTrue(
                all(result["status"] == "red" for result in case["expected"].values()),
                case,
            )

    def test_dry_run_output_is_deterministic_and_valid(self):
        stdout_a = io.StringIO()
        stdout_b = io.StringIO()

        with contextlib.redirect_stdout(stdout_a):
            self.assertEqual(generator.main([]), 0)
        with contextlib.redirect_stdout(stdout_b):
            self.assertEqual(generator.main([]), 0)

        self.assertEqual(stdout_a.getvalue(), stdout_b.getvalue())
        manifest = json.loads(stdout_a.getvalue())
        audit.validate_v2_manifest(manifest)

    def test_focused_domain_subcommand_emits_only_that_class(self):
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(generator.main(["proof-rules"]), 0)

        manifest = json.loads(stdout.getvalue())
        cases = audit.validate_v2_manifest(manifest)
        self.assertEqual(len(cases), 1)
        self.assertEqual(cases[0]["class"], "proof-rule")
        self.assertIn("proof-parse", cases[0]["expected"])
        self.assertIn("proof-replay", cases[0]["expected"])

    def test_manifest_entry_preserves_red_obligation_contract(self):
        case_id = generator.deterministic_case_id("command", "command:future")
        common = {
            "case_id": case_id,
            "file": generator.deterministic_case_file("command", case_id),
            "logic": "QF_UF",
            "standard": "SMT-LIB-2.7",
            "row_class": "command",
            "features": ["command:future"],
            "modes": ["parser-only"],
            "versions": ["4.13.0"],
            "source": generator.source("SMT-LIB-standard", "future command"),
        }

        with self.assertRaisesRegex(generator.GeneratorError, "implementation_obligation"):
            generator.manifest_entry(
                **common,
                expected={"parser-only": generator.expected_result("red")},
                implementation_obligation=None,
            )

        obligation = generator.implementation_obligation(
            files=["src/HolSmt/SmtLib_Parser.sml"],
            feature="command:future",
            test_ids=[case_id],
            failure_phase="parser",
        )
        with self.assertRaisesRegex(generator.GeneratorError, "must be null"):
            generator.manifest_entry(
                **common,
                expected={"parser-only": generator.expected_result("pass")},
                implementation_obligation=obligation,
            )

    def test_write_mode_is_idempotent_and_writes_case_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp) / "corpus"
            manifest_path = root / "manifest.json"

            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(generator.main(["--manifest", str(manifest_path), "samples", "--write"]), 0)
            first_manifest = manifest_path.read_text(encoding="utf-8")
            first_files = {
                str(path.relative_to(root)): path.read_text(encoding="utf-8")
                for path in sorted((root / "cases").rglob("*.smt2"))
            }

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(generator.main(["--manifest", str(manifest_path), "samples", "--write"]), 0)
            second_manifest = manifest_path.read_text(encoding="utf-8")
            second_files = {
                str(path.relative_to(root)): path.read_text(encoding="utf-8")
                for path in sorted((root / "cases").rglob("*.smt2"))
            }

            self.assertEqual(first_manifest, second_manifest)
            self.assertEqual(first_files, second_files)
            self.assertEqual(len(first_files), len(generator.CASE_CLASSES))
            audit.validate_v2_manifest(json.loads(second_manifest))

    def test_audit_subcommand_validates_existing_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest_path = pathlib.Path(tmp) / "manifest.json"
            manifest_path.write_text(
                json.dumps({"schema_version": "2", "cases": []}, indent=2) + "\n",
                encoding="utf-8",
            )

            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(generator.main(["--manifest", str(manifest_path), "audit"]), 0)

            self.assertIn("manifest ok: 0 case(s)", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
