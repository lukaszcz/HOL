#!/usr/bin/env python3

import hashlib
import json
import pathlib
import sys
import tempfile
import unittest
import contextlib
import io


TOOLS_DIR = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS_DIR))

import import_external_benchmarks as importer


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def source_lock():
    return {
        "schema_version": "holsmt-external-benchmark-sources-lock-v1",
        "sources": [
            {
                "id": "fixture-source",
                "kind": "unit-test",
                "url": "https://example.invalid/fixture",
                "pin": "unit-test",
                "pin_type": "fixture",
            }
        ],
    }


def pinned_manifest(content, sha256=None):
    case_id = "external-benchmark:fixture-qf-uf-sat"
    return {
        "schema_version": "holsmt-external-benchmarks-pinned-v1",
        "supported_logic_families": ["QF_UF"],
        "entries": [
            {
                "id": case_id,
                "source_id": "fixture-source",
                "source_url": "https://example.invalid/fixture/qf_uf_sat.smt2",
                "commit_or_release": "unit-test",
                "source_path": "fixture/qf_uf_sat.smt2",
                "sha256": sha256 or hashlib.sha256(content.encode("utf-8")).hexdigest(),
                "content": content,
                "target_file": "cases/external/fixture_qf_uf_sat.smt2",
                "logic_family": "QF_UF",
                "logic": "QF_UF",
                "standard": "SMT-LIB-2.7",
                "source_reference": "unit test pinned fixture",
                "features": [
                    "external-source:fixture",
                    "external-logic-family:QF_UF",
                    "external-status:sat",
                ],
                "expected_modes": [
                    "parser-only",
                    "typecheck-only",
                    "z3-oracle",
                    "z3-tac",
                ],
                "expected_status": {
                    "parser-only": {"status": "pass"},
                    "typecheck-only": {"status": "pass"},
                    "z3-oracle": {"status": "pass"},
                    "z3-tac": {
                        "status": "fail",
                        "diagnostic": "SAT benchmark has no HOL theorem to reconstruct",
                        "failure_phase": "theorem-shape",
                    },
                },
                "implementation_obligation": None,
            },
            {
                "id": "external-benchmark:fixture-qf-uf-missing-unsat-obligation",
                "source_id": "fixture-source",
                "source_url": "https://example.invalid/fixture/qf_uf_missing_unsat.smt2",
                "commit_or_release": "unit-test",
                "source_path": "fixture/qf_uf_missing_unsat.smt2",
                "sha256": hashlib.sha256(b"(set-logic QF_UF)\n").hexdigest(),
                "content": "(set-logic QF_UF)\n",
                "target_file": "cases/external/fixture_qf_uf_missing_unsat.smt2",
                "logic_family": "QF_UF",
                "logic": "QF_UF",
                "standard": "SMT-LIB-2.7",
                "source_reference": "unit test missing evidence obligation",
                "features": [
                    "external-source:fixture",
                    "external-logic-family:QF_UF",
                    "external-obligation:missing-benchmark-evidence",
                ],
                "expected_modes": ["parser-only"],
                "expected_status": {
                    "parser-only": {
                        "status": "red",
                        "diagnostic": "fixture lacks an UNSAT proof benchmark",
                        "failure_phase": "solver",
                    }
                },
                "implementation_obligation": {
                    "files": ["src/HolSmt/tools/external-benchmarks/pinned/manifest.json"],
                    "feature": "external-missing-benchmark-evidence:QF_UF",
                    "test_ids": ["external-benchmark:fixture-qf-uf-missing-unsat-obligation"],
                    "failure_phase": "solver",
                },
            },
        ],
    }


class ExternalBenchmarkImporterTests(unittest.TestCase):
    def test_import_verifies_hash_and_links_case_into_v2_manifest(self):
        content = "(set-logic QF_UF)\n(check-sat)\n"
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            pinned = root / "pinned.json"
            lock = root / "lock.json"
            corpus_root = root / "v2"
            corpus_manifest = corpus_root / "manifest.json"
            write_json(pinned, pinned_manifest(content))
            write_json(lock, source_lock())
            write_json(corpus_manifest, {"schema_version": "2", "cases": []})

            self.assertEqual(
                importer.main(
                    [
                        "--pinned-manifest",
                        str(pinned),
                        "--sources-lock",
                        str(lock),
                        "--corpus-root",
                        str(corpus_root),
                        "--corpus-manifest",
                        str(corpus_manifest),
                    ]
                ),
                0,
            )

            output = corpus_root / "cases" / "external" / "fixture_qf_uf_sat.smt2"
            self.assertEqual(output.read_text(encoding="utf-8"), content)
            manifest = json.loads(corpus_manifest.read_text(encoding="utf-8"))
            by_id = {case["id"]: case for case in manifest["cases"]}
            case = by_id["external-benchmark:fixture-qf-uf-sat"]
            self.assertEqual(case["class"], "external-benchmark")
            self.assertEqual(case["file"], "cases/external/fixture_qf_uf_sat.smt2")
            self.assertEqual(case["source"]["url"], "https://example.invalid/fixture/qf_uf_sat.smt2")

    def test_hash_mismatch_fails_before_writing_case(self):
        content = "(set-logic QF_UF)\n(check-sat)\n"
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            pinned = root / "pinned.json"
            lock = root / "lock.json"
            corpus_root = root / "v2"
            corpus_manifest = corpus_root / "manifest.json"
            write_json(pinned, pinned_manifest(content, sha256="0" * 64))
            write_json(lock, source_lock())
            write_json(corpus_manifest, {"schema_version": "2", "cases": []})

            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                self.assertEqual(
                    importer.main(
                        [
                            "--pinned-manifest",
                            str(pinned),
                            "--sources-lock",
                            str(lock),
                            "--corpus-root",
                            str(corpus_root),
                            "--corpus-manifest",
                            str(corpus_manifest),
                        ]
                    ),
                    1,
                )
            self.assertIn("hash mismatch", stderr.getvalue())

            self.assertFalse((corpus_root / "cases" / "external" / "fixture_qf_uf_sat.smt2").exists())
            self.assertEqual(json.loads(corpus_manifest.read_text(encoding="utf-8"))["cases"], [])


if __name__ == "__main__":
    unittest.main()
