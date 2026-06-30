#!/usr/bin/env python3

import json
import os
import pathlib
import stat
import sys
import tempfile
import textwrap
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import run_conformance_suite as conformance


def make_fake_z3(directory, proof_rule="asserted"):
    path = pathlib.Path(directory) / "fake-z3"
    script = f"""#!/usr/bin/env python3
import pathlib
import sys

if "-version" in sys.argv:
    print("Z3 version 4.13.0")
    raise SystemExit(0)

input_path = pathlib.Path(sys.argv[-1])
text = input_path.read_text(encoding="utf-8")
is_unsat = "(assert false)" in text or "(not " in text
print("unsat" if is_unsat else "sat")
if is_unsat and "(get-proof" in text:
    print("(proof ({proof_rule} false))")
"""
    path.write_text(script, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


class ConformanceSuiteTests(unittest.TestCase):
    def test_default_suite_represents_every_official_logic(self):
        cases = conformance.default_cases(None)
        represented = {case.logic for case in cases}
        self.assertFalse(set(conformance.OFFICIAL_LOGICS) - represented)
        self.assertIn("ALL", represented)
        self.assertTrue(any("metamorphic" in case.tags for case in cases))

    def test_versioned_corpus_covers_core_uf_and_arithmetic_families(self):
        cases = conformance.corpus_cases([conformance.DEFAULT_CORPUS_DIR], None)
        by_name = {case.name: case for case in cases}
        represented = {case.logic for case in cases}
        expected_logics = {
            "QF_UF",
            "UF",
            "QF_IDL",
            "QF_LIA",
            "QF_NIA",
            "QF_UFIDL",
            "QF_UFLIA",
            "LIA",
            "NIA",
            "UFIDL",
            "UFLIA",
            "UFNIA",
            "QF_RDL",
            "QF_LRA",
            "QF_NRA",
            "QF_UFLRA",
            "QF_UFNRA",
            "LRA",
            "NRA",
            "UFLRA",
            "UFNRA",
            "QF_LIRA",
            "QF_NIRA",
            "QF_UFLIRA",
            "QF_UFNIRA",
        }

        self.assertFalse(expected_logics - represented)
        self.assertIn("qf_uf_core_operators_sat", by_name)
        self.assertIn("qf_uf_symbols_sat", by_name)
        self.assertIn("uf_quantified_shadowing_sat", by_name)
        self.assertIn("qf_nia_div_mod_audit", by_name)
        self.assertIn("qf_nra_real_division_audit", by_name)
        self.assertIn("qf_lira_conversions_audit", by_name)
        self.assertIn("qf_lia_nonlinear_audit", by_name)
        self.assertIn("qf_uf_malformed_sexp_parser_error", by_name)
        self.assertIn("qf_uf_unterminated_string_parser_error", by_name)
        self.assertIn("qf_uf_duplicate_declaration_type_error", by_name)
        self.assertIn("qf_uf_sat_theorem_request_z3_tac_error", by_name)
        self.assertEqual(
            by_name["qf_uf_duplicate_declaration_type_error"].expected[
                conformance.MODE_TYPECHECK
            ].diagnostic_substring,
            "duplicate declaration for symbol 'p'",
        )
        metamorphic_groups = {
            tag.removeprefix("metamorphic-group:")
            for case in cases
            for tag in case.tags
            if tag.startswith("metamorphic-group:")
        }
        self.assertGreaterEqual(
            metamorphic_groups,
            {
                "alpha-renaming",
                "quoted-symbol-variant",
                "assertion-order-permutation",
                "commutative-operands",
                "nested-let-expansion",
                "push-pop-equivalence",
                "reset-assertions-equivalence",
                "boolean-rewrite-equivalence",
                "bv-width-parametrized-identity",
            },
        )
        self.assertEqual(
            by_name["qf_uf_unsat_proof"].modes,
            (
                conformance.MODE_PARSER,
                conformance.MODE_TYPECHECK,
                conformance.MODE_Z3_ORACLE,
                conformance.MODE_PROOF_PARSE,
                conformance.MODE_PROOF_REPLAY,
                conformance.MODE_Z3_TAC,
            ),
        )
        self.assertEqual(
            by_name["qf_lia_type_error"].expected[conformance.MODE_TYPECHECK].status,
            conformance.FAIL,
        )
        self.assertEqual(
            by_name["qf_lia_type_error"].expected[conformance.MODE_TYPECHECK].diagnostic_substring,
            "expected sort :bool",
        )

    def test_corpus_dir_cli_uses_manifest_names_modes_and_origins(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            out_dir = root / "out"
            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--corpus-dir",
                    str(conformance.DEFAULT_CORPUS_DIR),
                    "--mode",
                    conformance.MODE_PARSER,
                    "--logic",
                    "QF_UF",
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            by_case = {case["name"]: case for case in report["cases"]}
            self.assertIn("qf_uf_core_operators_sat", by_case)
            self.assertEqual(by_case["qf_uf_core_operators_sat"]["origin"], "corpus:v1")
            self.assertIn("corpus", by_case["qf_uf_core_operators_sat"]["tags"])
            self.assertGreaterEqual(
                report["summary"]["by_logic_mode"]["QF_UF"][conformance.MODE_PARSER]["pass"],
                20,
            )
            self.assertEqual(report["conformance_status_counts"][conformance.FAIL], 0)
            self.assertGreaterEqual(report["metamorphic_groups"]["group_count"], 8)
            self.assertEqual(
                report["metamorphic_groups"]["status_counts"][conformance.FAIL],
                0,
            )

    def test_external_benchmark_dir_and_unsupported_mode_are_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bench_dir = root / "bench"
            bench_dir.mkdir()
            (bench_dir / "case.smt2").write_text(
                "(set-logic QF_LIA)\n(assert true)\n(check-sat)\n",
                encoding="utf-8",
            )
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(bench_dir),
                    "--mode",
                    conformance.MODE_PARSER,
                    "--mode",
                    conformance.MODE_Z3_TAC,
                    "--z3-tac-command",
                    "",
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            qf_lia = report["summary"]["by_logic_mode"]["QF_LIA"]
            self.assertEqual(qf_lia[conformance.MODE_PARSER]["pass"], 1)
            self.assertEqual(qf_lia[conformance.MODE_Z3_TAC]["unsupported"], 1)
            self.assertIn("no z3-tac command configured", "\n".join(report["summary"]["unsupported_reasons"]))
            self.assertEqual(
                report["external_benchmark_coverage"]["by_kind"]["benchmark"]["cases"],
                1,
            )

    def test_external_benchmark_duplicate_file_stems_get_distinct_case_names(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bench_dir = root / "bench"
            (bench_dir / "family-a").mkdir(parents=True)
            (bench_dir / "family-b").mkdir(parents=True)
            for family, logic in (("family-a", "QF_UF"), ("family-b", "QF_LIA")):
                (bench_dir / family / "case.smt2").write_text(
                    f"; family: {family}\n(set-logic {logic})\n(assert true)\n(check-sat)\n",
                    encoding="utf-8",
                )
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(bench_dir),
                    "--mode",
                    conformance.MODE_PARSER,
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            case_names = [case["name"] for case in report["cases"]]
            self.assertEqual(len(case_names), 2)
            self.assertEqual(len(set(case_names)), 2)
            self.assertEqual(
                report["external_benchmark_coverage"]["by_kind"]["benchmark"]["cases"],
                2,
            )
            self.assertEqual(
                report["external_benchmark_coverage"]["by_logic"]["QF_UF"]["cases"],
                1,
            )
            self.assertEqual(
                report["external_benchmark_coverage"]["by_logic"]["QF_LIA"]["cases"],
                1,
            )

    def test_external_source_manifest_regressions_and_unsupported_families_are_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bench_dir = root / "bench"
            proof_dir = root / "proof"
            regression_dir = root / "regression"
            for directory in (bench_dir, proof_dir, regression_dir):
                directory.mkdir()
            (bench_dir / "bench.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; family: uf-official
                    ; holsmt-expected: {"z3-tac": {"status": "unsupported", "diagnostic": "no z3-tac command configured"}}
                    (set-logic QF_UF)
                    (declare-const p Bool)
                    (assert p)
                    (check-sat)
                    """
                ),
                encoding="utf-8",
            )
            (proof_dir / "proof.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; family: z3-proof-smoke
                    ; holsmt-expected: {"z3-tac": {"status": "unsupported", "diagnostic": "no z3-tac command configured"}}
                    (set-logic QF_LIA)
                    (assert false)
                    (check-sat)
                    """
                ),
                encoding="utf-8",
            )
            (regression_dir / "regression.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; family: unsupported-queries
                    ; holsmt-expected: {"z3-tac": {"status": "unsupported", "diagnostic": "no z3-tac command configured"}}
                    (set-logic QF_UF)
                    (assert true)
                    (check-sat)
                    """
                ),
                encoding="utf-8",
            )
            manifest = root / "sources.json"
            manifest.write_text(
                json.dumps(
                    {
                        "schema": conformance.EXTERNAL_SOURCE_SCHEMA,
                        "default_pending_reason": "pending by test",
                        "sources": [
                            {
                                "id": "official",
                                "kind": "official-smtlib",
                                "url": "https://example.invalid/smtlib",
                                "pin_type": "git-commit",
                                "pin": "abc123",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(bench_dir),
                    "--z3-proof-dir",
                    str(proof_dir),
                    "--regression-dir",
                    str(regression_dir),
                    "--external-source-manifest",
                    str(manifest),
                    "--mode",
                    conformance.MODE_PARSER,
                    "--mode",
                    conformance.MODE_Z3_TAC,
                    "--z3-tac-command",
                    "",
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            external = report["external_benchmark_coverage"]
            self.assertEqual(external["source_pins"][0]["pin"], "abc123")
            self.assertEqual(external["by_kind"]["benchmark"]["cases"], 1)
            self.assertEqual(external["by_kind"]["z3-proof"]["cases"], 1)
            self.assertEqual(external["by_kind"]["regression"]["cases"], 1)
            self.assertEqual(external["official_logic_status"]["QF_UF"]["status"], "covered")
            self.assertEqual(external["official_logic_status"]["QF_BV"]["status"], "pending")
            self.assertEqual(external["official_logic_status"]["QF_BV"]["reason"], "pending by test")
            families = {
                (item["kind"], item["family"], item["mode"]): item
                for item in external["unsupported_families"]
            }
            self.assertEqual(
                families[("regression", "unsupported-queries", conformance.MODE_Z3_TAC)]["count"],
                1,
            )
            self.assertEqual(
                report["summary"]["failure_class_counts"]["expected unsupported diagnostic"],
                3,
            )

    def test_checked_in_curated_benchmark_slice_covers_selected_logics(self):
        with tempfile.TemporaryDirectory() as tmp:
            out_dir = pathlib.Path(tmp) / "out"
            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(conformance.DEFAULT_CURATED_BENCHMARK_DIR),
                    "--mode",
                    conformance.MODE_PARSER,
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            external = report["external_benchmark_coverage"]
            for logic in ["QF_AUFLIA", "QF_BV", "QF_LIA", "QF_LRA", "QF_S", "QF_UF"]:
                self.assertEqual(external["official_logic_status"][logic]["status"], "covered")
            self.assertEqual(external["official_logic_status"]["UF"]["status"], "pending")
            self.assertTrue(external["source_pins"])

    def test_expected_pass_fail_and_unsupported_outcomes_are_valid(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bench_dir = root / "bench"
            bench_dir.mkdir()
            (bench_dir / "pass.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"parser-only": {"status": "pass"}}
                    (set-logic QF_LIA)
                    (assert true)
                    (check-sat)
                    """
                ),
                encoding="utf-8",
            )
            (bench_dir / "fail.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"parser-only": {"status": "fail", "diagnostic": "missing set-logic"}}
                    (assert true)
                    (check-sat)
                    """
                ),
                encoding="utf-8",
            )
            (bench_dir / "unsupported.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"z3-tac": {"status": "unsupported", "diagnostic": "no z3-tac command configured"}}
                    (set-logic QF_LIA)
                    (assert true)
                    (check-sat)
                    """
                ),
                encoding="utf-8",
            )
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(bench_dir),
                    "--mode",
                    conformance.MODE_PARSER,
                    "--mode",
                    conformance.MODE_Z3_TAC,
                    "--z3-tac-command",
                    "",
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            self.assertEqual(report["status_counts"][conformance.FAIL], 1)
            self.assertEqual(report["conformance_status_counts"][conformance.FAIL], 0)
            by_case_mode = {
                (item["case"], item["mode"]): item
                for item in report["results"]
            }
            self.assertEqual(
                by_case_mode[("pass", conformance.MODE_PARSER)]["classification"],
                conformance.CLASSIFICATION_MATCHED,
            )
            self.assertEqual(
                by_case_mode[("fail", conformance.MODE_PARSER)]["classification"],
                conformance.CLASSIFICATION_MATCHED,
            )
            self.assertEqual(
                by_case_mode[("unsupported", conformance.MODE_Z3_TAC)]["classification"],
                conformance.CLASSIFICATION_MATCHED,
            )
            fail_case = next(case for case in report["cases"] if case["name"] == "fail")
            self.assertEqual(
                fail_case["expected"][conformance.MODE_PARSER]["diagnostic_substring"],
                "missing set-logic",
            )

    def test_expected_diagnostic_mismatch_is_distinct_and_preserves_repro(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bench_dir = root / "bench"
            bench_dir.mkdir()
            (bench_dir / "unsupported.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"z3-tac": {"status": "unsupported", "diagnostic": "some other diagnostic"}}
                    (set-logic QF_LIA)
                    (assert true)
                    (check-sat)
                    """
                ),
                encoding="utf-8",
            )
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(bench_dir),
                    "--mode",
                    conformance.MODE_Z3_TAC,
                    "--z3-tac-command",
                    "",
                ]
            )

            self.assertEqual(code, 1)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            self.assertEqual(report["conformance_status_counts"][conformance.FAIL], 1)
            self.assertEqual(
                report["classification_counts"][conformance.CLASSIFICATION_DIAGNOSTIC_MISMATCH],
                1,
            )
            item = report["results"][0]
            self.assertEqual(item["status"], conformance.UNSUPPORTED)
            self.assertEqual(item["classification"], conformance.CLASSIFICATION_DIAGNOSTIC_MISMATCH)
            self.assertFalse(item["diagnostic_match"])
            self.assertTrue(list((out_dir / "repro").rglob("input.smt2")))
            self.assertTrue(list((out_dir / "repro").rglob("result.json")))

    def test_z3_tac_command_reports_success_and_expected_diagnostic(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bench_dir = root / "bench"
            bench_dir.mkdir()
            (bench_dir / "success.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"z3-tac": {"status": "pass"}}
                    (set-logic QF_UF)
                    (declare-const p Bool)
                    (assert p)
                    (assert (not p))
                    (check-sat)
                    (exit)
                    """
                ),
                encoding="utf-8",
            )
            (bench_dir / "diagnostic.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"z3-tac": {"status": "unsupported", "diagnostic": "get-model is outside checked Z3_TAC"}}
                    (set-logic QF_UF)
                    (declare-const p Bool)
                    (assert p)
                    (check-sat)
                    (get-model)
                    (exit)
                    """
                ),
                encoding="utf-8",
            )
            (bench_dir / "assuming.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"z3-tac": {"status": "unsupported", "diagnostic": "check-sat-assuming is outside checked Z3_TAC"}}
                    (set-logic QF_UF)
                    (declare-const p Bool)
                    (check-sat-assuming (p))
                    (exit)
                    """
                ),
                encoding="utf-8",
            )
            (bench_dir / "unsat_core.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"z3-tac": {"status": "unsupported", "diagnostic": "get-unsat-core is outside checked Z3_TAC"}}
                    (set-logic QF_UF)
                    (assert (! false :named bad))
                    (check-sat)
                    (get-unsat-core)
                    (exit)
                    """
                ),
                encoding="utf-8",
            )
            (bench_dir / "sat_theorem.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"z3-tac": {"status": "fail", "diagnostic": "satisfiable"}}
                    (set-logic QF_UF)
                    (declare-const p Bool)
                    (assert p)
                    (check-sat)
                    (exit)
                    """
                ),
                encoding="utf-8",
            )
            (bench_dir / "unknown_theorem.smt2").write_text(
                textwrap.dedent(
                    """\
                    ; holsmt-expected: {"z3-tac": {"status": "fail", "diagnostic": "unknown"}}
                    (set-logic QF_UF)
                    (declare-const p Bool)
                    (assert p)
                    (check-sat)
                    (exit)
                    """
                ),
                encoding="utf-8",
            )
            checker = root / "fake-z3-tac.py"
            checker.write_text(
                textwrap.dedent(
                    """\
                    import pathlib
                    import sys

                    path = pathlib.Path(sys.argv[1])
                    text = path.read_text(encoding="utf-8")
                    if "(get-model)" in text:
                        print("Z3_TAC_UNSUPPORTED")
                        print("diagnostic=raw SMT-LIB query get-model is outside checked Z3_TAC command-line entry point")
                        raise SystemExit(1)
                    if "(check-sat-assuming" in text:
                        print("Z3_TAC_UNSUPPORTED")
                        print("diagnostic=check-sat-assuming is outside checked Z3_TAC command-line entry point")
                        raise SystemExit(1)
                    if "(get-unsat-core)" in text:
                        print("Z3_TAC_UNSUPPORTED")
                        print("diagnostic=raw SMT-LIB query get-unsat-core is outside checked Z3_TAC command-line entry point")
                        raise SystemExit(1)
                    if "sat_theorem" in path.name:
                        print("Z3_TAC_FAIL")
                        print("diagnostic=solver reports negated term to be satisfiable")
                        raise SystemExit(1)
                    if "unknown_theorem" in path.name:
                        print("Z3_TAC_FAIL")
                        print("diagnostic=solver reports unknown: audit")
                        raise SystemExit(1)
                    print("Z3_TAC_PASS")
                    print("z3_version=4.13.0")
                    print("theorem=[] |- ~(p /\\ ~p)")
                    """
                ),
                encoding="utf-8",
            )
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(bench_dir),
                    "--mode",
                    conformance.MODE_Z3_TAC,
                    "--z3-tac-command",
                    f"{sys.executable} {checker} {{input}} {{logic}}",
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            by_case = {item["case"]: item for item in report["results"]}
            self.assertEqual(by_case["success"]["status"], conformance.PASS)
            self.assertEqual(by_case["diagnostic"]["status"], conformance.UNSUPPORTED)
            self.assertEqual(by_case["diagnostic"]["classification"], conformance.CLASSIFICATION_MATCHED)
            self.assertIn("get-model is outside checked Z3_TAC", by_case["diagnostic"]["actual_diagnostic"])
            self.assertEqual(by_case["assuming"]["status"], conformance.UNSUPPORTED)
            self.assertEqual(by_case["assuming"]["classification"], conformance.CLASSIFICATION_MATCHED)
            self.assertIn(
                "check-sat-assuming is outside checked Z3_TAC",
                by_case["assuming"]["actual_diagnostic"],
            )
            self.assertEqual(by_case["unsat_core"]["status"], conformance.UNSUPPORTED)
            self.assertEqual(by_case["unsat_core"]["classification"], conformance.CLASSIFICATION_MATCHED)
            self.assertIn(
                "get-unsat-core is outside checked Z3_TAC",
                by_case["unsat_core"]["actual_diagnostic"],
            )
            self.assertEqual(by_case["sat_theorem"]["status"], conformance.FAIL)
            self.assertEqual(by_case["sat_theorem"]["classification"], conformance.CLASSIFICATION_MATCHED)
            self.assertIn("satisfiable", by_case["sat_theorem"]["actual_diagnostic"])
            self.assertEqual(by_case["unknown_theorem"]["status"], conformance.FAIL)
            self.assertEqual(by_case["unknown_theorem"]["classification"], conformance.CLASSIFICATION_MATCHED)
            self.assertIn("unknown", by_case["unknown_theorem"]["actual_diagnostic"])

    def test_z3_tac_oracle_tag_output_is_a_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bench_dir = root / "bench"
            bench_dir.mkdir()
            (bench_dir / "oracle.smt2").write_text(
                "(set-logic QF_UF)\n(assert false)\n(check-sat)\n",
                encoding="utf-8",
            )
            checker = root / "fake-z3-tac.py"
            checker.write_text(
                textwrap.dedent(
                    """\
                    print("Z3_TAC_FAIL")
                    print("diagnostic=solver 'Z3_TAC conformance driver' produced unexpected oracle/axiom tags")
                    raise SystemExit(1)
                    """
                ),
                encoding="utf-8",
            )
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(bench_dir),
                    "--mode",
                    conformance.MODE_Z3_TAC,
                    "--z3-tac-command",
                    f"{sys.executable} {checker} {{input}} {{logic}}",
                ]
            )

            self.assertEqual(code, 1)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            item = report["results"][0]
            self.assertEqual(item["status"], conformance.FAIL)
            self.assertIn("oracle/axiom tags", item["actual_diagnostic"])

    @unittest.skipUnless(
        conformance.DEFAULT_TYPECHECK_DRIVER.exists(),
        "HolSmt typecheck driver has not been built",
    )
    def test_default_typecheck_driver_runs_representative_conformance_slice(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            out_dir = root / "out"
            fixture_dir = pathlib.Path(__file__).resolve().parent / "conformance" / "typecheck"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(fixture_dir),
                    "--mode",
                    conformance.MODE_TYPECHECK,
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            by_case = {item["case"]: item for item in report["results"]}
            self.assertEqual(by_case["pass_bool"]["status"], conformance.PASS)
            self.assertEqual(by_case["non_bool_assert"]["status"], conformance.FAIL)
            self.assertEqual(by_case["non_bool_assert"]["classification"], conformance.CLASSIFICATION_MATCHED)
            self.assertIn("expected sort :bool", by_case["non_bool_assert"]["actual_diagnostic"])

    @unittest.skipUnless(
        conformance.DEFAULT_Z3_TAC_DRIVER.exists(),
        "HolSmt z3-tac driver has not been built",
    )
    def test_default_z3_tac_driver_runs_representative_conformance_slice(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            out_dir = root / "out"
            fixture_dir = pathlib.Path(__file__).resolve().parent / "conformance" / "z3_tac"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(fixture_dir),
                    "--mode",
                    conformance.MODE_Z3_TAC,
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            by_case = {item["case"]: item for item in report["results"]}
            self.assertEqual(by_case["success"]["status"], conformance.PASS)
            self.assertEqual(by_case["diagnostic"]["status"], conformance.UNSUPPORTED)
            self.assertEqual(by_case["diagnostic"]["classification"], conformance.CLASSIFICATION_MATCHED)

    def test_proof_replay_failure_preserves_repro_input_and_raw_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            fake_z3 = make_fake_z3(root, proof_rule="mystery-rule")
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--z3",
                    str(fake_z3),
                    "--logic",
                    "QF_UF",
                    "--mode",
                    conformance.MODE_PARSER,
                    "--mode",
                    conformance.MODE_PROOF_PARSE,
                    "--mode",
                    conformance.MODE_PROOF_REPLAY,
                ]
            )

            self.assertEqual(code, 1)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            qf_uf_replay = report["summary"]["by_logic_mode"]["QF_UF"][conformance.MODE_PROOF_REPLAY]
            self.assertGreater(qf_uf_replay["fail"], 0)
            repro_inputs = list((out_dir / "repro").rglob("input.smt2"))
            repro_proofs = list((out_dir / "repro").rglob("proof.raw"))
            self.assertTrue(repro_inputs)
            self.assertTrue(repro_proofs)
            self.assertIn("mystery-rule", repro_proofs[0].read_text(encoding="utf-8"))

    def test_configured_command_mode_passes_command_context(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bench_dir = root / "bench"
            bench_dir.mkdir()
            (bench_dir / "qf_uf.smt2").write_text(
                "(set-logic QF_UF)\n(assert true)\n(check-sat)\n",
                encoding="utf-8",
            )
            checker = root / "checker.py"
            checker.write_text(
                textwrap.dedent(
                    """\
                    import pathlib
                    import sys

                    path = pathlib.Path(sys.argv[1])
                    logic = sys.argv[2]
                    assert path.read_text(encoding="utf-8").startswith(f"(set-logic {logic})")
                    """
                ),
                encoding="utf-8",
            )
            out_dir = root / "out"
            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(bench_dir),
                    "--logic",
                    "QF_UF",
                    "--mode",
                    conformance.MODE_TYPECHECK,
                    "--typecheck-command",
                    f"{sys.executable} {checker} {{input}} {{logic}}",
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            qf_uf = report["summary"]["by_logic_mode"]["QF_UF"][conformance.MODE_TYPECHECK]
            self.assertGreater(qf_uf["pass"], 0)
            self.assertEqual(qf_uf["fail"], 0)


if __name__ == "__main__":
    unittest.main()
