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
            checker = root / "fake-z3-tac.py"
            checker.write_text(
                textwrap.dedent(
                    """\
                    import pathlib
                    import sys

                    text = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
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
