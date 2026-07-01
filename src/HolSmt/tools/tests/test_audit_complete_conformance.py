#!/usr/bin/env python3

import contextlib
import io
import json
import pathlib
import sys
import tempfile
import unittest


sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import audit_complete_conformance as audit


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def write_logics(path, logics=("QF_UF", "QF_LIA")):
    branches = "\n".join(
        f'    | "{logic}" =>\n      ({logic}.tydict, {logic}.tmdict)' for logic in logics
    )
    path.write_text(
        f"""
structure SmtLib_Logics =
struct
  fun parsedicts_of_logic (logic : string) =
    case logic of
{branches}
    | _ =>
      raise Fail "unknown"

  (* returns the symbol metadata used to build the parse dictionaries of
     the given SMT-LIB 2 logic *)
  fun metadata_of_logic (logic : string) =
    []
end
""",
        encoding="utf-8",
    )


def obligation(feature="future feature"):
    return {
        "files": ["src/HolSmt/SmtLib_Parser.sml"],
        "feature": feature,
        "test_ids": ["complete:future"],
        "failure_phase": "parser",
    }


def v2_case(case_id, logic="QF_UF", *, features=None, modes=None, expected=None, impl=None, row_class="logic"):
    modes = modes or ["parser-only"]
    expected = expected or {"parser-only": {"status": "pass"}}
    return {
        "id": case_id,
        "file": f"cases/logics/{case_id}.smt2",
        "logic": logic,
        "standard": "SMT-LIB-2.7",
        "class": row_class,
        "features": features or [logic],
        "modes": modes,
        "versions": ["4.13.0"],
        "expected": expected,
        "implementation_obligation": impl,
        "source": {
            "kind": "SMT-LIB-logic",
            "reference": f"{logic} logic",
        },
    }


def logic_inventory(required=("QF_UF", "QF_LIA"), excluded=()):
    return {
        "schema_version": "2",
        "source": "src/HolSmt/SmtLib_Logics.sml",
        "accepted_logics": list(required),
        "excluded_logics": [
            {
                "logic": logic,
                "category": "HolSmt-internal",
                "reason": "test exclusion",
            }
            for logic in excluded
        ],
    }


class CompleteConformanceAuditTests(unittest.TestCase):
    def test_missing_accepted_logic_evidence_is_an_error(self):
        cases = [v2_case("qf_uf_smoke", logic="QF_UF")]
        issues = audit.audit_cases(cases, ["QF_UF", "QF_LIA"])

        self.assertTrue(
            any(issue.code == "logic_manifest_mismatch" for issue in issues),
            [issue.render() for issue in issues],
        )
        self.assertTrue(
            any(issue.code == "missing_logic_evidence" and issue.details["logic"] == "QF_LIA" for issue in issues),
            [issue.render() for issue in issues],
        )

    def test_logic_inventory_must_match_source_plus_documented_exclusions(self):
        accepted = ["ALL", "QF_LIA", "QF_UF"]
        required = audit.validate_logic_inventory(
            logic_inventory(required=("QF_LIA", "QF_UF"), excluded=("ALL",)),
            accepted,
        )
        self.assertEqual(required, ["QF_LIA", "QF_UF"])

        with self.assertRaisesRegex(audit.AuditError, "does not exactly match"):
            audit.validate_logic_inventory(
                logic_inventory(required=("QF_UF",), excluded=("ALL",)),
                accepted,
            )

    def test_logic_manifest_extra_logic_is_an_error(self):
        cases = [
            v2_case("logic_qf_uf_sat", logic="QF_UF", features=["logic-case:sat"]),
            v2_case("logic_all_sat", logic="ALL", features=["logic-case:sat"]),
        ]
        issues = audit.audit_cases(cases, ["QF_UF"])

        mismatch = [issue for issue in issues if issue.code == "logic_manifest_mismatch"]
        self.assertEqual(len(mismatch), 1, [issue.render() for issue in issues])
        self.assertEqual(mismatch[0].details["extra"], ["ALL"])

    def test_logic_packet_requires_unsat_schedule_and_sat_no_theorem(self):
        unsat = v2_case(
            "logic_qf_uf_unsat_proof",
            logic="QF_UF",
            features=["logic-case:unsat-proof"],
            modes=["parser-only", "typecheck-only", "z3-oracle", "proof-parse", "proof-replay", "z3-tac"],
            expected={
                "parser-only": {"status": "pass"},
                "typecheck-only": {"status": "pass"},
                "z3-oracle": {"status": "pass"},
                "proof-parse": {"status": "red"},
                "proof-replay": {"status": "red"},
                "z3-tac": {"status": "red"},
            },
            impl=obligation("logic unsat"),
        )
        unsat["versions"] = [
            "2.19.1",
            "4.11.2",
            "4.12.4",
            "4.13.0",
            "4.14.1",
            "4.15.3",
        ]
        sat = v2_case(
            "logic_qf_uf_sat",
            logic="QF_UF",
            features=["logic-case:sat"],
            modes=["parser-only", "typecheck-only", "z3-oracle", "z3-tac"],
            expected={
                "parser-only": {"status": "pass"},
                "typecheck-only": {"status": "pass"},
                "z3-oracle": {"status": "pass"},
                "z3-tac": {
                    "status": "fail",
                    "diagnostic": "SAT result has no HOL theorem to reconstruct",
                    "failure_phase": "theorem-shape",
                },
            },
        )

        issues = audit.audit_cases([sat, unsat], ["QF_UF"])
        self.assertFalse(
            [
                issue for issue in issues
                if issue.code in {
                    "missing_logic_unsat_proof_case",
                    "logic_unsat_proof_schedule_mismatch",
                    "missing_sat_no_theorem_diagnostic",
                }
            ],
            [issue.render() for issue in issues],
        )

    def test_unsat_case_requires_proof_parse_replay_and_z3_tac_modes(self):
        case = v2_case(
            "qf_uf_unsat",
            features=["QF_UF", "unsat"],
            modes=["parser-only"],
            expected={"parser-only": {"status": "pass"}},
        )
        issues = audit.audit_cases([case], ["QF_UF"])

        matches = [issue for issue in issues if issue.code == "missing_unsat_proof_mode"]
        self.assertEqual(len(matches), 1, [issue.render() for issue in issues])
        self.assertEqual(
            matches[0].details["missing_modes"],
            ["proof-parse", "proof-replay", "z3-tac"],
        )
        self.assertEqual(
            matches[0].details["missing_expected"],
            ["proof-parse", "proof-replay", "z3-tac"],
        )

    def test_string_regex_and_extension_theory_rows_reject_parse_only_coverage(self):
        case = v2_case(
            "theory_unicode_strings_str_len_sat",
            logic="QF_SLIA",
            features=[
                "theory:UnicodeStrings",
                "theory-entry:UnicodeStrings:str.len",
                "theory-case:sat",
            ],
            modes=["parser-only"],
            expected={"parser-only": {"status": "pass"}},
            row_class="theory",
        )
        case["file"] = "cases/theories/strings/theory_unicode_strings_str_len_sat.smt2"
        case["source"] = {
            "kind": "SMT-LIB-theory",
            "reference": "SMT-LIB 2.7 UnicodeStrings str.len",
        }

        issues = audit.audit_cases([case], [])

        self.assertTrue(
            any(issue.code == "parse_only_string_regex_extension_coverage" for issue in issues),
            [issue.render() for issue in issues],
        )

    def test_string_regex_and_extension_theory_rows_accept_required_modes(self):
        case = v2_case(
            "theory_z3_extensions_seq_sat",
            logic="ALL",
            features=[
                "theory:Z3_Extensions",
                "theory-entry:Z3_Extensions:seq",
                "theory-case:sat",
            ],
            modes=["parser-only", "typecheck-only", "z3-oracle"],
            expected={
                "parser-only": {"status": "pass"},
                "typecheck-only": {"status": "pass"},
                "z3-oracle": {"status": "pass"},
            },
            row_class="theory",
        )
        case["file"] = "cases/theories/z3_extensions/theory_z3_extensions_seq_sat.smt2"
        case["standard"] = "Z3-extension"
        case["source"] = {
            "kind": "Z3-extension",
            "reference": "Z3 Seq extension",
        }

        issues = audit.audit_cases([case], [])

        self.assertFalse(
            [issue for issue in issues if issue.code == "parse_only_string_regex_extension_coverage"],
            [issue.render() for issue in issues],
        )

    def test_red_rows_without_implementation_obligation_fail_manifest_validation(self):
        manifest = {
            "schema_version": "2",
            "cases": [
                v2_case(
                    "future_red",
                    expected={"parser-only": {"status": "red"}},
                    impl=None,
                )
            ],
        }

        with self.assertRaisesRegex(audit.AuditError, "implementation_obligation"):
            audit.validate_v2_manifest(manifest)

    def test_red_rows_with_obligation_are_reported_distinctly(self):
        case = v2_case(
            "future_red",
            expected={"parser-only": {"status": "red"}},
            impl=obligation("future parser command"),
        )

        issues = audit.audit_cases([case], ["QF_UF"])

        self.assertTrue(
            any(
                issue.code == "red_implementation_obligation"
                and issue.category == "implementation_obligation"
                for issue in issues
            ),
            [issue.render() for issue in issues],
        )

    def test_complete_required_row_cannot_be_only_parse_or_unsupported_evidence(self):
        rows = [
            audit.CoverageRow(
                section="commands",
                item="future-command",
                row_class="SMT-LIB 2.7",
                statuses={"parse_only", "unsupported_diagnostic"},
                diagnostic_evidence=2,
                complete_required=True,
            )
        ]

        issues = audit.audit_coverage(rows, [])

        self.assertTrue(
            any(issue.code == "missing_command_v2_evidence" for issue in issues),
            [issue.render() for issue in issues],
        )

    def test_command_coverage_rows_require_v2_command_cases(self):
        rows = [
            audit.CoverageRow(
                section="commands",
                item="check-sat-assuming",
                row_class="SMT-LIB 2.7",
                statuses={"implemented"},
                positive_evidence=1,
                complete_required=True,
            )
        ]
        cases = [
            v2_case(
                "check_sat_assuming_logic_smoke",
                features=["command:check-sat-assuming"],
                row_class="logic",
            )
        ]

        issues = audit.audit_coverage(rows, cases)

        self.assertTrue(
            any(
                issue.code == "missing_command_v2_evidence"
                and issue.details["missing_commands"] == ["check-sat-assuming"]
                for issue in issues
            ),
            [issue.render() for issue in issues],
        )

    def test_command_coverage_rows_accept_complete_v2_command_cases(self):
        rows = [
            audit.CoverageRow(
                section="commands",
                item="get-unsat-assumptions, get-unsat-core",
                row_class="SMT-LIB 2.7",
                statuses={"implemented"},
                positive_evidence=1,
                complete_required=True,
            )
        ]
        case = v2_case(
            "command_get_unsat_core",
            features=["command:get-unsat-assumptions", "command:get-unsat-core"],
            row_class="command",
        )
        case["file"] = "cases/commands/command_get_unsat_core.smt2"
        case["source"] = {
            "kind": "SMT-LIB-standard",
            "reference": "SMT-LIB 2.7 unsat core commands",
        }

        issues = audit.audit_coverage(rows, [case])

        self.assertFalse(
            [issue for issue in issues if issue.code == "missing_command_v2_evidence"],
            [issue.render() for issue in issues],
        )

    def test_complete_required_row_cannot_be_only_parse_or_unsupported_evidence_non_command(self):
        rows = [
            audit.CoverageRow(
                section="theories",
                item="future-theory",
                row_class="SMT-LIB 2.7",
                statuses={"parse_only", "unsupported_diagnostic"},
                diagnostic_evidence=2,
                complete_required=True,
            )
        ]

        issues = audit.audit_coverage(rows, [])

        self.assertTrue(
            any(issue.code == "weak_complete_required_evidence" for issue in issues),
            [issue.render() for issue in issues],
        )

    def test_complete_required_row_cannot_be_diagnostic_only_evidence(self):
        rows = [
            audit.CoverageRow(
                section="theories",
                item="future-theory",
                row_class="SMT-LIB 2.7",
                statuses={"implemented"},
                positive_evidence=0,
                diagnostic_evidence=1,
                complete_required=True,
            )
        ]

        issues = audit.audit_coverage(rows, [])

        self.assertTrue(
            any(issue.code == "diagnostic_only_complete_required_evidence" for issue in issues),
            [issue.render() for issue in issues],
        )

    def test_main_writes_json_and_uses_nonzero_for_missing_complete_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            manifest = root / "manifest.json"
            logics = root / "SmtLib_Logics.sml"
            report = root / "report.json"
            write_json(manifest, {"schema_version": "2", "cases": []})
            write_logics(logics, ("QF_UF",))

            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                code = audit.main(
                    [
                        "--manifest",
                        str(manifest),
                        "--logic-source",
                        str(logics),
                        "--no-coverage",
                        "--json-output",
                        str(report),
                    ]
                )

            self.assertEqual(code, 1)
            self.assertIn("complete conformance audit", stdout.getvalue())
            data = json.loads(report.read_text(encoding="utf-8"))
            self.assertFalse(data["summary"]["passed"])
            issue_codes = {issue["code"] for issue in data["issues"]}
            self.assertIn("logic_manifest_mismatch", issue_codes)
            self.assertIn("missing_logic_evidence", issue_codes)

    def test_main_uses_distinct_exit_code_for_infrastructure_errors(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            manifest = root / "manifest.json"
            logics = root / "SmtLib_Logics.sml"
            write_json(manifest, {"schema_version": "1", "cases": []})
            write_logics(logics, ("QF_UF",))

            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                code = audit.main(
                    [
                        "--manifest",
                        str(manifest),
                        "--logic-source",
                        str(logics),
                        "--no-coverage",
                    ]
                )

            self.assertEqual(code, 2)
            self.assertIn("infrastructure error", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
