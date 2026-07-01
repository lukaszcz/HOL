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


class CompleteConformanceAuditTests(unittest.TestCase):
    def test_missing_accepted_logic_evidence_is_an_error(self):
        cases = [v2_case("qf_uf_smoke", logic="QF_UF")]
        issues = audit.audit_cases(cases, ["QF_UF", "QF_LIA"])

        self.assertTrue(
            any(issue.code == "missing_logic_evidence" and issue.details["logic"] == "QF_LIA" for issue in issues),
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
            any(issue.code == "weak_complete_required_evidence" for issue in issues),
            [issue.render() for issue in issues],
        )

    def test_complete_required_row_cannot_be_diagnostic_only_evidence(self):
        rows = [
            audit.CoverageRow(
                section="commands",
                item="future-command",
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
            self.assertEqual(data["issues"][0]["code"], "missing_logic_evidence")

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
