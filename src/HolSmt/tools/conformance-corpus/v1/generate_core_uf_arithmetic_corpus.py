#!/usr/bin/env python3
"""Generate the v1 HolSmt Core/UF/arithmetic conformance corpus."""

from __future__ import annotations

import json
import pathlib
from dataclasses import dataclass


ROOT = pathlib.Path(__file__).resolve().parent
CASES = ROOT / "cases"
SCHEMA = "holsmt-conformance-corpus-v1"

MODE_PARSER = "parser-only"
MODE_TYPECHECK = "typecheck-only"
MODE_Z3_ORACLE = "z3-oracle"
MODE_PROOF_PARSE = "proof-parse"
MODE_PROOF_REPLAY = "proof-replay"
MODE_Z3_TAC = "z3-tac"

SAT_MODES = [MODE_PARSER, MODE_TYPECHECK, MODE_Z3_ORACLE]
PROOF_MODES = [
    MODE_PARSER,
    MODE_TYPECHECK,
    MODE_Z3_ORACLE,
    MODE_PROOF_PARSE,
    MODE_PROOF_REPLAY,
    MODE_Z3_TAC,
]
DIAGNOSTIC_MODES = [MODE_PARSER, MODE_TYPECHECK]

UF_LOGICS = ["QF_UF", "UF"]
INT_LOGICS = [
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
]
REAL_LOGICS = [
    "QF_RDL",
    "QF_LRA",
    "QF_NRA",
    "QF_UFLRA",
    "QF_UFNRA",
    "LRA",
    "NRA",
    "UFLRA",
    "UFNRA",
]
MIXED_LOGICS = ["QF_LIRA", "QF_NIRA", "QF_UFLIRA", "QF_UFNIRA"]


@dataclass(frozen=True)
class CorpusCase:
    case_id: str
    logic: str
    subdir: str
    text: str
    tags: tuple[str, ...]
    modes: tuple[str, ...]
    expected: dict[str, object] | None = None

    @property
    def relative_path(self) -> pathlib.Path:
        return pathlib.Path("cases") / self.subdir / f"{self.case_id}.smt2"


def script(logic: str, body: str) -> str:
    return f"(set-logic {logic})\n{body.rstrip()}\n"


def sat_case(logic: str, family: str) -> CorpusCase:
    if family == "uf":
        body = """
(declare-sort U 0)
(declare-const a U)
(declare-fun f (U Bool) U)
(declare-fun p (U) Bool)
(assert (= (f a true) (f a (not false))))
(assert (xor (p a) (not (p a))))
(check-sat)
(exit)
"""
    elif family == "ints":
        body = """
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ x 1) (+ y 2)))
(assert (= (- (+ x y) y) x))
(check-sat)
(exit)
"""
    elif family == "reals":
        body = """
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ x 1.0) (+ y 2.0)))
(assert (= (- (+ x y) y) x))
(check-sat)
(exit)
"""
    elif family == "mixed":
        body = """
(declare-const i Int)
(declare-const r Real)
(assert (<= (to_real i) (+ r 2.0)))
(assert (is_int (to_real i)))
(check-sat)
(exit)
"""
    else:
        raise AssertionError(f"unknown family {family}")
    return CorpusCase(
        case_id=f"{logic.lower()}_sat",
        logic=logic,
        subdir=family,
        text=script(logic, body),
        tags=(family, "sat", "representative"),
        modes=tuple(SAT_MODES),
    )


def proof_case(logic: str, family: str) -> CorpusCase:
    body = """
(assert false)
(check-sat)
(get-proof)
(exit)
"""
    return CorpusCase(
        case_id=f"{logic.lower()}_unsat_proof",
        logic=logic,
        subdir=family,
        text=script(logic, body),
        tags=(family, "unsat", "proof"),
        modes=tuple(PROOF_MODES),
    )


def diagnostic_case(logic: str, family: str) -> CorpusCase:
    if family == "uf":
        body = """
(declare-sort U 0)
(declare-const a U)
(assert a)
(check-sat)
(exit)
"""
    elif family == "ints":
        body = """
(assert (+ 1 2))
(check-sat)
(exit)
"""
    elif family == "reals":
        body = """
(assert (+ 1.0 2.0))
(check-sat)
(exit)
"""
    elif family == "mixed":
        body = """
(assert (to_real 1))
(check-sat)
(exit)
"""
    else:
        raise AssertionError(f"unknown family {family}")
    return CorpusCase(
        case_id=f"{logic.lower()}_type_error",
        logic=logic,
        subdir=family,
        text=script(logic, body),
        tags=(family, "diagnostic", "type-error"),
        modes=tuple(DIAGNOSTIC_MODES),
        expected={
            MODE_PARSER: {"status": "pass"},
            MODE_TYPECHECK: {
                "status": "fail",
                "diagnostic": "expected sort :bool",
            },
        },
    )


def hand_cases() -> list[CorpusCase]:
    return [
        CorpusCase(
            case_id="qf_uf_core_operators_sat",
            logic="QF_UF",
            subdir="core",
            text=script(
                "QF_UF",
                """
(declare-const p Bool)
(declare-const q Bool)
(assert (= (ite p true false) p))
(assert (= (=> p q) (or (not p) q)))
(assert (= (xor p q) (distinct p q)))
(assert (and true (or p (not p))))
(check-sat)
(exit)
""",
            ),
            tags=("core", "sat", "operators"),
            modes=tuple(SAT_MODES),
        ),
        CorpusCase(
            case_id="qf_uf_core_type_error",
            logic="QF_UF",
            subdir="core",
            text=script(
                "QF_UF",
                """
(declare-sort U 0)
(declare-const a U)
(assert (= a true))
(check-sat)
(exit)
""",
            ),
            tags=("core", "diagnostic", "type-error"),
            modes=tuple(DIAGNOSTIC_MODES),
            expected={
                MODE_PARSER: {"status": "pass"},
                MODE_TYPECHECK: {
                    "status": "fail",
                    "diagnostic": "failed to parse '='",
                },
            },
        ),
        CorpusCase(
            case_id="qf_uf_core_arity_error",
            logic="QF_UF",
            subdir="core",
            text=script(
                "QF_UF",
                """
(assert (not true false))
(check-sat)
(exit)
""",
            ),
            tags=("core", "diagnostic", "arity"),
            modes=tuple(DIAGNOSTIC_MODES),
            expected={
                MODE_PARSER: {"status": "pass"},
                MODE_TYPECHECK: {
                    "status": "fail",
                    "diagnostic": "failed to parse 'not'",
                },
            },
        ),
        CorpusCase(
            case_id="qf_uf_symbols_sat",
            logic="QF_UF",
            subdir="uf",
            text=script(
                "QF_UF",
                """
(declare-sort U 0)
(declare-fun c () U)
(declare-fun f (U U) U)
(declare-fun |quoted predicate| (U U) Bool)
(assert (= (f c c) (f c c)))
(assert (=> (|quoted predicate| c c) (|quoted predicate| c c)))
(check-sat)
(exit)
""",
            ),
            tags=("uf", "sat", "nullary", "n-ary", "predicate", "quoted-symbol"),
            modes=tuple(SAT_MODES),
        ),
        CorpusCase(
            case_id="uf_quantified_shadowing_sat",
            logic="UF",
            subdir="uf",
            text=script(
                "UF",
                """
(declare-sort U 0)
(declare-const |and| U)
(declare-fun |p q| (U) Bool)
(assert (forall ((|and| U)) (=> (|p q| |and|) (|p q| |and|))))
(assert (exists ((x U)) (let ((x x)) (= x x))))
(check-sat)
(exit)
""",
            ),
            tags=("uf", "sat", "quantified", "shadowing", "quoted-symbol"),
            modes=tuple(SAT_MODES),
        ),
        CorpusCase(
            case_id="qf_nia_div_mod_audit",
            logic="QF_NIA",
            subdir="arithmetic",
            text=script(
                "QF_NIA",
                """
(assert (= (div 7 3) 2))
(assert (= (mod 7 3) 1))
(assert (= (div 7 0) (div 7 0)))
(check-sat)
(exit)
""",
            ),
            tags=("ints", "audit-only", "division", "modulo"),
            modes=tuple(SAT_MODES),
        ),
        CorpusCase(
            case_id="qf_nra_real_division_audit",
            logic="QF_NRA",
            subdir="arithmetic",
            text=script(
                "QF_NRA",
                """
(assert (= (/ 6.0 3.0) 2.0))
(assert (= (/ 1.0 0.0) (/ 1.0 0.0)))
(check-sat)
(exit)
""",
            ),
            tags=("reals", "audit-only", "division"),
            modes=tuple(SAT_MODES),
        ),
        CorpusCase(
            case_id="qf_lira_conversions_audit",
            logic="QF_LIRA",
            subdir="arithmetic",
            text=script(
                "QF_LIRA",
                """
(declare-const i Int)
(assert (is_int (to_real i)))
(assert (= (to_int (to_real 4)) 4))
(check-sat)
(exit)
""",
            ),
            tags=("mixed", "audit-only", "conversion"),
            modes=tuple(SAT_MODES),
        ),
        CorpusCase(
            case_id="qf_lia_nonlinear_audit",
            logic="QF_LIA",
            subdir="arithmetic",
            text=script(
                "QF_LIA",
                """
(declare-const x Int)
(assert (= (* x x) 4))
(check-sat)
(exit)
""",
            ),
            tags=("ints", "audit-only", "linear-logic", "nonlinear-term"),
            modes=tuple(SAT_MODES),
        ),
        CorpusCase(
            case_id="qf_nia_nonlinear_sat",
            logic="QF_NIA",
            subdir="arithmetic",
            text=script(
                "QF_NIA",
                """
(declare-const x Int)
(assert (= (* x x) 4))
(check-sat)
(exit)
""",
            ),
            tags=("ints", "sat", "nonlinear"),
            modes=tuple(SAT_MODES),
        ),
    ]


def generated_cases() -> list[CorpusCase]:
    cases = hand_cases()
    for family, logics in (
        ("uf", UF_LOGICS),
        ("ints", INT_LOGICS),
        ("reals", REAL_LOGICS),
        ("mixed", MIXED_LOGICS),
    ):
        for logic in logics:
            cases.append(sat_case(logic, family))
            cases.append(proof_case(logic, family))
            cases.append(diagnostic_case(logic, family))
    return sorted(cases, key=lambda case: case.case_id)


def write_text(path: pathlib.Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def main() -> int:
    cases = generated_cases()
    for old_case in CASES.rglob("*.smt2") if CASES.exists() else []:
        old_case.unlink()

    manifest_cases: list[dict[str, object]] = []
    for case in cases:
        write_text(ROOT / case.relative_path, case.text)
        entry: dict[str, object] = {
            "id": case.case_id,
            "file": str(case.relative_path),
            "logic": case.logic,
            "tags": list(case.tags),
            "modes": list(case.modes),
        }
        if case.expected:
            entry["expected"] = case.expected
        manifest_cases.append(entry)

    manifest = {
        "schema": SCHEMA,
        "version": "v1",
        "smtlib_version": "2.7",
        "generator": "python3 src/HolSmt/tools/conformance-corpus/v1/generate_core_uf_arithmetic_corpus.py",
        "description": "Core, UF, Ints, Reals, and Reals_Ints curated SMT-LIB corpus for HolSmt conformance evidence.",
        "logic_families": {
            "uf": UF_LOGICS,
            "ints": INT_LOGICS,
            "reals": REAL_LOGICS,
            "mixed_reals_ints": MIXED_LOGICS,
        },
        "cases": manifest_cases,
    }
    with (ROOT / "manifest.json").open("w", encoding="utf-8") as outfile:
        json.dump(manifest, outfile, indent=2, sort_keys=True)
        outfile.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
