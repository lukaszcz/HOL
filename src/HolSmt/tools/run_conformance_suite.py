#!/usr/bin/env python3
"""Run a local HolSmt SMT-LIB conformance suite and write coverage reports."""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import pathlib
import re
import shutil
import shlex
import signal
import subprocess
import sys
from dataclasses import dataclass, field
from typing import Iterable, Mapping

from record_z3_proof_corpus import (
    Atom,
    ListNode,
    build_summary as build_proof_corpus_summary,
    detect_solver_result,
    line_col,
    parse_sexps,
    proof_options_for,
    record_one as record_proof_corpus_entry,
    z3_version,
)


SCHEMA = "holsmt-conformance-v1"
SMTLIB_VERSION = "2.7"
CORPUS_SCHEMA = "holsmt-conformance-corpus-v1"

MODE_PARSER = "parser-only"
MODE_TYPECHECK = "typecheck-only"
MODE_Z3_ORACLE = "z3-oracle"
MODE_PROOF_PARSE = "proof-parse"
MODE_PROOF_REPLAY = "proof-replay"
MODE_Z3_TAC = "z3-tac"

ALL_MODES = [
    MODE_PARSER,
    MODE_TYPECHECK,
    MODE_Z3_ORACLE,
    MODE_PROOF_PARSE,
    MODE_PROOF_REPLAY,
    MODE_Z3_TAC,
]

PASS = "pass"
FAIL = "fail"
UNSUPPORTED = "unsupported"
RED = "red"
VALID_EXPECTED_STATUSES = {PASS, FAIL, UNSUPPORTED, RED}

CLASSIFICATION_ACCEPTED = "accepted"
CLASSIFICATION_MATCHED = "matched"
CLASSIFICATION_UNEXPECTED_FAILURE = "unexpected-failure"
CLASSIFICATION_UNEXPECTED_STATUS = "unexpected-status"
CLASSIFICATION_DIAGNOSTIC_MISMATCH = "diagnostic-mismatch"
CLASSIFICATION_EXPECTED_IMPLEMENTATION_GAP = "expected-implementation-gap"

# This mirrors SmtLib_Logics.sml.  ALL is HolSmt's aggregate pseudo-logic, not
# an official SMT-LIB logic, so it is tracked separately in reports.
OFFICIAL_LOGICS = [
    "ALIA",
    "ALIRA",
    "ANIA",
    "ANIRA",
    "AUFLIA",
    "AUFLIRA",
    "AUFNIRA",
    "BV",
    "LIA",
    "LRA",
    "NIA",
    "NRA",
    "QF_ABV",
    "QF_ALIA",
    "QF_ALRA",
    "QF_ANIA",
    "QF_ANRA",
    "QF_AUFBV",
    "QF_AUFLIA",
    "QF_AUFLIRA",
    "QF_AUFNIA",
    "QF_AUFNIRA",
    "QF_AX",
    "QF_BV",
    "QF_BVFP",
    "QF_FP",
    "QF_FPBV",
    "QF_IDL",
    "QF_LIA",
    "QF_LIRA",
    "QF_LRA",
    "QF_NIA",
    "QF_NIRA",
    "QF_NRA",
    "QF_RDL",
    "QF_S",
    "QF_SLIA",
    "QF_SNIA",
    "QF_UF",
    "QF_UFBV",
    "QF_UFBVFP",
    "QF_UFFP",
    "QF_UFIDL",
    "QF_UFLIA",
    "QF_UFLIRA",
    "QF_UFLRA",
    "QF_UFNIRA",
    "QF_UFNRA",
    "UF",
    "UFBV",
    "UFIDL",
    "UFLIA",
    "UFLRA",
    "UFNIA",
    "UFNRA",
]

HOLSMT_LOGICS = ["ALL", *OFFICIAL_LOGICS]
SOLVER_RESULTS = {"sat", "unsat", "unknown"}
DEFAULT_TYPECHECK_DRIVER = pathlib.Path(__file__).resolve().parents[1] / "holsmt-typecheck"
DEFAULT_TYPECHECK_COMMAND = f"{shlex.quote(str(DEFAULT_TYPECHECK_DRIVER))} {{input}} {{logic}}"
DEFAULT_Z3_TAC_DRIVER = pathlib.Path(__file__).resolve().parents[1] / "holsmt-z3-tac"
DEFAULT_Z3_TAC_COMMAND = f"{shlex.quote(str(DEFAULT_Z3_TAC_DRIVER))} {{input}} {{logic}}"
DEFAULT_CORPUS_DIR = pathlib.Path(__file__).resolve().parent / "conformance-corpus" / "v1"
EXTERNAL_SOURCE_SCHEMA = "holsmt-external-benchmark-sources-v1"
DEFAULT_EXTERNAL_BENCHMARK_ROOT = pathlib.Path(__file__).resolve().parent / "external-benchmarks"
DEFAULT_EXTERNAL_SOURCE_MANIFEST = DEFAULT_EXTERNAL_BENCHMARK_ROOT / "sources.json"
DEFAULT_CURATED_BENCHMARK_DIR = DEFAULT_EXTERNAL_BENCHMARK_ROOT / "curated-small"

SOURCE_KIND_BENCHMARK = "benchmark"
SOURCE_KIND_Z3_PROOF = "z3-proof"
SOURCE_KIND_REGRESSION = "regression"
SOURCE_KIND_CORPUS = "corpus"


@dataclass(frozen=True)
class ExpectedOutcome:
    status: str
    diagnostic_substring: str | None = None


@dataclass(frozen=True)
class Case:
    name: str
    logic: str
    text: str
    origin: str
    tags: tuple[str, ...]
    modes: tuple[str, ...] = tuple(ALL_MODES)
    source_path: pathlib.Path | None = None
    expected: Mapping[str, ExpectedOutcome] = field(default_factory=dict)


def json_dump(path: pathlib.Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as outfile:
        json.dump(value, outfile, indent=2, sort_keys=True)
        outfile.write("\n")


def write_text(path: pathlib.Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def slug(text: str) -> str:
    value = re.sub(r"[^A-Za-z0-9_.-]+", "-", text.strip())
    value = value.strip("-")
    return value or "case"


def find_set_logic(text: str) -> str | None:
    match = re.search(r"\(\s*set-logic\s+([^\s()]+)\s*\)", text)
    return match.group(1) if match else None


def find_family_directive(text: str) -> str | None:
    for line in text.splitlines():
        match = re.match(r"\s*;\s*family\s*:\s*(.*?)\s*$", line, flags=re.IGNORECASE)
        if match:
            family = slug(match.group(1))
            return family if family else None
    return None


def normalize_expected_outcome(value: object, *, context: str) -> ExpectedOutcome:
    if isinstance(value, str):
        status = value
        diagnostic = None
    elif isinstance(value, dict):
        status = value.get("status")
        diagnostic = (
            value.get("diagnostic_substring")
            or value.get("diagnostic")
            or value.get("detail")
        )
    else:
        raise ValueError(f"{context}: expected outcome must be a status string or object")

    if not isinstance(status, str) or status not in VALID_EXPECTED_STATUSES:
        raise ValueError(f"{context}: expected status must be one of {sorted(VALID_EXPECTED_STATUSES)}")
    if diagnostic is not None and not isinstance(diagnostic, str):
        raise ValueError(f"{context}: expected diagnostic substring must be a string")
    if status == UNSUPPORTED and not diagnostic:
        raise ValueError(f"{context}: expected unsupported outcomes require a diagnostic substring")
    return ExpectedOutcome(status=status, diagnostic_substring=diagnostic)


def parse_expected_directive(payload: str, *, context: str) -> dict[str, ExpectedOutcome]:
    payload = payload.strip()
    if not payload:
        raise ValueError(f"{context}: empty holsmt-expected directive")

    if payload.startswith("{"):
        parsed = json.loads(payload)
        if not isinstance(parsed, dict):
            raise ValueError(f"{context}: holsmt-expected JSON must be an object")
        if "mode" in parsed:
            mode = parsed.get("mode")
            if not isinstance(mode, str):
                raise ValueError(f"{context}: expected mode must be a string")
            if mode not in ALL_MODES:
                raise ValueError(f"{context}: unknown expected mode {mode!r}")
            return {mode: normalize_expected_outcome(parsed, context=context)}

        outcomes: dict[str, ExpectedOutcome] = {}
        for mode, value in parsed.items():
            if mode not in ALL_MODES:
                raise ValueError(f"{context}: unknown expected mode {mode!r}")
            outcomes[mode] = normalize_expected_outcome(value, context=f"{context} {mode}")
        return outcomes

    parts = payload.split(maxsplit=2)
    if len(parts) < 2:
        raise ValueError(f"{context}: expected '<mode> <status> [diagnostic substring]'")
    mode, status = parts[0], parts[1]
    if mode not in ALL_MODES:
        raise ValueError(f"{context}: unknown expected mode {mode!r}")
    value: dict[str, object] = {"status": status}
    if len(parts) == 3:
        value["diagnostic"] = parts[2]
    return {mode: normalize_expected_outcome(value, context=context)}


def parse_expected_outcomes(text: str, *, context: str) -> dict[str, ExpectedOutcome]:
    outcomes: dict[str, ExpectedOutcome] = {}
    for line_number, line in enumerate(text.splitlines(), start=1):
        match = re.match(r"\s*;\s*holsmt-expected\s*:\s*(.*?)\s*$", line, flags=re.IGNORECASE)
        if not match:
            continue
        for mode, expected in parse_expected_directive(
            match.group(1),
            context=f"{context}:{line_number}",
        ).items():
            outcomes[mode] = expected
    return outcomes


def expected_outcome_json(expected: Mapping[str, ExpectedOutcome]) -> dict[str, dict[str, str | None]]:
    return {
        mode: {
            "status": outcome.status,
            "diagnostic_substring": outcome.diagnostic_substring,
        }
        for mode, outcome in sorted(expected.items())
    }


def logic_smoke_case(logic: str, unsat: bool) -> Case:
    body = "(assert false)" if unsat else "(assert true)"
    proof = "\n(get-proof)" if unsat else ""
    name = f"{logic.lower()}-{'proof' if unsat else 'smoke'}"
    return Case(
        name=name,
        logic=logic,
        text=f"(set-logic {logic})\n{body}\n(check-sat){proof}\n(exit)\n",
        origin="generated-default",
        tags=("logic-smoke", "generated", "proof" if unsat else "oracle"),
    )


def metamorphic_cases() -> list[Case]:
    return [
        Case(
            name="qf_uf_operand_commutation",
            logic="QF_UF",
            text=(
                "(set-logic QF_UF)\n"
                "(declare-const p Bool)\n"
                "(declare-const q Bool)\n"
                "(assert (not (= (and p q) (and q p))))\n"
                "(check-sat)\n(get-proof)\n(exit)\n"
            ),
            origin="generated-default",
            tags=("metamorphic", "operand-commutation", "proof"),
        ),
        Case(
            name="qf_uf_variable_renaming",
            logic="QF_UF",
            text=(
                "(set-logic QF_UF)\n"
                "(declare-const renamed Bool)\n"
                "(assert (not (= renamed renamed)))\n"
                "(check-sat)\n(get-proof)\n(exit)\n"
            ),
            origin="generated-default",
            tags=("metamorphic", "variable-renaming", "proof"),
        ),
        Case(
            name="qf_uf_nested_lets",
            logic="QF_UF",
            text=(
                "(set-logic QF_UF)\n"
                "(declare-const p Bool)\n"
                "(assert (not (let ((x p)) (let ((y x)) (= y p)))))\n"
                "(check-sat)\n(get-proof)\n(exit)\n"
            ),
            origin="generated-default",
            tags=("metamorphic", "nested-lets", "proof"),
        ),
        Case(
            name="qf_uf_scoped_assertions",
            logic="QF_UF",
            text=(
                "(set-logic QF_UF)\n"
                "(declare-const p Bool)\n"
                "(push 1)\n(assert p)\n(pop 1)\n"
                "(assert (not (= p p)))\n"
                "(check-sat)\n(get-proof)\n(exit)\n"
            ),
            origin="generated-default",
            tags=("metamorphic", "scoped-assertions", "proof"),
        ),
        Case(
            name="qf_auflia_mixed_array_int",
            logic="QF_AUFLIA",
            text=(
                "(set-logic QF_AUFLIA)\n"
                "(declare-const a (Array Int Int))\n"
                "(declare-const i Int)\n"
                "(declare-const v Int)\n"
                "(assert (not (= (select (store a i v) i) v)))\n"
                "(check-sat)\n(get-proof)\n(exit)\n"
            ),
            origin="generated-default",
            tags=("metamorphic", "mixed-theories", "proof"),
        ),
    ]


def default_cases(selected_logics: set[str] | None) -> list[Case]:
    logics = [logic for logic in HOLSMT_LOGICS if selected_logics is None or logic in selected_logics]
    cases = [logic_smoke_case(logic, False) for logic in logics]
    cases.extend(logic_smoke_case(logic, True) for logic in logics)
    if selected_logics is None or {"QF_UF", "QF_AUFLIA"} & selected_logics:
        cases.extend(
            case for case in metamorphic_cases()
            if selected_logics is None or case.logic in selected_logics
        )
    return cases


def discover_smt2_files(paths: Iterable[pathlib.Path]) -> list[tuple[pathlib.Path, str]]:
    files: list[tuple[pathlib.Path, str]] = []
    for path in paths:
        path = path.resolve()
        if path.is_file():
            files.append((path, path.stem))
        elif path.is_dir():
            for child in sorted(path.rglob("*.smt2")):
                files.append((child, str(child.relative_to(path).with_suffix(""))))

    by_path: dict[pathlib.Path, str] = {}
    for path, label in files:
        by_path.setdefault(path, label)
    return sorted(by_path.items(), key=lambda item: (item[1], str(item[0])))


def external_case_names(discovered: list[tuple[pathlib.Path, str]]) -> dict[pathlib.Path, str]:
    candidates = {path: slug(label) for path, label in discovered}
    counts = collections.Counter(candidates.values())
    names: dict[pathlib.Path, str] = {}
    for path, candidate in candidates.items():
        if counts[candidate] == 1:
            names[path] = candidate
            continue
        digest = hashlib.sha1(str(path).encode("utf-8")).hexdigest()[:8]
        names[path] = f"{candidate}-{digest}"
    return names


def external_cases(
    paths: Iterable[pathlib.Path],
    selected_logics: set[str] | None,
    *,
    source_kind: str = SOURCE_KIND_BENCHMARK,
) -> list[Case]:
    cases: list[Case] = []
    discovered = discover_smt2_files(paths)
    names = external_case_names(discovered)
    for path, _label in discovered:
        text = path.read_text(encoding="utf-8")
        logic = find_set_logic(text) or "UNKNOWN"
        if selected_logics is not None and logic not in selected_logics:
            continue
        family = find_family_directive(text)
        tags = ["external", source_kind]
        if family:
            tags.append(f"family:{family}")
        cases.append(
            Case(
                name=names[path],
                logic=logic,
                text=text,
                origin=f"external:{source_kind}",
                tags=tuple(tags),
                source_path=path,
                expected=parse_expected_outcomes(text, context=str(path)),
            )
        )
    return cases


def load_corpus_manifest(corpus_dir: pathlib.Path) -> dict[str, object]:
    manifest_path = corpus_dir / "manifest.json"
    with manifest_path.open(encoding="utf-8") as infile:
        manifest = json.load(infile)
    if not isinstance(manifest, dict):
        raise ValueError(f"{manifest_path}: corpus manifest root must be an object")
    is_v1 = manifest.get("schema") == CORPUS_SCHEMA
    is_v2 = manifest.get("schema_version") == "2"
    if not is_v1 and not is_v2:
        raise ValueError(
            f"{manifest_path}: corpus manifest schema must be {CORPUS_SCHEMA} or schema_version 2"
        )
    cases = manifest.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ValueError(f"{manifest_path}: corpus manifest cases must be a non-empty list")
    return manifest


def corpus_cases(paths: Iterable[pathlib.Path], selected_logics: set[str] | None) -> list[Case]:
    cases: list[Case] = []
    seen: set[str] = set()
    for corpus_dir in paths:
        corpus_dir = corpus_dir.resolve()
        manifest = load_corpus_manifest(corpus_dir)
        for index, entry in enumerate(manifest["cases"], start=1):  # type: ignore[index]
            context = f"{corpus_dir / 'manifest.json'} cases[{index}]"
            if not isinstance(entry, dict):
                raise ValueError(f"{context}: case entry must be an object")
            case_id = entry.get("id")
            logic = entry.get("logic")
            file_name = entry.get("file")
            if not isinstance(case_id, str) or not case_id:
                raise ValueError(f"{context}: id must be a non-empty string")
            if not isinstance(logic, str) or not logic:
                raise ValueError(f"{context}: logic must be a non-empty string")
            if not isinstance(file_name, str) or not file_name:
                raise ValueError(f"{context}: file must be a non-empty string")
            if case_id in seen:
                raise ValueError(f"{context}: duplicate corpus case id {case_id!r}")
            seen.add(case_id)
            if selected_logics is not None and logic not in selected_logics:
                continue

            case_path = (corpus_dir / file_name).resolve()
            text = case_path.read_text(encoding="utf-8")
            observed_logic = find_set_logic(text)
            if logic != "ALL" and observed_logic is not None and observed_logic != logic:
                raise ValueError(
                    f"{context}: file set-logic {observed_logic!r} does not match manifest logic {logic!r}"
                )

            tags_value = entry.get("tags", entry.get("features", []))
            if not isinstance(tags_value, list) or not all(isinstance(tag, str) for tag in tags_value):
                raise ValueError(f"{context}: tags/features must be a list of strings")
            row_class = entry.get("class")
            if isinstance(row_class, str) and row_class:
                tags_value = [f"class:{row_class}", *tags_value]
            modes_value = entry.get("modes", ALL_MODES)
            if not isinstance(modes_value, list) or not modes_value:
                raise ValueError(f"{context}: modes must be a non-empty list")
            modes: list[str] = []
            for mode in modes_value:
                if not isinstance(mode, str) or mode not in ALL_MODES:
                    raise ValueError(f"{context}: unknown mode {mode!r}")
                modes.append(mode)

            expected: dict[str, ExpectedOutcome] = {}
            expected_value = entry.get("expected", {})
            if expected_value:
                if not isinstance(expected_value, dict):
                    raise ValueError(f"{context}: expected must be an object")
                for mode, value in expected_value.items():
                    if mode not in ALL_MODES:
                        raise ValueError(f"{context}: unknown expected mode {mode!r}")
                    expected[mode] = normalize_expected_outcome(
                        value,
                        context=f"{context} expected {mode}",
                    )
            expected.update(parse_expected_outcomes(text, context=str(case_path)))

            cases.append(
                Case(
                    name=case_id,
                    logic=logic,
                    text=text,
                    origin=f"corpus:{manifest.get('version', manifest.get('schema_version', corpus_dir.name))}",
                    tags=("corpus", *tuple(tags_value)),
                    modes=tuple(modes),
                    source_path=case_path,
                    expected=expected,
                )
            )
    return cases


def write_case_inputs(cases: Iterable[Case], out_dir: pathlib.Path) -> list[tuple[Case, pathlib.Path]]:
    paths: list[tuple[Case, pathlib.Path]] = []
    for index, case in enumerate(cases):
        name = f"{index:04d}-{slug(case.logic)}-{slug(case.name)}.smt2"
        path = out_dir / "inputs" / name
        write_text(path, case.text)
        paths.append((case, path))
    return paths


def result(
    case: Case,
    mode: str,
    status: str,
    detail: str,
    *,
    artifact: dict[str, object] | None = None,
    version: str | None = None,
) -> dict[str, object]:
    return {
        "case": case.name,
        "logic": case.logic,
        "mode": mode,
        "status": status,
        "actual_status": status,
        "detail": detail,
        "actual_diagnostic": detail,
        "origin": case.origin,
        "tags": list(case.tags),
        "tool_version": version,
        "artifact": artifact or {},
    }


def observed_diagnostic_text(item: dict[str, object]) -> str:
    parts = [
        str(item.get("detail") or ""),
        str(item.get("actual_diagnostic") or ""),
    ]
    artifact = item.get("artifact")
    if isinstance(artifact, dict):
        for key in ("stdout", "stderr", "hol_error", "error"):
            value = artifact.get(key)
            if isinstance(value, str):
                parts.append(value)
        for key in ("raw_stdout_path", "raw_stderr_path"):
            value = artifact.get(key)
            if isinstance(value, str) and value:
                path = pathlib.Path(value)
                if path.exists():
                    parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(part for part in parts if part)


def apply_expectation(case: Case, item: dict[str, object]) -> dict[str, object]:
    expected = case.expected.get(str(item["mode"]))
    actual_status = str(item["status"])
    actual_diagnostic = observed_diagnostic_text(item)
    item["actual_status"] = actual_status
    item["actual_diagnostic"] = actual_diagnostic

    if expected is None:
        item["expected_status"] = None
        item["expected_diagnostic"] = None
        item["diagnostic_match"] = None
        if actual_status == FAIL:
            item["conformance_status"] = FAIL
            item["classification"] = CLASSIFICATION_UNEXPECTED_FAILURE
        else:
            item["conformance_status"] = PASS
            item["classification"] = CLASSIFICATION_ACCEPTED
        return item

    item["expected_status"] = expected.status
    item["expected_diagnostic"] = expected.diagnostic_substring
    diagnostic_match = (
        expected.diagnostic_substring in actual_diagnostic
        if expected.diagnostic_substring is not None
        else None
    )
    item["diagnostic_match"] = diagnostic_match

    if expected.status == RED:
        item["red_obligation"] = True
        item["conformance_status"] = PASS
        item["classification"] = CLASSIFICATION_EXPECTED_IMPLEMENTATION_GAP
        return item

    if actual_status != expected.status:
        item["conformance_status"] = FAIL
        item["classification"] = CLASSIFICATION_UNEXPECTED_STATUS
    elif expected.status == UNSUPPORTED and expected.diagnostic_substring is not None and not diagnostic_match:
        item["conformance_status"] = FAIL
        item["classification"] = CLASSIFICATION_DIAGNOSTIC_MISMATCH
    else:
        item["conformance_status"] = PASS
        item["classification"] = CLASSIFICATION_MATCHED
    return item


def failure_class(item: dict[str, object]) -> str | None:
    status = str(item.get("status"))
    conformance_status = str(item.get("conformance_status", status))
    mode = str(item.get("mode"))
    expected_status = item.get("expected_status")

    if expected_status == RED:
        return "expected implementation gap"
    if expected_status == UNSUPPORTED and status == UNSUPPORTED:
        return "expected unsupported diagnostic"
    if status == UNSUPPORTED and mode == MODE_Z3_ORACLE:
        return "solver unsupported behavior"
    if status != FAIL and conformance_status != FAIL:
        return None
    if mode == MODE_PARSER:
        return "parser"
    if mode == MODE_TYPECHECK:
        return "typecheck"
    if mode == MODE_Z3_ORACLE:
        return "solver unsupported behavior" if status == UNSUPPORTED else "solver"
    if mode == MODE_PROOF_PARSE:
        return "proof parse"
    if mode == MODE_PROOF_REPLAY:
        return "proof replay"
    if expected_status == UNSUPPORTED:
        return "expected unsupported diagnostic"
    return mode


def parser_command_error(text: str, node: object, message: str) -> ValueError:
    offset = getattr(node, "start", 0)
    pos = line_col(text, offset)
    return ValueError(f"{message} at line {pos['line']}, column {pos['column']}")


def atom_text(node: object) -> str | None:
    return node.text if isinstance(node, Atom) else None


def expect_command_len(text: str, node: ListNode, command: str, length: int, diagnostic: str) -> None:
    if len(node.items) != length:
        raise parser_command_error(text, node, diagnostic)


def expect_command_list_arg(text: str, node: ListNode, index: int, diagnostic: str) -> None:
    if len(node.items) <= index or not isinstance(node.items[index], ListNode):
        raise parser_command_error(text, node, diagnostic)


def validate_smtlib_command_shapes(text: str, nodes: list[object]) -> None:
    for node in nodes:
        if not isinstance(node, ListNode) or not node.items:
            raise parser_command_error(text, node, "malformed command")
        command = atom_text(node.items[0])
        if command is None:
            raise parser_command_error(text, node, "malformed command")

        if command in {"check-sat", "reset", "reset-assertions", "exit",
                       "get-proof", "get-unsat-assumptions", "get-unsat-core",
                       "get-model", "get-assignment", "get-assertions"}:
            labels = {
                "check-sat": "malformed check-sat",
                "reset": "malformed reset",
                "reset-assertions": "malformed reset-assertions",
                "exit": "malformed exit",
            }
            expect_command_len(text, node, command, 1, labels.get(command, f"malformed {command}"))
        elif command in {"set-logic", "get-info", "get-option", "assert"}:
            labels = {"get-option": "malformed get-option"}
            expect_command_len(text, node, command, 2, labels.get(command, f"malformed {command}"))
        elif command in {"declare-sort", "declare-const", "set-option"}:
            expect_command_len(text, node, command, 3, f"malformed {command}")
        elif command == "set-info":
            if len(node.items) < 2 or len(node.items) > 3:
                raise parser_command_error(text, node, "malformed set-info attribute")
            if atom_text(node.items[1]) == ":source" and len(node.items) != 3:
                raise parser_command_error(text, node, "malformed set-info attribute")
        elif command in {"declare-fun", "define-sort"}:
            expect_command_len(text, node, command, 4, f"malformed {command}")
            expect_command_list_arg(text, node, 2, f"malformed {command}")
        elif command == "define-const":
            expect_command_len(text, node, command, 4, f"malformed {command}")
        elif command == "declare-datatype":
            expect_command_len(text, node, command, 3, "malformed declare-datatype")
        elif command in {"define-fun", "define-fun-rec"}:
            expect_command_len(text, node, command, 5, f"malformed {command}")
            expect_command_list_arg(text, node, 2, f"malformed {command}")
        elif command == "define-funs-rec":
            expect_command_len(text, node, command, 3, "malformed recursive definition block")
            expect_command_list_arg(text, node, 1, "malformed recursive definition block")
            expect_command_list_arg(text, node, 2, "malformed recursive definition block")
            signatures = node.items[1].items  # type: ignore[union-attr]
            bodies = node.items[2].items  # type: ignore[union-attr]
            if len(signatures) != len(bodies):
                raise parser_command_error(text, node, "malformed recursive definition block")
        elif command == "declare-datatypes":
            expect_command_len(text, node, command, 3, "malformed declare-datatypes")
            expect_command_list_arg(text, node, 1, "malformed declare-datatypes")
            expect_command_list_arg(text, node, 2, "malformed declare-datatypes")
        elif command in {"push", "pop"}:
            if len(node.items) not in {1, 2}:
                raise parser_command_error(text, node, f"malformed {command}")
        elif command in {"check-sat-assuming", "get-value"}:
            label = "malformed get-value" if command == "get-value" else "malformed check-sat-assuming"
            expect_command_len(text, node, command, 2, label)
            expect_command_list_arg(text, node, 1, label)
        elif command == "echo":
            expect_command_len(text, node, command, 2, "echo requires a string literal")
            msg = atom_text(node.items[1])
            if msg is None or not (msg.startswith('"') and msg.endswith('"')):
                raise parser_command_error(text, node, "echo requires a string literal")


def parser_check(case: Case) -> dict[str, object]:
    try:
        sexps = parse_sexps(case.text)
        validate_smtlib_command_shapes(case.text, sexps)
    except Exception as exc:  # SexpParseError comes from the recorder module.
        return result(case, MODE_PARSER, FAIL, str(exc))
    logic = find_set_logic(case.text)
    if logic is None:
        if case.logic == "ALL":
            return result(
                case,
                MODE_PARSER,
                PASS,
                "SMT-LIB S-expression parse succeeded without a concrete set-logic",
            )
        return result(case, MODE_PARSER, FAIL, "missing set-logic command")
    if case.logic not in {"UNKNOWN", "ALL"} and logic != case.logic:
        return result(
            case,
            MODE_PARSER,
            FAIL,
            f"set-logic {logic} does not match case logic {case.logic}",
        )
    return result(case, MODE_PARSER, PASS, "SMT-LIB S-expression parse succeeded")


def executable_available(executable: str) -> bool:
    if os.path.sep in executable:
        return pathlib.Path(executable).exists()
    return shutil.which(executable) is not None


def run_shell_command(command: str, timeout: int) -> subprocess.CompletedProcess[str]:
    process = subprocess.Popen(
        command,
        shell=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        raise subprocess.TimeoutExpired(command, timeout, output=stdout, stderr=stderr) from exc
    return subprocess.CompletedProcess(command, process.returncode, stdout, stderr)


def run_z3_oracle(case: Case, input_path: pathlib.Path, z3: str, timeout: int, version: str) -> dict[str, object]:
    command = [z3, "-smt2", str(input_path)]
    if not executable_available(z3):
        return result(
            case,
            MODE_Z3_ORACLE,
            UNSUPPORTED,
            f"Z3 executable not found: {z3}",
            artifact={"command_line": command},
            version=version,
        )
    try:
        completed = subprocess.run(
            command,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        return result(
            case,
            MODE_Z3_ORACLE,
            FAIL,
            f"Z3 timed out after {timeout}s",
            artifact={"command_line": command, "stdout": exc.stdout or "", "stderr": exc.stderr or ""},
            version=version,
        )
    except OSError as exc:
        return result(case, MODE_Z3_ORACLE, UNSUPPORTED, str(exc), artifact={"command_line": command}, version=version)

    solver_result, _ = detect_solver_result(completed.stdout)
    artifact = {
        "command_line": command,
        "exit_code": completed.returncode,
        "solver_result": solver_result,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    }
    if solver_result not in SOLVER_RESULTS:
        stderr_lower = completed.stderr.lower()
        if "unsupported" in stderr_lower or "unknown logic" in stderr_lower:
            return result(
                case,
                MODE_Z3_ORACLE,
                UNSUPPORTED,
                "Z3 reported unsupported input",
                artifact=artifact,
                version=version,
            )
        if completed.returncode != 0:
            return result(case, MODE_Z3_ORACLE, FAIL, "Z3 exited nonzero", artifact=artifact, version=version)
        return result(case, MODE_Z3_ORACLE, FAIL, "Z3 did not print a solver result", artifact=artifact, version=version)
    detail = f"Z3 returned {solver_result}"
    if completed.returncode != 0:
        detail += " before a nonzero exit"
    return result(case, MODE_Z3_ORACLE, PASS, detail, artifact=artifact, version=version)


def proof_checks(
    case: Case,
    input_path: pathlib.Path,
    out_dir: pathlib.Path,
    z3: str,
    timeout: int,
    version: str,
) -> tuple[dict[str, object], dict[str, object], dict[str, object] | None]:
    if not executable_available(z3):
        artifact = {"command_line": [z3, *proof_options_for(version), "-smt2", str(input_path)]}
        unsupported = result(case, MODE_PROOF_PARSE, UNSUPPORTED, f"Z3 executable not found: {z3}", artifact=artifact, version=version)
        unsupported_replay = result(case, MODE_PROOF_REPLAY, UNSUPPORTED, f"Z3 executable not found: {z3}", artifact=artifact, version=version)
        return unsupported, unsupported_replay, None

    entry = record_proof_corpus_entry(
        input_path,
        out_dir / "proof-corpus",
        z3,
        version,
        [],
        True,
        timeout,
    )
    proof = entry["proof"]  # type: ignore[index]
    solver = entry["solver"]  # type: ignore[index]
    proof_summary = {
        "available": proof["available"],  # type: ignore[index]
        "rule_histogram": proof["rule_histogram"],  # type: ignore[index]
        "unknown_rules": proof["unknown_rules"],  # type: ignore[index]
        "malformed_fragments": proof["malformed_fragments"],  # type: ignore[index]
    }
    artifact = {
        "proof_corpus_entry": entry,
        "command_line": entry["z3"]["command_line"],  # type: ignore[index]
        "z3_version": version,
        "solver_result": solver["result"],  # type: ignore[index]
        "proof_summary": proof_summary,
        "raw_proof_path": proof.get("raw_path"),  # type: ignore[union-attr]
        "raw_stdout_path": entry["z3"]["stdout_path"],  # type: ignore[index]
        "raw_stderr_path": entry["z3"]["stderr_path"],  # type: ignore[index]
    }

    if solver["result"] != "unsat":  # type: ignore[index]
        parse = result(
            case,
            MODE_PROOF_PARSE,
            UNSUPPORTED,
            f"proof modes require unsat input; Z3 returned {solver['result']}",  # type: ignore[index]
            artifact=artifact,
            version=version,
        )
        replay = result(
            case,
            MODE_PROOF_REPLAY,
            UNSUPPORTED,
            f"proof modes require unsat input; Z3 returned {solver['result']}",  # type: ignore[index]
            artifact=artifact,
            version=version,
        )
        return parse, replay, entry

    if not proof["available"]:  # type: ignore[index]
        parse = result(case, MODE_PROOF_PARSE, FAIL, "Z3 did not emit a raw proof", artifact=artifact, version=version)
        replay = result(case, MODE_PROOF_REPLAY, FAIL, "Z3 did not emit a raw proof", artifact=artifact, version=version)
        return parse, replay, entry

    malformed = proof["malformed_fragments"]  # type: ignore[index]
    unknown = proof["unknown_rules"]  # type: ignore[index]
    if malformed:
        parse_status = result(case, MODE_PROOF_PARSE, FAIL, "raw proof contains malformed fragments", artifact=artifact, version=version)
    else:
        parse_status = result(case, MODE_PROOF_PARSE, PASS, "raw proof parsed for rule coverage", artifact=artifact, version=version)

    if malformed:
        replay_status = result(case, MODE_PROOF_REPLAY, FAIL, "raw proof contains malformed fragments", artifact=artifact, version=version)
    elif unknown:
        replay_status = result(case, MODE_PROOF_REPLAY, FAIL, "raw proof uses replay-unknown rules", artifact=artifact, version=version)
    else:
        replay_status = result(case, MODE_PROOF_REPLAY, PASS, "all discovered proof rules are replay-supported or parse-only", artifact=artifact, version=version)
    return parse_status, replay_status, entry


def run_command_mode(
    case: Case,
    mode: str,
    input_path: pathlib.Path,
    command_template: str | None,
    timeout: int,
) -> dict[str, object]:
    if not command_template:
        return result(case, mode, UNSUPPORTED, f"no {mode} command configured")
    command = command_template.format(
        input=str(input_path),
        logic=case.logic,
        name=case.name,
    )
    try:
        completed = run_shell_command(command, timeout)
    except subprocess.TimeoutExpired as exc:
        return result(
            case,
            mode,
            FAIL,
            f"{mode} command timed out after {timeout}s",
            artifact={"command": command, "stdout": exc.stdout or "", "stderr": exc.stderr or ""},
        )
    artifact = {
        "command": command,
        "exit_code": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    }
    if completed.returncode == 0:
        return result(case, mode, PASS, f"{mode} command succeeded", artifact=artifact)
    return result(case, mode, FAIL, f"{mode} command failed", artifact=artifact)


def default_typecheck_command() -> str:
    return DEFAULT_TYPECHECK_COMMAND


def run_typecheck_mode(
    case: Case,
    input_path: pathlib.Path,
    command_template: str | None,
    timeout: int,
) -> dict[str, object]:
    if command_template == DEFAULT_TYPECHECK_COMMAND and not DEFAULT_TYPECHECK_DRIVER.exists():
        return result(
            case,
            MODE_TYPECHECK,
            UNSUPPORTED,
            f"default typecheck-only driver not built: {DEFAULT_TYPECHECK_DRIVER}",
            artifact={"command": command_template},
        )
    return run_command_mode(case, MODE_TYPECHECK, input_path, command_template, timeout)


def command_output_field(stdout: str, stderr: str, field: str) -> str | None:
    prefix = f"{field}="
    for line in stdout.splitlines() + stderr.splitlines():
        if line.startswith(prefix):
            return line[len(prefix):]
    return None


def z3_tac_unsound_success_diagnostic(stdout: str, stderr: str) -> str | None:
    diagnostic = command_output_field(stdout, stderr, "diagnostic")
    solver_result = command_output_field(stdout, stderr, "result")
    theorem = command_output_field(stdout, stderr, "theorem")
    if theorem is not None and solver_result in {"sat", "unknown"}:
        return (
            "checked Z3_TAC reported "
            f"{solver_result} with a HOL theorem on a non-theorem-producing path"
        )

    if diagnostic is not None:
        diagnostic_lower = diagnostic.lower()
        if "satisfiable" in diagnostic_lower:
            return diagnostic
        if "unknown" in diagnostic_lower:
            return diagnostic

    for line in stdout.splitlines() + stderr.splitlines():
        normalized = line.strip().lower()
        if normalized in {"sat", "unknown", "status=sat", "status=unknown"}:
            return f"checked Z3_TAC reported {normalized} on a theorem-producing path"
        if "solver reports negated term to be satisfiable" in normalized:
            return line.strip()
        if "solver reports unknown" in normalized:
            return line.strip()
    return None


def default_z3_tac_command() -> str:
    return DEFAULT_Z3_TAC_COMMAND


def run_z3_tac_mode(
    case: Case,
    input_path: pathlib.Path,
    command_template: str | None,
    timeout: int,
) -> dict[str, object]:
    if not command_template:
        return result(case, MODE_Z3_TAC, UNSUPPORTED, "no z3-tac command configured")
    if command_template == DEFAULT_Z3_TAC_COMMAND and not DEFAULT_Z3_TAC_DRIVER.exists():
        return result(
            case,
            MODE_Z3_TAC,
            UNSUPPORTED,
            f"default z3-tac driver not built: {DEFAULT_Z3_TAC_DRIVER}",
            artifact={"command": command_template},
        )

    command = command_template.format(
        input=str(input_path),
        logic=case.logic,
        name=case.name,
    )
    try:
        completed = run_shell_command(command, timeout)
    except subprocess.TimeoutExpired as exc:
        return result(
            case,
            MODE_Z3_TAC,
            FAIL,
            f"{MODE_Z3_TAC} command timed out after {timeout}s",
            artifact={"command": command, "stdout": exc.stdout or "", "stderr": exc.stderr or ""},
        )

    stdout = completed.stdout
    stderr = completed.stderr
    artifact = {
        "command": command,
        "exit_code": completed.returncode,
        "stdout": stdout,
        "stderr": stderr,
    }
    diagnostic = command_output_field(stdout, stderr, "diagnostic")
    version = command_output_field(stdout, stderr, "z3_version")
    solver_result = command_output_field(stdout, stderr, "result")

    combined = f"{stdout}\n{stderr}"
    if "Z3_TAC_PASS" in combined and completed.returncode == 0:
        unsound_success = z3_tac_unsound_success_diagnostic(stdout, stderr)
        if unsound_success is not None:
            return result(
                case,
                MODE_Z3_TAC,
                FAIL,
                unsound_success,
                artifact=artifact,
                version=version,
            )
        if solver_result == "sat":
            return result(
                case,
                MODE_Z3_TAC,
                PASS,
                f"checked Z3_TAC solver result {solver_result}",
                artifact=artifact,
                version=version,
            )
        return result(
            case,
            MODE_Z3_TAC,
            PASS,
            "checked Z3_TAC theorem proved",
            artifact=artifact,
            version=version,
        )
    if "Z3_TAC_UNSUPPORTED" in combined:
        return result(
            case,
            MODE_Z3_TAC,
            UNSUPPORTED,
            diagnostic or "checked Z3_TAC driver reported unsupported input",
            artifact=artifact,
            version=version,
        )
    if "unexpected oracle/axiom tags" in combined:
        return result(
            case,
            MODE_Z3_TAC,
            FAIL,
            "checked Z3_TAC result carried oracle/axiom tags",
            artifact=artifact,
            version=version,
        )
    if "Z3_TAC_FAIL" in combined:
        return result(
            case,
            MODE_Z3_TAC,
            FAIL,
            diagnostic or "checked Z3_TAC driver failed",
            artifact=artifact,
            version=version,
        )
    if completed.returncode == 0:
        return result(case, MODE_Z3_TAC, PASS, f"{MODE_Z3_TAC} command succeeded", artifact=artifact, version=version)
    return result(case, MODE_Z3_TAC, FAIL, f"{MODE_Z3_TAC} command failed", artifact=artifact, version=version)


def preserve_repro(out_dir: pathlib.Path, case: Case, input_path: pathlib.Path, item: dict[str, object]) -> None:
    repro_dir = out_dir / "repro" / slug(case.logic) / slug(case.name) / slug(str(item["mode"]))
    repro_dir.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(input_path, repro_dir / "input.smt2")
    json_dump(repro_dir / "result.json", item)
    version = item.get("tool_version")
    if isinstance(version, str) and version:
        write_text(repro_dir / "tool-version.txt", version)
    artifact = item.get("artifact", {})
    if isinstance(artifact, dict):
        command_line = artifact.get("command_line")
        command = artifact.get("command")
        if isinstance(command_line, list):
            write_text(repro_dir / "command.txt", " ".join(shlex.quote(str(part)) for part in command_line) + "\n")
        elif isinstance(command, str):
            write_text(repro_dir / "command.txt", command + "\n")

        stdout = artifact.get("stdout")
        stderr = artifact.get("stderr")
        if isinstance(stdout, str):
            write_text(repro_dir / "stdout.txt", stdout)
        else:
            stdout_path = artifact.get("raw_stdout_path")
            if isinstance(stdout_path, str) and stdout_path:
                source = pathlib.Path(stdout_path)
                if source.exists():
                    shutil.copyfile(source, repro_dir / "stdout.txt")
        if isinstance(stderr, str):
            write_text(repro_dir / "stderr.txt", stderr)
        else:
            stderr_path = artifact.get("raw_stderr_path")
            if isinstance(stderr_path, str) and stderr_path:
                source = pathlib.Path(stderr_path)
                if source.exists():
                    shutil.copyfile(source, repro_dir / "stderr.txt")

        hol_error = artifact.get("hol_error")
        if isinstance(hol_error, str):
            write_text(repro_dir / "hol-error.txt", hol_error)

        proof_summary = artifact.get("proof_summary")
        if isinstance(proof_summary, dict):
            json_dump(repro_dir / "proof-summary.json", proof_summary)
        proof_entry = artifact.get("proof_corpus_entry")
        if isinstance(proof_entry, dict):
            json_dump(repro_dir / "proof-corpus-entry.json", proof_entry)

        proof_path = artifact.get("raw_proof_path")
        if isinstance(proof_path, str) and proof_path:
            source = pathlib.Path(proof_path)
            if source.exists():
                shutil.copyfile(source, repro_dir / "proof.raw")


def summarize(results: Iterable[dict[str, object]]) -> dict[str, object]:
    summary: dict[str, dict[str, collections.Counter[str]]] = {
        logic: {mode: collections.Counter() for mode in ALL_MODES}
        for logic in HOLSMT_LOGICS
    }
    summary["UNKNOWN"] = {mode: collections.Counter() for mode in ALL_MODES}
    unsupported_reasons: collections.Counter[str] = collections.Counter()
    classification_counts: collections.Counter[str] = collections.Counter()
    conformance_counts: collections.Counter[str] = collections.Counter()
    failure_class_counts: collections.Counter[str] = collections.Counter()
    diagnostic_mismatches: list[dict[str, object]] = []

    for item in results:
        logic = str(item["logic"])
        mode = str(item["mode"])
        status = str(item["status"])
        classification = str(item.get("classification", "unclassified"))
        conformance_status = str(item.get("conformance_status", status))
        summary.setdefault(logic, {m: collections.Counter() for m in ALL_MODES})
        summary[logic][mode][status] += 1
        classification_counts[classification] += 1
        conformance_counts[conformance_status] += 1
        item_failure_class = item.get("failure_class")
        if isinstance(item_failure_class, str) and item_failure_class:
            failure_class_counts[item_failure_class] += 1
        if status == UNSUPPORTED:
            unsupported_reasons[f"{mode}: {item['detail']}"] += 1
        if classification == CLASSIFICATION_DIAGNOSTIC_MISMATCH:
            diagnostic_mismatches.append(
                {
                    "case": item["case"],
                    "logic": logic,
                    "mode": mode,
                    "expected_diagnostic": item.get("expected_diagnostic"),
                    "actual_diagnostic": item.get("actual_diagnostic"),
                }
            )

    serial_summary = {
        logic: {
            mode: {
                PASS: counts[PASS],
                FAIL: counts[FAIL],
                UNSUPPORTED: counts[UNSUPPORTED],
            }
            for mode, counts in modes.items()
        }
        for logic, modes in sorted(summary.items())
    }
    return {
        "by_logic_mode": serial_summary,
        "unsupported_reasons": dict(sorted(unsupported_reasons.items())),
        "classification_counts": dict(sorted(classification_counts.items())),
        "failure_class_counts": dict(sorted(failure_class_counts.items())),
        "conformance_status_counts": {
            PASS: conformance_counts[PASS],
            FAIL: conformance_counts[FAIL],
        },
        "diagnostic_mismatches": diagnostic_mismatches,
    }


def tag_value(tags: Iterable[str], prefix: str) -> str | None:
    marker = f"{prefix}:"
    for tag in tags:
        if tag.startswith(marker):
            return tag[len(marker):]
    return None


def semantic_result(item: dict[str, object]) -> str | None:
    artifact = item.get("artifact")
    if isinstance(artifact, dict):
        solver_result = artifact.get("solver_result")
        if isinstance(solver_result, str) and solver_result:
            return solver_result
    return None


def result_signature(items: Iterable[dict[str, object]]) -> dict[str, dict[str, str | None]]:
    signature: dict[str, dict[str, str | None]] = {}
    for item in sorted(items, key=lambda result: str(result["mode"])):
        mode = str(item["mode"])
        signature[mode] = {
            "status": str(item.get("status")),
            "conformance_status": str(item.get("conformance_status", item.get("status"))),
            "semantic_result": semantic_result(item),
        }
    return signature


def build_metamorphic_groups(
    cases: list[Case],
    results: list[dict[str, object]],
) -> dict[str, object]:
    cases_by_group: dict[str, list[Case]] = {}
    expected_semantics: dict[str, set[str]] = {}
    for case in cases:
        group = tag_value(case.tags, "metamorphic-group")
        if group is None:
            continue
        cases_by_group.setdefault(group, []).append(case)
        expected = tag_value(case.tags, "metamorphic-result")
        if expected is not None:
            expected_semantics.setdefault(group, set()).add(expected)

    results_by_case: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    for item in results:
        results_by_case[str(item["case"])].append(item)

    groups: list[dict[str, object]] = []
    failing = 0
    for group, group_cases in sorted(cases_by_group.items()):
        signatures = {
            case.name: result_signature(results_by_case.get(case.name, []))
            for case in group_cases
        }
        non_empty_signatures = [sig for sig in signatures.values() if sig]
        reference = non_empty_signatures[0] if non_empty_signatures else {}
        agree = bool(non_empty_signatures) and all(
            signature == reference for signature in non_empty_signatures
        )
        expected = sorted(expected_semantics.get(group, set()))
        expected_agree = len(expected) <= 1
        status = PASS if agree and expected_agree else FAIL
        if status == FAIL:
            failing += 1
        groups.append(
            {
                "group": group,
                "status": status,
                "cases": [case.name for case in group_cases],
                "expected_semantic_results": expected,
                "signatures": signatures,
            }
        )

    return {
        "group_count": len(groups),
        "status_counts": {
            PASS: len(groups) - failing,
            FAIL: failing,
        },
        "groups": groups,
    }


def load_external_source_manifest(path: pathlib.Path) -> dict[str, object]:
    if not path.exists():
        return {
            "schema": EXTERNAL_SOURCE_SCHEMA,
            "sources": [],
            "default_pending_reason": "No curated external benchmark source is configured for this logic.",
            "logic_status": {},
        }
    with path.open(encoding="utf-8") as infile:
        manifest = json.load(infile)
    if not isinstance(manifest, dict):
        raise ValueError(f"{path}: external source manifest root must be an object")
    if manifest.get("schema") != EXTERNAL_SOURCE_SCHEMA:
        raise ValueError(f"{path}: external source manifest schema must be {EXTERNAL_SOURCE_SCHEMA}")
    sources = manifest.get("sources", [])
    if not isinstance(sources, list):
        raise ValueError(f"{path}: sources must be a list")
    for index, source in enumerate(sources, start=1):
        context = f"{path} sources[{index}]"
        if not isinstance(source, dict):
            raise ValueError(f"{context}: source must be an object")
        for field_name in ("id", "kind", "url", "pin_type", "pin"):
            if not isinstance(source.get(field_name), str) or not source.get(field_name):
                raise ValueError(f"{context}: {field_name} must be a non-empty string")
    logic_status = manifest.get("logic_status", {})
    if not isinstance(logic_status, dict):
        raise ValueError(f"{path}: logic_status must be an object")
    default_pending = manifest.get("default_pending_reason")
    if default_pending is not None and not isinstance(default_pending, str):
        raise ValueError(f"{path}: default_pending_reason must be a string")
    return manifest


def case_source_kind(case: Case) -> str | None:
    for kind in (SOURCE_KIND_BENCHMARK, SOURCE_KIND_Z3_PROOF, SOURCE_KIND_REGRESSION):
        if kind in case.tags:
            return kind
    return None


def benchmark_family(case: Case) -> str:
    tagged = tag_value(case.tags, "family")
    if tagged:
        return tagged
    if case.source_path is not None:
        parent = case.source_path.parent.name
        if parent and parent != ".":
            return parent
    return case.logic


def summarize_external_benchmarks(
    cases: list[Case],
    results: list[dict[str, object]],
    source_manifest: Mapping[str, object],
) -> dict[str, object]:
    external_cases_by_name = {
        case.name: case
        for case in cases
        if case_source_kind(case) is not None
    }
    results_by_case: dict[str, list[dict[str, object]]] = collections.defaultdict(list)
    for item in results:
        case_name = str(item["case"])
        if case_name in external_cases_by_name:
            results_by_case[case_name].append(item)

    by_kind: dict[str, collections.Counter[str]] = collections.defaultdict(collections.Counter)
    by_logic: dict[str, collections.Counter[str]] = collections.defaultdict(collections.Counter)
    unsupported_families: dict[str, dict[str, object]] = {}
    for case_name, case in external_cases_by_name.items():
        kind = case_source_kind(case) or "external"
        by_kind[kind]["cases"] += 1
        by_logic[case.logic]["cases"] += 1
        for item in results_by_case.get(case_name, []):
            status = str(item["status"])
            by_kind[kind][status] += 1
            by_logic[case.logic][status] += 1
            if status == UNSUPPORTED:
                key = f"{kind}:{benchmark_family(case)}:{item['mode']}"
                family = unsupported_families.setdefault(
                    key,
                    {
                        "kind": kind,
                        "family": benchmark_family(case),
                        "logic": case.logic,
                        "mode": item["mode"],
                        "count": 0,
                        "reasons": collections.Counter(),
                        "cases": set(),
                    },
                )
                family["count"] = int(family["count"]) + 1
                family["reasons"][str(item["detail"])] += 1  # type: ignore[index]
                family["cases"].add(case.name)  # type: ignore[union-attr]

    logic_status = source_manifest.get("logic_status", {})
    if not isinstance(logic_status, dict):
        logic_status = {}
    default_pending = source_manifest.get("default_pending_reason")
    if not isinstance(default_pending, str) or not default_pending:
        default_pending = "Curated external benchmark coverage is pending for this logic."

    official_logic_status: dict[str, dict[str, object]] = {}
    for logic in OFFICIAL_LOGICS:
        covered = by_logic.get(logic, collections.Counter())["cases"]
        configured = logic_status.get(logic, {})
        if not isinstance(configured, dict):
            configured = {"reason": str(configured)}
        reason = configured.get("reason")
        source = configured.get("source")
        status = "covered" if covered else "pending"
        official_logic_status[logic] = {
            "status": status,
            "case_count": covered,
            "reason": None if covered else (reason if isinstance(reason, str) and reason else default_pending),
            "source": source if isinstance(source, str) else None,
        }

    unsupported_serial = []
    for value in unsupported_families.values():
        reasons = value["reasons"]
        cases_set = value["cases"]
        unsupported_serial.append(
            {
                "kind": value["kind"],
                "family": value["family"],
                "logic": value["logic"],
                "mode": value["mode"],
                "count": value["count"],
                "reasons": dict(sorted(reasons.items())),  # type: ignore[union-attr]
                "cases": sorted(cases_set),  # type: ignore[arg-type]
            }
        )

    def counter_json(counter: collections.Counter[str]) -> dict[str, int]:
        return {
            "cases": counter["cases"],
            PASS: counter[PASS],
            FAIL: counter[FAIL],
            UNSUPPORTED: counter[UNSUPPORTED],
        }

    sources = source_manifest.get("sources", [])
    return {
        "schema": EXTERNAL_SOURCE_SCHEMA,
        "source_pins": sources if isinstance(sources, list) else [],
        "by_kind": {kind: counter_json(counts) for kind, counts in sorted(by_kind.items())},
        "by_logic": {logic: counter_json(counts) for logic, counts in sorted(by_logic.items())},
        "unsupported_families": sorted(
            unsupported_serial,
            key=lambda item: (str(item["kind"]), str(item["family"]), str(item["mode"])),
        ),
        "official_logic_status": official_logic_status,
    }


def build_report(
    cases: list[Case],
    results: list[dict[str, object]],
    proof_entries: list[dict[str, object]],
    z3: str,
    z3_ver: str,
    external_source_manifest: Mapping[str, object],
) -> dict[str, object]:
    counts = collections.Counter(str(item["status"]) for item in results)
    logic_summary = summarize(results)
    conformance_counts = logic_summary["conformance_status_counts"]  # type: ignore[index]
    proof_summary = build_proof_corpus_summary(proof_entries) if proof_entries else None
    official_missing = sorted(set(OFFICIAL_LOGICS) - {case.logic for case in cases})
    metamorphic_summary = build_metamorphic_groups(cases, results)
    benchmark_summary = summarize_external_benchmarks(cases, results, external_source_manifest)
    return {
        "schema": SCHEMA,
        "smtlib_version": SMTLIB_VERSION,
        "runner_version": 2,
        "z3": {
            "executable": z3,
            "version": z3_ver,
        },
        "modes": ALL_MODES,
        "case_count": len(cases),
        "result_count": len(results),
        "status_counts": {
            PASS: counts[PASS],
            FAIL: counts[FAIL],
            UNSUPPORTED: counts[UNSUPPORTED],
        },
        "conformance_status_counts": conformance_counts,
        "classification_counts": logic_summary["classification_counts"],  # type: ignore[index]
        "official_logic_coverage": {
            "represented_count": len(OFFICIAL_LOGICS) - len(official_missing),
            "total_count": len(OFFICIAL_LOGICS),
            "missing": official_missing,
        },
        "summary": logic_summary,
        "proof_corpus_summary": proof_summary,
        "metamorphic_groups": metamorphic_summary,
        "external_benchmark_coverage": benchmark_summary,
        "cases": [
            {
                "name": case.name,
                "logic": case.logic,
                "origin": case.origin,
                "tags": list(case.tags),
                "source_path": str(case.source_path) if case.source_path else None,
                "modes": list(case.modes),
                "expected": expected_outcome_json(case.expected),
            }
            for case in cases
        ],
        "results": results,
    }


def markdown_report(report: dict[str, object]) -> str:
    z3 = report["z3"]  # type: ignore[index]
    status_counts = report["status_counts"]  # type: ignore[index]
    conformance_counts = report["conformance_status_counts"]  # type: ignore[index]
    coverage = report["official_logic_coverage"]  # type: ignore[index]
    lines = [
        "# HolSmt SMT-LIB Conformance Report",
        "",
        f"- Schema: `{report['schema']}`",
        f"- SMT-LIB target: `{report['smtlib_version']}`",
        f"- Z3: `{z3['executable']}` version `{z3['version']}`",  # type: ignore[index]
        f"- Cases: {report['case_count']}",
        f"- Actual results: pass {status_counts[PASS]}, fail {status_counts[FAIL]}, unsupported {status_counts[UNSUPPORTED]}",  # type: ignore[index]
        f"- Conformance: pass {conformance_counts[PASS]}, fail {conformance_counts[FAIL]}",  # type: ignore[index]
        f"- Official logic coverage: {coverage['represented_count']}/{coverage['total_count']}",  # type: ignore[index]
        "",
        "## Counts By Logic And Mode",
        "",
        "| Logic | Mode | Pass | Fail | Unsupported |",
        "| --- | --- | ---: | ---: | ---: |",
    ]
    summary = report["summary"]["by_logic_mode"]  # type: ignore[index]
    for logic in sorted(summary):  # type: ignore[union-attr]
        modes = summary[logic]  # type: ignore[index]
        for mode in ALL_MODES:
            counts = modes[mode]
            lines.append(
                f"| {logic} | {mode} | {counts[PASS]} | {counts[FAIL]} | {counts[UNSUPPORTED]} |"
            )

    unsupported = report["summary"]["unsupported_reasons"]  # type: ignore[index]
    if unsupported:
        lines.extend(["", "## Unsupported Reasons", "", "| Reason | Count |", "| --- | ---: |"])
        for reason, count in unsupported.items():  # type: ignore[union-attr]
            lines.append(f"| `{reason}` | {count} |")

    classifications = report.get("classification_counts")
    if classifications:
        lines.extend(["", "## Expectation Classifications", "", "| Classification | Count |", "| --- | ---: |"])
        for classification, count in classifications.items():  # type: ignore[union-attr]
            lines.append(f"| `{classification}` | {count} |")

    failure_classes = report["summary"].get("failure_class_counts", {})  # type: ignore[index]
    if failure_classes:
        lines.extend(["", "## Failure Classes", "", "| Class | Count |", "| --- | ---: |"])
        for classification, count in failure_classes.items():  # type: ignore[union-attr]
            lines.append(f"| `{classification}` | {count} |")

    benchmark = report.get("external_benchmark_coverage")
    if isinstance(benchmark, dict):
        by_kind = benchmark.get("by_kind", {})
        lines.extend(["", "## External Benchmark Coverage", ""])
        if by_kind:
            lines.extend(["| Kind | Cases | Pass | Fail | Unsupported |", "| --- | ---: | ---: | ---: | ---: |"])
            for kind, counts in by_kind.items():  # type: ignore[union-attr]
                lines.append(
                    f"| {kind} | {counts['cases']} | {counts[PASS]} | {counts[FAIL]} | {counts[UNSUPPORTED]} |"
                )
        else:
            lines.append("No external benchmark directories were selected.")
        unsupported_families = benchmark.get("unsupported_families", [])
        if unsupported_families:
            lines.extend(["", "### Unsupported Benchmark Families", "", "| Kind | Family | Logic | Mode | Count |", "| --- | --- | --- | --- | ---: |"])
            for family in unsupported_families:  # type: ignore[union-attr]
                lines.append(
                    f"| {family['kind']} | {family['family']} | {family['logic']} | {family['mode']} | {family['count']} |"
                )

    proof_summary = report.get("proof_corpus_summary")
    if proof_summary:
        lines.extend(
            [
                "",
                "## Proof Corpus Coverage",
                "",
                f"- Proof entries: {proof_summary['entry_count']}",  # type: ignore[index]
                f"- Proofs: {proof_summary['proof_count']}",  # type: ignore[index]
                f"- Discovered rules: {', '.join(proof_summary['discovered_rules']) or '(none)'}",  # type: ignore[index]
                f"- Malformed fragments: {proof_summary['malformed_fragment_count']}",  # type: ignore[index]
            ]
        )

    metamorphic = report.get("metamorphic_groups")
    if isinstance(metamorphic, dict) and metamorphic.get("group_count"):
        counts = metamorphic["status_counts"]  # type: ignore[index]
        lines.extend(
            [
                "",
                "## Metamorphic Groups",
                "",
                f"- Groups: {metamorphic['group_count']}",  # type: ignore[index]
                f"- Agreement: pass {counts[PASS]}, fail {counts[FAIL]}",  # type: ignore[index]
            ]
        )

    lines.extend(
        [
            "",
            "## Reproducing Failures",
            "",
            "Failing modes preserve `input.smt2`, `result.json`, command output, and raw Z3 proof text when available under `repro/` in the report directory.",
        ]
    )
    return "\n".join(lines) + "\n"


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run HolSmt SMT-LIB conformance modes and write JSON/Markdown reports.")
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("src/HolSmt/tools/conformance-out"))
    parser.add_argument("--z3", default=os.environ.get("HOL4_Z3_EXECUTABLE") or "z3")
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--logic", action="append", choices=HOLSMT_LOGICS)
    parser.add_argument("--mode", action="append", choices=ALL_MODES)
    parser.add_argument("--no-default-suite", action="store_true")
    parser.add_argument(
        "--corpus-dir",
        action="append",
        type=pathlib.Path,
        default=[],
        help=(
            "versioned conformance corpus directory containing manifest.json; "
            f"defaults to {DEFAULT_CORPUS_DIR} with the default suite"
        ),
    )
    parser.add_argument("--benchmark-dir", action="append", type=pathlib.Path, default=[])
    parser.add_argument("--z3-proof-dir", action="append", type=pathlib.Path, default=[])
    parser.add_argument(
        "--regression-dir",
        action="append",
        type=pathlib.Path,
        default=[],
        help="local minimized HolSmt regression directory or .smt2 file",
    )
    parser.add_argument(
        "--external-source-manifest",
        type=pathlib.Path,
        default=DEFAULT_EXTERNAL_SOURCE_MANIFEST,
        help="JSON manifest documenting pinned external benchmark/proof sources",
    )
    parser.add_argument(
        "--typecheck-command",
        default=default_typecheck_command(),
        help=(
            "shell command template for typecheck-only mode; placeholders: "
            "{input}, {logic}, {name}; defaults to src/HolSmt/holsmt-typecheck"
        ),
    )
    parser.add_argument(
        "--z3-tac-command",
        default=default_z3_tac_command(),
        help=(
            "shell command template for z3-tac mode; placeholders: "
            "{input}, {logic}, {name}; defaults to src/HolSmt/holsmt-z3-tac"
        ),
    )
    parser.add_argument("--json-report", default="conformance.json")
    parser.add_argument("--markdown-report", default="CONFORMANCE.md")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    out_dir = args.out.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    selected_logics = set(args.logic) if args.logic else None
    selected_modes = tuple(args.mode) if args.mode else tuple(ALL_MODES)

    cases: list[Case] = []
    if not args.no_default_suite:
        cases.extend(default_cases(selected_logics))
    corpus_dirs = list(args.corpus_dir)
    if not args.no_default_suite and DEFAULT_CORPUS_DIR.exists():
        corpus_dirs.insert(0, DEFAULT_CORPUS_DIR)
    cases.extend(corpus_cases(corpus_dirs, selected_logics))
    cases.extend(
        external_cases(
            args.benchmark_dir,
            selected_logics,
            source_kind=SOURCE_KIND_BENCHMARK,
        )
    )
    cases.extend(
        external_cases(
            args.z3_proof_dir,
            selected_logics,
            source_kind=SOURCE_KIND_Z3_PROOF,
        )
    )
    cases.extend(
        external_cases(
            args.regression_dir,
            selected_logics,
            source_kind=SOURCE_KIND_REGRESSION,
        )
    )
    if not cases:
        print("no conformance cases selected", file=sys.stderr)
        return 2
    external_source_manifest = load_external_source_manifest(args.external_source_manifest)

    case_inputs = write_case_inputs(cases, out_dir)
    z3_ver = z3_version(args.z3) if executable_available(args.z3) else "unavailable"
    results: list[dict[str, object]] = []
    proof_entries: list[dict[str, object]] = []

    for case, input_path in case_inputs:
        proof_result_cache: tuple[dict[str, object], dict[str, object], dict[str, object] | None] | None = None
        for mode in selected_modes:
            if mode not in case.modes:
                continue
            if mode == MODE_PARSER:
                item = parser_check(case)
            elif mode == MODE_Z3_ORACLE:
                item = run_z3_oracle(case, input_path, args.z3, args.timeout, z3_ver)
            elif mode in {MODE_PROOF_PARSE, MODE_PROOF_REPLAY}:
                if proof_result_cache is None:
                    proof_result_cache = proof_checks(case, input_path, out_dir, args.z3, args.timeout, z3_ver)
                    if proof_result_cache[2] is not None:
                        proof_entries.append(proof_result_cache[2])
                item = proof_result_cache[0] if mode == MODE_PROOF_PARSE else proof_result_cache[1]
            elif mode == MODE_TYPECHECK:
                item = run_typecheck_mode(case, input_path, args.typecheck_command, args.timeout)
            elif mode == MODE_Z3_TAC:
                item = run_z3_tac_mode(case, input_path, args.z3_tac_command, args.timeout)
            else:
                raise AssertionError(f"unhandled conformance mode: {mode}")

            item = apply_expectation(case, item)
            item["failure_class"] = failure_class(item)
            results.append(item)
            if item["status"] == FAIL or item["conformance_status"] == FAIL:
                preserve_repro(out_dir, case, input_path, item)

    report = build_report(cases, results, proof_entries, args.z3, z3_ver, external_source_manifest)
    json_path = out_dir / args.json_report
    markdown_path = out_dir / args.markdown_report
    json_dump(json_path, report)
    write_text(markdown_path, markdown_report(report))
    print(f"wrote conformance JSON report to {json_path}")
    print(f"wrote conformance Markdown report to {markdown_path}")
    metamorphic_counts = report["metamorphic_groups"]["status_counts"]  # type: ignore[index]
    return 1 if (
        report["conformance_status_counts"][FAIL] or metamorphic_counts[FAIL]  # type: ignore[index]
    ) else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
