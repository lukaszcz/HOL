#!/usr/bin/env python3
"""Run a local HolSmt SMT-LIB conformance suite and write coverage reports."""

from __future__ import annotations

import argparse
import collections
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from typing import Iterable

from record_z3_proof_corpus import (
    build_summary as build_proof_corpus_summary,
    detect_solver_result,
    parse_sexps,
    record_one as record_proof_corpus_entry,
    z3_version,
)


SCHEMA = "holsmt-conformance-v1"
SMTLIB_VERSION = "2.7"

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


@dataclass(frozen=True)
class Case:
    name: str
    logic: str
    text: str
    origin: str
    tags: tuple[str, ...]
    modes: tuple[str, ...] = tuple(ALL_MODES)
    source_path: pathlib.Path | None = None


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


def discover_smt2_files(paths: Iterable[pathlib.Path]) -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for path in paths:
        path = path.resolve()
        if path.is_file():
            files.append(path)
        elif path.is_dir():
            files.extend(sorted(path.rglob("*.smt2")))
    return sorted(dict.fromkeys(files))


def external_cases(paths: Iterable[pathlib.Path], selected_logics: set[str] | None) -> list[Case]:
    cases: list[Case] = []
    for path in discover_smt2_files(paths):
        text = path.read_text(encoding="utf-8")
        logic = find_set_logic(text) or "UNKNOWN"
        if selected_logics is not None and logic not in selected_logics:
            continue
        cases.append(
            Case(
                name=slug(path.stem),
                logic=logic,
                text=text,
                origin="external",
                tags=("external",),
                source_path=path,
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
        "detail": detail,
        "origin": case.origin,
        "tags": list(case.tags),
        "tool_version": version,
        "artifact": artifact or {},
    }


def parser_check(case: Case) -> dict[str, object]:
    try:
        parse_sexps(case.text)
    except Exception as exc:  # SexpParseError comes from the recorder module.
        return result(case, MODE_PARSER, FAIL, str(exc))
    logic = find_set_logic(case.text)
    if logic is None:
        return result(case, MODE_PARSER, FAIL, "missing set-logic command")
    if case.logic != "UNKNOWN" and logic != case.logic:
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


def run_z3_oracle(case: Case, input_path: pathlib.Path, z3: str, timeout: int, version: str) -> dict[str, object]:
    if not executable_available(z3):
        return result(case, MODE_Z3_ORACLE, UNSUPPORTED, f"Z3 executable not found: {z3}", version=version)
    try:
        completed = subprocess.run(
            [z3, "-smt2", str(input_path)],
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
            artifact={"stdout": exc.stdout or "", "stderr": exc.stderr or ""},
            version=version,
        )
    except OSError as exc:
        return result(case, MODE_Z3_ORACLE, UNSUPPORTED, str(exc), version=version)

    solver_result, _ = detect_solver_result(completed.stdout)
    artifact = {
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
        unsupported = result(case, MODE_PROOF_PARSE, UNSUPPORTED, f"Z3 executable not found: {z3}", version=version)
        unsupported_replay = result(case, MODE_PROOF_REPLAY, UNSUPPORTED, f"Z3 executable not found: {z3}", version=version)
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
    artifact = {
        "proof_corpus_entry": entry,
        "solver_result": solver["result"],  # type: ignore[index]
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
        completed = subprocess.run(
            command,
            shell=True,
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
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


def preserve_repro(out_dir: pathlib.Path, case: Case, input_path: pathlib.Path, item: dict[str, object]) -> None:
    repro_dir = out_dir / "repro" / slug(case.logic) / slug(case.name) / slug(str(item["mode"]))
    repro_dir.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(input_path, repro_dir / "input.smt2")
    json_dump(repro_dir / "result.json", item)
    artifact = item.get("artifact", {})
    if isinstance(artifact, dict):
        stdout = artifact.get("stdout")
        stderr = artifact.get("stderr")
        if isinstance(stdout, str):
            write_text(repro_dir / "stdout.txt", stdout)
        if isinstance(stderr, str):
            write_text(repro_dir / "stderr.txt", stderr)
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

    for item in results:
        logic = str(item["logic"])
        mode = str(item["mode"])
        status = str(item["status"])
        summary.setdefault(logic, {m: collections.Counter() for m in ALL_MODES})
        summary[logic][mode][status] += 1
        if status == UNSUPPORTED:
            unsupported_reasons[f"{mode}: {item['detail']}"] += 1

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
    }


def build_report(
    cases: list[Case],
    results: list[dict[str, object]],
    proof_entries: list[dict[str, object]],
    z3: str,
    z3_ver: str,
) -> dict[str, object]:
    counts = collections.Counter(str(item["status"]) for item in results)
    logic_summary = summarize(results)
    proof_summary = build_proof_corpus_summary(proof_entries) if proof_entries else None
    official_missing = sorted(set(OFFICIAL_LOGICS) - {case.logic for case in cases})
    return {
        "schema": SCHEMA,
        "smtlib_version": SMTLIB_VERSION,
        "runner_version": 1,
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
        "official_logic_coverage": {
            "represented_count": len(OFFICIAL_LOGICS) - len(official_missing),
            "total_count": len(OFFICIAL_LOGICS),
            "missing": official_missing,
        },
        "summary": logic_summary,
        "proof_corpus_summary": proof_summary,
        "cases": [
            {
                "name": case.name,
                "logic": case.logic,
                "origin": case.origin,
                "tags": list(case.tags),
                "source_path": str(case.source_path) if case.source_path else None,
                "modes": list(case.modes),
            }
            for case in cases
        ],
        "results": results,
    }


def markdown_report(report: dict[str, object]) -> str:
    z3 = report["z3"]  # type: ignore[index]
    status_counts = report["status_counts"]  # type: ignore[index]
    coverage = report["official_logic_coverage"]  # type: ignore[index]
    lines = [
        "# HolSmt SMT-LIB Conformance Report",
        "",
        f"- Schema: `{report['schema']}`",
        f"- SMT-LIB target: `{report['smtlib_version']}`",
        f"- Z3: `{z3['executable']}` version `{z3['version']}`",  # type: ignore[index]
        f"- Cases: {report['case_count']}",
        f"- Results: pass {status_counts[PASS]}, fail {status_counts[FAIL]}, unsupported {status_counts[UNSUPPORTED]}",  # type: ignore[index]
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
    parser.add_argument("--benchmark-dir", action="append", type=pathlib.Path, default=[])
    parser.add_argument("--z3-proof-dir", action="append", type=pathlib.Path, default=[])
    parser.add_argument("--typecheck-command", help="shell command template for typecheck-only mode; placeholders: {input}, {logic}, {name}")
    parser.add_argument("--z3-tac-command", help="shell command template for z3-tac mode; placeholders: {input}, {logic}, {name}")
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
    cases.extend(external_cases([*args.benchmark_dir, *args.z3_proof_dir], selected_logics))
    if not cases:
        print("no conformance cases selected", file=sys.stderr)
        return 2

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
                item = run_command_mode(case, mode, input_path, args.typecheck_command, args.timeout)
            elif mode == MODE_Z3_TAC:
                item = run_command_mode(case, mode, input_path, args.z3_tac_command, args.timeout)
            else:
                raise AssertionError(f"unhandled conformance mode: {mode}")

            results.append(item)
            if item["status"] == FAIL:
                preserve_repro(out_dir, case, input_path, item)

    report = build_report(cases, results, proof_entries, args.z3, z3_ver)
    json_path = out_dir / args.json_report
    markdown_path = out_dir / args.markdown_report
    json_dump(json_path, report)
    write_text(markdown_path, markdown_report(report))
    print(f"wrote conformance JSON report to {json_path}")
    print(f"wrote conformance Markdown report to {markdown_path}")
    return 1 if report["status_counts"][FAIL] else 0  # type: ignore[index]


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
