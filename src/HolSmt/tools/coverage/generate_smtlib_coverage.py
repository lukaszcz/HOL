#!/usr/bin/env python3
"""Generate the checked-in HolSmt SMT-LIB coverage report."""

from __future__ import annotations

import json
import sys
import argparse
from pathlib import Path
from typing import Iterable

import audit_coverage_manifest


ROOT = Path(__file__).resolve().parents[4]
COVERAGE_DIR = ROOT / "src" / "HolSmt" / "tools" / "coverage"
DATA_PATH = COVERAGE_DIR / "smtlib_coverage.json"
MANIFEST_PATH = COVERAGE_DIR / "coverage_manifest.json"
DEFAULT_PROOF_REPORT = (
    ROOT / "src" / "HolSmt" / "tools" / "proof-corpus" / "supported_versions" / "summary.json"
)
REPORT_PATH = COVERAGE_DIR / "SMTLIB_COVERAGE.md"

STATUS_COLUMNS = ("parsed", "translated", "solved", "reconstructed", "tested")
SECTIONS = (
    ("version_targets", "Version Targets"),
    ("commands", "SMT-LIB Commands"),
    ("theories", "Theories"),
    ("logics", "Logics"),
    ("z3_proof_rules", "Z3 Proof Rules"),
    ("selftest_categories", "Current HolSmt Selftest Categories"),
    ("soundness_audit", "Soundness Audit and Semantic Mismatches"),
)

OFFICIAL_SMTLIB_27_COMMANDS = {
    "assert",
    "check-sat",
    "check-sat-assuming",
    "declare-const",
    "declare-datatype",
    "declare-datatypes",
    "declare-fun",
    "declare-sort",
    "define-const",
    "define-fun",
    "define-fun-rec",
    "define-funs-rec",
    "define-sort",
    "echo",
    "exit",
    "get-assertions",
    "get-assignment",
    "get-info",
    "get-model",
    "get-option",
    "get-proof",
    "get-unsat-assumptions",
    "get-unsat-core",
    "get-value",
    "pop",
    "push",
    "reset",
    "reset-assertions",
    "set-info",
    "set-logic",
    "set-option",
}
EXECUTABLE_EVIDENCE_KINDS = {
    "conformance_result",
    "proof_rule",
    "proof_version",
    "source",
}


class CoverageGenerationError(ValueError):
    pass


def load_data() -> dict:
    with DATA_PATH.open(encoding="utf-8") as stream:
        return json.load(stream)


def load_json(path: Path) -> object:
    with path.open(encoding="utf-8") as stream:
        return json.load(stream)


def row_key(section_name: str, row: dict) -> tuple[str, str, str]:
    return section_name, str(row["item"]), str(row["class"])


def evidence_id(evidence: dict[str, object]) -> str:
    kind = str(evidence.get("kind", ""))
    if kind == "source":
        path = str(evidence.get("path", ""))
        match = evidence.get("match")
        return f"source:{path}" + (f"#{match}" if isinstance(match, str) and match else "")
    if kind == "conformance_result":
        parts = [
            str(evidence.get("logic", "*")),
            str(evidence.get("mode", "*")),
            str(evidence.get("status", "*")),
        ]
        return "conformance_result:" + ":".join(parts)
    if kind == "proof_rule":
        rule = str(evidence.get("rule", ""))
        version = evidence.get("version")
        return f"proof_rule:{rule}" + (f"@{version}" if isinstance(version, str) and version else "")
    if kind == "proof_version":
        return f"proof_version:{evidence.get('version', '')}"
    if kind == "manual":
        return f"manual:{evidence.get('description', '')}"
    return kind


def unique(values: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for value in values:
        if value in seen:
            continue
        seen.add(value)
        result.append(value)
    return result


def executable_ids(evidence_items: object) -> list[str]:
    if not isinstance(evidence_items, list):
        return []
    return [
        evidence_id(evidence)
        for evidence in evidence_items
        if isinstance(evidence, dict)
        and str(evidence.get("kind")) in EXECUTABLE_EVIDENCE_KINDS
    ]


def has_executable_evidence(entry: dict[str, object], field: str) -> bool:
    return bool(executable_ids(entry.get(field)))


def entries_for_phase(
    entries: list[dict[str, object]], phase: str, expected_status: str
) -> list[dict[str, object]]:
    return [
        entry
        for entry in entries
        if expected_status == entry.get("expected_status")
        and phase in entry.get("phases", [])
    ]


def verify_manifest_evidence(
    manifest_entries: list[dict[str, object]],
    conformance_reports: list[object],
    proof_reports: list[object],
    root: Path = ROOT,
) -> None:
    errors: list[str] = []
    for entry in manifest_entries:
        label = (
            f"{entry['section']}/{entry['item']} "
            f"({entry['class']})"
        )
        for field in ("positive_tests", "negative_tests", "artifacts"):
            evidence_items = entry[field]
            assert isinstance(evidence_items, list)
            for evidence in evidence_items:
                assert isinstance(evidence, dict)
                error = audit_coverage_manifest.check_evidence(
                    evidence,
                    conformance_reports,
                    proof_reports,
                    root,
                )
                if error is not None:
                    errors.append(f"{label} {field} {evidence_id(evidence)}: {error}")
    if errors:
        raise CoverageGenerationError(
            "invalid coverage manifest evidence:\n- " + "\n- ".join(errors)
        )


def enrich_rows_with_manifest_evidence(
    data: dict,
    manifest: dict,
    conformance_reports: list[object],
    proof_reports: list[object],
) -> dict:
    entries = audit_coverage_manifest.validate_manifest(manifest, data)
    verify_manifest_evidence(entries, conformance_reports, proof_reports)

    by_row: dict[tuple[str, str, str], list[dict[str, object]]] = {}
    for entry in entries:
        key = (str(entry["section"]), str(entry["item"]), str(entry["class"]))
        by_row.setdefault(key, []).append(entry)

    for section_name, _ in SECTIONS:
        for row in data.get(section_name, []):
            key = row_key(section_name, row)
            row_entries = by_row.get(key, [])
            test_ids = unique(
                evidence_id(evidence)
                for entry in row_entries
                for evidence in entry.get("positive_tests", [])
                if isinstance(evidence, dict)
                and str(evidence.get("kind")) in EXECUTABLE_EVIDENCE_KINDS
            )
            diagnostic_test_ids = unique(
                evidence_id(evidence)
                for entry in row_entries
                if entry.get("expected_status") == "unsupported_diagnostic"
                for evidence in entry.get("negative_tests", [])
                if isinstance(evidence, dict)
                and str(evidence.get("kind")) in EXECUTABLE_EVIDENCE_KINDS
            )
            row["test_ids"] = test_ids
            row["last_verified_by"] = "coverage_manifest.json" if row_entries else "unverified"
            row["diagnostic_test_ids"] = diagnostic_test_ids

    return data


def validate(data: dict, manifest: dict | None = None, release: bool = False) -> None:
    statuses = set(data["status_legend"])
    source_classes = set(data["source_classes"])
    missing_sections = [name for name, _ in SECTIONS if name not in data]
    if missing_sections:
        raise SystemExit(f"missing section(s): {', '.join(missing_sections)}")

    seen_statuses = set()
    for section_name, _ in SECTIONS:
      rows = data[section_name]
      if not rows:
          raise SystemExit(f"section {section_name} has no rows")
      for index, row in enumerate(rows, 1):
          item = row.get("item")
          if not item:
              raise SystemExit(f"{section_name} row {index} is missing item")
          row_class = row.get("class")
          if row_class not in source_classes:
              raise SystemExit(
                  f"{section_name} row {item!r} has invalid class {row_class!r}"
              )
          for column in STATUS_COLUMNS:
              value = row.get(column)
              if value not in statuses:
                  raise SystemExit(
                      f"{section_name} row {item!r} has invalid {column}: {value!r}"
                  )
              seen_statuses.add(value)
          if "test_ids" not in row:
              raise SystemExit(f"{section_name} row {item!r} is missing test_ids")
          if "last_verified_by" not in row:
              raise SystemExit(f"{section_name} row {item!r} is missing last_verified_by")
          if "diagnostic_test_ids" not in row:
              raise SystemExit(
                  f"{section_name} row {item!r} is missing diagnostic_test_ids"
              )

    if release:
        validate_release_unknowns(data)

    required_statuses = {"implemented", "unsupported_diagnostic", "untested"}
    if not release:
        required_statuses.add("unknown")
    missing_statuses = sorted(required_statuses - seen_statuses)
    if missing_statuses:
        raise SystemExit(
            "matrix does not exercise required status value(s): "
            + ", ".join(missing_statuses)
        )

    for required_section in ("commands", "theories", "logics", "z3_proof_rules"):
        classes = {row["class"] for row in data[required_section]}
        if not {"SMT-LIB 2.7", "SMT-LIB 3", "Z3 extension"} & classes:
            raise SystemExit(f"{required_section} does not record a source class")

    covered_commands = set()
    for row in data["commands"]:
        if row["class"] != "SMT-LIB 2.7":
            continue
        commands = row.get("commands")
        if commands is None:
            commands = [part.strip() for part in row["item"].split(",")]
        for command in commands:
            if command:
                covered_commands.add(command)
    missing_commands = sorted(OFFICIAL_SMTLIB_27_COMMANDS - covered_commands)
    extra_commands = sorted(covered_commands - OFFICIAL_SMTLIB_27_COMMANDS)
    if missing_commands:
        raise SystemExit(
            "SMT-LIB 2.7 command matrix is missing command(s): "
            + ", ".join(missing_commands)
        )
    if extra_commands:
        raise SystemExit(
            "SMT-LIB 2.7 command matrix contains unrecognized command(s): "
            + ", ".join(extra_commands)
        )

    if manifest is not None:
        validate_claim_discipline(data, manifest)


def validate_release_unknowns(data: dict) -> None:
    for section_name, _ in SECTIONS:
        for row in data.get(section_name, []):
            if any(row.get(column) == "unknown" for column in STATUS_COLUMNS):
                raise SystemExit(
                    f"{section_name} row {row.get('item')!r} contains unknown status in release mode"
                )


def validate_claim_discipline(data: dict, manifest: dict) -> None:
    entries = audit_coverage_manifest.validate_manifest(manifest, data)
    by_row: dict[tuple[str, str, str], list[dict[str, object]]] = {}
    for entry in entries:
        key = (str(entry["section"]), str(entry["item"]), str(entry["class"]))
        by_row.setdefault(key, []).append(entry)

    errors: list[str] = []
    for section_name, _ in SECTIONS:
        for row in data.get(section_name, []):
            key = row_key(section_name, row)
            row_entries = by_row.get(key, [])
            label = f"{section_name}/{row['item']} ({row['class']})"

            if row.get("tested") == "implemented":
                for phase in STATUS_COLUMNS:
                    if row.get(phase) != "implemented":
                        continue
                    evidence_entries = entries_for_phase(row_entries, phase, "implemented")
                    if not any(
                        has_executable_evidence(entry, "positive_tests")
                        for entry in evidence_entries
                    ):
                        errors.append(
                            f"{label} {phase}=implemented is tested but has no "
                            "manifest-backed executable positive evidence"
                        )

            for phase in STATUS_COLUMNS:
                if row.get(phase) != "unsupported_diagnostic":
                    continue
                evidence_entries = entries_for_phase(
                    row_entries, phase, "unsupported_diagnostic"
                )
                if not any(
                    has_executable_evidence(entry, "negative_tests")
                    for entry in evidence_entries
                ):
                    errors.append(
                        f"{label} {phase}=unsupported_diagnostic has no "
                        "manifest-backed executable diagnostic evidence"
                    )

            if any(row.get(phase) == "unsupported_diagnostic" for phase in STATUS_COLUMNS):
                diagnostic_ids = row.get("diagnostic_test_ids")
                if not isinstance(diagnostic_ids, list) or not diagnostic_ids:
                    errors.append(f"{label} has unsupported status but no diagnostic_test_ids")

    if errors:
        raise SystemExit(
            "coverage claims are not backed by executable manifest evidence:\n- "
            + "\n- ".join(errors)
        )


def cell(text: object) -> str:
    value = str(text)
    return value.replace("|", "\\|").replace("\n", "<br>")


def status(value: str) -> str:
    return value.replace("_", " ")


def table(headers: Iterable[str], rows: Iterable[Iterable[object]]) -> list[str]:
    headers = list(headers)
    lines = [
        "| " + " | ".join(cell(header) for header in headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(cell(value) for value in row) + " |")
    return lines


def row_values(row: dict) -> list[str]:
    return [
        row["item"],
        row["class"],
        *[status(row[column]) for column in STATUS_COLUMNS],
        "<br>".join(row.get("test_ids", [])),
        "<br>".join(row.get("diagnostic_test_ids", [])),
        row.get("last_verified_by", ""),
        row.get("evidence", ""),
        row.get("notes", ""),
    ]


def render(data: dict) -> str:
    metadata = data["metadata"]
    lines: list[str] = [
        f"# {metadata['title']}",
        "",
        "<!-- Generated by python3 src/HolSmt/tools/coverage/generate_smtlib_coverage.py; do not edit by hand. -->",
        "",
        f"- Target SMT-LIB version: {metadata['smtlib_target']}",
        f"- Last reviewed: {metadata['last_reviewed']}",
        f"- Regenerate with: `{metadata['generator']}`",
        "",
        metadata["scope_note"],
        "",
        "## Status Legend",
        "",
    ]
    lines.extend(
        table(
            ("Status", "Meaning"),
            (
                (status_name.replace("_", " "), meaning)
                for status_name, meaning in data["status_legend"].items()
            ),
        )
    )
    lines.extend(["", "## Source Classes", ""])
    lines.extend(table(("Class", "Meaning"), data["source_classes"].items()))

    headers = (
        "Item",
        "Class",
        "Parsed",
        "Translated",
        "Solved",
        "Reconstructed",
        "Tested",
        "Test IDs",
        "Diagnostic Test IDs",
        "Last Verified By",
        "Evidence",
        "Notes",
    )
    for section_name, title in SECTIONS:
        lines.extend(["", f"## {title}", ""])
        lines.extend(table(headers, (row_values(row) for row in data[section_name])))

    lines.append("")
    return "\n".join(lines)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the checked-in HolSmt SMT-LIB coverage report."
    )
    parser.add_argument("--coverage", type=Path, default=DATA_PATH)
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--report", type=Path, default=REPORT_PATH)
    parser.add_argument("--conformance-report", action="append", type=Path, default=[])
    parser.add_argument("--proof-report", action="append", type=Path, default=[DEFAULT_PROOF_REPORT])
    parser.add_argument(
        "--release",
        "--ci",
        dest="release",
        action="store_true",
        help="fail generation when any coverage row still contains unknown status",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        data = load_json(args.coverage)
        manifest = load_json(args.manifest)
        if not isinstance(data, dict):
            raise CoverageGenerationError("coverage JSON root must be an object")
        if not isinstance(manifest, dict):
            raise CoverageGenerationError("manifest JSON root must be an object")
        conformance_reports = [load_json(path) for path in args.conformance_report]
        proof_reports = [load_json(path) for path in args.proof_report]
        data = enrich_rows_with_manifest_evidence(
            data,
            manifest,
            conformance_reports,
            proof_reports,
        )
        validate(data, manifest, release=args.release)
        args.coverage.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        args.report.write_text(render(data), encoding="utf-8")
    except (
        OSError,
        json.JSONDecodeError,
        audit_coverage_manifest.ManifestError,
        CoverageGenerationError,
        SystemExit,
    ) as exc:
        print(f"coverage generation failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
