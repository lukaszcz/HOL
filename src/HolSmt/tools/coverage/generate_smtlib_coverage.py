#!/usr/bin/env python3
"""Generate the checked-in HolSmt SMT-LIB coverage report."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[4]
COVERAGE_DIR = ROOT / "src" / "HolSmt" / "tools" / "coverage"
DATA_PATH = COVERAGE_DIR / "smtlib_coverage.json"
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


def load_data() -> dict:
    with DATA_PATH.open(encoding="utf-8") as stream:
        return json.load(stream)


def validate(data: dict) -> None:
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

    required_statuses = {"implemented", "unsupported_diagnostic", "untested", "unknown"}
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
        "Evidence",
        "Notes",
    )
    for section_name, title in SECTIONS:
        lines.extend(["", f"## {title}", ""])
        lines.extend(table(headers, (row_values(row) for row in data[section_name])))

    lines.append("")
    return "\n".join(lines)


def main() -> None:
    data = load_data()
    validate(data)
    REPORT_PATH.write_text(render(data), encoding="utf-8")


if __name__ == "__main__":
    main()
