#!/usr/bin/env python3
"""Audit the HolSmt SMT-LIB complete conformance corpus foundation."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[3]
TOOLS_DIR = ROOT / "src" / "HolSmt" / "tools"
DEFAULT_MANIFEST = TOOLS_DIR / "conformance-corpus" / "v2" / "manifest.json"
DEFAULT_LOGIC_SOURCE = ROOT / "src" / "HolSmt" / "SmtLib_Logics.sml"
DEFAULT_COVERAGE = TOOLS_DIR / "coverage" / "smtlib_coverage.json"
DEFAULT_COVERAGE_MANIFEST = TOOLS_DIR / "coverage" / "coverage_manifest.json"

SCHEMA = "holsmt-complete-conformance-audit-v1"
MANIFEST_SCHEMA_VERSION = "2"
STATUS_COLUMNS = ("parsed", "translated", "solved", "reconstructed", "tested")
V2_MODES = {
    "parser-only",
    "typecheck-only",
    "z3-oracle",
    "proof-parse",
    "proof-replay",
    "z3-tac",
}
V2_STATUSES = {"pass", "fail", "red"}
UNSAT_REQUIRED_MODES = {"proof-parse", "proof-replay", "z3-tac"}
COMPLETE_REQUIRED_CLASSES = {"SMT-LIB 2.7", "Z3 extension"}
WEAK_COVERAGE_STATUSES = {
    "parse_only",
    "unsupported",
    "unsupported_diagnostic",
    "not_applicable",
}
UNRESOLVED_COVERAGE_STATUSES = {"unknown", "untested"}


class AuditError(ValueError):
    pass


@dataclass(frozen=True)
class Issue:
    code: str
    category: str
    subject: str
    message: str
    severity: str = "error"
    details: dict[str, object] = field(default_factory=dict)

    def to_json(self) -> dict[str, object]:
        result: dict[str, object] = {
            "code": self.code,
            "category": self.category,
            "severity": self.severity,
            "subject": self.subject,
            "message": self.message,
        }
        if self.details:
            result["details"] = self.details
        return result

    def render(self) -> str:
        return f"{self.code}: {self.subject}: {self.message}"


@dataclass
class CoverageRow:
    section: str
    item: str
    row_class: str
    statuses: set[str] = field(default_factory=set)
    positive_evidence: int = 0
    diagnostic_evidence: int = 0
    complete_required: bool = False

    @property
    def key(self) -> tuple[str, str, str]:
        return self.section, self.item, self.row_class


def load_json(path: Path) -> object:
    with path.open(encoding="utf-8") as infile:
        return json.load(infile)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def require_string(value: object, label: str, *, allow_empty: bool = False) -> str:
    require(isinstance(value, str), f"{label} must be a string")
    if not allow_empty:
        require(bool(value), f"{label} must not be empty")
    return value


def require_string_list(value: object, label: str, *, min_items: int = 0) -> list[str]:
    require(isinstance(value, list), f"{label} must be a list")
    require(len(value) >= min_items, f"{label} must have at least {min_items} item(s)")
    require(len(set(value)) == len(value), f"{label} must contain unique items")
    for index, item in enumerate(value, 1):
        require_string(item, f"{label}[{index}]")
    return list(value)


def validate_implementation_obligation(value: object, label: str) -> None:
    require(isinstance(value, dict), f"{label} must be an object")
    allowed = {"files", "feature", "test_ids", "failure_phase", "notes"}
    extra = sorted(set(value) - allowed)
    require(not extra, f"{label} has unknown field(s): {', '.join(extra)}")
    for required in ("files", "feature", "test_ids", "failure_phase"):
        require(required in value, f"{label} is missing {required}")
    require_string_list(value["files"], f"{label}.files", min_items=1)
    require_string(value["feature"], f"{label}.feature")
    require_string_list(value["test_ids"], f"{label}.test_ids", min_items=1)
    require(
        value["failure_phase"]
        in {
            "parser",
            "typecheck",
            "translation",
            "solver",
            "proof-parse",
            "proof-replay",
            "theorem-shape",
            "oracle-tag",
            "version-drift",
        },
        f"{label}.failure_phase is invalid",
    )
    if "notes" in value:
        require_string(value["notes"], f"{label}.notes", allow_empty=True)


def validate_expected_result(value: object, label: str) -> str:
    require(isinstance(value, dict), f"{label} must be an object")
    allowed = {"status", "diagnostic", "theorem_shape", "proof_rule_histogram", "notes"}
    extra = sorted(set(value) - allowed)
    require(not extra, f"{label} has unknown field(s): {', '.join(extra)}")
    require("status" in value, f"{label} is missing status")
    status = value["status"]
    require(status in V2_STATUSES, f"{label}.status must be one of {sorted(V2_STATUSES)}")
    for string_field in ("diagnostic", "theorem_shape", "notes"):
        if string_field in value:
            require_string(value[string_field], f"{label}.{string_field}", allow_empty=string_field == "notes")
    if "proof_rule_histogram" in value:
        histogram = value["proof_rule_histogram"]
        require(isinstance(histogram, dict), f"{label}.proof_rule_histogram must be an object")
        for rule, count in histogram.items():
            require_string(rule, f"{label}.proof_rule_histogram key")
            require(isinstance(count, int) and count >= 0, f"{label}.proof_rule_histogram[{rule!r}] must be a non-negative integer")
    return str(status)


def validate_source(value: object, label: str) -> None:
    require(isinstance(value, dict), f"{label} must be an object")
    allowed = {"kind", "reference", "url", "notes"}
    extra = sorted(set(value) - allowed)
    require(not extra, f"{label} has unknown field(s): {', '.join(extra)}")
    require("kind" in value, f"{label} is missing kind")
    require("reference" in value, f"{label} is missing reference")
    require(
        value["kind"]
        in {
            "SMT-LIB-standard",
            "SMT-LIB-theory",
            "SMT-LIB-logic",
            "Z3-extension",
            "Z3-proof",
            "external-benchmark",
            "HolSmt-internal",
        },
        f"{label}.kind is invalid",
    )
    require_string(value["reference"], f"{label}.reference")
    for string_field in ("url", "notes"):
        if string_field in value:
            require_string(value[string_field], f"{label}.{string_field}", allow_empty=string_field == "notes")


def validate_case(case: object, index: int) -> dict[str, object]:
    label = f"manifest case {index}"
    require(isinstance(case, dict), f"{label} must be an object")
    required = {
        "id",
        "file",
        "logic",
        "standard",
        "class",
        "features",
        "modes",
        "versions",
        "expected",
        "implementation_obligation",
        "source",
    }
    extra = sorted(set(case) - required)
    missing = sorted(required - set(case))
    require(not extra, f"{label} has unknown field(s): {', '.join(extra)}")
    require(not missing, f"{label} is missing required field(s): {', '.join(missing)}")

    case_id = require_string(case["id"], f"{label}.id")
    require(
        re.match(r"^[A-Za-z0-9][A-Za-z0-9_.:-]*$", case_id) is not None,
        f"{label}.id has invalid syntax",
    )
    filename = require_string(case["file"], f"{label}.file")
    require(
        re.match(r"^cases/(commands|theories|logics|proof_rules|soundness|external)/[^/].*[.]smt2$", filename)
        is not None,
        f"{label}.file has invalid path",
    )
    require_string(case["logic"], f"{label}.logic")
    require(case["standard"] in {"SMT-LIB-2.7", "SMT-LIB-3", "Z3-extension"}, f"{label}.standard is invalid")
    require(
        case["class"]
        in {
            "command",
            "theory",
            "logic",
            "proof-rule",
            "soundness-audit",
            "external-benchmark",
        },
        f"{label}.class is invalid",
    )
    require_string_list(case["features"], f"{label}.features", min_items=1)
    modes = require_string_list(case["modes"], f"{label}.modes", min_items=1)
    invalid_modes = sorted(set(modes) - V2_MODES)
    require(not invalid_modes, f"{label}.modes has invalid mode(s): {', '.join(invalid_modes)}")
    require_string_list(case["versions"], f"{label}.versions", min_items=1)

    expected = case["expected"]
    require(isinstance(expected, dict), f"{label}.expected must be an object")
    require(bool(expected), f"{label}.expected must not be empty")
    invalid_expected_modes = sorted(set(expected) - V2_MODES)
    require(
        not invalid_expected_modes,
        f"{label}.expected has invalid mode(s): {', '.join(invalid_expected_modes)}",
    )
    for mode, result in expected.items():
        validate_expected_result(result, f"{label}.expected[{mode}]")

    red_modes = [
        mode
        for mode, result in expected.items()
        if isinstance(result, dict) and result.get("status") == "red"
    ]
    obligation = case["implementation_obligation"]
    if red_modes:
        validate_implementation_obligation(
            obligation,
            f"{label}.implementation_obligation for red mode(s) {', '.join(red_modes)}",
        )
    elif obligation is not None:
        raise AuditError(f"{label}.implementation_obligation must be null when no expected row is red")
    validate_source(case["source"], f"{label}.source")
    return case


def validate_v2_manifest(manifest: object) -> list[dict[str, object]]:
    require(isinstance(manifest, dict), "v2 manifest root must be an object")
    extra = sorted(set(manifest) - {"schema_version", "cases"})
    require(not extra, f"v2 manifest has unknown field(s): {', '.join(extra)}")
    require(manifest.get("schema_version") == MANIFEST_SCHEMA_VERSION, "v2 manifest schema_version must be 2")
    cases = manifest.get("cases")
    require(isinstance(cases, list), "v2 manifest cases must be a list")
    validated = [validate_case(case, index) for index, case in enumerate(cases, 1)]
    ids = [str(case["id"]) for case in validated]
    duplicates = sorted({case_id for case_id in ids if ids.count(case_id) > 1})
    require(not duplicates, f"v2 manifest has duplicate case id(s): {', '.join(duplicates)}")
    return validated


def parse_accepted_logics(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    match = re.search(
        r"fun\s+parsedicts_of_logic\s*\([^)]*\)\s*=\s*case\s+logic\s+of(?P<body>.*?)"
        r"\n\s*\(\*\s*returns the symbol metadata",
        text,
        flags=re.DOTALL,
    )
    if match is None:
        raise AuditError(f"could not find parsedicts_of_logic case expression in {path}")
    logics = re.findall(r'"([A-Z][A-Z0-9_]*)"\s*=>', match.group("body"))
    require(bool(logics), f"no accepted logic names found in {path}")
    return sorted(set(logics))


def case_expected_statuses(case: dict[str, object]) -> set[str]:
    expected = case.get("expected")
    if not isinstance(expected, dict):
        return set()
    return {
        str(result.get("status"))
        for result in expected.values()
        if isinstance(result, dict) and isinstance(result.get("status"), str)
    }


def is_case_complete_evidence(case: dict[str, object]) -> bool:
    return "pass" in case_expected_statuses(case) and "red" not in case_expected_statuses(case)


def is_unsat_case(case: dict[str, object]) -> bool:
    case_id = str(case.get("id", "")).lower()
    features = [str(feature).lower() for feature in case.get("features", []) if isinstance(feature, str)]
    if "unsat" in case_id or any(feature == "unsat" or feature.endswith(":unsat") for feature in features):
        return True
    if any("proof" in str(mode) for mode in case.get("modes", [])):
        return True
    expected = case.get("expected")
    if isinstance(expected, dict):
        for result in expected.values():
            if isinstance(result, dict) and (
                "proof_rule_histogram" in result or "theorem_shape" in result
            ):
                return True
    return False


def add_coverage_row(rows: dict[tuple[str, str, str], CoverageRow], row: CoverageRow) -> None:
    existing = rows.setdefault(row.key, CoverageRow(row.section, row.item, row.row_class))
    existing.statuses.update(row.statuses)
    existing.positive_evidence += row.positive_evidence
    existing.diagnostic_evidence += row.diagnostic_evidence
    existing.complete_required = existing.complete_required or row.complete_required


def rows_from_coverage_json(data: object) -> list[CoverageRow]:
    require(isinstance(data, dict), "coverage JSON root must be an object")
    rows: list[CoverageRow] = []
    for section, value in data.items():
        if section in {"metadata", "status_legend", "source_classes"} or not isinstance(value, list):
            continue
        for index, item in enumerate(value, 1):
            require(isinstance(item, dict), f"coverage section {section} row {index} must be an object")
            name = require_string(item.get("item"), f"coverage section {section} row {index}.item")
            row_class = require_string(item.get("class"), f"coverage section {section} row {index}.class")
            statuses = {str(item[phase]) for phase in STATUS_COLUMNS if isinstance(item.get(phase), str)}
            test_ids = item.get("test_ids")
            diagnostic_ids = item.get("diagnostic_test_ids")
            rows.append(
                CoverageRow(
                    section=section,
                    item=name,
                    row_class=row_class,
                    statuses=statuses,
                    positive_evidence=len(test_ids) if isinstance(test_ids, list) else 0,
                    diagnostic_evidence=len(diagnostic_ids) if isinstance(diagnostic_ids, list) else 0,
                    complete_required=row_class in COMPLETE_REQUIRED_CLASSES,
                )
            )
    return rows


def rows_from_coverage_manifest(data: object) -> list[CoverageRow]:
    require(isinstance(data, dict), "coverage manifest root must be an object")
    entries = data.get("entries")
    require(isinstance(entries, list), "coverage manifest entries must be a list")
    rows: list[CoverageRow] = []
    for index, entry in enumerate(entries, 1):
        require(isinstance(entry, dict), f"coverage manifest entry {index} must be an object")
        section = require_string(entry.get("section"), f"coverage manifest entry {index}.section")
        item = require_string(entry.get("item"), f"coverage manifest entry {index}.item")
        row_class = require_string(entry.get("class"), f"coverage manifest entry {index}.class")
        status = require_string(entry.get("expected_status"), f"coverage manifest entry {index}.expected_status")
        positive = entry.get("positive_tests")
        negative = entry.get("negative_tests")
        artifacts = entry.get("artifacts")
        artifact_count = len(artifacts) if isinstance(artifacts, list) else 0
        weak_artifact_count = artifact_count if status in WEAK_COVERAGE_STATUSES else 0
        rows.append(
            CoverageRow(
                section=section,
                item=item,
                row_class=row_class,
                statuses={status},
                positive_evidence=len(positive) if isinstance(positive, list) else 0,
                diagnostic_evidence=(len(negative) if isinstance(negative, list) else 0)
                + weak_artifact_count,
                complete_required=row_class in COMPLETE_REQUIRED_CLASSES,
            )
        )
    return rows


def load_coverage_rows(coverage_path: Path | None, coverage_manifest_path: Path | None) -> list[CoverageRow]:
    rows: list[CoverageRow] = []
    if coverage_path is not None and coverage_path.exists():
        rows.extend(rows_from_coverage_json(load_json(coverage_path)))
    if coverage_manifest_path is not None and coverage_manifest_path.exists():
        rows.extend(rows_from_coverage_manifest(load_json(coverage_manifest_path)))
    return rows


def normalized_feature_tokens(case: dict[str, object]) -> set[str]:
    tokens = {str(case.get("id", "")).lower(), str(case.get("logic", "")).lower()}
    for feature in case.get("features", []):
        if isinstance(feature, str):
            lowered = feature.lower()
            tokens.add(lowered)
            tokens.update(part for part in re.split(r"[^a-z0-9_+-]+", lowered) if part)
    return tokens


def row_has_v2_evidence(row: CoverageRow, cases: Iterable[dict[str, object]]) -> bool:
    item = row.item.lower()
    for case in cases:
        if not is_case_complete_evidence(case):
            continue
        tokens = normalized_feature_tokens(case)
        if item in tokens or item.replace(" ", "-") in tokens:
            return True
    return False


def audit_cases(cases: list[dict[str, object]], accepted_logics: list[str]) -> list[Issue]:
    issues: list[Issue] = []
    logic_cases: dict[str, list[dict[str, object]]] = {}
    for case in cases:
        if case.get("class") == "logic":
            logic_cases.setdefault(str(case["logic"]), []).append(case)

    for logic in accepted_logics:
        if logic not in logic_cases:
            issues.append(
                Issue(
                    code="missing_logic_evidence",
                    category="missing_complete_evidence",
                    subject=f"logic/{logic}",
                    message="accepted logic has no v2 manifest logic evidence",
                    details={"logic": logic},
                )
            )

    for case in cases:
        case_id = str(case["id"])
        if is_unsat_case(case):
            modes = set(str(mode) for mode in case["modes"])
            expected_modes = set(str(mode) for mode in case["expected"])
            missing = sorted(UNSAT_REQUIRED_MODES - modes)
            missing_expected = sorted(UNSAT_REQUIRED_MODES - expected_modes)
            if missing or missing_expected:
                issues.append(
                    Issue(
                        code="missing_unsat_proof_mode",
                        category="missing_complete_evidence",
                        subject=f"case/{case_id}",
                        message="unsat case lacks required proof-parse, proof-replay, or z3-tac evidence",
                        details={
                            "missing_modes": missing,
                            "missing_expected": missing_expected,
                        },
                    )
                )

        for mode, result in case["expected"].items():
            if isinstance(result, dict) and result.get("status") == "red":
                obligation = case.get("implementation_obligation")
                assert isinstance(obligation, dict)
                issues.append(
                    Issue(
                        code="red_implementation_obligation",
                        category="implementation_obligation",
                        subject=f"case/{case_id}:{mode}",
                        message=f"red expected row requires implementation work for {obligation['feature']}",
                        details={
                            "failure_phase": obligation["failure_phase"],
                            "files": obligation["files"],
                            "test_ids": obligation["test_ids"],
                        },
                    )
                )
    return issues


def audit_coverage(rows: list[CoverageRow], cases: list[dict[str, object]]) -> list[Issue]:
    combined: dict[tuple[str, str, str], CoverageRow] = {}
    for row in rows:
        add_coverage_row(combined, row)

    issues: list[Issue] = []
    for row in sorted(combined.values(), key=lambda item: item.key):
        if not row.complete_required:
            continue
        statuses = row.statuses
        if statuses & UNRESOLVED_COVERAGE_STATUSES:
            issues.append(
                Issue(
                    code="unresolved_complete_required_row",
                    category="missing_complete_evidence",
                    subject=f"{row.section}/{row.item} ({row.row_class})",
                    message="complete-required coverage row still has unknown or untested status",
                    details={"statuses": sorted(statuses)},
                )
            )
            continue
        if row_has_v2_evidence(row, cases):
            continue
        if statuses and statuses <= WEAK_COVERAGE_STATUSES:
            issues.append(
                Issue(
                    code="weak_complete_required_evidence",
                    category="missing_complete_evidence",
                    subject=f"{row.section}/{row.item} ({row.row_class})",
                    message="complete-required row is backed only by parse-only, unsupported, not-applicable, or diagnostic evidence",
                    details={"statuses": sorted(statuses)},
                )
            )
        elif row.positive_evidence == 0 and row.diagnostic_evidence > 0:
            issues.append(
                Issue(
                    code="diagnostic_only_complete_required_evidence",
                    category="missing_complete_evidence",
                    subject=f"{row.section}/{row.item} ({row.row_class})",
                    message="complete-required row has diagnostic evidence but no positive complete evidence",
                    details={"statuses": sorted(statuses)},
                )
            )
    return issues


def build_report(
    *,
    manifest_path: Path,
    logic_source: Path,
    coverage_path: Path | None,
    coverage_manifest_path: Path | None,
) -> dict[str, object]:
    manifest = load_json(manifest_path)
    cases = validate_v2_manifest(manifest)
    accepted_logics = parse_accepted_logics(logic_source)
    coverage_rows = load_coverage_rows(coverage_path, coverage_manifest_path)
    issues = audit_cases(cases, accepted_logics)
    issues.extend(audit_coverage(coverage_rows, cases))

    category_counts: dict[str, int] = {}
    for issue in issues:
        category_counts[issue.category] = category_counts.get(issue.category, 0) + 1

    return {
        "schema": SCHEMA,
        "inputs": {
            "manifest": str(manifest_path),
            "logic_source": str(logic_source),
            "coverage": str(coverage_path) if coverage_path is not None else None,
            "coverage_manifest": str(coverage_manifest_path) if coverage_manifest_path is not None else None,
        },
        "summary": {
            "accepted_logic_count": len(accepted_logics),
            "v2_case_count": len(cases),
            "coverage_row_count": len({row.key for row in coverage_rows}),
            "issue_count": len(issues),
            "category_counts": category_counts,
            "passed": not issues,
        },
        "accepted_logics": accepted_logics,
        "issues": [issue.to_json() for issue in issues],
    }


def print_text_summary(report: dict[str, object]) -> None:
    summary = report["summary"]
    assert isinstance(summary, dict)
    print("complete conformance audit")
    print(f"accepted logics: {summary['accepted_logic_count']}")
    print(f"v2 cases: {summary['v2_case_count']}")
    print(f"coverage rows: {summary['coverage_row_count']}")
    print(f"issues: {summary['issue_count']}")
    category_counts = summary.get("category_counts")
    if isinstance(category_counts, dict) and category_counts:
        counts = ", ".join(f"{name}={count}" for name, count in sorted(category_counts.items()))
        print(f"categories: {counts}")
    issues = report.get("issues")
    if isinstance(issues, list) and issues:
        for issue in issues[:25]:
            if isinstance(issue, dict):
                print(f"- {issue['code']}: {issue['subject']}: {issue['message']}")
        if len(issues) > 25:
            print(f"- ... {len(issues) - 25} more issue(s)")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Audit the HolSmt SMT-LIB v2 complete conformance corpus foundation."
    )
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--logic-source", type=Path, default=DEFAULT_LOGIC_SOURCE)
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--coverage-manifest", type=Path, default=DEFAULT_COVERAGE_MANIFEST)
    parser.add_argument(
        "--no-coverage",
        action="store_true",
        help="skip coverage JSON and coverage manifest checks",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="write either a concise text summary or machine-readable JSON to stdout",
    )
    parser.add_argument("--json-output", type=Path, help="also write the machine-readable JSON report")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    coverage_path = None if args.no_coverage else args.coverage
    coverage_manifest_path = None if args.no_coverage else args.coverage_manifest
    try:
        report = build_report(
            manifest_path=args.manifest,
            logic_source=args.logic_source,
            coverage_path=coverage_path,
            coverage_manifest_path=coverage_manifest_path,
        )
    except (OSError, json.JSONDecodeError, AuditError) as exc:
        print(f"complete conformance audit infrastructure error: {exc}", file=sys.stderr)
        return 2

    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        with args.json_output.open("w", encoding="utf-8") as outfile:
            json.dump(report, outfile, indent=2, sort_keys=True)
            outfile.write("\n")

    if args.format == "json":
        json.dump(report, sys.stdout, indent=2, sort_keys=True)
        print()
    else:
        print_text_summary(report)

    summary = report["summary"]
    assert isinstance(summary, dict)
    return 0 if summary.get("passed") else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
