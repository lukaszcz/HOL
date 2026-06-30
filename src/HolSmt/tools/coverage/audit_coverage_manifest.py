#!/usr/bin/env python3
"""Report HolSmt SMT-LIB coverage rows without executable manifest evidence."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[4]
COVERAGE_DIR = ROOT / "src" / "HolSmt" / "tools" / "coverage"
DEFAULT_COVERAGE = COVERAGE_DIR / "smtlib_coverage.json"
DEFAULT_MANIFEST = COVERAGE_DIR / "coverage_manifest.json"
DEFAULT_PROOF_REPORT = (
    ROOT / "src" / "HolSmt" / "tools" / "proof-corpus" / "supported_versions" / "summary.json"
)
SCHEMA = "holsmt-coverage-manifest-v1"
STATUS_COLUMNS = ("parsed", "translated", "solved", "reconstructed", "tested")
IGNORED_COVERAGE_KEYS = {"metadata", "status_legend", "source_classes"}
OBLIGATION_STATUSES = {
    "implemented",
    "parse_only",
    "unsupported_diagnostic",
    "untested",
    "unknown",
    "not_applicable",
}


class ManifestError(ValueError):
    pass


@dataclass(frozen=True)
class Issue:
    code: str
    section: str
    item: str
    row_class: str
    phase: str
    message: str

    def render(self) -> str:
        suffix = f" [{self.phase}]" if self.phase else ""
        return (
            f"{self.code}: {self.section}/{self.item} "
            f"({self.row_class}){suffix}: {self.message}"
        )


def load_json(path: Path) -> object:
    with path.open(encoding="utf-8") as infile:
        return json.load(infile)


def row_key(row: dict[str, object], section: str) -> tuple[str, str, str]:
    return section, str(row["item"]), str(row["class"])


def coverage_rows(data: dict[str, object]) -> dict[tuple[str, str, str], dict[str, object]]:
    rows: dict[tuple[str, str, str], dict[str, object]] = {}
    for section, value in data.items():
        if section in IGNORED_COVERAGE_KEYS:
            continue
        if not isinstance(value, list):
            continue
        for index, row in enumerate(value, 1):
            if not isinstance(row, dict):
                raise ManifestError(f"coverage section {section} row {index} is not an object")
            try:
                key = row_key(row, section)
            except KeyError as exc:
                raise ManifestError(
                    f"coverage section {section} row {index} is missing {exc.args[0]}"
                ) from exc
            if key in rows:
                raise ManifestError(
                    f"coverage row is duplicated: {section}/{key[1]} ({key[2]})"
                )
            rows[key] = row
    return rows


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ManifestError(message)


def validate_evidence_list(entry_label: str, field: str, value: object) -> None:
    require(isinstance(value, list), f"{entry_label} field {field} must be a list")
    for index, item in enumerate(value, 1):
        require(isinstance(item, dict), f"{entry_label} {field}[{index}] must be an object")
        kind = item.get("kind")
        require(isinstance(kind, str) and bool(kind), f"{entry_label} {field}[{index}] is missing kind")
        for string_field in ("path", "match", "mode", "status", "logic", "rule", "version", "description"):
            if string_field in item:
                require(
                    isinstance(item[string_field], str),
                    f"{entry_label} {field}[{index}].{string_field} must be a string",
                )


def validate_manifest(
    manifest: object, coverage_data: dict[str, object]
) -> list[dict[str, object]]:
    require(isinstance(manifest, dict), "manifest root must be an object")
    require(manifest.get("schema") == SCHEMA, f"manifest schema must be {SCHEMA}")
    entries = manifest.get("entries")
    require(isinstance(entries, list) and bool(entries), "manifest entries must be a non-empty list")

    rows = coverage_rows(coverage_data)
    statuses = set(coverage_data.get("status_legend", {}))
    classes = set(coverage_data.get("source_classes", {}))
    require(bool(statuses), "coverage status_legend must be present")
    require(bool(classes), "coverage source_classes must be present")

    seen: set[tuple[str, str, str, tuple[str, ...]]] = set()
    validated_entries: list[dict[str, object]] = []
    required = {
        "section",
        "item",
        "class",
        "phases",
        "expected_status",
        "positive_tests",
        "negative_tests",
        "z3_versions",
        "artifacts",
    }
    for index, entry in enumerate(entries, 1):
        label = f"manifest entry {index}"
        require(isinstance(entry, dict), f"{label} must be an object")
        missing = sorted(required - set(entry))
        require(not missing, f"{label} is missing required field(s): {', '.join(missing)}")

        section = entry["section"]
        item = entry["item"]
        row_class = entry["class"]
        require(isinstance(section, str) and bool(section), f"{label} section must be a string")
        require(isinstance(item, str) and bool(item), f"{label} item must be a string")
        require(isinstance(row_class, str) and bool(row_class), f"{label} class must be a string")
        require(row_class in classes, f"{label} has unknown class {row_class!r}")

        phases = entry["phases"]
        require(isinstance(phases, list) and bool(phases), f"{label} phases must be a non-empty list")
        require(
            all(isinstance(phase, str) for phase in phases),
            f"{label} phases must all be strings",
        )
        require(
            set(phases) <= set(STATUS_COLUMNS),
            f"{label} has invalid phase(s): {', '.join(sorted(set(phases) - set(STATUS_COLUMNS)))}",
        )
        require(len(set(phases)) == len(phases), f"{label} phases must be unique")

        expected_status = entry["expected_status"]
        require(
            isinstance(expected_status, str) and expected_status in statuses,
            f"{label} expected_status must be a coverage status",
        )

        z3_versions = entry["z3_versions"]
        require(isinstance(z3_versions, list), f"{label} z3_versions must be a list")
        require(
            all(isinstance(version, str) for version in z3_versions),
            f"{label} z3_versions must all be strings",
        )

        validate_evidence_list(label, "positive_tests", entry["positive_tests"])
        validate_evidence_list(label, "negative_tests", entry["negative_tests"])
        validate_evidence_list(label, "artifacts", entry["artifacts"])

        key = (section, item, row_class)
        require(key in rows, f"{label} does not match a coverage row: {section}/{item} ({row_class})")
        dup_key = (section, item, row_class, tuple(phases))
        require(dup_key not in seen, f"{label} duplicates an earlier entry for the same phases")
        seen.add(dup_key)
        validated_entries.append(entry)

    return validated_entries


def read_source_evidence(evidence: dict[str, object], root: Path) -> str | None:
    path_value = evidence.get("path")
    if not isinstance(path_value, str) or not path_value:
        return "source evidence is missing path"
    path = Path(path_value)
    if not path.is_absolute():
        path = root / path
    if not path.exists():
        return f"source path does not exist: {path_value}"
    match = evidence.get("match")
    if isinstance(match, str) and match:
        text = path.read_text(encoding="utf-8")
        if match not in text:
            return f"source path {path_value} does not contain {match!r}"
    return None


def report_sources(conformance_reports: Iterable[object], proof_reports: Iterable[object]) -> list[object]:
    sources: list[object] = []
    sources.extend(conformance_reports)
    for report in conformance_reports:
        if isinstance(report, dict) and report.get("proof_corpus_summary"):
            sources.append(report["proof_corpus_summary"])
    sources.extend(proof_reports)
    return sources


def conformance_matches(evidence: dict[str, object], reports: Iterable[object]) -> bool:
    for report in reports:
        if not isinstance(report, dict):
            continue
        results = report.get("results")
        if not isinstance(results, list):
            continue
        for result in results:
            if not isinstance(result, dict):
                continue
            for field in ("logic", "mode", "status"):
                expected = evidence.get(field)
                if isinstance(expected, str) and result.get(field) != expected:
                    break
            else:
                return True
    return False


def proof_rule_matches(evidence: dict[str, object], reports: Iterable[object]) -> bool:
    rule = evidence.get("rule")
    if not isinstance(rule, str) or not rule:
        return False
    version = evidence.get("version")
    for report in reports:
        if not isinstance(report, dict):
            continue
        discovered = report.get("discovered_rules")
        if isinstance(discovered, list) and rule in discovered and not version:
            return True
        histogram = report.get("aggregate_rule_histogram")
        if isinstance(histogram, dict) and rule in histogram and not version:
            return True
        rules_by_version = report.get("rules_by_version")
        if isinstance(rules_by_version, list):
            for item in rules_by_version:
                if not isinstance(item, dict):
                    continue
                if isinstance(version, str) and item.get("z3_version") != version:
                    continue
                rules = item.get("rules")
                if isinstance(rules, list) and rule in rules:
                    return True
        proof = report.get("proof")
        if isinstance(proof, dict):
            histogram = proof.get("rule_histogram")
            z3 = report.get("z3")
            if isinstance(version, str) and isinstance(z3, dict) and z3.get("version") != version:
                continue
            if isinstance(histogram, dict) and rule in histogram:
                return True
    return False


def proof_version_matches(version: str, reports: Iterable[object]) -> bool:
    for report in reports:
        if not isinstance(report, dict):
            continue
        versions = report.get("z3_versions")
        if isinstance(versions, list):
            for item in versions:
                if isinstance(item, dict) and item.get("version") == version:
                    return True
        z3 = report.get("z3")
        if isinstance(z3, dict) and z3.get("version") == version:
            return True
    return False


def check_evidence(
    evidence: dict[str, object],
    conformance_reports: list[object],
    proof_reports: list[object],
    root: Path,
) -> str | None:
    kind = evidence.get("kind")
    if kind == "manual":
        return None
    if kind == "source":
        return read_source_evidence(evidence, root)
    if kind == "conformance_result":
        if not conformance_reports:
            return "conformance report evidence was requested, but no conformance reports were provided"
        if not conformance_matches(evidence, conformance_reports):
            return "no supplied conformance report contains the requested result"
        return None
    if kind == "proof_rule":
        reports = report_sources(conformance_reports, proof_reports)
        if not reports:
            return "proof rule evidence was requested, but no proof or conformance reports were provided"
        if not proof_rule_matches(evidence, reports):
            return "no supplied proof report contains the requested rule"
        return None
    if kind == "proof_version":
        version = evidence.get("version")
        if not isinstance(version, str) or not version:
            return "proof_version evidence is missing version"
        reports = report_sources(conformance_reports, proof_reports)
        if not reports:
            return "Z3 version evidence was requested, but no proof or conformance reports were provided"
        if not proof_version_matches(version, reports):
            return "no supplied proof report contains the requested Z3 version"
        return None
    return f"unknown evidence kind {kind!r}"


def issue_for_entry(
    entry: dict[str, object],
    phase: str,
    code: str,
    message: str,
) -> Issue:
    return Issue(
        code=code,
        section=str(entry["section"]),
        item=str(entry["item"]),
        row_class=str(entry["class"]),
        phase=phase,
        message=message,
    )


def audit(
    coverage_data: dict[str, object],
    manifest: dict[str, object],
    conformance_reports: list[object],
    proof_reports: list[object],
    root: Path = ROOT,
) -> list[Issue]:
    entries = validate_manifest(manifest, coverage_data)
    rows = coverage_rows(coverage_data)
    manifest_phases: dict[tuple[str, str, str], set[str]] = {}
    for entry in entries:
        key = (str(entry["section"]), str(entry["item"]), str(entry["class"]))
        manifest_phases.setdefault(key, set()).update(str(phase) for phase in entry["phases"])
    issues: list[Issue] = []

    for key, row in sorted(rows.items()):
        section, item, row_class = key
        missing_phases = [
            f"{phase}={row.get(phase)}"
            for phase in STATUS_COLUMNS
            if row.get(phase) in OBLIGATION_STATUSES
            and phase not in manifest_phases.get(key, set())
        ]
        if not missing_phases:
            continue
        if key in manifest_phases:
            for phase_status in missing_phases:
                phase, value = phase_status.split("=", 1)
                issues.append(
                    Issue(
                        code="missing_manifest_phase",
                        section=section,
                        item=item,
                        row_class=row_class,
                        phase=phase,
                        message=f"no executable evidence manifest entry for status {value}",
                    )
                )
            continue
        issues.append(
            Issue(
                code="missing_manifest_entry",
                section=section,
                item=item,
                row_class=row_class,
                phase="",
                message="no executable evidence manifest entry"
                + (f"; statuses: {', '.join(missing_phases)}" if missing_phases else ""),
            )
        )

    for entry in entries:
        row = rows[(str(entry["section"]), str(entry["item"]), str(entry["class"]))]
        expected_status = str(entry["expected_status"])
        phases = [str(phase) for phase in entry["phases"]]
        for phase in phases:
            actual_status = row.get(phase)
            if actual_status != expected_status:
                issues.append(
                    issue_for_entry(
                        entry,
                        phase,
                        "status_mismatch",
                        f"coverage row has {actual_status!r}, manifest expects {expected_status!r}",
                    )
                )

        positive_tests = entry["positive_tests"]
        negative_tests = entry["negative_tests"]
        artifacts = entry["artifacts"]
        assert isinstance(positive_tests, list)
        assert isinstance(negative_tests, list)
        assert isinstance(artifacts, list)

        if expected_status == "implemented" and not positive_tests:
            for phase in phases:
                issues.append(
                    issue_for_entry(
                        entry,
                        phase,
                        "missing_positive_tests",
                        "implemented coverage requires positive_tests evidence",
                    )
                )
        if expected_status == "unsupported_diagnostic" and not negative_tests:
            for phase in phases:
                issues.append(
                    issue_for_entry(
                        entry,
                        phase,
                        "missing_negative_tests",
                        "unsupported diagnostic coverage requires negative_tests evidence",
                    )
                )
        if expected_status in {"parse_only", "not_applicable"} and not artifacts:
            for phase in phases:
                issues.append(
                    issue_for_entry(
                        entry,
                        phase,
                        "missing_artifacts",
                        f"{expected_status} coverage requires artifact or justification evidence",
                    )
                )
        if expected_status in {"unknown", "untested"}:
            for phase in phases:
                issues.append(
                    issue_for_entry(
                        entry,
                        phase,
                        "unresolved_expected_status",
                        "manifest entry still expects an unresolved coverage status",
                    )
                )

        for field, evidence_items in (
            ("positive_tests", positive_tests),
            ("negative_tests", negative_tests),
            ("artifacts", artifacts),
        ):
            for evidence in evidence_items:
                assert isinstance(evidence, dict)
                error = check_evidence(evidence, conformance_reports, proof_reports, root)
                if error is not None:
                    issues.append(
                        issue_for_entry(
                            entry,
                            "",
                            f"invalid_{field}",
                            error,
                        )
                    )

        for version in entry["z3_versions"]:
            assert isinstance(version, str)
            reports = report_sources(conformance_reports, proof_reports)
            if not reports:
                issues.append(
                    issue_for_entry(
                        entry,
                        "",
                        "missing_z3_version_evidence",
                        f"Z3 version {version} is listed, but no proof or conformance reports were provided",
                    )
                )
            elif not proof_version_matches(version, reports):
                issues.append(
                    issue_for_entry(
                        entry,
                        "",
                        "missing_z3_version_evidence",
                        f"no supplied proof or conformance report contains Z3 version {version}",
                    )
                )

    return issues


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Audit HolSmt SMT-LIB coverage manifest evidence."
    )
    parser.add_argument("--coverage", type=Path, default=DEFAULT_COVERAGE)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--conformance-report", action="append", type=Path, default=[])
    parser.add_argument("--proof-report", action="append", type=Path, default=[DEFAULT_PROOF_REPORT])
    parser.add_argument(
        "--enforce",
        action="store_true",
        help="return nonzero when missing obligations are found",
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        coverage_data = load_json(args.coverage)
        manifest = load_json(args.manifest)
        require(isinstance(coverage_data, dict), "coverage JSON root must be an object")
        require(isinstance(manifest, dict), "manifest JSON root must be an object")
        conformance_reports = [load_json(path) for path in args.conformance_report]
        proof_reports = [load_json(path) for path in args.proof_report]
        issues = audit(
            coverage_data,
            manifest,
            conformance_reports,
            proof_reports,
            ROOT,
        )
    except (OSError, json.JSONDecodeError, ManifestError) as exc:
        print(f"coverage manifest audit validation failed: {exc}", file=sys.stderr)
        return 2

    print(f"coverage rows audited: {len(coverage_rows(coverage_data))}")
    print(f"manifest entries: {len(manifest['entries'])}")
    if issues:
        print(f"missing obligations: {len(issues)}")
        for issue in issues:
            print(f"- {issue.render()}")
        if args.enforce:
            return 1
        print("report-only mode: missing obligations do not fail this audit")
        return 0

    print("missing obligations: 0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
