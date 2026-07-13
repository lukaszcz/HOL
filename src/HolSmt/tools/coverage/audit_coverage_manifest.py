#!/usr/bin/env python3
"""Report HolSmt SMT-LIB coverage rows without executable manifest evidence."""

from __future__ import annotations

import argparse
import json
import re
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
DEFAULT_COMPLETE_MANIFEST = (
    ROOT / "src" / "HolSmt" / "tools" / "conformance-corpus" / "v2" / "manifest.json"
)
DEFAULT_LOGIC_SOURCE = ROOT / "src" / "HolSmt" / "SmtLib_Logics.sml"
DEFAULT_COMPLETE_PROOF_REPORT = (
    ROOT / "src" / "HolSmt" / "tools" / "proof-corpus" / "complete" / "summary.json"
)
SCHEMA = "holsmt-coverage-manifest-v1"
STATUS_COLUMNS = ("parsed", "translated", "solved", "reconstructed", "tested")
IGNORED_COVERAGE_KEYS = {"metadata", "status_legend", "source_classes"}
COMPLETE_REQUIRED_CLASSES = {"SMT-LIB 2.7", "Z3 extension"}
COMPLETE_REQUIRED_STATUSES = {"reconstructed", "red", "not_applicable"}
COMPLETE_WEAK_CURRENT_STATUSES = {
    "parse_only",
    "unsupported_diagnostic",
    "untested",
    "unknown",
    "not_applicable",
}
UNSAT_REQUIRED_MODES = {"proof-parse", "proof-replay", "z3-tac"}
OBLIGATION_STATUSES = {
    "implemented",
    "parse_only",
    "unsupported_diagnostic",
    "untested",
    "unknown",
    "not_applicable",
}
THEORY_FEATURE_ALIASES = {
    "FixedSizeBitVectors": ["theory:Fixed_Size_BitVectors"],
    "Strings and regular expressions": ["theory:UnicodeStrings"],
    "Sequences, sets, bags": ["theory:Z3_Extensions"],
}
PROOF_RULE_FEATURE_ALIASES = {
    "def-axiom, elim-unused, hypothesis, intro-def, sk, true-axiom": [
        "proof-rule:def-axiom",
        "proof-rule:elim-unused",
        "proof-rule:hypothesis",
        "proof-rule:intro-def",
        "proof-rule:sk",
        "proof-rule:true-axiom",
    ],
    "mp, mp~": ["proof-rule:mp", "proof-rule:mp~"],
    "nnf-neg, nnf-pos": ["proof-rule:nnf-neg", "proof-rule:nnf-pos"],
    "refl, symm, trans, trans*": [
        "proof-rule:refl",
        "proof-rule:symm",
        "proof-rule:trans",
        "proof-rule:trans*",
    ],
    "th-lemma-arith collected subkinds": ["proof-rule:th-lemma-arith"],
    "th-lemma-array collected subkinds": ["proof-rule:th-lemma-array"],
    "th-lemma-basic collected subkinds": ["proof-rule:th-lemma-basic"],
    "th-lemma-bv collected subkinds": ["proof-rule:th-lemma-bv"],
    "th-lemma advanced theory families": [
        "proof-rule:th-lemma-fp",
        "proof-rule:th-lemma-regexp",
        "proof-rule:th-lemma-seq",
        "proof-rule:th-lemma-string",
    ],
}
SOUNDNESS_FEATURE_ALIASES = {
    "Z3_TAC oracle-tag boundary": ["soundness:oracle-tag-boundary"],
    "Replay assumptions and theorem shape": ["soundness:theorem-shape"],
    "Bit-vector division, remainder and overflow edge cases": [
        "theory:Fixed_Size_BitVectors",
        "soundness:bit-vector-edge-cases",
    ],
    "Floating-point NaN, infinity and rounding-mode semantics": ["theory:FloatingPoint"],
    "HOL strings versus SMT-LIB UnicodeStrings and regex": ["theory:UnicodeStrings"],
    "ArraysEx select/store versus HOL function encoding": ["theory:ArraysEx"],
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


def validate_complete_manifest(manifest: object) -> list[dict[str, object]]:
    require(isinstance(manifest, dict), "complete manifest root must be an object")
    require(manifest.get("schema_version") == "2", "complete manifest schema_version must be 2")
    cases = manifest.get("cases")
    require(isinstance(cases, list), "complete manifest cases must be a list")
    result: list[dict[str, object]] = []
    seen: set[str] = set()
    for index, case in enumerate(cases, 1):
        label = f"complete manifest case {index}"
        require(isinstance(case, dict), f"{label} must be an object")
        for field in ("id", "class", "features", "modes", "expected"):
            require(field in case, f"{label} is missing {field}")
        case_id = case["id"]
        require(isinstance(case_id, str) and bool(case_id), f"{label}.id must be a string")
        require(case_id not in seen, f"{label}.id duplicates an earlier case")
        seen.add(case_id)
        require(isinstance(case["class"], str) and bool(case["class"]), f"{label}.class must be a string")
        require(isinstance(case["features"], list), f"{label}.features must be a list")
        require(isinstance(case["modes"], list), f"{label}.modes must be a list")
        require(isinstance(case["expected"], dict), f"{label}.expected must be an object")
        result.append(case)
    return result


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


def current_status(row: dict[str, object]) -> str:
    values = [str(row.get(column)) for column in STATUS_COLUMNS if isinstance(row.get(column), str)]
    for value in ("unknown", "untested", "unsupported_diagnostic", "parse_only", "implemented"):
        if value in values:
            return value
    return "not_applicable"


def complete_case_statuses(case: dict[str, object]) -> set[str]:
    expected = case.get("expected")
    if not isinstance(expected, dict):
        return set()
    return {
        str(result.get("status"))
        for result in expected.values()
        if isinstance(result, dict) and isinstance(result.get("status"), str)
    }


def is_red_case(case: dict[str, object]) -> bool:
    return "red" in complete_case_statuses(case)


def is_alethe_upstream_blocker_case(case: dict[str, object]) -> bool:
    values: list[str] = []
    for key in ("id", "file", "implementation_obligation"):
        value = case.get(key)
        if isinstance(value, str):
            values.append(value)
    features = case.get("features")
    if isinstance(features, list):
        values.extend(feature for feature in features if isinstance(feature, str))
    text = " ".join(values).lower()
    return "cvc5-alethe-datatype-export" in text


def is_coverage_red_case(case: dict[str, object]) -> bool:
    return is_red_case(case) and not is_alethe_upstream_blocker_case(case)


def is_complete_evidence_case(case: dict[str, object]) -> bool:
    statuses = complete_case_statuses(case)
    return "pass" in statuses and "red" not in statuses


def split_item_names(item: object) -> list[str]:
    return [part.strip() for part in str(item).split(",") if part.strip()]


def feature_slug(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")


def row_feature_tokens(section: str, row: dict[str, object]) -> set[str]:
    item = str(row.get("item", ""))
    tokens = {item.lower(), feature_slug(item)}
    if section == "commands":
        commands = row.get("commands")
        names = commands if isinstance(commands, list) else split_item_names(item)
        for command in names:
            if isinstance(command, str) and command:
                tokens.add(f"command:{command.lower()}")
    elif section == "theories":
        aliases = THEORY_FEATURE_ALIASES.get(item, [])
        for name in split_item_names(item):
            tokens.add(f"theory:{name}")
            tokens.add(f"theory:{name.replace(' ', '_')}")
        tokens.update(alias.lower() for alias in aliases)
    elif section == "logics":
        for logic in split_item_names(item):
            tokens.add(f"logic:{logic}")
            tokens.add(logic.lower())
    elif section == "z3_proof_rules":
        aliases = PROOF_RULE_FEATURE_ALIASES.get(item, [])
        for rule in split_item_names(item):
            tokens.add(f"proof-rule:{rule}")
        tokens.update(alias.lower() for alias in aliases)
    elif section == "soundness_audit":
        tokens.update(alias.lower() for alias in SOUNDNESS_FEATURE_ALIASES.get(item, []))
    return {token.lower() for token in tokens}


def case_feature_tokens(case: dict[str, object]) -> set[str]:
    tokens = {str(case.get("id", "")).lower(), feature_slug(str(case.get("id", "")))}
    logic = case.get("logic")
    if isinstance(logic, str) and logic:
        tokens.add(f"logic:{logic}".lower())
        tokens.add(logic.lower())
    features = case.get("features")
    if isinstance(features, list):
        for feature in features:
            if isinstance(feature, str):
                tokens.add(feature.lower())
                tokens.add(feature_slug(feature))
    return tokens


def complete_case_matches_row(section: str, row: dict[str, object], case: dict[str, object]) -> bool:
    row_tokens = row_feature_tokens(section, row)
    case_tokens = case_feature_tokens(case)
    if section == "commands":
        return case.get("class") == "command" and bool(row_tokens & case_tokens)
    if section == "logics":
        return case.get("class") == "logic" and bool(row_tokens & case_tokens)
    if section == "z3_proof_rules":
        return case.get("class") == "proof-rule" and bool(row_tokens & case_tokens)
    return bool(row_tokens & case_tokens)


def complete_case_ids_for_row(
    section: str,
    row: dict[str, object],
    cases: Iterable[dict[str, object]],
    predicate,
) -> list[str]:
    result: list[str] = []
    for case in cases:
        if predicate(case) and complete_case_matches_row(section, row, case):
            result.append(str(case["id"]))
    return sorted(set(result))


def outside_complete_scope_reason(row: dict[str, object]) -> str:
    row_class = str(row.get("class", ""))
    item = str(row.get("item", ""))
    lowered = item.lower()
    if row_class == "SMT-LIB 3":
        return "SMT-LIB 3 deferred"
    if "sat and unknown" in lowered:
        return "solver result SAT/UNKNOWN not proof-producing"
    if any(name in lowered for name in ("get-model", "get-value", "get-assignment", "get-assertions")):
        return "model-producing command not theorem-producing"
    if row_class == "HolSmt":
        return "non-SMT-LIB extension"
    return ""


def enrich_complete_metadata(
    coverage_data: dict[str, object],
    complete_cases: list[dict[str, object]],
) -> dict[str, object]:
    for section, row in coverage_rows(coverage_data).items():
        section_name = section[0]
        row["current_status"] = current_status(row)
        row["complete_test_ids"] = complete_case_ids_for_row(
            section_name, row, complete_cases, is_complete_evidence_case
        )
        row["red_obligation_ids"] = complete_case_ids_for_row(
            section_name, row, complete_cases, is_coverage_red_case
        )
        if str(row.get("class")) not in COMPLETE_REQUIRED_CLASSES:
            row["complete_required_status"] = "not_applicable"
            row["outside_complete_scope_reason"] = outside_complete_scope_reason(row)
        elif row["red_obligation_ids"] or not row["complete_test_ids"]:
            row["complete_required_status"] = "red"
            row.pop("outside_complete_scope_reason", None)
        else:
            row["complete_required_status"] = "reconstructed"
            row.pop("outside_complete_scope_reason", None)
    return coverage_data


def parse_accepted_logics(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    match = re.search(
        r"fun\s+parsedicts_of_logic\s*\([^)]*\)\s*=\s*case\s+logic\s+of(?P<body>.*?)"
        r"\n\s*\(\*\s*returns the symbol metadata",
        text,
        flags=re.DOTALL,
    )
    if match is None:
        raise ManifestError(f"could not find parsedicts_of_logic case expression in {path}")
    logics = re.findall(r'"([A-Z][A-Z0-9_]*)"\s*=>', match.group("body"))
    require(bool(logics), f"no accepted logic names found in {path}")
    return sorted(set(logics))


def proof_report_rules(reports: Iterable[object]) -> set[str]:
    rules: set[str] = set()
    for report in reports:
        if not isinstance(report, dict):
            continue
        discovered = report.get("discovered_rules")
        if isinstance(discovered, list):
            rules.update(str(rule) for rule in discovered if isinstance(rule, str))
        histogram = report.get("aggregate_rule_histogram")
        if isinstance(histogram, dict):
            rules.update(str(rule) for rule in histogram)
        rules_by_version = report.get("rules_by_version")
        if isinstance(rules_by_version, list):
            for item in rules_by_version:
                if isinstance(item, dict) and isinstance(item.get("rules"), list):
                    rules.update(str(rule) for rule in item["rules"] if isinstance(rule, str))
    return rules


def row_proof_rules(row: dict[str, object]) -> set[str]:
    return {
        token.removeprefix("proof-rule:")
        for token in row_feature_tokens("z3_proof_rules", row)
        if token.startswith("proof-rule:")
    }


def accepted_logic_has_complete_modes(logic: str, cases: Iterable[dict[str, object]]) -> bool:
    for case in cases:
        if case.get("class") != "logic" or case.get("logic") != logic:
            continue
        statuses = complete_case_statuses(case)
        if "red" in statuses:
            continue
        modes = {str(mode) for mode in case.get("modes", []) if isinstance(mode, str)}
        expected = case.get("expected")
        expected_modes = set(str(mode) for mode in expected) if isinstance(expected, dict) else set()
        if UNSAT_REQUIRED_MODES <= modes and UNSAT_REQUIRED_MODES <= expected_modes:
            return True
    return False


def audit_complete_coverage(
    coverage_data: dict[str, object],
    complete_cases: list[dict[str, object]],
    accepted_logics: list[str],
    complete_proof_reports: list[object],
) -> list[Issue]:
    issues: list[Issue] = []
    real_rules = proof_report_rules(complete_proof_reports)

    for (section, item, row_class), row in sorted(coverage_rows(coverage_data).items()):
        missing_fields = [
            field
            for field in (
                "current_status",
                "complete_required_status",
                "red_obligation_ids",
                "complete_test_ids",
            )
            if field not in row
        ]
        if missing_fields:
            issues.append(
                Issue(
                    "missing_complete_metadata",
                    section,
                    item,
                    row_class,
                    "",
                    "coverage row is missing complete metadata field(s): "
                    + ", ".join(missing_fields),
                )
            )
            continue

        complete_required_status = row.get("complete_required_status")
        current = row.get("current_status")
        red_ids = row.get("red_obligation_ids")
        complete_ids = row.get("complete_test_ids")
        if complete_required_status not in COMPLETE_REQUIRED_STATUSES:
            issues.append(
                Issue(
                    "invalid_complete_required_status",
                    section,
                    item,
                    row_class,
                    "",
                    f"complete_required_status must be one of {sorted(COMPLETE_REQUIRED_STATUSES)}",
                )
            )
            continue
        if not isinstance(red_ids, list) or not all(isinstance(value, str) for value in red_ids):
            issues.append(Issue("invalid_red_obligation_ids", section, item, row_class, "", "red_obligation_ids must be a list of strings"))
            continue
        if not isinstance(complete_ids, list) or not all(isinstance(value, str) for value in complete_ids):
            issues.append(Issue("invalid_complete_test_ids", section, item, row_class, "", "complete_test_ids must be a list of strings"))
            continue
        if complete_required_status == "not_applicable":
            reason = row.get("outside_complete_scope_reason")
            if not isinstance(reason, str) or not reason:
                issues.append(
                    Issue(
                        "missing_outside_complete_scope_reason",
                        section,
                        item,
                        row_class,
                        "",
                        "rows outside COMPLETE scope must say why",
                    )
                )
            continue

        if red_ids:
            if complete_required_status != "red":
                issues.append(
                    Issue(
                        "red_obligation_not_red",
                        section,
                        item,
                        row_class,
                        "",
                        "row has red obligations but complete_required_status is not red",
                    )
                )
            issues.append(
                Issue(
                    "red_complete_obligation",
                    section,
                    item,
                    row_class,
                    "",
                    "complete-required row still has red obligation IDs: " + ", ".join(red_ids[:8]),
                )
            )
        if not complete_ids:
            code = "diagnostic_only_complete_evidence" if row.get("diagnostic_test_ids") else "missing_complete_evidence"
            issues.append(
                Issue(
                    code,
                    section,
                    item,
                    row_class,
                    "",
                    "complete-required row lacks real complete evidence",
                )
            )
        if complete_required_status == "reconstructed" and current in COMPLETE_WEAK_CURRENT_STATUSES:
            issues.append(
                Issue(
                    "weak_current_status_for_reconstructed_required",
                    section,
                    item,
                    row_class,
                    "",
                    f"current_status={current!r} cannot satisfy complete_required_status='reconstructed'",
                )
            )

        if section == "z3_proof_rules":
            required_rules = row_proof_rules(row)
            if required_rules and required_rules.isdisjoint(real_rules):
                issues.append(
                    Issue(
                        "missing_real_proof_occurrence",
                        section,
                        item,
                        row_class,
                        "",
                        "required proof-rule row lacks a real Z3 proof-corpus occurrence",
                    )
                )

    for logic in accepted_logics:
        if not accepted_logic_has_complete_modes(logic, complete_cases):
            issues.append(
                Issue(
                    "missing_accepted_logic_mode_coverage",
                    "logics",
                    logic,
                    "SMT-LIB 2.7",
                    "",
                    "accepted logic lacks complete proof-parse/proof-replay/z3-tac mode coverage",
                )
            )

    return issues


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
    parser.add_argument("--complete-manifest", type=Path, default=DEFAULT_COMPLETE_MANIFEST)
    parser.add_argument("--logic-source", type=Path, default=DEFAULT_LOGIC_SOURCE)
    parser.add_argument(
        "--complete-proof-report",
        action="append",
        type=Path,
        default=[DEFAULT_COMPLETE_PROOF_REPORT],
    )
    parser.add_argument(
        "--complete",
        action="store_true",
        help="enforce COMPLETE conformance coverage semantics and red obligations",
    )
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
        if args.complete:
            complete_cases = validate_complete_manifest(load_json(args.complete_manifest))
            accepted_logics = parse_accepted_logics(args.logic_source)
            complete_proof_reports = [
                load_json(path) for path in args.complete_proof_report if path.exists()
            ]
            issues.extend(
                audit_complete_coverage(
                    coverage_data,
                    complete_cases,
                    accepted_logics,
                    complete_proof_reports,
                )
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
