#!/usr/bin/env python3
"""Audit HolSmt Z3 proof-rule replay coverage.

The audit has two different coverage levels:

* synthetic replay coverage is mandatory for every registered replay rule;
* real proof-corpus occurrences are reported as red obligations, because the
  current checked-in corpus is intentionally minimal.
"""

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
DEFAULT_PROOF_SOURCE = ROOT / "src" / "HolSmt" / "Z3_Proof.sml"
DEFAULT_UNITTEST_SOURCE = ROOT / "src" / "HolSmt" / "Unittest.sml"
DEFAULT_MANIFEST = TOOLS_DIR / "conformance-corpus" / "v2" / "manifest.json"
DEFAULT_PROOF_SUMMARY = TOOLS_DIR / "proof-corpus" / "complete" / "summary.json"
DEFAULT_COVERAGE_REPORT = TOOLS_DIR / "coverage" / "smtlib_coverage.json"

SCHEMA = "holsmt-proof-completeness-audit-v1"

ADVANCED_TH_LEMMA_THEORY_TO_RULE = {
    "fp": "th-lemma-fp",
    "fpa": "th-lemma-fp",
    "floating-point": "th-lemma-fp",
    "seq": "th-lemma-seq",
    "sequence": "th-lemma-seq",
    "sequences": "th-lemma-seq",
    "string": "th-lemma-string",
    "strings": "th-lemma-string",
    "str": "th-lemma-string",
    "regexp": "th-lemma-regexp",
    "regex": "th-lemma-regexp",
    "re": "th-lemma-regexp",
    "datatype": "th-lemma-datatype",
    "datatypes": "th-lemma-datatype",
    "dt": "th-lemma-datatype",
    "nonlinear-arith": "th-lemma-nonlinear-arith",
    "nonlinear": "th-lemma-nonlinear-arith",
    "nla": "th-lemma-nonlinear-arith",
    "nra": "th-lemma-nonlinear-arith",
    "nia": "th-lemma-nonlinear-arith",
}

TH_LEMMA_OBLIGATION_RULES = {
    "th-lemma-fp",
    "th-lemma-seq",
    "th-lemma-string",
    "th-lemma-regexp",
    "th-lemma-datatype",
}


class AuditError(ValueError):
    pass


@dataclass(frozen=True)
class ProofRule:
    name: str
    aliases: tuple[str, ...]
    premise_shape: str
    replay_handler: str

    @property
    def names(self) -> tuple[str, ...]:
        return (self.name, *self.aliases)


@dataclass(frozen=True)
class Issue:
    code: str
    category: str
    subject: str
    message: str
    severity: str = "error"
    blocking: bool = True
    details: dict[str, object] = field(default_factory=dict)

    def to_json(self) -> dict[str, object]:
        result: dict[str, object] = {
            "code": self.code,
            "category": self.category,
            "severity": self.severity,
            "blocking": self.blocking,
            "subject": self.subject,
            "message": self.message,
        }
        if self.details:
            result["details"] = self.details
        return result

    def render(self) -> str:
        return f"{self.code}: {self.subject}: {self.message}"


def load_json(path: Path) -> object:
    with path.open(encoding="utf-8") as infile:
        return json.load(infile)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def parse_string_list(source: str) -> tuple[str, ...]:
    return tuple(re.findall(r'"([^"]+)"', source))


def parse_proof_rules(path: Path) -> list[ProofRule]:
    text = path.read_text(encoding="utf-8")
    match = re.search(
        r"val\s+proof_rule_registry\s*:\s*proof_rule\s+list\s*=\s*\[(?P<body>.*?)\n\s*\]",
        text,
        flags=re.DOTALL,
    )
    if match is None:
        raise AuditError(f"could not find proof_rule_registry in {path}")

    rules: list[ProofRule] = []
    pattern = re.compile(
        r'mk_rule\s*\(\s*"(?P<name>[^"]+)"\s*,\s*'
        r'(?P<aliases>\[(?:\s*"[^"]+"\s*,?)*\s*\])\s*,\s*'
        r"(?P<premise_shape>[A-Za-z0-9_]+)\s*,\s*"
        r'"(?P<handler>[^"]+)"\s*\)',
        flags=re.DOTALL,
    )
    for item in pattern.finditer(match.group("body")):
        rules.append(
            ProofRule(
                name=item.group("name"),
                aliases=parse_string_list(item.group("aliases")),
                premise_shape=item.group("premise_shape"),
                replay_handler=item.group("handler"),
            )
        )
    require(bool(rules), f"no proof rules found in {path}")
    names = [rule.name for rule in rules]
    duplicates = sorted({name for name in names if names.count(name) > 1})
    require(not duplicates, f"duplicate proof rule name(s): {', '.join(duplicates)}")
    return rules


def parse_th_lemma_classes(path: Path, rules: Iterable[ProofRule]) -> list[str]:
    text = path.read_text(encoding="utf-8")
    constructor_classes = {
        "th-lemma-" + name.lower()
        for name in re.findall(r"\|\s*TH_LEMMA_([A-Z_]+)\s+of", text)
        if name != "ADVANCED"
    }
    registry_classes = {rule.name for rule in rules if rule.name.startswith("th-lemma-")}
    return sorted(constructor_classes | registry_classes)


def function_body(text: str, function_name: str, next_function_name: str) -> str:
    match = re.search(
        rf"fun\s+{re.escape(function_name)}\b(?P<body>.*?)\nfun\s+{re.escape(next_function_name)}\b",
        text,
        flags=re.DOTALL,
    )
    if match is None:
        raise AuditError(f"could not find function body for {function_name}")
    return match.group("body")


def parse_core_synthetic_tests(text: str) -> set[str]:
    body = function_body(
        text,
        "z3_core_proof_rule_replay_minimal_raw_success",
        "z3_th_lemma_existing_theory_replay_minimal_success",
    )
    return set(re.findall(r'\(\s*"([^"]+)"\s*,', body))


def normalize_th_lemma_rule(theory: str, subkind: str | None = None) -> str:
    if theory == "arith" and subkind in {"nla", "nra", "nia", "nonlinear", "nonlinear-arith"}:
        return "th-lemma-nonlinear-arith"
    if theory in {"arith", "array", "basic", "bv"}:
        return f"th-lemma-{theory}"
    return ADVANCED_TH_LEMMA_THEORY_TO_RULE.get(theory, f"th-lemma-{theory}")


def parse_th_lemma_synthetic_tests(text: str) -> set[str]:
    rules: set[str] = set()
    for match in re.finditer(
        r"\(\(_\s+th-lemma\s+([A-Za-z0-9_-]+)(?:\s+([A-Za-z0-9_-]+))?",
        text,
    ):
        theory = match.group(1)
        subkind = match.group(2)
        rules.add(normalize_th_lemma_rule(theory, subkind))
    return rules


def parse_synthetic_replay_tests(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8")
    rules = parse_core_synthetic_tests(text)
    rules.update(parse_th_lemma_synthetic_tests(text))
    return rules


def manifest_cases(path: Path | None) -> list[dict[str, object]]:
    if path is None or not path.exists():
        return []
    manifest = load_json(path)
    require(isinstance(manifest, dict), f"{path} root must be an object")
    cases = manifest.get("cases")
    require(isinstance(cases, list), f"{path} cases must be a list")
    return [case for case in cases if isinstance(case, dict)]


def manifest_proof_rule_features(path: Path | None) -> set[str]:
    features: set[str] = set()
    for case in manifest_cases(path):
        raw_features = case.get("features", [])
        if isinstance(raw_features, list):
            for feature in raw_features:
                if isinstance(feature, str) and feature.startswith("proof-rule:"):
                    features.add(feature.removeprefix("proof-rule:"))
    return features


def manifest_red_proof_rule_features(path: Path | None) -> set[str]:
    features: set[str] = set()
    for case in manifest_cases(path):
        expected = case.get("expected")
        raw_features = case.get("features", [])
        has_red = (
            isinstance(expected, dict)
            and any(isinstance(value, dict) and value.get("status") == "red" for value in expected.values())
        )
        if has_red and isinstance(raw_features, list):
            for feature in raw_features:
                if isinstance(feature, str) and feature.startswith("proof-rule:"):
                    features.add(feature.removeprefix("proof-rule:"))
    return features


def manifest_proof_rule_rows(path: Path | None) -> dict[str, dict[str, object]]:
    rows: dict[str, dict[str, object]] = {}
    for case in manifest_cases(path):
        raw_features = case.get("features", [])
        if not isinstance(raw_features, list):
            continue
        rules = [
            feature.removeprefix("proof-rule:")
            for feature in raw_features
            if isinstance(feature, str) and feature.startswith("proof-rule:")
        ]
        if not rules:
            continue
        case_id = case.get("id")
        obligation = case.get("implementation_obligation")
        files: list[str] = []
        if isinstance(obligation, dict):
            raw_files = obligation.get("files", [])
            if isinstance(raw_files, list):
                files = [item for item in raw_files if isinstance(item, str)]
        for rule in rules:
            row = rows.setdefault(rule, {"case_ids": [], "implementation_files": []})
            if isinstance(case_id, str):
                row["case_ids"].append(case_id)  # type: ignore[index, union-attr]
            row["implementation_files"].extend(files)  # type: ignore[index, union-attr]
    for row in rows.values():
        row["case_ids"] = sorted(set(row["case_ids"]))  # type: ignore[index, arg-type]
        row["implementation_files"] = sorted(set(row["implementation_files"]))  # type: ignore[index, arg-type]
    return rows


def coverage_proof_rule_rows(path: Path | None) -> dict[str, dict[str, object]]:
    if path is None or not path.exists():
        return {}
    coverage = load_json(path)
    require(isinstance(coverage, dict), f"{path} root must be an object")
    rows = coverage.get("z3_proof_rules", [])
    require(isinstance(rows, list), f"{path} z3_proof_rules must be a list")
    result: dict[str, dict[str, object]] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        item = row.get("item")
        if not isinstance(item, str):
            continue
        test_ids = row.get("test_ids", [])
        result[item] = {
            "item": item,
            "tested": row.get("tested"),
            "reconstructed": row.get("reconstructed"),
            "test_ids": [test_id for test_id in test_ids if isinstance(test_id, str)]
            if isinstance(test_ids, list)
            else [],
        }
    return result


def real_proof_occurrences(path: Path | None) -> set[str]:
    if path is None or not path.exists():
        return set()
    summary = load_json(path)
    require(isinstance(summary, dict), f"{path} root must be an object")
    discovered = summary.get("discovered_rules")
    histogram = summary.get("aggregate_rule_histogram")
    inferred = summary.get("inferred_rules")
    inferred_histogram = summary.get("aggregate_inferred_rule_histogram")
    rules: set[str] = set()
    if isinstance(discovered, list):
        rules.update(item for item in discovered if isinstance(item, str))
    if isinstance(histogram, dict):
        rules.update(rule for rule, count in histogram.items() if isinstance(rule, str) and isinstance(count, int) and count > 0)
    if isinstance(inferred, list):
        rules.update(item for item in inferred if isinstance(item, str))
    if isinstance(inferred_histogram, dict):
        rules.update(
            rule
            for rule, count in inferred_histogram.items()
            if isinstance(rule, str) and isinstance(count, int) and count > 0
        )
    return rules


def synthetic_coverage_names(rule: ProofRule) -> set[str]:
    names = set(rule.names)
    if rule.replay_handler == "mp_eq":
        names.add("mp~")
    if rule.replay_handler == "skolem":
        names.add("sk")
    if rule.replay_handler == "trans_star":
        names.add("trans*")
    return names


def audit(
    rules: list[ProofRule],
    th_lemma_classes: list[str],
    synthetic_rules: set[str],
    manifest_features: set[str],
    manifest_red_features: set[str],
    real_rules: set[str],
    manifest_rows: dict[str, dict[str, object]],
    coverage_rows: dict[str, dict[str, object]],
) -> list[Issue]:
    issues: list[Issue] = []

    def proof_rule_obligation_details(rule_name: str) -> dict[str, object]:
        manifest_row = manifest_rows.get(rule_name, {})
        files = manifest_row.get("implementation_files", [])
        if not files:
            files = [
                "src/HolSmt/Z3_Proof.sml",
                "src/HolSmt/Z3_ProofParser.sml",
                "src/HolSmt/Z3_ProofReplay.sml",
            ]
        test_ids = manifest_row.get("case_ids", [])
        if not test_ids:
            test_ids = [f"proof-rule:{rule_name}"]
        return {
            "failure_phase": "proof-replay",
            "feature": rule_name,
            "files": sorted(str(item) for item in files),
            "test_ids": sorted(str(item) for item in test_ids),
        }

    for rule in rules:
        if synthetic_coverage_names(rule).isdisjoint(synthetic_rules):
            issues.append(
                Issue(
                    code="missing_synthetic_replay_test",
                    category="synthetic-replay",
                    subject=rule.name,
                    message="registered Z3 proof rule has no synthetic replay unit-test mapping",
                    details={
                        "aliases": list(rule.aliases),
                        "premise_shape": rule.premise_shape,
                        "replay_handler": rule.replay_handler,
                    },
                )
            )

    for rule in rules:
        if rule.name not in manifest_features:
            issues.append(
                Issue(
                    code="missing_manifest_proof_rule_row",
                    category="proof-rule-manifest",
                    subject=rule.name,
                    message="registered Z3 proof rule has no v2 proof-rule manifest row",
                    severity="warning",
                    blocking=False,
                )
            )

    for rule in sorted(TH_LEMMA_OBLIGATION_RULES):
        if (
            rule in th_lemma_classes
            and rule not in manifest_red_features
            and rule not in real_rules
        ):
            issues.append(
                Issue(
                    code="missing_th_lemma_red_obligation",
                    category="proof-rule-obligation",
                    subject=rule,
                    message="diagnostic-only th-lemma family lacks a red proof-rule obligation row",
                    severity="red",
                    blocking=True,
                    details=proof_rule_obligation_details(rule),
                )
            )

    for rule in rules:
        if rule.name not in coverage_rows:
            issues.append(
                Issue(
                    code="missing_coverage_proof_rule_row",
                    category="coverage-report",
                    subject=rule.name,
                    message="registered Z3 proof rule has no generated coverage report row",
                    severity="warning",
                    blocking=False,
                )
            )

    for rule in rules:
        if rule.name not in real_rules and set(rule.aliases).isdisjoint(real_rules):
            manifest_row = manifest_rows.get(rule.name, {})
            coverage_row = coverage_rows.get(rule.name, {})
            implementation_files = manifest_row.get("implementation_files", [])
            if not implementation_files:
                implementation_files = [
                    "src/HolSmt/Z3_Proof.sml",
                    "src/HolSmt/Z3_ProofParser.sml",
                    "src/HolSmt/Z3_ProofReplay.sml",
                ]
            case_ids = manifest_row.get("case_ids", [])
            if not case_ids:
                case_ids = [f"proof-rule:{rule.name}:real-proof-occurrence"]
            issues.append(
                Issue(
                    code="missing_real_proof_occurrence",
                    category="real-proof-corpus",
                    subject=rule.name,
                    message="registered Z3 proof rule has no checked-in real proof-corpus occurrence yet",
                    severity="red",
                    blocking=False,
                    details={
                        "aliases": list(rule.aliases),
                        "case_ids": case_ids,
                        "coverage_row": coverage_row,
                        "failure_phase": "proof-parse",
                        "feature": f"real-proof-occurrence:{rule.name}",
                        "files": implementation_files,
                        "implementation_files": implementation_files,
                        "test_ids": case_ids,
                    },
                )
            )

    return issues


def build_report(
    *,
    proof_source: Path,
    unittest_source: Path,
    manifest_path: Path | None,
    proof_summary_path: Path | None,
    coverage_report_path: Path | None = DEFAULT_COVERAGE_REPORT,
) -> dict[str, object]:
    rules = parse_proof_rules(proof_source)
    th_lemma_classes = parse_th_lemma_classes(proof_source, rules)
    synthetic_rules = parse_synthetic_replay_tests(unittest_source)
    manifest_features = manifest_proof_rule_features(manifest_path)
    manifest_red_features = manifest_red_proof_rule_features(manifest_path)
    manifest_rows = manifest_proof_rule_rows(manifest_path)
    coverage_rows = coverage_proof_rule_rows(coverage_report_path)
    real_rules = real_proof_occurrences(proof_summary_path)
    issues = audit(
        rules,
        th_lemma_classes,
        synthetic_rules,
        manifest_features,
        manifest_red_features,
        real_rules,
        manifest_rows,
        coverage_rows,
    )
    blocking_issues = [issue for issue in issues if issue.blocking]
    red_obligations = [issue for issue in issues if issue.severity == "red"]
    category_counts: dict[str, int] = {}
    for issue in issues:
        category_counts[issue.category] = category_counts.get(issue.category, 0) + 1

    return {
        "schema": SCHEMA,
        "inputs": {
            "proof_source": str(proof_source),
            "unittest_source": str(unittest_source),
            "manifest": str(manifest_path) if manifest_path is not None else None,
            "proof_summary": str(proof_summary_path) if proof_summary_path is not None else None,
            "coverage_report": str(coverage_report_path) if coverage_report_path is not None else None,
        },
        "summary": {
            "registry_rule_count": len(rules),
            "th_lemma_class_count": len(th_lemma_classes),
            "synthetic_rule_count": len(synthetic_rules),
            "manifest_proof_rule_count": len(manifest_features),
            "coverage_proof_rule_count": len(coverage_rows),
            "real_proof_rule_count": len(real_rules),
            "issue_count": len(issues),
            "blocking_issue_count": len(blocking_issues),
            "red_obligation_count": len(red_obligations),
            "category_counts": category_counts,
            "passed": not blocking_issues,
        },
        "registry_rules": [
            {
                "name": rule.name,
                "aliases": list(rule.aliases),
                "premise_shape": rule.premise_shape,
                "replay_handler": rule.replay_handler,
            }
            for rule in rules
        ],
        "th_lemma_classes": th_lemma_classes,
        "synthetic_rules": sorted(synthetic_rules),
        "manifest_proof_rules": sorted(manifest_features),
        "coverage_proof_rules": sorted(coverage_rows),
        "real_proof_rules": sorted(real_rules),
        "issues": [issue.to_json() for issue in issues],
    }


def print_text_summary(report: dict[str, object]) -> None:
    summary = report["summary"]
    assert isinstance(summary, dict)
    print("proof completeness audit")
    print(f"registry rules: {summary['registry_rule_count']}")
    print(f"th-lemma classes: {summary['th_lemma_class_count']}")
    print(f"synthetic rules: {summary['synthetic_rule_count']}")
    print(f"manifest proof-rule rows: {summary['manifest_proof_rule_count']}")
    print(f"coverage proof-rule rows: {summary['coverage_proof_rule_count']}")
    print(f"real proof rules: {summary['real_proof_rule_count']}")
    print(f"issues: {summary['issue_count']}")
    print(f"blocking issues: {summary['blocking_issue_count']}")
    print(f"red obligations: {summary['red_obligation_count']}")
    category_counts = summary.get("category_counts")
    if isinstance(category_counts, dict) and category_counts:
        counts = ", ".join(f"{name}={count}" for name, count in sorted(category_counts.items()))
        print(f"categories: {counts}")
    issues = report.get("issues")
    if isinstance(issues, list) and issues:
        for issue in issues[:25]:
            if isinstance(issue, dict):
                print(f"- {issue['severity']}: {issue['code']}: {issue['subject']}: {issue['message']}")
        if len(issues) > 25:
            print(f"- ... {len(issues) - 25} more issue(s)")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Audit HolSmt Z3 proof registry coverage against synthetic and real proof evidence."
    )
    parser.add_argument("--proof-source", type=Path, default=DEFAULT_PROOF_SOURCE)
    parser.add_argument("--unittest-source", type=Path, default=DEFAULT_UNITTEST_SOURCE)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--proof-summary", type=Path, default=DEFAULT_PROOF_SUMMARY)
    parser.add_argument("--coverage-report", type=Path, default=DEFAULT_COVERAGE_REPORT)
    parser.add_argument("--no-manifest", action="store_true", help="skip v2 manifest checks")
    parser.add_argument("--no-proof-summary", action="store_true", help="skip real proof-corpus occurrence checks")
    parser.add_argument("--no-coverage-report", action="store_true", help="skip generated coverage report checks")
    parser.add_argument(
        "--fail-on-red-obligations",
        action="store_true",
        help="exit nonzero when nonblocking red real-corpus obligations remain",
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
    manifest_path = None if args.no_manifest else args.manifest
    proof_summary_path = None if args.no_proof_summary else args.proof_summary
    coverage_report_path = None if args.no_coverage_report else args.coverage_report
    try:
        report = build_report(
            proof_source=args.proof_source,
            unittest_source=args.unittest_source,
            manifest_path=manifest_path,
            proof_summary_path=proof_summary_path,
            coverage_report_path=coverage_report_path,
        )
    except (OSError, json.JSONDecodeError, AuditError) as exc:
        print(f"proof completeness audit infrastructure error: {exc}", file=sys.stderr)
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
    if not summary.get("passed"):
        return 1
    if args.fail_on_red_obligations and summary.get("red_obligation_count"):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
