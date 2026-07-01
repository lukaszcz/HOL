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
DEFAULT_LOGICS_JSON = TOOLS_DIR / "conformance-corpus" / "v2" / "logics.json"
DEFAULT_LOGIC_SOURCE = ROOT / "src" / "HolSmt" / "SmtLib_Logics.sml"
DEFAULT_THEORY_SOURCE = ROOT / "src" / "HolSmt" / "SmtLib_Theories.sml"
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
THEORY_REQUIRED_CASE_KINDS = {"sat", "unsat-proof", "type-error", "boundary"}
COMPLETE_REQUIRED_CLASSES = {"SMT-LIB 2.7", "Z3 extension"}
WEAK_COVERAGE_STATUSES = {
    "parse_only",
    "unsupported",
    "unsupported_diagnostic",
    "not_applicable",
}
UNRESOLVED_COVERAGE_STATUSES = {"unknown", "untested"}

REQUIRED_THEORY_METADATA: dict[str, dict[str, set[str]]] = {
    "ArraysEx": {
        "sort": {"Array"},
        "term": {"select", "store"},
    },
    "UnicodeStrings": {
        "sort": {"String", "RegLan"},
        "term": {
            "str.++",
            "str.len",
            "str.<",
            "str.<=",
            "str.at",
            "str.substr",
            "str.prefixof",
            "str.suffixof",
            "str.contains",
            "str.indexof",
            "str.replace",
            "str.replace_all",
            "str.is_digit",
            "str.to_code",
            "str.from_code",
            "str.to_int",
            "str.from_int",
            "str.to_re",
            "str.in_re",
            "str.replace_re",
            "str.replace_re_all",
            "re.none",
            "re.all",
            "re.allchar",
            "re.++",
            "re.union",
            "re.inter",
            "re.diff",
            "re.*",
            "re.+",
            "re.opt",
            "re.range",
            "re.^",
            "re.loop",
        },
    },
    "Fixed_Size_BitVectors": {
        "sort": {"BitVec"},
        "term": {
            "_",
            "concat",
            "extract",
            "bvnot",
            "bvneg",
            "bvand",
            "bvor",
            "bvxor",
            "bvxnor",
            "bvadd",
            "bvmul",
            "bvudiv",
            "bvurem",
            "bvsub",
            "bvnand",
            "bvnor",
            "bvcomp",
            "bvsdiv",
            "bvsrem",
            "bvsmod",
            "bvshl",
            "bvlshr",
            "bvashr",
            "repeat",
            "zero_extend",
            "sign_extend",
            "rotate_left",
            "rotate_right",
            "bvredand",
            "bvredor",
            "bvult",
            "bvule",
            "bvugt",
            "bvuge",
            "bvslt",
            "bvsle",
            "bvsgt",
            "bvsge",
            "ubv_to_int",
            "sbv_to_int",
            "int_to_bv",
            "bvnego",
            "bvuaddo",
            "bvsaddo",
            "bvumulo",
            "bvsmulo",
            "bvusubo",
            "bvssubo",
            "bvsdivo",
        },
    },
    "FloatingPoint": {
        "sort": {"RoundingMode", "FloatingPoint", "Float16", "Float32", "Float64", "Float128"},
        "term": {
            "roundNearestTiesToEven",
            "RNE",
            "roundNearestTiesToAway",
            "RNA",
            "roundTowardPositive",
            "RTP",
            "roundTowardNegative",
            "RTN",
            "roundTowardZero",
            "RTZ",
            "+zero",
            "-zero",
            "+oo",
            "-oo",
            "NaN",
            "fp",
            "fp.add",
            "fp.sub",
            "fp.mul",
            "fp.div",
            "fp.fma",
            "fp.sqrt",
            "fp.roundToIntegral",
            "fp.rem",
            "fp.min",
            "fp.max",
            "fp.abs",
            "fp.neg",
            "fp.leq",
            "fp.lt",
            "fp.geq",
            "fp.gt",
            "fp.eq",
            "fp.isNormal",
            "fp.isSubnormal",
            "fp.isZero",
            "fp.isInfinite",
            "fp.isNaN",
            "fp.isNegative",
            "fp.isPositive",
            "to_fp",
            "to_fp_unsigned",
            "fp.to_ubv",
            "fp.to_sbv",
            "fp.to_real",
        },
    },
    "Z3_Extensions": {
        "sort": {"Seq", "Set", "Bag"},
        "term": {
            "seq.++",
            "seq.len",
            "seq.extract",
            "seq.contains",
            "set.member",
            "set.insert",
            "set.union",
            "set.intersect",
            "set.minus",
            "set.subset",
            "bag.union_disjoint",
            "bag.union_max",
            "bag.inter_min",
            "bag.difference_subtract",
            "bag.count",
        },
    },
}


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


@dataclass(frozen=True)
class TheoryMetadataSymbol:
    theory: str
    slug: str
    kind: str
    name: str
    declarations: tuple[str, ...]

    @property
    def key(self) -> tuple[str, str]:
        return self.theory, self.slug


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
    allowed = {"status", "diagnostic", "failure_phase", "theorem_shape", "proof_rule_histogram", "notes"}
    extra = sorted(set(value) - allowed)
    require(not extra, f"{label} has unknown field(s): {', '.join(extra)}")
    require("status" in value, f"{label} is missing status")
    status = value["status"]
    require(status in V2_STATUSES, f"{label}.status must be one of {sorted(V2_STATUSES)}")
    for string_field in ("diagnostic", "theorem_shape", "notes"):
        if string_field in value:
            require_string(value[string_field], f"{label}.{string_field}", allow_empty=string_field == "notes")
    if "failure_phase" in value:
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


def validate_logic_inventory(data: object, accepted_logics: list[str]) -> list[str]:
    require(isinstance(data, dict), "logic inventory root must be an object")
    required = {"schema_version", "source", "accepted_logics", "excluded_logics"}
    extra = sorted(set(data) - required)
    missing = sorted(required - set(data))
    require(not extra, f"logic inventory has unknown field(s): {', '.join(extra)}")
    require(not missing, f"logic inventory is missing required field(s): {', '.join(missing)}")
    require(data.get("schema_version") == MANIFEST_SCHEMA_VERSION, "logic inventory schema_version must be 2")
    require_string(data["source"], "logic inventory source")
    packet_logics = require_string_list(data["accepted_logics"], "logic inventory accepted_logics")
    excluded_raw = data["excluded_logics"]
    require(isinstance(excluded_raw, list), "logic inventory excluded_logics must be a list")

    excluded: list[str] = []
    for index, item in enumerate(excluded_raw, 1):
        label = f"logic inventory excluded_logics[{index}]"
        require(isinstance(item, dict), f"{label} must be an object")
        required_item = {"logic", "category", "reason"}
        extra_item = sorted(set(item) - required_item)
        missing_item = sorted(required_item - set(item))
        require(not extra_item, f"{label} has unknown field(s): {', '.join(extra_item)}")
        require(not missing_item, f"{label} is missing required field(s): {', '.join(missing_item)}")
        excluded.append(require_string(item["logic"], f"{label}.logic"))
        require_string(item["category"], f"{label}.category")
        require_string(item["reason"], f"{label}.reason")

    require(len(set(packet_logics)) == len(packet_logics), "logic inventory accepted_logics has duplicates")
    require(len(set(excluded)) == len(excluded), "logic inventory excluded_logics has duplicates")
    overlap = sorted(set(packet_logics) & set(excluded))
    require(not overlap, f"logic inventory accepted/excluded overlap: {', '.join(overlap)}")
    documented = sorted(set(packet_logics) | set(excluded))
    require(
        documented == sorted(accepted_logics),
        "logic inventory does not exactly match SmtLib_Logics.sml accepted names plus exclusions",
    )
    return sorted(packet_logics)


def extract_structure_body(text: str, structure_name: str) -> str:
    marker = f"structure {structure_name} ="
    start = text.find(marker)
    if start < 0:
        raise AuditError(f"could not find {structure_name} structure in SMT-LIB theory source")
    next_section = text.find("\n  (*", start + len(marker))
    if next_section < 0:
        next_section = text.find("\nend  (* local *)", start + len(marker))
    require(next_section > start, f"could not find end of {structure_name} structure in SMT-LIB theory source")
    return text[start:next_section]


def extract_entry_region(body: str, list_name: str) -> str:
    start = body.find(f"val {list_name} = [")
    if start < 0:
        return ""
    if list_name == "tyentries":
        end_marker = "\n\n    val tmentries"
    else:
        end_marker = "\n\n    val tydict"
    end = body.find(end_marker, start)
    if end < 0:
        return ""
    return body[start:end]


def official_entries_from_region(region: str) -> list[tuple[str, tuple[str, ...]]]:
    entries: list[tuple[str, tuple[str, ...]]] = []
    pattern = re.compile(r'official_entry\s+"(?P<name>[^"]+)"')

    def matching_bracket(start: int) -> int:
        depth = 0
        in_string = False
        escaped = False
        for index in range(start, len(region)):
            char = region[index]
            if in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
                continue
            if char == '"':
                in_string = True
            elif char == "[":
                depth += 1
            elif char == "]":
                depth -= 1
                if depth == 0:
                    return index
        return -1

    def looks_like_declaration_list(strings: tuple[str, ...]) -> bool:
        return any(
            item.startswith("(")
            or item.startswith("#")
            or item.startswith("<")
            for item in strings
        )

    for match in pattern.finditer(region):
        name = match.group("name")
        search_from = match.end()
        while True:
            start = region.find("[", search_from)
            if start < 0:
                break
            end = matching_bracket(start)
            if end < 0:
                break
            declarations = tuple(re.findall(r'"([^"]+)"', region[start:end + 1]))
            if declarations and looks_like_declaration_list(declarations):
                entries.append((name, declarations))
                break
            search_from = end + 1
    return entries


HELPER_GENERATED_TERMS: dict[str, tuple[tuple[str, tuple[str, ...]], ...]] = {
    "Fixed_Size_BitVectors": (
        ("bvredand", ("(bvredand (_ BitVec m) Bool)",)),
        ("bvredor", ("(bvredor (_ BitVec m) Bool)",)),
    ),
    "UnicodeStrings": (
        ("str.at", ("(str.at String Int String)",)),
        ("str.suffixof", ("(str.suffixof String String Bool)",)),
        ("str.contains", ("(str.contains String String Bool)",)),
        ("re.++", ("(re.++ (RegLan String) (RegLan String) (RegLan String))",)),
        ("re.diff", ("(re.diff (RegLan String) (RegLan String) (RegLan String))",)),
    ),
    "Z3_Extensions": (
        ("seq.++", ("(seq.++ (Seq A) (Seq A) (Seq A) :left-assoc)",)),
        ("seq.len", ("(seq.len (Seq A) Int)",)),
        ("seq.extract", ("(seq.extract (Seq A) Int Int (Seq A))",)),
        ("seq.contains", ("(seq.contains (Seq A) (Seq A) Bool)",)),
        ("set.member", ("(set.member A (Set A) Bool)",)),
        ("set.insert", ("(set.insert A (Set A) (Set A))",)),
        ("set.union", ("(set.union (Set A) (Set A) (Set A) :left-assoc)",)),
        ("set.intersect", ("(set.intersect (Set A) (Set A) (Set A) :left-assoc)",)),
        ("set.minus", ("(set.minus (Set A) (Set A) (Set A))",)),
        ("set.subset", ("(set.subset (Set A) (Set A) Bool)",)),
        ("bag.union_disjoint", ("(bag.union_disjoint (Bag A) (Bag A) (Bag A) :left-assoc)",)),
        ("bag.union_max", ("(bag.union_max (Bag A) (Bag A) (Bag A) :left-assoc)",)),
        ("bag.inter_min", ("(bag.inter_min (Bag A) (Bag A) (Bag A) :left-assoc)",)),
        ("bag.difference_subtract", ("(bag.difference_subtract (Bag A) (Bag A) (Bag A))",)),
        ("bag.count", ("(bag.count A (Bag A) Int)",)),
    ),
}

HELPER_GENERATED_SORTS: dict[str, tuple[tuple[str, tuple[str, ...]], ...]] = {
    "Z3_Extensions": (
        ("Seq", ("(Seq Element)",)),
        ("Set", ("(Set Element)",)),
        ("Bag", ("(Bag Element)",)),
    ),
}


def theory_symbol_slug(kind: str, name: str, declarations: tuple[str, ...]) -> str:
    if kind == "sort":
        if name == "BitVec":
            return "bitvec"
        return name.lower().replace("_", "-")
    declaration = declarations[0] if declarations else ""
    symbol_slugs = {
        "=>": "implies",
        "=": "eq",
        "+": "plus",
        "+zero": "positive-zero",
        "-zero": "negative-zero",
        "+oo": "positive-infinity",
        "-oo": "negative-infinity",
        "*": "times",
        "**": "pow",
        "/": "div",
        "<=": "le",
        "<": "lt",
        ">=": "ge",
        ">": "gt",
        "to_real": "to-real",
        "to_int": "to-int",
        "is_int": "is-int",
        "zero_extend": "zero-extend",
        "sign_extend": "sign-extend",
        "rotate_left": "rotate-left",
        "rotate_right": "rotate-right",
        "ubv_to_int": "ubv-to-int",
        "sbv_to_int": "sbv-to-int",
        "int_to_bv": "int-to-bv",
        "<string literal>": "string-literal",
        "str.++": "str-concat",
        "str.<": "str-lt",
        "str.<=": "str-le",
        "str.is_digit": "str.is-digit",
        "str.to_code": "str.to-code",
        "str.from_code": "str.from-code",
        "str.to_int": "str.to-int",
        "str.from_int": "str.from-int",
        "str.to_re": "str.to-re",
        "str.in_re": "str.in-re",
        "str.replace_re": "str.replace-re",
        "str.replace_re_all": "str.replace-re-all",
        "re.++": "re-concat",
        "re.*": "re-star",
        "re.+": "re-plus",
        "re.^": "re-power",
        "seq.++": "seq-concat",
        "bag.union_disjoint": "bag.union-disjoint",
        "bag.union_max": "bag.union-max",
        "bag.inter_min": "bag.inter-min",
        "bag.difference_subtract": "bag.difference-subtract",
    }
    if name == "_":
        if declaration == "<decimal>":
            return "decimal"
        if declaration == "#b<binary>":
            return "binary-hex-literal"
        if declaration.startswith("((_ bv<numeral>"):
            return "decimal-literal"
        return "numeral"
    if name == "-":
        if re.match(r"^\(- (Int|Real) \1\)$", declaration):
            return "neg"
        return "sub"
    return symbol_slugs.get(name, name.lower().replace("_", "-"))


FLOATINGPOINT_MANUAL_TERMS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("roundNearestTiesToEven", ("(roundNearestTiesToEven RoundingMode)",)),
    ("RNE", ("(RNE RoundingMode)",)),
    ("roundNearestTiesToAway", ("(roundNearestTiesToAway RoundingMode)",)),
    ("RNA", ("(RNA RoundingMode)",)),
    ("roundTowardPositive", ("(roundTowardPositive RoundingMode)",)),
    ("RTP", ("(RTP RoundingMode)",)),
    ("roundTowardNegative", ("(roundTowardNegative RoundingMode)",)),
    ("RTN", ("(RTN RoundingMode)",)),
    ("roundTowardZero", ("(roundTowardZero RoundingMode)",)),
    ("RTZ", ("(RTZ RoundingMode)",)),
    ("+zero", ("((_ +zero eb sb) (_ FloatingPoint eb sb))",)),
    ("-zero", ("((_ -zero eb sb) (_ FloatingPoint eb sb))",)),
    ("+oo", ("((_ +oo eb sb) (_ FloatingPoint eb sb))",)),
    ("-oo", ("((_ -oo eb sb) (_ FloatingPoint eb sb))",)),
    ("NaN", ("((_ NaN eb sb) (_ FloatingPoint eb sb))",)),
    ("fp", ("(fp (_ BitVec 1) (_ BitVec eb) (_ BitVec (- sb 1)) (_ FloatingPoint eb sb))",)),
    ("fp.add", ("(fp.add RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.sub", ("(fp.sub RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.mul", ("(fp.mul RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.div", ("(fp.div RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.fma", ("(fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.sqrt", ("(fp.sqrt RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.roundToIntegral", ("(fp.roundToIntegral RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.rem", ("(fp.rem (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.min", ("(fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.max", ("(fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.abs", ("(fp.abs (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.neg", ("(fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",)),
    ("fp.leq", ("(fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)",)),
    ("fp.lt", ("(fp.lt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)",)),
    ("fp.geq", ("(fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)",)),
    ("fp.gt", ("(fp.gt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)",)),
    ("fp.eq", ("(fp.eq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool)",)),
    ("fp.isNormal", ("(fp.isNormal (_ FloatingPoint eb sb) Bool)",)),
    ("fp.isSubnormal", ("(fp.isSubnormal (_ FloatingPoint eb sb) Bool)",)),
    ("fp.isZero", ("(fp.isZero (_ FloatingPoint eb sb) Bool)",)),
    ("fp.isInfinite", ("(fp.isInfinite (_ FloatingPoint eb sb) Bool)",)),
    ("fp.isNaN", ("(fp.isNaN (_ FloatingPoint eb sb) Bool)",)),
    ("fp.isNegative", ("(fp.isNegative (_ FloatingPoint eb sb) Bool)",)),
    ("fp.isPositive", ("(fp.isPositive (_ FloatingPoint eb sb) Bool)",)),
    ("to_fp", ("((_ to_fp eb sb) ... (_ FloatingPoint eb sb))",)),
    ("to_fp_unsigned", ("((_ to_fp_unsigned eb sb) ... (_ FloatingPoint eb sb))",)),
    ("fp.to_ubv", ("((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))",)),
    ("fp.to_sbv", ("((_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))",)),
    ("fp.to_real", ("(fp.to_real (_ FloatingPoint eb sb) Real)",)),
)


def floatingpoint_terms_from_body(body: str) -> list[tuple[str, tuple[str, ...]]]:
    entries: list[tuple[str, tuple[str, ...]]] = []
    for name, declarations in FLOATINGPOINT_MANUAL_TERMS:
        if name in body:
            entries.append((name, declarations))
    return entries


def parse_dictionary_theory_symbols(path: Path) -> list[TheoryMetadataSymbol]:
    text = path.read_text(encoding="utf-8")
    symbols: dict[tuple[str, str], TheoryMetadataSymbol] = {}

    for theory in (
        "Core",
        "Ints",
        "Reals",
        "UnicodeStrings",
        "ArraysEx",
        "Fixed_Size_BitVectors",
        "FloatingPoint",
        "Z3_Extensions",
    ):
        body = extract_structure_body(text, theory)
        for kind, list_name in (("sort", "tyentries"), ("term", "tmentries")):
            for name, declarations in official_entries_from_region(extract_entry_region(body, list_name)):
                symbol = TheoryMetadataSymbol(
                    theory=theory,
                    slug=theory_symbol_slug(kind, name, declarations),
                    kind=kind,
                    name=name,
                    declarations=declarations,
                )
                symbols[symbol.key] = symbol
        for name, declarations in HELPER_GENERATED_SORTS.get(theory, ()):
            if name in body:
                symbol = TheoryMetadataSymbol(
                    theory=theory,
                    slug=theory_symbol_slug("sort", name, declarations),
                    kind="sort",
                    name=name,
                    declarations=declarations,
                )
                symbols[symbol.key] = symbol
        for name, declarations in HELPER_GENERATED_TERMS.get(theory, ()):
            if name in body:
                symbol = TheoryMetadataSymbol(
                    theory=theory,
                    slug=theory_symbol_slug("term", name, declarations),
                    kind="term",
                    name=name,
                    declarations=declarations,
                )
                symbols[symbol.key] = symbol
        if theory == "FloatingPoint":
            for name, declarations in floatingpoint_terms_from_body(body):
                symbol = TheoryMetadataSymbol(
                    theory="FloatingPoint",
                    slug=theory_symbol_slug("term", name, declarations),
                    kind="term",
                    name=name,
                    declarations=declarations,
                )
                symbols[symbol.key] = symbol

    reals_ints_body = extract_structure_body(text, "Reals_Ints")
    for name, declarations in official_entries_from_region(reals_ints_body):
        symbol = TheoryMetadataSymbol(
            theory="Reals_Ints",
            slug=theory_symbol_slug("term", name, declarations),
            kind="term",
            name=name,
            declarations=declarations,
        )
        symbols[symbol.key] = symbol

    return [symbols[key] for key in sorted(symbols)]


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


def is_logic_case_kind(case: dict[str, object], logic: str, kind: str) -> bool:
    if case.get("class") != "logic" or case.get("logic") != logic:
        return False
    expected_feature = f"logic-case:{kind}"
    return any(feature == expected_feature for feature in case.get("features", []) if isinstance(feature, str))


def case_has_expected_modes(case: dict[str, object], modes: set[str]) -> bool:
    case_modes = {str(mode) for mode in case.get("modes", [])}
    expected_modes = set()
    expected = case.get("expected")
    if isinstance(expected, dict):
        expected_modes = {str(mode) for mode in expected}
    return modes <= case_modes and modes <= expected_modes


def is_string_regex_or_extension_theory_case(case: dict[str, object]) -> bool:
    if case.get("class") != "theory":
        return False
    features = {feature for feature in case.get("features", []) if isinstance(feature, str)}
    return bool(features & {"theory:UnicodeStrings", "theory:Z3_Extensions"})


def case_has_all_supported_versions(case: dict[str, object]) -> bool:
    return set(str(version) for version in case.get("versions", [])) == {
        "2.19.1",
        "4.11.2",
        "4.12.4",
        "4.13.0",
        "4.14.1",
        "4.15.3",
    }


def case_has_sat_no_theorem_diagnostic(case: dict[str, object]) -> bool:
    expected = case.get("expected")
    if not isinstance(expected, dict):
        return False
    z3_tac = expected.get("z3-tac")
    if not isinstance(z3_tac, dict):
        return False
    diagnostic = str(z3_tac.get("diagnostic", "")).lower()
    return z3_tac.get("status") == "fail" and "no" in diagnostic and "theorem" in diagnostic


def is_theory_case_kind(case: dict[str, object], symbol: TheoryMetadataSymbol, kind: str) -> bool:
    if case.get("class") != "theory":
        return False
    features = {feature for feature in case.get("features", []) if isinstance(feature, str)}
    return {
        f"theory:{symbol.theory}",
        f"theory-entry:{symbol.theory}:{symbol.slug}",
        f"theory-case:{kind}",
    } <= features


def audit_theory_symbols(cases: list[dict[str, object]], symbols: list[TheoryMetadataSymbol]) -> list[Issue]:
    issues: list[Issue] = []
    for symbol in symbols:
        missing_kinds = sorted(
            kind
            for kind in THEORY_REQUIRED_CASE_KINDS
            if not any(is_theory_case_kind(case, symbol, kind) for case in cases)
        )
        if missing_kinds:
            issues.append(
                Issue(
                    code="missing_theory_symbol_case",
                    category="missing_complete_evidence",
                    subject=f"theory/{symbol.theory}/{symbol.slug}",
                    message="SMT-LIB theory metadata entry lacks required v2 symbol case coverage",
                    details={
                        "theory": symbol.theory,
                        "kind": symbol.kind,
                        "name": symbol.name,
                        "declarations": list(symbol.declarations),
                        "missing_case_kinds": missing_kinds,
                    },
                )
            )
    return issues


def audit_required_theory_metadata(symbols: list[TheoryMetadataSymbol]) -> list[Issue]:
    issues: list[Issue] = []
    actual = {
        (symbol.theory, symbol.kind, symbol.name)
        for symbol in symbols
    }
    for theory, by_kind in sorted(REQUIRED_THEORY_METADATA.items()):
        for kind, names in sorted(by_kind.items()):
            missing = sorted(
                name
                for name in names
                if (theory, kind, name) not in actual
            )
            if missing:
                issues.append(
                    Issue(
                        code="missing_theory_dictionary_metadata",
                        category="missing_complete_evidence",
                        subject=f"theory/{theory}/{kind}",
                        message="required theory dictionary metadata is absent",
                        details={
                            "theory": theory,
                            "kind": kind,
                            "missing_names": missing,
                            "files": ["src/HolSmt/SmtLib_Theories.sml"],
                        },
                    )
                )
    return issues


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


def command_names_from_coverage_item(item: str) -> list[str]:
    return [part.strip().lower() for part in item.split(",") if part.strip()]


def case_has_complete_command_evidence(case: dict[str, object], command: str) -> bool:
    if case.get("class") != "command" or not is_case_complete_evidence(case):
        return False
    tokens = normalized_feature_tokens(case)
    return command in tokens or f"command:{command}" in tokens


def missing_v2_command_evidence(row: CoverageRow, cases: Iterable[dict[str, object]]) -> list[str]:
    commands = command_names_from_coverage_item(row.item)
    case_list = list(cases)
    return [
        command
        for command in commands
        if not any(case_has_complete_command_evidence(case, command) for case in case_list)
    ]


def row_has_v2_evidence(row: CoverageRow, cases: Iterable[dict[str, object]]) -> bool:
    if row.section == "commands":
        return not missing_v2_command_evidence(row, cases)
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

    manifest_logics = set(logic_cases)
    expected_logics = set(accepted_logics)
    missing_manifest_logics = sorted(expected_logics - manifest_logics)
    extra_manifest_logics = sorted(manifest_logics - expected_logics)
    if missing_manifest_logics or extra_manifest_logics:
        issues.append(
            Issue(
                code="logic_manifest_mismatch",
                category="missing_complete_evidence",
                subject="logic-manifest",
                message="accepted logic names and v2 manifest logic names differ",
                details={
                    "missing": missing_manifest_logics,
                    "extra": extra_manifest_logics,
                },
            )
        )

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
            issues.append(
                Issue(
                    code="missing_logic_unsat_proof_case",
                    category="missing_complete_evidence",
                    subject=f"logic/{logic}",
                    message="accepted logic lacks an UNSAT proof case for the supported Z3 version matrix",
                    details={"logic": logic},
                )
            )
            issues.append(
                Issue(
                    code="missing_sat_no_theorem_diagnostic",
                    category="missing_complete_evidence",
                    subject=f"logic/{logic}",
                    message="accepted logic lacks a SAT case with a checked no-theorem diagnostic expectation",
                    details={"logic": logic},
                )
            )
            continue

        unsat_cases = [
            case for case in logic_cases[logic]
            if is_logic_case_kind(case, logic, "unsat-proof")
        ]
        if not unsat_cases:
            issues.append(
                Issue(
                    code="missing_logic_unsat_proof_case",
                    category="missing_complete_evidence",
                    subject=f"logic/{logic}",
                    message="accepted logic lacks an UNSAT proof case for the supported Z3 version matrix",
                    details={"logic": logic},
                )
            )
        else:
            complete_unsat_cases = [
                case for case in unsat_cases
                if case_has_expected_modes(case, UNSAT_REQUIRED_MODES)
                and case_has_all_supported_versions(case)
            ]
            if not complete_unsat_cases:
                issues.append(
                    Issue(
                        code="logic_unsat_proof_schedule_mismatch",
                        category="missing_complete_evidence",
                        subject=f"logic/{logic}",
                        message="logic UNSAT proof case is not scheduled for required proof modes and all supported Z3 versions",
                        details={
                            "logic": logic,
                            "case_ids": [str(case["id"]) for case in unsat_cases],
                        },
                    )
                )

        sat_cases = [
            case for case in logic_cases[logic]
            if is_logic_case_kind(case, logic, "sat")
        ]
        if not any(case_has_sat_no_theorem_diagnostic(case) for case in sat_cases):
            issues.append(
                Issue(
                    code="missing_sat_no_theorem_diagnostic",
                    category="missing_complete_evidence",
                    subject=f"logic/{logic}",
                    message="accepted logic lacks a SAT case with a checked no-theorem diagnostic expectation",
                    details={"logic": logic},
                )
            )

    for case in cases:
        case_id = str(case["id"])
        if is_string_regex_or_extension_theory_case(case):
            modes = {str(mode) for mode in case["modes"]}
            expected_modes = {str(mode) for mode in case["expected"]}
            non_parser_modes = sorted(modes - {"parser-only"})
            non_parser_expected = sorted(expected_modes - {"parser-only"})
            if not non_parser_modes or not non_parser_expected:
                issues.append(
                    Issue(
                        code="parse_only_string_regex_extension_coverage",
                        category="missing_complete_evidence",
                        subject=f"case/{case_id}",
                        message="string/regex and Z3 extension theory rows must not be counted as parser-only coverage",
                        details={
                            "modes": sorted(modes),
                            "expected_modes": sorted(expected_modes),
                            "non_parser_modes": non_parser_modes,
                            "non_parser_expected": non_parser_expected,
                        },
                    )
                )

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
        if row.section == "commands":
            missing_commands = missing_v2_command_evidence(row, cases)
            if missing_commands:
                issues.append(
                    Issue(
                        code="missing_command_v2_evidence",
                        category="missing_complete_evidence",
                        subject=f"{row.section}/{row.item} ({row.row_class})",
                        message="complete-required command row has no v2 command test evidence",
                        details={"missing_commands": missing_commands},
                    )
                )
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


def audit_floatingpoint_solver_proof_evidence(cases: list[dict[str, object]]) -> list[Issue]:
    issues: list[Issue] = []
    fp_cases = [
        case
        for case in cases
        if case.get("class") == "theory"
        and "theory:FloatingPoint" in {feature for feature in case.get("features", []) if isinstance(feature, str)}
    ]
    for case in fp_cases:
        case_id = str(case.get("id", ""))
        features = {feature for feature in case.get("features", []) if isinstance(feature, str)}
        case_kinds = [feature.removeprefix("theory-case:") for feature in features if feature.startswith("theory-case:")]
        if not case_kinds:
            continue
        kind = case_kinds[0]
        if kind == "sat":
            required_modes = {"z3-oracle", "z3-tac"}
        elif kind == "unsat-proof":
            required_modes = {"z3-oracle", "proof-parse", "proof-replay", "z3-tac"}
        elif kind == "boundary":
            required_modes = {"z3-oracle"}
        elif kind == "type-error":
            required_modes = {"typecheck-only", "z3-tac"}
        else:
            continue
        if not case_has_expected_modes(case, required_modes):
            issues.append(
                Issue(
                    code="floatingpoint_parser_only_evidence",
                    category="missing_complete_evidence",
                    subject=case_id,
                    message="FloatingPoint theory case lacks required solver/proof modes; parser/typecheck-only FP evidence is not complete conformance evidence",
                    details={
                        "case_kind": kind,
                        "required_modes": sorted(required_modes),
                    },
                )
            )
            continue
        if kind in {"sat", "unsat-proof", "boundary"} and "red" not in case_expected_statuses(case):
            issues.append(
                Issue(
                    code="floatingpoint_missing_red_obligation",
                    category="missing_complete_evidence",
                    subject=case_id,
                    message="FloatingPoint solver/proof case must remain red until HOL translation, solver behavior, proof replay, and theorem reconstruction are implemented",
                    details={"case_kind": kind},
                )
            )
    return issues


def build_report(
    *,
    manifest_path: Path,
    logic_source: Path,
    theory_source: Path,
    logics_json_path: Path | None,
    coverage_path: Path | None,
    coverage_manifest_path: Path | None,
) -> dict[str, object]:
    manifest = load_json(manifest_path)
    cases = validate_v2_manifest(manifest)
    accepted_logics = parse_accepted_logics(logic_source)
    theory_symbols = parse_dictionary_theory_symbols(theory_source)
    packet_logics = accepted_logics
    excluded_logics: list[str] = []
    if logics_json_path is not None and logics_json_path.exists():
        logics_json = load_json(logics_json_path)
        packet_logics = validate_logic_inventory(logics_json, accepted_logics)
        assert isinstance(logics_json, dict)
        excluded_raw = logics_json.get("excluded_logics", [])
        if isinstance(excluded_raw, list):
            excluded_logics = [
                str(item["logic"])
                for item in excluded_raw
                if isinstance(item, dict) and isinstance(item.get("logic"), str)
            ]
    coverage_rows = load_coverage_rows(coverage_path, coverage_manifest_path)
    issues = audit_cases(cases, packet_logics)
    issues.extend(audit_required_theory_metadata(theory_symbols))
    issues.extend(audit_theory_symbols(cases, theory_symbols))
    issues.extend(audit_floatingpoint_solver_proof_evidence(cases))
    issues.extend(audit_coverage(coverage_rows, cases))

    category_counts: dict[str, int] = {}
    for issue in issues:
        category_counts[issue.category] = category_counts.get(issue.category, 0) + 1
    core_arithmetic_theory_symbol_count = sum(
        1
        for symbol in theory_symbols
        if symbol.theory in {"Core", "Ints", "Reals", "Reals_Ints"}
    )

    return {
        "schema": SCHEMA,
        "inputs": {
            "manifest": str(manifest_path),
            "logic_source": str(logic_source),
            "theory_source": str(theory_source),
            "logics_json": str(logics_json_path) if logics_json_path is not None else None,
            "coverage": str(coverage_path) if coverage_path is not None else None,
            "coverage_manifest": str(coverage_manifest_path) if coverage_manifest_path is not None else None,
        },
        "summary": {
            "accepted_logic_count": len(accepted_logics),
            "logic_packet_count": len(packet_logics),
            "dictionary_theory_symbol_count": len(theory_symbols),
            "core_arithmetic_theory_symbol_count": core_arithmetic_theory_symbol_count,
            "v2_case_count": len(cases),
            "coverage_row_count": len({row.key for row in coverage_rows}),
            "issue_count": len(issues),
            "category_counts": category_counts,
            "passed": not issues,
        },
        "accepted_logics": accepted_logics,
        "logic_packet_logics": packet_logics,
        "excluded_logics": excluded_logics,
        "issues": [issue.to_json() for issue in issues],
    }


def print_text_summary(report: dict[str, object]) -> None:
    summary = report["summary"]
    assert isinstance(summary, dict)
    print("complete conformance audit")
    print(f"accepted logics: {summary['accepted_logic_count']}")
    if "logic_packet_count" in summary:
        print(f"logic packet logics: {summary['logic_packet_count']}")
    if "dictionary_theory_symbol_count" in summary:
        print(f"dictionary theory symbols: {summary['dictionary_theory_symbol_count']}")
    elif "core_arithmetic_theory_symbol_count" in summary:
        print(f"core arithmetic theory symbols: {summary['core_arithmetic_theory_symbol_count']}")
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
    parser.add_argument("--theory-source", type=Path, default=DEFAULT_THEORY_SOURCE)
    parser.add_argument("--logics-json", type=Path, default=DEFAULT_LOGICS_JSON)
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
    logics_json_path = args.logics_json
    if args.logic_source != DEFAULT_LOGIC_SOURCE and args.logics_json == DEFAULT_LOGICS_JSON:
        logics_json_path = None
    try:
        report = build_report(
            manifest_path=args.manifest,
            logic_source=args.logic_source,
            theory_source=args.theory_source,
            logics_json_path=logics_json_path,
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
