#!/usr/bin/env python3
"""Generate the HolSmt complete SMT-LIB conformance corpus skeleton."""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping, Sequence


CORPUS_DIR = Path(__file__).resolve().parent
TOOLS_DIR = CORPUS_DIR.parents[1]
DEFAULT_MANIFEST = CORPUS_DIR / "manifest.json"
DEFAULT_LOGIC_SOURCE = TOOLS_DIR.parent / "SmtLib_Logics.sml"
DEFAULT_LOGICS_JSON = CORPUS_DIR / "logics.json"
MANIFEST_SCHEMA_VERSION = "2"

SUPPORTED_Z3_VERSIONS = (
    "2.19.1",
    "4.11.2",
    "4.12.4",
    "4.13.0",
    "4.14.1",
    "4.15.3",
)

STANDARDS = ("SMT-LIB-2.7", "SMT-LIB-3", "Z3-extension")
CASE_CLASSES = (
    "command",
    "theory",
    "logic",
    "proof-rule",
    "soundness-audit",
    "external-benchmark",
)
MODES = (
    "parser-only",
    "typecheck-only",
    "z3-oracle",
    "proof-parse",
    "proof-replay",
    "z3-tac",
)
EXPECTED_STATUSES = ("pass", "fail", "unsupported", "red")
FAILURE_PHASES = (
    "parser",
    "typecheck",
    "translation",
    "solver",
    "proof-parse",
    "proof-replay",
    "theorem-shape",
    "oracle-tag",
    "version-drift",
)
SOURCE_KINDS = (
    "SMT-LIB-standard",
    "SMT-LIB-theory",
    "SMT-LIB-logic",
    "Z3-extension",
    "Z3-proof",
    "external-benchmark",
    "HolSmt-internal",
)

GENERATED_OBLIGATION_NOTES = "Generated red seed row; keep red until executable evidence is added."

CLASS_DIRECTORIES = {
    "command": "commands",
    "theory": "theories",
    "logic": "logics",
    "proof-rule": "proof_rules",
    "soundness-audit": "soundness",
    "external-benchmark": "external",
}

DOMAIN_CLASSES = {
    "commands": "command",
    "theories": "theory",
    "logics": "logic",
    "proof-rules": "proof-rule",
    "soundness": "soundness-audit",
    "external": "external-benchmark",
}

EXCLUDED_ACCEPTED_LOGICS = {
    "ALL": {
        "category": "HolSmt-internal",
        "reason": "Aggregate parse dictionary accepted by HolSmt, not an SMT-LIB logic packet target.",
    },
}

UNDERREPRESENTED_LOGICS = {
    "ALIRA",
    "ANIA",
    "ANIRA",
    "AUFLIA",
    "AUFLIRA",
    "AUFNIRA",
    "BV",
    "QF_ABV",
    "QF_ALRA",
    "QF_ANIA",
    "QF_ANRA",
    "QF_AUFLIA",
    "QF_AUFNIA",
    "QF_AUFNIRA",
    "QF_BVFP",
    "QF_FPBV",
    "QF_SNIA",
    "QF_UFBV",
    "QF_UFBVFP",
    "QF_UFFP",
    "UFBV",
}

SPARSE_LOGICS = {
    "QF_AUFBV",
    "QF_AUFLIRA",
    "QF_FP",
    "QF_S",
    "QF_SLIA",
}

INT_REAL_COERCION_LOGICS = {
    "ALIRA",
    "ANIRA",
    "AUFLIRA",
    "AUFNIRA",
    "QF_AUFLIRA",
    "QF_AUFNIRA",
    "QF_LIRA",
    "QF_NIRA",
    "QF_UFLIRA",
    "QF_UFNIRA",
}


class GeneratorError(ValueError):
    pass


@dataclass(frozen=True)
class GeneratedCase:
    entry: dict[str, object]
    script: str

    @property
    def case_id(self) -> str:
        return str(self.entry["id"])

    @property
    def file(self) -> str:
        return str(self.entry["file"])


@dataclass(frozen=True)
class CommandGroup:
    slug: str
    commands: tuple[str, ...]
    positive_script: str
    negative_script: str
    state_script: str
    reconstruction_script: str
    negative_diagnostic: str
    negative_phase: str
    reconstruction_applies: bool
    reconstruction_diagnostic: str
    reconstruction_phase: str
    obligation_files: tuple[str, ...]
    obligation_notes: str = GENERATED_OBLIGATION_NOTES
    red_when_reconstruction_not_applicable: bool = False
    reconstruction_unsat_core: str | None = None
    reconstruction_unsat_assumptions: str | None = None


@dataclass(frozen=True)
class TheorySymbol:
    theory: str
    slug: str
    kind: str
    name: str
    logic: str
    declarations: tuple[str, ...]
    sat_script: str
    unsat_proof_script: str
    type_error_script: str
    boundary_script: str
    behavior_features: tuple[str, ...] = ()


@dataclass(frozen=True)
class ScriptedCase:
    slug: str
    script: str
    modes: tuple[str, ...]
    expected: dict[str, dict[str, object]]
    features: tuple[str, ...]
    implementation_feature: str | None = None
    implementation_files: tuple[str, ...] = ()
    implementation_phase: str | None = None
    logic: str = "QF_UF"
    standard: str = "SMT-LIB-2.7"
    source_kind: str = "SMT-LIB-theory"
    source_reference: str = ""


def slug(value: str) -> str:
    result = re.sub(r"[^A-Za-z0-9]+", "_", value.lower()).strip("_")
    result = re.sub(r"_+", "_", result)
    if not result:
        raise GeneratorError("cannot derive a slug from an empty value")
    return result


def deterministic_case_id(row_class: str, feature: str) -> str:
    require_choice(row_class, "class", CASE_CLASSES)
    feature_slug = slug(feature).replace("_", "-")
    class_slug = slug(row_class).replace("_", "-")
    if feature_slug.startswith(f"{class_slug}-"):
        feature_slug = feature_slug[len(class_slug) + 1 :]
    return f"{row_class}:{feature_slug}"


def deterministic_case_file(row_class: str, case_id: str) -> str:
    require_choice(row_class, "class", CASE_CLASSES)
    return f"cases/{CLASS_DIRECTORIES[row_class]}/{slug(case_id)}.smt2"


def require_string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise GeneratorError(f"{label} must be a non-empty string")
    return value


def require_string_list(value: Sequence[str], label: str) -> list[str]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        raise GeneratorError(f"{label} must be a sequence of strings")
    result = [require_string(item, f"{label} item") for item in value]
    if not result:
        raise GeneratorError(f"{label} must not be empty")
    if len(set(result)) != len(result):
        raise GeneratorError(f"{label} must not contain duplicates")
    return result


def require_choice(value: str, label: str, choices: Sequence[str]) -> str:
    value = require_string(value, label)
    if value not in choices:
        raise GeneratorError(f"{label} must be one of {', '.join(choices)}")
    return value


def expected_result(
    status: str,
    *,
    diagnostic: str | None = None,
    failure_phase: str | None = None,
    theorem_shape: str | None = None,
    proof_rule_histogram: Mapping[str, int] | None = None,
    notes: str | None = None,
    unsat_core: str | None = None,
    unsat_assumptions: str | None = None,
) -> dict[str, object]:
    require_choice(status, "expected status", EXPECTED_STATUSES)
    result: dict[str, object] = {"status": status}
    if diagnostic is not None:
        result["diagnostic"] = require_string(diagnostic, "diagnostic")
    if failure_phase is not None:
        result["failure_phase"] = require_choice(failure_phase, "failure_phase", FAILURE_PHASES)
    if theorem_shape is not None:
        result["theorem_shape"] = require_string(theorem_shape, "theorem_shape")
    if proof_rule_histogram is not None:
        histogram: dict[str, int] = {}
        for rule, count in sorted(proof_rule_histogram.items()):
            require_string(rule, "proof_rule_histogram key")
            if not isinstance(count, int) or count < 0:
                raise GeneratorError("proof_rule_histogram counts must be non-negative integers")
            histogram[rule] = count
        result["proof_rule_histogram"] = histogram
    if unsat_core is not None:
        result["unsat_core"] = require_string(unsat_core, "unsat_core")
    if unsat_assumptions is not None:
        result["unsat_assumptions"] = require_string(unsat_assumptions, "unsat_assumptions")
    if notes is not None:
        result["notes"] = notes
    return result


def implementation_obligation(
    *,
    files: Sequence[str],
    feature: str,
    test_ids: Sequence[str],
    failure_phase: str,
    notes: str | None = None,
) -> dict[str, object]:
    require_choice(failure_phase, "failure_phase", FAILURE_PHASES)
    obligation: dict[str, object] = {
        "files": sorted(require_string_list(files, "implementation_obligation.files")),
        "feature": require_string(feature, "implementation_obligation.feature"),
        "test_ids": sorted(require_string_list(test_ids, "implementation_obligation.test_ids")),
        "failure_phase": failure_phase,
    }
    if notes is not None:
        obligation["notes"] = notes
    return obligation


def source(kind: str, reference: str, *, url: str | None = None, notes: str | None = None) -> dict[str, object]:
    require_choice(kind, "source.kind", SOURCE_KINDS)
    result: dict[str, object] = {
        "kind": kind,
        "reference": require_string(reference, "source.reference"),
    }
    if url is not None:
        result["url"] = require_string(url, "source.url")
    if notes is not None:
        result["notes"] = notes
    return result


def parse_accepted_logics(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    match = re.search(
        r"fun\s+parsedicts_of_logic\s*\([^)]*\)\s*=\s*case\s+logic\s+of(?P<body>.*?)"
        r"\n\s*\(\*\s*returns the symbol metadata",
        text,
        flags=re.DOTALL,
    )
    if match is None:
        raise GeneratorError(f"could not find parsedicts_of_logic case expression in {path}")
    logics = re.findall(r'"([A-Z][A-Z0-9_]*)"\s*=>', match.group("body"))
    if not logics:
        raise GeneratorError(f"no accepted logic names found in {path}")
    return sorted(set(logics))


def logic_packet_logics(logic_source: Path = DEFAULT_LOGIC_SOURCE) -> list[str]:
    accepted = parse_accepted_logics(logic_source)
    return [logic for logic in accepted if logic not in EXCLUDED_ACCEPTED_LOGICS]


def logics_manifest(logic_source: Path = DEFAULT_LOGIC_SOURCE) -> dict[str, object]:
    accepted = parse_accepted_logics(logic_source)
    packet_logics = [logic for logic in accepted if logic not in EXCLUDED_ACCEPTED_LOGICS]
    excluded = [
        {"logic": logic, **EXCLUDED_ACCEPTED_LOGICS[logic]}
        for logic in accepted
        if logic in EXCLUDED_ACCEPTED_LOGICS
    ]
    return {
        "schema_version": MANIFEST_SCHEMA_VERSION,
        "source": "src/HolSmt/SmtLib_Logics.sml",
        "accepted_logics": packet_logics,
        "excluded_logics": excluded,
    }


def manifest_entry(
    *,
    case_id: str,
    file: str,
    logic: str,
    standard: str,
    row_class: str,
    features: Sequence[str],
    modes: Sequence[str],
    versions: Sequence[str],
    expected: Mapping[str, Mapping[str, object]],
    implementation_obligation: Mapping[str, object] | None,
    source: Mapping[str, object],
) -> dict[str, object]:
    case_id = require_string(case_id, "id")
    if re.match(r"^[A-Za-z0-9][A-Za-z0-9_.:-]*$", case_id) is None:
        raise GeneratorError(f"id has invalid syntax: {case_id}")
    file = require_string(file, "file")
    if re.match(r"^cases/(commands|theories|logics|proof_rules|soundness|external)/[^/].*[.]smt2$", file) is None:
        raise GeneratorError(f"file has invalid corpus path: {file}")
    require_choice(standard, "standard", STANDARDS)
    require_choice(row_class, "class", CASE_CLASSES)
    features_list = sorted(require_string_list(features, "features"))
    modes_raw = require_string_list(modes, "modes")
    versions_raw = require_string_list(versions, "versions")
    for mode in modes_raw:
        require_choice(mode, "mode", MODES)
    for version in versions_raw:
        require_choice(version, "version", SUPPORTED_Z3_VERSIONS)
    modes_list = sorted(modes_raw, key=MODES.index)
    versions_list = sorted(versions_raw, key=SUPPORTED_Z3_VERSIONS.index)

    if not isinstance(expected, Mapping) or not expected:
        raise GeneratorError("expected must be a non-empty mapping")
    expected_result_by_mode: dict[str, dict[str, object]] = {}
    for mode in modes_list:
        if mode not in expected:
            raise GeneratorError(f"expected is missing required mode {mode}")
    expected_items = []
    for mode, value in expected.items():
        require_choice(mode, "expected mode", MODES)
        expected_items.append((mode, value))
    for mode, value in sorted(expected_items, key=lambda item: MODES.index(item[0])):
        if mode not in modes_list:
            raise GeneratorError(f"expected mode {mode} is not listed in modes")
        if not isinstance(value, Mapping):
            raise GeneratorError(f"expected[{mode}] must be an object")
        status = require_choice(str(value.get("status", "")), f"expected[{mode}].status", EXPECTED_STATUSES)
        expected_result_by_mode[mode] = dict(value)
        expected_result_by_mode[mode]["status"] = status

    red_modes = [
        mode
        for mode, value in expected_result_by_mode.items()
        if value.get("status") == "red"
    ]
    if red_modes and implementation_obligation is None:
        raise GeneratorError(
            "red expected results require implementation_obligation metadata "
            f"({', '.join(red_modes)})"
        )
    if not red_modes and implementation_obligation is not None:
        raise GeneratorError("implementation_obligation must be null when no expected result is red")

    return {
        "id": case_id,
        "file": file,
        "logic": require_string(logic, "logic"),
        "standard": standard,
        "class": row_class,
        "features": features_list,
        "modes": modes_list,
        "versions": versions_list,
        "expected": expected_result_by_mode,
        "implementation_obligation": dict(implementation_obligation) if implementation_obligation is not None else None,
        "source": dict(source),
    }


def red_sample(
    *,
    row_class: str,
    feature: str,
    logic: str,
    standard: str,
    modes: Sequence[str],
    files: Sequence[str],
    failure_phase: str,
    source_info: Mapping[str, object],
    script: str,
    diagnostic: str,
    theorem_shape: str | None = None,
    proof_rule_histogram: Mapping[str, int] | None = None,
) -> GeneratedCase:
    case_id = deterministic_case_id(row_class, feature)
    expected = {
        mode: expected_result(
            "red",
            diagnostic=diagnostic,
            theorem_shape=theorem_shape if mode == "z3-tac" else None,
            proof_rule_histogram=proof_rule_histogram if mode in {"proof-parse", "proof-replay"} else None,
        )
        for mode in modes
    }
    entry = manifest_entry(
        case_id=case_id,
        file=deterministic_case_file(row_class, case_id),
        logic=logic,
        standard=standard,
        row_class=row_class,
        features=[feature],
        modes=modes,
        versions=SUPPORTED_Z3_VERSIONS,
        expected=expected,
        implementation_obligation=implementation_obligation(
            files=files,
            feature=feature,
            test_ids=[case_id],
            failure_phase=failure_phase,
            notes=GENERATED_OBLIGATION_NOTES,
        ),
        source=source_info,
    )
    return GeneratedCase(entry=entry, script=script)


def pass_sample(
    *,
    row_class: str,
    feature: str,
    logic: str,
    standard: str,
    modes: Sequence[str],
    source_info: Mapping[str, object],
    script: str,
    theorem_shape: str | None = None,
    proof_rule_histogram: Mapping[str, int] | None = None,
) -> GeneratedCase:
    case_id = deterministic_case_id(row_class, feature)
    expected = {
        mode: expected_result(
            "pass",
            theorem_shape=theorem_shape if mode == "z3-tac" else None,
            proof_rule_histogram=proof_rule_histogram if mode in {"proof-parse", "proof-replay"} else None,
        )
        for mode in modes
    }
    entry = manifest_entry(
        case_id=case_id,
        file=deterministic_case_file(row_class, case_id),
        logic=logic,
        standard=standard,
        row_class=row_class,
        features=[feature],
        modes=modes,
        versions=SUPPORTED_Z3_VERSIONS,
        expected=expected,
        implementation_obligation=None,
        source=source_info,
    )
    return GeneratedCase(entry=entry, script=script)


PROOF_RULE_SCRIPT = (
    "(set-option :produce-proofs true)\n"
    "(set-logic QF_UF)\n"
    "(assert false)\n"
    "(check-sat)\n"
    "(get-proof)\n"
)


@dataclass(frozen=True)
class ProofRuleObligation:
    rule: str
    file_slug: str
    diagnostic: str
    notes: str
    behavior: str


TH_LEMMA_PROOF_RULE_OBLIGATIONS: tuple[ProofRuleObligation, ...] = (
    ProofRuleObligation(
        rule="th-lemma-datatype",
        file_slug="th_lemma_datatype",
        diagnostic="datatype th-lemma replay is diagnostic-only",
        notes=(
            "Diagnostic-only synthetic coverage exists; keep this row red until "
            "checked replay and real proof-corpus evidence are added."
        ),
        behavior="diagnostic-only",
    ),
    ProofRuleObligation(
        rule="th-lemma-fp",
        file_slug="th_lemma_fp",
        diagnostic="floating-point th-lemma replay is diagnostic-only",
        notes=(
            "Diagnostic-only synthetic coverage exists; keep this row red until "
            "checked replay and real proof-corpus evidence are added."
        ),
        behavior="diagnostic-only",
    ),
    ProofRuleObligation(
        rule="th-lemma-regexp",
        file_slug="th_lemma_regexp",
        diagnostic="regular-expression th-lemma replay is diagnostic-only",
        notes=(
            "Diagnostic-only synthetic coverage exists; keep this row red until "
            "checked replay and real proof-corpus evidence are added."
        ),
        behavior="diagnostic-only",
    ),
    ProofRuleObligation(
        rule="th-lemma-seq",
        file_slug="th_lemma_seq",
        diagnostic="sequence th-lemma replay is diagnostic-only",
        notes=(
            "Diagnostic-only synthetic coverage exists; keep this row red until "
            "checked replay and real proof-corpus evidence are added."
        ),
        behavior="diagnostic-only",
    ),
    ProofRuleObligation(
        rule="th-lemma-string",
        file_slug="th_lemma_string",
        diagnostic="string th-lemma replay is diagnostic-only",
        notes=(
            "Diagnostic-only synthetic coverage exists; keep this row red until "
            "checked replay and real proof-corpus evidence are added."
        ),
        behavior="diagnostic-only",
    ),
)


def proof_rule_asserted_case() -> GeneratedCase:
    feature = "proof-rule:asserted"
    entry = manifest_entry(
        case_id=feature,
        file="cases/proof_rules/proof_rule_asserted.smt2",
        logic="QF_UF",
        standard="Z3-extension",
        row_class="proof-rule",
        features=[feature],
        modes=("proof-parse", "proof-replay", "z3-tac"),
        versions=SUPPORTED_Z3_VERSIONS,
        expected={
            "proof-parse": expected_result(
                "pass",
                proof_rule_histogram={"asserted": 1},
            ),
            "proof-replay": expected_result(
                "pass",
                proof_rule_histogram={"asserted": 1},
            ),
            "z3-tac": expected_result(
                "pass",
                theorem_shape="closed theorem without oracle tags",
            ),
        },
        implementation_obligation=None,
        source=source("Z3-proof", "Z3 proof rule asserted"),
    )
    return GeneratedCase(entry=entry, script=PROOF_RULE_SCRIPT)


def proof_rule_th_lemma_basic_case() -> GeneratedCase:
    feature = "proof-rule:th-lemma-basic"
    script = (
        "(set-option :produce-proofs true)\n"
        "(set-logic QF_LIA)\n"
        "(declare-const x Int)\n"
        "(declare-const y Int)\n"
        "(assert (= x y))\n"
        "(assert (not (= y x)))\n"
        "(check-sat)\n"
        "(get-proof)\n"
    )
    entry = manifest_entry(
        case_id=feature,
        file="cases/proof_rules/proof_rule_th_lemma_basic.smt2",
        logic="QF_LIA",
        standard="Z3-extension",
        row_class="proof-rule",
        features=[
            feature,
            "proof-rule-family:th-lemma",
            "proof-rule-behavior:checked-replay",
        ],
        modes=("proof-parse", "proof-replay", "z3-tac"),
        versions=SUPPORTED_Z3_VERSIONS,
        expected={
            "proof-parse": expected_result(
                "pass",
                proof_rule_histogram={"th-lemma-basic": 1},
            ),
            "proof-replay": expected_result(
                "pass",
                proof_rule_histogram={"th-lemma-basic": 1},
            ),
            "z3-tac": expected_result(
                "pass",
                theorem_shape="closed theorem without oracle tags",
                proof_rule_histogram={"th-lemma-basic": 1},
            ),
        },
        implementation_obligation=None,
        source=source("Z3-proof", "Z3 proof rule th-lemma-basic"),
    )
    return GeneratedCase(entry=entry, script=script)


def th_lemma_proof_rule_case(obligation: ProofRuleObligation) -> GeneratedCase:
    feature = f"proof-rule:{obligation.rule}"
    expected = {
        "proof-parse": expected_result(
            "red",
            diagnostic=obligation.diagnostic,
            failure_phase="proof-parse",
            proof_rule_histogram={obligation.rule: 1},
        ),
        "proof-replay": expected_result(
            "red",
            diagnostic=obligation.diagnostic,
            failure_phase="proof-replay",
            proof_rule_histogram={obligation.rule: 1},
        ),
        "z3-tac": expected_result(
            "red",
            diagnostic="diagnostic-only proof-rule obligation has no reconstructed HOL theorem yet",
            failure_phase="proof-replay",
            theorem_shape="closed theorem without oracle tags",
            proof_rule_histogram={obligation.rule: 1},
        ),
    }
    entry = manifest_entry(
        case_id=feature,
        file=f"cases/proof_rules/proof_rule_{obligation.file_slug}.smt2",
        logic="QF_UF",
        standard="Z3-extension",
        row_class="proof-rule",
        features=[
            feature,
            "proof-rule-family:th-lemma",
            f"proof-rule-behavior:{obligation.behavior}",
        ],
        modes=("proof-parse", "proof-replay", "z3-tac"),
        versions=SUPPORTED_Z3_VERSIONS,
        expected=expected,
        implementation_obligation=implementation_obligation(
            files=(
                "src/HolSmt/Z3_ProofParser.sml",
                "src/HolSmt/Z3_ProofReplay.sml",
                "src/HolSmt/Unittest.sml",
            ),
            feature=feature,
            test_ids=[feature],
            failure_phase="proof-replay",
            notes=obligation.notes,
        ),
        source=source("Z3-proof", f"Z3 proof rule {obligation.rule}"),
    )
    return GeneratedCase(entry=entry, script=PROOF_RULE_SCRIPT)


def proof_rule_th_lemma_nonlinear_arith_case() -> GeneratedCase:
    feature = "proof-rule:th-lemma-nonlinear-arith"
    script = (
        "(set-option :produce-proofs true)\n"
        "(set-logic QF_NIA)\n"
        "(declare-const x Int)\n"
        "(assert (not (>= (* x x) 0)))\n"
        "(check-sat)\n"
        "(get-proof)\n"
    )
    entry = manifest_entry(
        case_id=feature,
        file="cases/proof_rules/proof_rule_th_lemma_nonlinear_arith.smt2",
        logic="QF_NIA",
        standard="Z3-extension",
        row_class="proof-rule",
        features=[
            feature,
            "proof-rule-family:th-lemma",
            "proof-rule-behavior:checked-replay",
        ],
        modes=("proof-parse", "proof-replay", "z3-tac"),
        versions=SUPPORTED_Z3_VERSIONS,
        expected={
            "proof-parse": expected_result(
                "pass",
                proof_rule_histogram={"th-lemma-nonlinear-arith": 1},
            ),
            "proof-replay": expected_result(
                "pass",
                theorem_shape="closed theorem without oracle tags",
                proof_rule_histogram={"th-lemma-nonlinear-arith": 1},
            ),
            "z3-tac": expected_result(
                "pass",
                theorem_shape="closed theorem without oracle tags",
                proof_rule_histogram={"th-lemma-nonlinear-arith": 1},
            ),
        },
        implementation_obligation=None,
        source=source("Z3-proof", "Z3 proof rule th-lemma-nonlinear-arith"),
    )
    return GeneratedCase(entry=entry, script=script)


def proof_rule_cases() -> list[GeneratedCase]:
    return [
        proof_rule_asserted_case(),
        proof_rule_th_lemma_basic_case(),
        proof_rule_th_lemma_nonlinear_arith_case(),
    ] + [
        th_lemma_proof_rule_case(obligation)
        for obligation in TH_LEMMA_PROOF_RULE_OBLIGATIONS
    ]


COMMAND_GROUPS: tuple[CommandGroup, ...] = (
    CommandGroup(
        slug="set-logic",
        commands=("set-logic",),
        positive_script="(set-logic QF_UF)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(set-logic QF_LIA)\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(assert false)\n(check-sat)\n",
        negative_diagnostic="duplicate set-logic",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="checked reconstruction evidence for set-logic state is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Logics.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="set-info",
        commands=("set-info",),
        positive_script='(set-logic QF_UF)\n(set-info :source "command corpus")\n(check-sat)\n',
        negative_script="(set-logic QF_UF)\n(set-info :source)\n",
        state_script='(set-logic QF_UF)\n(set-info :category "crafted")\n(declare-const p Bool)\n(check-sat)\n',
        reconstruction_script='(set-logic QF_UF)\n(set-info :source "no theorem effect")\n(assert false)\n(check-sat)\n',
        negative_diagnostic="malformed set-info attribute",
        negative_phase="parser",
        reconstruction_applies=False,
        reconstruction_diagnostic="set-info has no theorem reconstruction result object",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/tools/conformance-corpus"),
    ),
    CommandGroup(
        slug="set-option",
        commands=("set-option",),
        positive_script="(set-option :produce-proofs true)\n(set-option :produce-models true)\n(set-logic QF_UF)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(set-option :produce-proofs true)\n",
        state_script="(set-option :global-declarations true)\n(set-logic QF_UF)\n(declare-const p Bool)\n(check-sat)\n",
        reconstruction_script="(set-option :produce-proofs true)\n(set-logic QF_UF)\n(assert false)\n(check-sat)\n(get-proof)\n",
        negative_diagnostic="set-option after logic or assertions",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="checked proof option reconstruction matrix is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/Z3.sml"),
    ),
    CommandGroup(
        slug="get-info-get-option",
        commands=("get-info", "get-option"),
        positive_script="(set-logic QF_UF)\n(get-info :name)\n(get-option :produce-proofs)\n",
        negative_script="(set-logic QF_UF)\n(get-option)\n",
        state_script="(set-option :produce-proofs true)\n(set-logic QF_UF)\n(get-option :produce-proofs)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(get-info :version)\n(get-option :print-success)\n(check-sat)\n",
        negative_diagnostic="malformed get-option",
        negative_phase="parser",
        reconstruction_applies=False,
        reconstruction_diagnostic="raw SMT-LIB query get-info is outside checked Z3_TAC command-line entry point",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/tools/conformance-corpus"),
    ),
    CommandGroup(
        slug="declare-sort",
        commands=("declare-sort",),
        positive_script=(
            "(set-logic QF_UF)\n"
            "(declare-sort A 0)\n"
            "(declare-sort B 0)\n"
            "(declare-sort Box 1)\n"
            "(declare-sort Pair 2)\n"
            "(declare-const x1 (Box A))\n"
            "(declare-const x2 (Box A))\n"
            "(declare-const y (Box B))\n"
            "(declare-const p (Pair A B))\n"
            "(assert (= x1 x2))\n"
            "(assert (= y y))\n"
            "(assert (= p p))\n"
            "(check-sat)\n"
        ),
        negative_script=(
            "(set-logic QF_UF)\n"
            "(declare-sort A 0)\n"
            "(declare-sort Box 1)\n"
            "(declare-const bad (Box A A))\n"
        ),
        state_script=(
            "(set-logic QF_UF)\n"
            "(declare-sort A 0)\n"
            "(declare-sort Box 1)\n"
            "(push 1)\n"
            "(declare-const a (Box A))\n"
            "(pop 1)\n"
            "(check-sat)\n"
        ),
        reconstruction_script=(
            "(set-logic QF_UF)\n"
            "(declare-sort U 0)\n"
            "(declare-const a U)\n"
            "(assert (not (= a a)))\n"
            "(check-sat)\n"
        ),
        negative_diagnostic="declare-sort arity mismatch",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="abstract sort reconstruction coverage is incomplete",
        reconstruction_phase="translation",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/SmtLib.sml"),
    ),
    CommandGroup(
        slug="define-sort",
        commands=("define-sort",),
        positive_script="(set-logic QF_UF)\n(define-sort UAlias () Bool)\n(declare-const p UAlias)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(define-sort Bad () Bad)\n",
        state_script="(set-logic QF_UF)\n(define-sort Pair (A B) Bool)\n(declare-const p Bool)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(define-sort UAlias () Bool)\n(declare-const p UAlias)\n(assert p)\n(assert (not p))\n(check-sat)\n",
        negative_diagnostic="recursive sort alias",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="define-sort alias replay evidence is incomplete",
        reconstruction_phase="translation",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/SmtLib.sml"),
    ),
    CommandGroup(
        slug="declare-const",
        commands=("declare-const",),
        positive_script="(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const p Bool)\n(declare-const i U)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const p Bool)\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n",
        negative_diagnostic="duplicate declaration",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="declare-const checked replay matrix is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="declare-fun",
        commands=("declare-fun",),
        positive_script="(set-logic QF_UF)\n(declare-fun f (Bool Bool) Bool)\n(declare-const p Bool)\n(assert (f p p))\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(declare-fun f (Bool) Bool)\n(assert (f true false))\n",
        state_script="(set-logic QF_UF)\n(declare-sort U 0)\n(declare-fun pred (U) Bool)\n(declare-const x U)\n(assert (pred x))\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(declare-const id (-> Bool Bool))\n(declare-fun h ((-> Bool Bool)) Bool)\n(assert (h id))\n(assert (not (h id)))\n(check-sat)\n",
        negative_diagnostic="function arity mismatch",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="unsupported higher-order/function sort",
        reconstruction_phase="translation",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/SmtLib.sml"),
        obligation_notes=(
            "First-order declarations are typechecked, but checked reconstruction for "
            "function-sort and higher-order declarations remains outside the current translator."
        ),
    ),
    CommandGroup(
        slug="define-const",
        commands=("define-const",),
        positive_script="(set-logic QF_UF)\n(define-const p Bool true)\n(assert p)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(define-const p Bool true)\n(define-const p Bool false)\n",
        state_script="(set-logic QF_UF)\n(define-const p Bool true)\n(push 1)\n(assert p)\n(pop 1)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(define-const p Bool false)\n(assert p)\n(check-sat)\n",
        negative_diagnostic="duplicate define-const",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="define-const replay evidence is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="define-fun",
        commands=("define-fun",),
        positive_script="(set-logic QF_UF)\n(define-fun id ((p Bool)) Bool p)\n(assert (id true))\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(define-fun loop ((p Bool)) Bool (loop p))\n",
        state_script="(set-logic QF_UF)\n(define-fun both ((p Bool) (q Bool)) Bool (and p q))\n(assert (both true true))\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(define-fun bad () Bool false)\n(assert bad)\n(check-sat)\n",
        negative_diagnostic="recursive self-reference",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="define-fun replay coverage is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="define-fun-rec-define-funs-rec",
        commands=("define-fun-rec", "define-funs-rec"),
        positive_script="(set-logic QF_UF)\n(define-fun-rec f ((p Bool)) Bool p)\n(assert (f true))\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(define-funs-rec ((f ((p Bool)) Bool)) ())\n",
        state_script="(set-logic QF_UF)\n(define-funs-rec ((f ((p Bool)) Bool)) ((not p)))\n(assert (f false))\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(define-funs-rec ((even ((p Bool)) Bool) (odd ((p Bool)) Bool)) ((odd p) (not (even p))))\n(assert (even true))\n(check-sat)\n",
        negative_diagnostic="malformed recursive definition block",
        negative_phase="parser",
        reconstruction_applies=True,
        reconstruction_diagnostic="define-fun-rec replay coverage is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/SmtLib.sml"),
        obligation_notes=(
            "Recursive definition commands are predeclared and equated as asserted "
            "hypotheses; checked Z3_TAC replay must preserve that theorem shape."
        ),
    ),
    CommandGroup(
        slug="declare-datatype-declare-datatypes",
        commands=("declare-datatype", "declare-datatypes"),
        positive_script="(set-logic QF_UF)\n(declare-datatype Color ((red) (blue)))\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(declare-datatypes ((Tree 1)) (((node (left Tree) (right Tree)))))\n",
        state_script="(set-logic QF_UF)\n(declare-datatypes ((Color 0)) (((red) (blue))))\n(declare-const c Color)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(declare-datatype Color ((red) (blue)))\n(assert (= red blue))\n(check-sat)\n",
        negative_diagnostic="declare-datatypes arity for 'Tree'",
        negative_phase="typecheck",
        reconstruction_applies=False,
        reconstruction_diagnostic="datatype declaration command declare-datatype is outside checked Z3_TAC command-line entry point",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/Z3_ProofReplay.sml"),
        obligation_notes=(
            "Parser/typecheck state installs bounded datatype symbols, but checked Z3_TAC "
            "translation still lacks native datatype constructor replay evidence."
        ),
    ),
    CommandGroup(
        slug="assert",
        commands=("assert",),
        positive_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert (! p :named named_p))\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const x U)\n(assert x)\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(push 1)\n(assert p)\n(pop 1)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(assert false)\n(check-sat)\n(get-proof)\n",
        negative_diagnostic="assert term must have Bool sort",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="assertion replay coverage for command corpus is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="check-sat",
        commands=("check-sat",),
        positive_script="(set-logic QF_UF)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(check-sat true)\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n(assert (not p))\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(assert false)\n(check-sat)\n(get-proof)\n",
        negative_diagnostic="malformed check-sat",
        negative_phase="parser",
        reconstruction_applies=True,
        reconstruction_diagnostic="check-sat proof reconstruction matrix is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SolverSpec.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="check-sat-assuming",
        commands=("check-sat-assuming",),
        positive_script="(set-logic QF_UF)\n(declare-const p Bool)\n(check-sat-assuming (p))\n",
        negative_script="(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const x U)\n(check-sat-assuming (x))\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(push 1)\n(check-sat-assuming (p))\n(pop 1)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert (! p :named p_name))\n(check-sat-assuming ((not p)))\n",
        negative_diagnostic="assumption literal must have Bool sort",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="check-sat-assuming replay evidence is incomplete",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/z3_tac_driver.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="get-proof",
        commands=("get-proof",),
        positive_script="(set-option :produce-proofs true)\n(set-logic QF_UF)\n(assert false)\n(check-sat)\n(get-proof)\n",
        negative_script="(set-option :produce-proofs true)\n(set-logic QF_UF)\n(get-proof)\n",
        state_script="(set-option :produce-proofs true)\n(set-logic QF_UF)\n(assert false)\n(check-sat)\n(get-proof)\n",
        reconstruction_script="(set-option :produce-proofs true)\n(set-logic QF_UF)\n(assert false)\n(check-sat)\n(get-proof)\n",
        negative_diagnostic="get-proof before unsat check-sat",
        negative_phase="solver",
        reconstruction_applies=True,
        reconstruction_diagnostic="get-proof parse/replay evidence is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/Z3_ProofParser.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="get-unsat-assumptions-get-unsat-core",
        commands=("get-unsat-assumptions", "get-unsat-core"),
        positive_script="(set-option :produce-unsat-cores true)\n(set-logic QF_UF)\n(assert (! false :named bad))\n(check-sat)\n(get-unsat-core)\n(get-unsat-assumptions)\n",
        negative_script="(set-logic QF_UF)\n(get-unsat-core)\n",
        state_script="(set-option :produce-unsat-cores true)\n(set-logic QF_UF)\n(assert (! false :named bad))\n(check-sat)\n(get-unsat-core)\n",
        reconstruction_script="(set-option :produce-unsat-cores true)\n(set-logic QF_UF)\n(declare-const p Bool)\n(assert (! p :named p_name))\n(check-sat-assuming ((not p)))\n(get-unsat-core)\n(get-unsat-assumptions)\n",
        negative_diagnostic="unsat core requested before unsat result",
        negative_phase="solver",
        reconstruction_applies=True,
        reconstruction_diagnostic="unsat-core and unsat-assumption extraction evidence is incomplete",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/z3_tac_driver.sml", "src/HolSmt/Z3_ProofReplay.sml"),
        reconstruction_unsat_core="(p_name)",
        reconstruction_unsat_assumptions="(~p)",
    ),
    CommandGroup(
        slug="get-model-get-value-get-assignment-get-assertions",
        commands=("get-model", "get-value", "get-assignment", "get-assertions"),
        positive_script="(set-option :produce-models true)\n(set-logic QF_UF)\n(declare-const p Bool)\n(check-sat)\n(get-model)\n(get-value (p))\n(get-assignment)\n(get-assertions)\n",
        negative_script="(set-logic QF_UF)\n(get-value)\n",
        state_script="(set-option :produce-models true)\n(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n(get-value (p))\n",
        reconstruction_script="(set-option :produce-models true)\n(set-logic QF_UF)\n(declare-const p Bool)\n(check-sat)\n(get-model)\n",
        negative_diagnostic="malformed get-value",
        negative_phase="parser",
        reconstruction_applies=False,
        reconstruction_diagnostic="raw SMT-LIB query get-model is outside checked Z3_TAC command-line entry point",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/tools/conformance-corpus"),
    ),
    CommandGroup(
        slug="push-pop",
        commands=("push", "pop"),
        positive_script="(set-logic QF_UF)\n(push 1)\n(pop 1)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(pop 1)\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(push 1)\n(assert p)\n(pop 1)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(push 1)\n(assert false)\n(check-sat)\n(pop 1)\n",
        negative_diagnostic="pop scope underflow",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="scoped assertion proof replay is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="reset-reset-assertions",
        commands=("reset", "reset-assertions"),
        positive_script="(set-logic QF_UF)\n(declare-const p Bool)\n(reset-assertions)\n(check-sat)\n(reset)\n",
        negative_script="(set-logic QF_UF)\n(reset true)\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(reset-assertions)\n(assert (not p))\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(assert true)\n(reset-assertions)\n(assert false)\n(check-sat)\n",
        negative_diagnostic="malformed reset",
        negative_phase="parser",
        reconstruction_applies=True,
        reconstruction_diagnostic="reset/reset-assertions replay semantics are incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/SolverSpec.sml"),
    ),
    CommandGroup(
        slug="echo",
        commands=("echo",),
        positive_script='(set-logic QF_UF)\n(echo "hello command corpus")\n(check-sat)\n',
        negative_script="(set-logic QF_UF)\n(echo hello)\n",
        state_script='(set-logic QF_UF)\n(echo "state is unchanged")\n(declare-const p Bool)\n(check-sat)\n',
        reconstruction_script='(set-logic QF_UF)\n(echo "no theorem effect")\n(assert false)\n(check-sat)\n',
        negative_diagnostic="echo requires a string literal",
        negative_phase="parser",
        reconstruction_applies=False,
        reconstruction_diagnostic="echo response behavior is not represented in theorem reconstruction",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/tools/conformance-corpus"),
    ),
    CommandGroup(
        slug="exit",
        commands=("exit",),
        positive_script="(set-logic QF_UF)\n(exit)\n",
        negative_script="(set-logic QF_UF)\n(exit true)\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(exit)\n(assert p)\n",
        reconstruction_script=(
            "(set-logic QF_UF)\n(assert false)\n(exit)\n"
            "(declare-datatype Color ((red) (blue)))\n(check-sat)\n"
        ),
        negative_diagnostic="malformed exit",
        negative_phase="parser",
        reconstruction_applies=False,
        reconstruction_diagnostic="no check-sat query in raw SMT-LIB script for checked Z3_TAC",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/tools/conformance-corpus"),
    ),
)

RECONSTRUCTED_COMMAND_GROUPS = {
    "assert",
    "check-sat",
    "check-sat-assuming",
    "declare-const",
    "declare-fun",
    "declare-sort",
    "define-const",
    "define-fun",
    "define-fun-rec-define-funs-rec",
    "define-sort",
    "echo",
    "get-proof",
    "get-unsat-assumptions-get-unsat-core",
    "push-pop",
    "reset-reset-assertions",
    "set-info",
    "set-logic",
    "set-option",
}

UNSAT_PROOF_MODE_BLOCKED_THEORY_CASES = {
    "theory:Fixed_Size_BitVectors:bvnego:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsaddo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsdivo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsmulo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvssubo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvuaddo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvumulo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvusubo:unsat-proof",
    "theory:Fixed_Size_BitVectors:int-to-bv:unsat-proof",
    "theory:Fixed_Size_BitVectors:sbv-to-int:unsat-proof",
    "theory:Fixed_Size_BitVectors:ubv-to-int:unsat-proof",
    "theory:Ints:divisible:unsat-proof",
    "theory:Ints:pow:unsat-proof",
    "theory:Z3_Extensions:bag.count:unsat-proof",
    "theory:Z3_Extensions:bag.difference-subtract:unsat-proof",
    "theory:Z3_Extensions:bag.inter-min:unsat-proof",
    "theory:Z3_Extensions:bag.union-disjoint:unsat-proof",
    "theory:Z3_Extensions:bag.union-max:unsat-proof",
    "theory:Z3_Extensions:bag:unsat-proof",
    "theory:Z3_Extensions:set.insert:unsat-proof",
    "theory:Z3_Extensions:set.intersect:unsat-proof",
    "theory:Z3_Extensions:set.member:unsat-proof",
    "theory:Z3_Extensions:set.minus:unsat-proof",
    "theory:Z3_Extensions:set.subset:unsat-proof",
    "theory:Z3_Extensions:set.union:unsat-proof",
}

RECONSTRUCTED_THEORY_Z3_TAC_UNSAT_PROOFS = {
    "theory:ArraysEx:array:unsat-proof",
    "theory:ArraysEx:extensionality:unsat-proof",
    "theory:ArraysEx:mixed-index-value-sorts:unsat-proof",
    "theory:ArraysEx:read-over-write:unsat-proof",
    "theory:ArraysEx:select:unsat-proof",
    "theory:ArraysEx:store:unsat-proof",
    "theory:ArraysEx:write-over-write:unsat-proof",
    "theory:Core:and:unsat-proof",
    "theory:Core:bool:unsat-proof",
    "theory:Core:eq:unsat-proof",
    "theory:Core:false:unsat-proof",
    "theory:Core:implies:unsat-proof",
    "theory:Core:ite:unsat-proof",
    "theory:Core:not:unsat-proof",
    "theory:Core:or:unsat-proof",
    "theory:Core:true:unsat-proof",
    "theory:Core:distinct:unsat-proof",
    "theory:Core:xor:unsat-proof",
    "theory:UnicodeStrings:string-literal:unsat-proof",
    "theory:Fixed_Size_BitVectors:binary-hex-literal:unsat-proof",
    "theory:Fixed_Size_BitVectors:bitvec:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvadd:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvand:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvashr:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvcomp:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvlshr:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvmul:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvnand:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvneg:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvnego:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvnor:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvnot:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvor:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsdiv:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsdivo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsge:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsgt:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvshl:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsle:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvslt:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsmulo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsmod:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsrem:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvsub:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvuaddo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvudiv:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvuge:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvugt:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvule:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvult:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvumulo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvurem:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvusubo:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvxnor:unsat-proof",
    "theory:Fixed_Size_BitVectors:bvxor:unsat-proof",
    "theory:Fixed_Size_BitVectors:concat:unsat-proof",
    "theory:Fixed_Size_BitVectors:decimal-literal:unsat-proof",
    "theory:Fixed_Size_BitVectors:extract:unsat-proof",
    "theory:Fixed_Size_BitVectors:int-to-bv:unsat-proof",
    "theory:Fixed_Size_BitVectors:repeat:unsat-proof",
    "theory:Fixed_Size_BitVectors:rotate-left:unsat-proof",
    "theory:Fixed_Size_BitVectors:rotate-right:unsat-proof",
    "theory:Fixed_Size_BitVectors:sbv-to-int:unsat-proof",
    "theory:Fixed_Size_BitVectors:sign-extend:unsat-proof",
    "theory:Fixed_Size_BitVectors:ubv-to-int:unsat-proof",
    "theory:Fixed_Size_BitVectors:zero-extend:unsat-proof",
    "theory:FloatingPoint:float128:unsat-proof",
    "theory:FloatingPoint:float16:unsat-proof",
    "theory:FloatingPoint:float32:unsat-proof",
    "theory:FloatingPoint:float64:unsat-proof",
    "theory:FloatingPoint:fp.abs:unsat-proof",
    "theory:FloatingPoint:fp.add:unsat-proof",
    "theory:FloatingPoint:fp.div:unsat-proof",
    "theory:FloatingPoint:fp.eq:unsat-proof",
    "theory:FloatingPoint:fp.fma:unsat-proof",
    "theory:FloatingPoint:fp.geq:unsat-proof",
    "theory:FloatingPoint:fp.gt:unsat-proof",
    "theory:FloatingPoint:fp.isinfinite:unsat-proof",
    "theory:FloatingPoint:fp.isnan:unsat-proof",
    "theory:FloatingPoint:fp.isnegative:unsat-proof",
    "theory:FloatingPoint:fp.isnormal:unsat-proof",
    "theory:FloatingPoint:fp.ispositive:unsat-proof",
    "theory:FloatingPoint:fp.issubnormal:unsat-proof",
    "theory:FloatingPoint:fp.iszero:unsat-proof",
    "theory:FloatingPoint:fp.leq:unsat-proof",
    "theory:FloatingPoint:fp.lt:unsat-proof",
    "theory:FloatingPoint:fp.max:unsat-proof",
    "theory:FloatingPoint:fp.min:unsat-proof",
    "theory:FloatingPoint:fp.mul:unsat-proof",
    "theory:FloatingPoint:fp.neg:unsat-proof",
    "theory:FloatingPoint:fp.rem:unsat-proof",
    "theory:FloatingPoint:fp.roundtointegral:unsat-proof",
    "theory:FloatingPoint:fp.sqrt:unsat-proof",
    "theory:FloatingPoint:fp.sub:unsat-proof",
    "theory:FloatingPoint:fp.to-real:unsat-proof",
    "theory:FloatingPoint:fp:unsat-proof",
    "theory:FloatingPoint:nan:unsat-proof",
    "theory:FloatingPoint:negative-infinity:unsat-proof",
    "theory:FloatingPoint:negative-zero:unsat-proof",
    "theory:FloatingPoint:positive-infinity:unsat-proof",
    "theory:FloatingPoint:positive-zero:unsat-proof",
    "theory:FloatingPoint:rna:unsat-proof",
    "theory:FloatingPoint:rne:unsat-proof",
    "theory:FloatingPoint:roundingmode:unsat-proof",
    "theory:FloatingPoint:roundnearesttiestoaway:unsat-proof",
    "theory:FloatingPoint:roundnearesttiestoeven:unsat-proof",
    "theory:FloatingPoint:roundtowardnegative:unsat-proof",
    "theory:FloatingPoint:roundtowardpositive:unsat-proof",
    "theory:FloatingPoint:roundtowardzero:unsat-proof",
    "theory:FloatingPoint:rtn:unsat-proof",
    "theory:FloatingPoint:rtp:unsat-proof",
    "theory:FloatingPoint:rtz:unsat-proof",
    "theory:FloatingPoint:to-fp-unsigned:unsat-proof",
    "theory:FloatingPoint:to-fp:unsat-proof",
    "theory:Ints:abs:unsat-proof",
    "theory:Ints:div:unsat-proof",
    "theory:Ints:ge:unsat-proof",
    "theory:Ints:gt:unsat-proof",
    "theory:Ints:int:unsat-proof",
    "theory:Ints:le:unsat-proof",
    "theory:Ints:lt:unsat-proof",
    "theory:Ints:mod:unsat-proof",
    "theory:Ints:neg:unsat-proof",
    "theory:Ints:numeral:unsat-proof",
    "theory:Ints:plus:unsat-proof",
    "theory:Ints:pow:unsat-proof",
    "theory:Ints:sub:unsat-proof",
    "theory:Ints:times:unsat-proof",
    "theory:Reals:ge:unsat-proof",
    "theory:Reals:gt:unsat-proof",
    "theory:Reals:le:unsat-proof",
    "theory:Reals:lt:unsat-proof",
    "theory:Reals:neg:unsat-proof",
    "theory:Reals:numeral:unsat-proof",
    "theory:Reals:plus:unsat-proof",
    "theory:Reals:real:unsat-proof",
    "theory:Reals:sub:unsat-proof",
    "theory:Reals:times:unsat-proof",
    "theory:Reals_Ints:to-int:unsat-proof",
    "theory:Reals_Ints:to-real:unsat-proof",
    "theory:UnicodeStrings:re.all:unsat-proof",
    "theory:UnicodeStrings:re.allchar:unsat-proof",
    "theory:UnicodeStrings:re.none:unsat-proof",
    "theory:UnicodeStrings:reglan:unsat-proof",
    "theory:UnicodeStrings:str.from-code:unsat-proof",
    "theory:UnicodeStrings:str.from-int:unsat-proof",
    "theory:UnicodeStrings:str.is-digit:unsat-proof",
    "theory:UnicodeStrings:str.to-int:unsat-proof",
    "theory:UnicodeStrings:string:unsat-proof",
    "theory:Z3_Extensions:seq-concat:unsat-proof",
    "theory:Z3_Extensions:seq.contains:unsat-proof",
    "theory:Z3_Extensions:seq.extract:unsat-proof",
    "theory:Z3_Extensions:seq.len:unsat-proof",
    "theory:Z3_Extensions:seq:unsat-proof",
    "theory:Z3_Extensions:set:unsat-proof",
}


def command_features(group: CommandGroup) -> list[str]:
    return [*(f"command:{command}" for command in group.commands), f"command-group:{group.slug}"]


def command_case(
    group: CommandGroup,
    kind: str,
    script: str,
    modes: Sequence[str],
    expected: Mapping[str, Mapping[str, object]],
    *,
    implementation: Mapping[str, object] | None = None,
) -> GeneratedCase:
    case_id = f"command:{group.slug}" if kind == "positive" else f"command:{group.slug}:{kind}"
    entry = manifest_entry(
        case_id=case_id,
        file=deterministic_case_file("command", case_id),
        logic="QF_UF",
        standard="SMT-LIB-2.7",
        row_class="command",
        features=command_features(group) + [f"command-case:{kind}"],
        modes=modes,
        versions=SUPPORTED_Z3_VERSIONS,
        expected=expected,
        implementation_obligation=implementation,
        source=source(
            "SMT-LIB-standard",
            "SMT-LIB 2.7 command group: " + ", ".join(group.commands),
        ),
    )
    return GeneratedCase(entry=entry, script=script)


DATATYPE_COMMAND_CORPUS_CASES: tuple[ScriptedCase, ...] = (
    ScriptedCase(
        slug="simple-enum",
        script=(
            "(set-logic ALL)\n"
            "(declare-datatype Color ((red) (green) (blue)))\n"
            "(declare-const c Color)\n"
            "(assert (or ((_ is red) c) ((_ is green) c) ((_ is blue) c)))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only", "z3-oracle"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
        },
        features=(
            "command-case:datatype-corpus",
            "command:declare-datatype",
            "datatype-command:simple",
            "theory:Datatypes",
            "theory-behavior:constructor",
            "theory-behavior:tester",
        ),
        logic="ALL",
        source_reference="SMT-LIB 2.7 declare-datatype simple datatype command",
        source_kind="SMT-LIB-standard",
    ),
    ScriptedCase(
        slug="recursive-list",
        script=(
            "(set-logic ALL)\n"
            "(declare-datatype List ((nil) (cons (head Int) (tail List))))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
        },
        features=(
            "command-case:datatype-corpus",
            "command:declare-datatype",
            "datatype-command:recursive",
            "theory:Datatypes",
            "theory-behavior:recursive-datatype",
        ),
        logic="ALL",
        source_reference="SMT-LIB 2.7 declare-datatype recursive datatype command",
        source_kind="SMT-LIB-standard",
    ),
    ScriptedCase(
        slug="mutual-tree-forest",
        script=(
            "(set-logic ALL)\n"
            "(declare-datatypes ((Tree 0) (Forest 0))\n"
            "  (((leaf) (node (children Forest)))\n"
            "   ((nilF) (consF (head Tree) (tail Forest)))))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
        },
        features=(
            "command-case:datatype-corpus",
            "command:declare-datatypes",
            "datatype-command:mutual",
            "theory:Datatypes",
            "theory-behavior:mutual-datatype",
        ),
        logic="ALL",
        source_reference="SMT-LIB 2.7 declare-datatypes mutual datatype command",
        source_kind="SMT-LIB-standard",
    ),
    ScriptedCase(
        slug="parametric-box",
        script=(
            "(set-logic ALL)\n"
            "(declare-datatype Box (par (T) ((box (value T)))))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
        },
        features=(
            "command-case:datatype-corpus",
            "command:declare-datatype",
            "datatype-command:parametric",
            "theory:Datatypes",
            "theory-behavior:parametric-datatype",
        ),
        logic="ALL",
        source_reference="SMT-LIB 2.7 declare-datatype parametric datatype command",
        source_kind="SMT-LIB-standard",
    ),
)


def scripted_obligation(case: ScriptedCase, case_id: str) -> dict[str, object] | None:
    if case.implementation_feature is None:
        return None
    if case.implementation_phase is None:
        raise GeneratorError(f"{case_id} has an implementation feature without a failure phase")
    return implementation_obligation(
        files=case.implementation_files,
        feature=case.implementation_feature,
        test_ids=[case_id],
        failure_phase=case.implementation_phase,
        notes=GENERATED_OBLIGATION_NOTES,
    )


def datatype_command_corpus_case(case: ScriptedCase) -> GeneratedCase:
    case_id = f"command:datatypes:{case.slug}"
    entry = manifest_entry(
        case_id=case_id,
        file=f"cases/commands/datatypes/{slug(case_id)}.smt2",
        logic=case.logic,
        standard=case.standard,
        row_class="command",
        features=case.features,
        modes=case.modes,
        versions=SUPPORTED_Z3_VERSIONS,
        expected=case.expected,
        implementation_obligation=scripted_obligation(case, case_id),
        source=source(case.source_kind, case.source_reference),
    )
    return GeneratedCase(entry=entry, script=case.script)


def mode_for_failure_phase(failure_phase: str) -> str:
    require_choice(failure_phase, "failure_phase", FAILURE_PHASES)
    if failure_phase == "parser":
        return "parser-only"
    if failure_phase in {"typecheck", "translation"}:
        return "typecheck-only"
    if failure_phase == "solver":
        return "z3-oracle"
    if failure_phase in {"proof-parse", "proof-replay"}:
        return failure_phase
    return "z3-tac"


def first_red_failure_phase(expected: Mapping[str, Mapping[str, object]]) -> str:
    for mode in MODES:
        result = expected.get(mode)
        if result is None or result.get("status") != "red":
            continue
        phase = result.get("failure_phase")
        if not isinstance(phase, str):
            raise GeneratorError(f"red expected result for {mode} is missing failure_phase")
        return require_choice(phase, "failure_phase", FAILURE_PHASES)
    raise GeneratorError("expected results contain no red failure phase")


def command_cases() -> list[GeneratedCase]:
    cases: list[GeneratedCase] = []
    for group in COMMAND_GROUPS:
        cases.append(
            command_case(
                group,
                "positive",
                group.positive_script,
                ("parser-only", "typecheck-only"),
                {
                    "parser-only": expected_result("pass"),
                    "typecheck-only": expected_result("pass"),
                },
            )
        )
        cases.append(
            command_case(
                group,
                "negative",
                group.negative_script,
                (mode_for_failure_phase(group.negative_phase),),
                {
                    mode_for_failure_phase(group.negative_phase): expected_result(
                        "fail",
                        diagnostic=group.negative_diagnostic,
                        failure_phase=group.negative_phase,
                    )
                },
            )
        )
        state_expected = {
            "typecheck-only": expected_result(
                "pass",
                notes=f"theorem reconstruction applies: {str(group.reconstruction_applies).lower()}",
            ),
            "z3-oracle": expected_result(
                "pass",
                notes=f"theorem reconstruction applies: {str(group.reconstruction_applies).lower()}",
            ),
        }
        if group.slug == "exit":
            state_expected["z3-oracle"] = expected_result(
                "fail",
                diagnostic="Z3 did not print a solver result",
                failure_phase="solver",
                notes="exit terminates the script before a check-sat query",
            )
        cases.append(
            command_case(
                group,
                "state",
                group.state_script,
                ("typecheck-only", "z3-oracle"),
                state_expected,
            )
        )
        reconstruction_case_id = f"command:{group.slug}:reconstruction"
        reconstruction_is_fixed = group.slug in RECONSTRUCTED_COMMAND_GROUPS
        if reconstruction_is_fixed:
            reconstruction_expected = expected_result(
                "pass",
                notes=f"theorem reconstruction applies: {str(group.reconstruction_applies).lower()}",
                unsat_core=group.reconstruction_unsat_core,
                unsat_assumptions=group.reconstruction_unsat_assumptions,
            )
        elif not group.reconstruction_applies and not group.red_when_reconstruction_not_applicable:
            reconstruction_expected = expected_result(
                "unsupported",
                diagnostic=group.reconstruction_diagnostic,
                failure_phase=group.reconstruction_phase,
                notes=f"theorem reconstruction applies: false",
            )
        else:
            reconstruction_expected = expected_result(
                "red",
                diagnostic=group.reconstruction_diagnostic,
                failure_phase=group.reconstruction_phase,
                notes=f"theorem reconstruction applies: {str(group.reconstruction_applies).lower()}",
            )
        reconstruction_obligation = None if reconstruction_is_fixed or (not group.reconstruction_applies and not group.red_when_reconstruction_not_applicable) else implementation_obligation(
            files=group.obligation_files,
            feature=f"command-reconstruction:{group.slug}",
            test_ids=[reconstruction_case_id],
            failure_phase=group.reconstruction_phase,
            notes=group.obligation_notes,
        )
        cases.append(
            command_case(
                group,
                "reconstruction",
                group.reconstruction_script,
                ("z3-tac",),
                {"z3-tac": reconstruction_expected},
                implementation=reconstruction_obligation,
            )
        )
    recursive_group = next(
        group for group in COMMAND_GROUPS
        if group.slug == "define-fun-rec-define-funs-rec"
    )
    full_replay_modes = (
        "parser-only",
        "typecheck-only",
        "z3-tac",
    )
    full_replay_expected = {
        mode: expected_result(
            "pass",
            notes="recursive equations are asserted hypotheses, not HOL definitions",
        )
        for mode in full_replay_modes
    }
    cases.append(
        command_case(
            recursive_group,
            "define-fun-rec-replay",
            "(set-logic QF_UF)\n"
            "(define-fun-rec f ((p Bool)) Bool p)\n"
            "(assert (not (f true)))\n"
            "(check-sat)\n",
            full_replay_modes,
            full_replay_expected,
        )
    )
    cases.append(
        command_case(
            recursive_group,
            "define-funs-rec-replay",
            "(set-logic QF_UF)\n"
            "(define-funs-rec ((even ((p Bool)) Bool) (odd ((p Bool)) Bool)) "
            "((odd p) (not (even p))))\n"
            "(assert (even true))\n"
            "(check-sat)\n",
            full_replay_modes,
            full_replay_expected,
        )
    )
    cases.extend(datatype_command_corpus_case(case) for case in DATATYPE_COMMAND_CORPUS_CASES)
    return cases


def proof_script(logic: str, body: str) -> str:
    return f"(set-option :produce-proofs true)\n(set-logic {logic})\n{body}(check-sat)\n(get-proof)\n"


def check_sat_script(logic: str, body: str) -> str:
    return f"(set-logic {logic})\n{body}(check-sat)\n"


CORE_ARITHMETIC_THEORY_SYMBOLS: tuple[TheorySymbol, ...] = (
    TheorySymbol(
        "Core",
        "bool",
        "sort",
        "Bool",
        "QF_UF",
        ("(Bool 0)",),
        "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n",
        proof_script("QF_UF", "(assert false)\n"),
        "(set-logic QF_UF)\n(declare-const bad (Bool Bool))\n(check-sat)\n",
        "(set-logic QF_UF)\n(declare-fun f (Bool) Bool)\n(assert (f true))\n(check-sat)\n",
        ("theory-behavior:sort-arity",),
    ),
    TheorySymbol(
        "Core",
        "true",
        "term",
        "true",
        "QF_UF",
        ("(true Bool)",),
        "(set-logic QF_UF)\n(assert true)\n(check-sat)\n",
        proof_script("QF_UF", "(assert (not true))\n"),
        "(set-logic QF_UF)\n(assert (true))\n(check-sat)\n",
        "(set-logic QF_UF)\n(assert (= true true))\n(check-sat)\n",
        ("theory-behavior:arity",),
    ),
    TheorySymbol(
        "Core",
        "false",
        "term",
        "false",
        "QF_UF",
        ("(false Bool)",),
        "(set-logic QF_UF)\n(assert (not false))\n(check-sat)\n",
        proof_script("QF_UF", "(assert false)\n"),
        "(set-logic QF_UF)\n(assert (false))\n(check-sat)\n",
        "(set-logic QF_UF)\n(assert (= false false))\n(check-sat)\n",
        ("theory-behavior:arity",),
    ),
    TheorySymbol(
        "Core",
        "not",
        "term",
        "not",
        "QF_UF",
        ("(not Bool Bool)",),
        "(set-logic QF_UF)\n(assert (not false))\n(check-sat)\n",
        proof_script("QF_UF", "(assert (not true))\n"),
        "(set-logic QF_UF)\n(assert (not true false))\n(check-sat)\n",
        "(set-logic QF_UF)\n(assert (= (not (not true)) true))\n(check-sat)\n",
        ("theory-behavior:arity",),
    ),
    TheorySymbol(
        "Core",
        "implies",
        "term",
        "=>",
        "QF_UF",
        ("(=> Bool Bool Bool :right-assoc)",),
        "(set-logic QF_UF)\n(assert (=> true true))\n(check-sat)\n",
        proof_script("QF_UF", "(assert (=> true false))\n"),
        "(set-logic QF_UF)\n(assert (=> true 0))\n(check-sat)\n",
        "(set-logic QF_UF)\n(assert (=> true false false))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:right-associative"),
    ),
    TheorySymbol(
        "Core",
        "and",
        "term",
        "and",
        "QF_UF",
        ("(and Bool Bool Bool :left-assoc)",),
        "(set-logic QF_UF)\n(assert (and true true true))\n(check-sat)\n",
        proof_script("QF_UF", "(assert (and true false true))\n"),
        "(set-logic QF_UF)\n(assert (and true 0))\n(check-sat)\n",
        "(set-logic QF_UF)\n(assert (= (and true true true) true))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative"),
    ),
    TheorySymbol(
        "Core",
        "or",
        "term",
        "or",
        "QF_UF",
        ("(or Bool Bool Bool :left-assoc)",),
        "(set-logic QF_UF)\n(assert (or false false true))\n(check-sat)\n",
        proof_script("QF_UF", "(assert (or false false false))\n"),
        "(set-logic QF_UF)\n(assert (or false 0))\n(check-sat)\n",
        "(set-logic QF_UF)\n(assert (= (or false false true) true))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative"),
    ),
    TheorySymbol(
        "Core",
        "xor",
        "term",
        "xor",
        "QF_UF",
        ("(xor Bool Bool Bool :left-assoc)",),
        "(set-logic QF_UF)\n(assert (xor true false))\n(check-sat)\n",
        proof_script("QF_UF", "(assert (xor true true))\n"),
        "(set-logic QF_UF)\n(assert (xor true 0))\n(check-sat)\n",
        "(set-logic QF_UF)\n(assert (= (xor true false false) true))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative"),
    ),
    TheorySymbol(
        "Core",
        "eq",
        "term",
        "=",
        "QF_LIA",
        ("(par (A) (= A A Bool :chainable))",),
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x x))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (not (= 1 1)))\n"),
        "(set-logic QF_LIA)\n(assert (= true 0))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 1 1 x))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:chainable", "theory-behavior:polymorphic-equality"),
    ),
    TheorySymbol(
        "Core",
        "distinct",
        "term",
        "distinct",
        "QF_LIA",
        ("(par (A) (distinct A A Bool :pairwise))",),
        "(set-logic QF_LIA)\n(assert (distinct 0 1 2))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (distinct 1 1))\n"),
        "(set-logic QF_LIA)\n(assert (distinct true 0))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (distinct 0 1 2 3))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:pairwise", "theory-behavior:polymorphic-equality"),
    ),
    TheorySymbol(
        "Core",
        "ite",
        "term",
        "ite",
        "QF_LIA",
        ("(par (A) (ite Bool A A A))",),
        "(set-logic QF_LIA)\n(assert (ite true true false))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (not (ite true true false)))\n"),
        "(set-logic QF_LIA)\n(assert (ite true 0 false))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(declare-const p Bool)\n(assert (= (ite p 1 2) 1))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:parametric-sort"),
    ),
    TheorySymbol(
        "Ints",
        "int",
        "sort",
        "Int",
        "QF_LIA",
        ("(Int 0)",),
        "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (= x 0))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (not (= 0 0)))\n"),
        "(set-logic QF_LIA)\n(declare-const bad (Int Int))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(declare-const huge Int)\n(assert (= huge 123456789012345678901234567890))\n(check-sat)\n",
        ("theory-behavior:sort-arity", "theory-behavior:large-numeral"),
    ),
    TheorySymbol(
        "Ints",
        "numeral",
        "term",
        "_",
        "QF_LIA",
        ("<numeral>",),
        "(set-logic QF_LIA)\n(assert (= 42 42))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (not (= 42 42)))\n"),
        "(set-logic QF_LIA)\n(assert 42)\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (= 123456789012345678901234567890 123456789012345678901234567890))\n(check-sat)\n",
        ("theory-behavior:large-numeral",),
    ),
    TheorySymbol(
        "Ints",
        "neg",
        "term",
        "-",
        "QF_LIA",
        ("(- Int Int)",),
        "(set-logic QF_LIA)\n(assert (= (+ (- 3) 3) 0))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (= (- 3) 3))\n"),
        "(set-logic QF_LIA)\n(assert (= (- 1 2 3) 0))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (= (- 0) 0))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Ints",
        "sub",
        "term",
        "-",
        "QF_LIA",
        ("(- Int Int Int)",),
        "(set-logic QF_LIA)\n(assert (= (- 7 2 3) 2))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (= (- 7 2) 6))\n"),
        "(set-logic QF_LIA)\n(assert (= (- 1 true) 0))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (= (- 10 3 2) 5))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative"),
    ),
    TheorySymbol(
        "Ints",
        "plus",
        "term",
        "+",
        "QF_LIA",
        ("(+ Int Int Int :left-assoc)",),
        "(set-logic QF_LIA)\n(assert (= (+ 1 2 3) 6))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (= (+ 1 2) 4))\n"),
        "(set-logic QF_LIA)\n(assert (= (+ 1) 1))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (= (+ 1 2 3 4) 10))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative", "theory-behavior:overloaded-arithmetic"),
    ),
    TheorySymbol(
        "Ints",
        "times",
        "term",
        "*",
        "QF_NIA",
        ("(* Int Int Int :left-assoc)",),
        "(set-logic QF_NIA)\n(assert (= (* 2 3 4) 24))\n(check-sat)\n",
        proof_script("QF_NIA", "(assert (= (* 2 3) 7))\n"),
        "(set-logic QF_NIA)\n(assert (= (* 2) 2))\n(check-sat)\n",
        "(set-logic QF_NIA)\n(assert (= (* 2 3 4 5) 120))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative", "theory-behavior:overloaded-arithmetic"),
    ),
    TheorySymbol(
        "Ints",
        "pow",
        "term",
        "**",
        "QF_NIA",
        ("(** Int Int Int)",),
        "(set-logic QF_NIA)\n(assert (= (** 2 3) 8))\n(check-sat)\n",
        proof_script("QF_NIA", "(assert (= (** 2 3) 9))\n"),
        "(set-logic QF_NIA)\n(assert (= (** 2 true) 1))\n(check-sat)\n",
        "(set-logic QF_NIA)\n(assert (= (** 2 0) 1))\n(check-sat)\n",
        ("theory-behavior:arity",),
    ),
    TheorySymbol(
        "Ints",
        "div",
        "term",
        "div",
        "QF_LIA",
        ("(div Int Int Int :left-assoc)",),
        "(set-logic QF_LIA)\n(assert (= (div 7 3) 2))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (= (div 7 3) 3))\n"),
        "(set-logic QF_LIA)\n(assert (= (div 7) 7))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (= (div 20 3 2) 3))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative", "theory-behavior:division-modulo"),
    ),
    TheorySymbol(
        "Ints",
        "mod",
        "term",
        "mod",
        "QF_LIA",
        ("(mod Int Int Int :left-assoc)",),
        "(set-logic QF_LIA)\n(assert (= (mod 7 3) 1))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (= (mod 7 3) 2))\n"),
        "(set-logic QF_LIA)\n(assert (= (mod 7) 0))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (= (mod 17 5) 2))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative", "theory-behavior:division-modulo"),
    ),
    TheorySymbol(
        "Ints",
        "abs",
        "term",
        "abs",
        "QF_LIA",
        ("(abs Int Int)",),
        "(set-logic QF_LIA)\n(assert (= (abs (- 7)) 7))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (= (abs (- 7)) (- 7)))\n"),
        "(set-logic QF_LIA)\n(assert (= (abs 1 2) 1))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (= (abs 0) 0))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Ints",
        "divisible",
        "term",
        "divisible",
        "QF_LIA",
        ("((_ divisible n) Int Bool)",),
        "(set-logic QF_LIA)\n(assert ((_ divisible 3) 6))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert ((_ divisible 3) 7))\n"),
        "(set-logic QF_LIA)\n(assert ((_ divisible 3) true))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert ((_ divisible 1) 12345678901234567890))\n(check-sat)\n",
        ("theory-behavior:indexed", "theory-behavior:division-modulo"),
    ),
    TheorySymbol(
        "Ints",
        "le",
        "term",
        "<=",
        "QF_LIA",
        ("(<= Int Int Bool :chainable)",),
        "(set-logic QF_LIA)\n(assert (<= 1 2 3))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (<= 3 2 1))\n"),
        "(set-logic QF_LIA)\n(assert (<= 1 true))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (<= (- 10) 0 10))\n(check-sat)\n",
        ("theory-behavior:chainable", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Ints",
        "lt",
        "term",
        "<",
        "QF_LIA",
        ("(< Int Int Bool :chainable)",),
        "(set-logic QF_LIA)\n(assert (< 1 2 3))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (< 3 2 1))\n"),
        "(set-logic QF_LIA)\n(assert (< 1 true))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (< (- 10) 0 10))\n(check-sat)\n",
        ("theory-behavior:chainable", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Ints",
        "ge",
        "term",
        ">=",
        "QF_LIA",
        ("(>= Int Int Bool :chainable)",),
        "(set-logic QF_LIA)\n(assert (>= 3 2 1))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (>= 1 2 3))\n"),
        "(set-logic QF_LIA)\n(assert (>= 1 true))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (>= 10 0 (- 10)))\n(check-sat)\n",
        ("theory-behavior:chainable", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Ints",
        "gt",
        "term",
        ">",
        "QF_LIA",
        ("(> Int Int Bool :chainable)",),
        "(set-logic QF_LIA)\n(assert (> 3 2 1))\n(check-sat)\n",
        proof_script("QF_LIA", "(assert (> 1 2 3))\n"),
        "(set-logic QF_LIA)\n(assert (> 1 true))\n(check-sat)\n",
        "(set-logic QF_LIA)\n(assert (> 10 0 (- 10)))\n(check-sat)\n",
        ("theory-behavior:chainable", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Reals",
        "real",
        "sort",
        "Real",
        "QF_LRA",
        ("(Real 0)",),
        "(set-logic QF_LRA)\n(declare-const x Real)\n(assert (= x 0.0))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (not (= 0.0 0.0)))\n"),
        "(set-logic QF_LRA)\n(declare-const bad (Real Real))\n(check-sat)\n",
        "(set-logic QF_LRA)\n(declare-const x Real)\n(assert (= x 12345678901234567890.0))\n(check-sat)\n",
        ("theory-behavior:sort-arity", "theory-behavior:large-numeral"),
    ),
    TheorySymbol(
        "Reals",
        "numeral",
        "term",
        "_",
        "QF_LRA",
        ("<numeral>",),
        "(set-logic QF_LRA)\n(assert (= 42 42.0))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (not (= 42 42.0)))\n"),
        "(set-logic QF_LRA)\n(assert 42.0)\n(check-sat)\n",
        "(set-logic QF_LRA)\n(assert (= 123456789012345678901234567890 123456789012345678901234567890.0))\n(check-sat)\n",
        ("theory-behavior:large-numeral",),
    ),
    TheorySymbol(
        "Reals",
        "decimal",
        "term",
        "_",
        "QF_LRA",
        ("<decimal>",),
        "(set-logic QF_LRA)\n(assert (= 1.5 (/ 3.0 2.0)))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (not (= 1.5 (/ 3.0 2.0))))\n"),
        "(set-logic QF_LRA)\n(assert 1.5)\n(check-sat)\n",
        "(set-logic QF_LRA)\n(assert (= 1.50 1.5))\n(check-sat)\n",
        ("theory-behavior:rational-normalization",),
    ),
    TheorySymbol(
        "Reals",
        "neg",
        "term",
        "-",
        "QF_LRA",
        ("(- Real Real)",),
        "(set-logic QF_LRA)\n(assert (= (+ (- 3.0) 3.0) 0.0))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (= (- 3.0) 3.0))\n"),
        "(set-logic QF_LRA)\n(assert (= (- 1.0 2.0 3.0) 0.0))\n(check-sat)\n",
        "(set-logic QF_LRA)\n(assert (= (- 0.0) 0.0))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Reals",
        "sub",
        "term",
        "-",
        "QF_LRA",
        ("(- Real Real Real)",),
        "(set-logic QF_LRA)\n(assert (= (- 7.0 2.0 3.0) 2.0))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (= (- 7.0 2.0) 6.0))\n"),
        "(set-logic QF_LRA)\n(assert (= (- 1.0 true) 0.0))\n(check-sat)\n",
        "(set-logic QF_LRA)\n(assert (= (- 10.0 3.0 2.0) 5.0))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative"),
    ),
    TheorySymbol(
        "Reals",
        "plus",
        "term",
        "+",
        "QF_LRA",
        ("(+ Real Real Real :left-assoc)",),
        "(set-logic QF_LRA)\n(assert (= (+ 1.0 2.0 3.0) 6.0))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (= (+ 1.0 2.0) 4.0))\n"),
        "(set-logic QF_LRA)\n(assert (= (+ 1.0) 1.0))\n(check-sat)\n",
        "(set-logic QF_LRA)\n(assert (= (+ 1.0 2.0 3.0 4.0) 10.0))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative", "theory-behavior:overloaded-arithmetic"),
    ),
    TheorySymbol(
        "Reals",
        "times",
        "term",
        "*",
        "QF_NRA",
        ("(* Real Real Real :left-assoc)",),
        "(set-logic QF_NRA)\n(assert (= (* 2.0 3.0 4.0) 24.0))\n(check-sat)\n",
        proof_script("QF_NRA", "(assert (= (* 2.0 3.0) 7.0))\n"),
        "(set-logic QF_NRA)\n(assert (= (* 2.0) 2.0))\n(check-sat)\n",
        "(set-logic QF_NRA)\n(assert (= (* 2.0 3.0 4.0 5.0) 120.0))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative", "theory-behavior:overloaded-arithmetic"),
    ),
    TheorySymbol(
        "Reals",
        "div",
        "term",
        "/",
        "QF_NRA",
        ("(/ Real Real Real :left-assoc)",),
        "(set-logic QF_NRA)\n(assert (= (/ 3.0 2.0) 1.5))\n(check-sat)\n",
        proof_script("QF_NRA", "(assert (= (/ 3.0 2.0) 2.0))\n"),
        "(set-logic QF_NRA)\n(assert (= (/ 1.0) 1.0))\n(check-sat)\n",
        "(set-logic QF_NRA)\n(assert (= (/ 6.0 2.0 1.5) 2.0))\n(check-sat)\n",
        ("theory-behavior:arity", "theory-behavior:left-associative", "theory-behavior:division-modulo", "theory-behavior:rational-normalization"),
    ),
    TheorySymbol(
        "Reals",
        "le",
        "term",
        "<=",
        "QF_LRA",
        ("(<= Real Real Bool :chainable)",),
        "(set-logic QF_LRA)\n(assert (<= 1.0 2.0 3.0))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (<= 3.0 2.0 1.0))\n"),
        "(set-logic QF_LRA)\n(assert (<= 1.0 true))\n(check-sat)\n",
        "(set-logic QF_LRA)\n(assert (<= (- 10.0) 0.0 10.0))\n(check-sat)\n",
        ("theory-behavior:chainable", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Reals",
        "lt",
        "term",
        "<",
        "QF_LRA",
        ("(< Real Real Bool :chainable)",),
        "(set-logic QF_LRA)\n(assert (< 1.0 2.0 3.0))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (< 3.0 2.0 1.0))\n"),
        "(set-logic QF_LRA)\n(assert (< 1.0 true))\n(check-sat)\n",
        "(set-logic QF_LRA)\n(assert (< (- 10.0) 0.0 10.0))\n(check-sat)\n",
        ("theory-behavior:chainable", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Reals",
        "ge",
        "term",
        ">=",
        "QF_LRA",
        ("(>= Real Real Bool :chainable)",),
        "(set-logic QF_LRA)\n(assert (>= 3.0 2.0 1.0))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (>= 1.0 2.0 3.0))\n"),
        "(set-logic QF_LRA)\n(assert (>= 1.0 true))\n(check-sat)\n",
        "(set-logic QF_LRA)\n(assert (>= 10.0 0.0 (- 10.0)))\n(check-sat)\n",
        ("theory-behavior:chainable", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Reals",
        "gt",
        "term",
        ">",
        "QF_LRA",
        ("(> Real Real Bool :chainable)",),
        "(set-logic QF_LRA)\n(assert (> 3.0 2.0 1.0))\n(check-sat)\n",
        proof_script("QF_LRA", "(assert (> 1.0 2.0 3.0))\n"),
        "(set-logic QF_LRA)\n(assert (> 1.0 true))\n(check-sat)\n",
        "(set-logic QF_LRA)\n(assert (> 10.0 0.0 (- 10.0)))\n(check-sat)\n",
        ("theory-behavior:chainable", "theory-behavior:negative-numeral"),
    ),
    TheorySymbol(
        "Reals_Ints",
        "to-real",
        "term",
        "to_real",
        "QF_NIRA",
        ("(to_real Int Real)",),
        "(set-logic QF_NIRA)\n(assert (= (to_real 2) 2.0))\n(check-sat)\n",
        proof_script("QF_NIRA", "(assert (not (= (to_real 2) 2.0)))\n"),
        "(set-logic QF_NIRA)\n(assert (= (to_real 2.0) 2.0))\n(check-sat)\n",
        "(set-logic QF_NIRA)\n(assert (= (+ (to_real 2) 1.5) 3.5))\n(check-sat)\n",
        ("theory-behavior:conversion", "theory-behavior:overloaded-arithmetic", "theory-behavior:rational-normalization"),
    ),
    TheorySymbol(
        "Reals_Ints",
        "to-int",
        "term",
        "to_int",
        "QF_NIRA",
        ("(to_int Real Int)",),
        "(set-logic QF_NIRA)\n(assert (= (to_int 2.0) 2))\n(check-sat)\n",
        proof_script("QF_NIRA", "(assert (not (= (to_int 2.0) 2)))\n"),
        "(set-logic QF_NIRA)\n(assert (= (to_int 2) 2))\n(check-sat)\n",
        "(set-logic QF_NIRA)\n(assert (= (to_int (/ 7.0 2.0)) 3))\n(check-sat)\n",
        ("theory-behavior:conversion", "theory-behavior:rational-normalization"),
    ),
    TheorySymbol(
        "Reals_Ints",
        "is-int",
        "term",
        "is_int",
        "QF_NIRA",
        ("(is_int Real Bool)",),
        "(set-logic QF_NIRA)\n(assert (is_int 2.0))\n(check-sat)\n",
        proof_script("QF_NIRA", "(assert (is_int 2.5))\n"),
        "(set-logic QF_NIRA)\n(assert (is_int 2))\n(check-sat)\n",
        "(set-logic QF_NIRA)\n(assert (is_int (/ 4.0 2.0)))\n(check-sat)\n",
        ("theory-behavior:conversion", "theory-behavior:rational-normalization"),
    ),
)


ARRAY_RECONSTRUCTION_FILES = (
    "src/HolSmt/SmtLib_Theories.sml",
    "src/HolSmt/HolSmtScript.sml",
    "src/HolSmt/Z3_ProofReplay.sml",
)

BITVECTOR_RECONSTRUCTION_FILES = (
    "src/HolSmt/SmtLib_Theories.sml",
    "src/HolSmt/SmtLib.sml",
    "src/HolSmt/Z3_ProofReplay.sml",
)

FLOATINGPOINT_RECONSTRUCTION_FILES = (
    "src/HolSmt/SmtLib_Theories.sml",
    "src/HolSmt/SmtLib.sml",
    "src/HolSmt/HolSmtScript.sml",
    "src/HolSmt/Z3_ProofReplay.sml",
)

STRING_RECONSTRUCTION_FILES = (
    "src/HolSmt/SmtLib_Parser.sml",
    "src/HolSmt/SmtLib_Theories.sml",
    "src/HolSmt/SmtLib.sml",
    "src/HolSmt/Z3_ProofReplay.sml",
)

Z3_EXTENSION_RECONSTRUCTION_FILES = (
    "src/HolSmt/SmtLib_Theories.sml",
    "src/HolSmt/SmtLib_Logics.sml",
    "src/HolSmt/SmtLib.sml",
    "src/HolSmt/Z3_ProofReplay.sml",
)

Z3_UNSUPPORTED_BITVECTOR_OPERATORS = {
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
}


def array_symbol(
    slug_name: str,
    kind: str,
    name: str,
    declarations: tuple[str, ...],
    sat_body: str,
    unsat_body: str,
    type_error_body: str,
    boundary_body: str,
    behavior_features: tuple[str, ...],
    *,
    logic: str = "QF_AX",
    proof_logic: str | None = None,
) -> TheorySymbol:
    proof_logic = logic if proof_logic is None else proof_logic
    return TheorySymbol(
        "ArraysEx",
        slug_name,
        kind,
        name,
        logic,
        declarations,
        check_sat_script(logic, sat_body),
        proof_script(proof_logic, unsat_body),
        check_sat_script(logic, type_error_body),
        check_sat_script(logic, boundary_body),
        ("theory-behavior:array", *behavior_features),
    )


ARRAY_THEORY_SYMBOLS: tuple[TheorySymbol, ...] = (
    array_symbol(
        "array",
        "sort",
        "Array",
        ("(Array Index Element)",),
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(assert (= a a))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(assert (not (= a a)))\n",
        "(declare-sort I 0)\n(declare-const bad (Array I))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const nested (Array I (Array I E)))\n(assert (= nested nested))\n",
        ("theory-behavior:parametric-sort", "theory-behavior:nested-arrays"),
    ),
    array_symbol(
        "select",
        "term",
        "select",
        ("(par (Index Element) (select (Array Index Element) Index Element))",),
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(assert (= (select a i) (select a i)))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(assert (not (= (select a i) (select a i))))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const e E)\n(assert (= (select a e) e))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const outer (Array I (Array I E)))\n(declare-const i I)\n(assert (= (select (select outer i) i) (select (select outer i) i)))\n",
        ("theory-behavior:select-store", "theory-behavior:nested-arrays"),
    ),
    array_symbol(
        "store",
        "term",
        "store",
        ("(par (Index Element) (store (Array Index Element) Index Element Element (Array Index Element)))",),
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const e E)\n(assert (= (store a i e) (store a i e)))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const e E)\n(assert (not (= (store a i e) (store a i e))))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(assert (= (store a i i) a))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const outer (Array I (Array I E)))\n(declare-const inner (Array I E))\n(declare-const i I)\n(assert (= (store outer i inner) (store outer i inner)))\n",
        ("theory-behavior:select-store", "theory-behavior:nested-arrays"),
    ),
    array_symbol(
        "read-over-write",
        "behavior",
        "read-over-write",
        ("select", "store"),
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const e E)\n(assert (= (select (store a i e) i) e))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const e E)\n(assert (not (= (select (store a i e) i) e)))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(assert (= (select (store a i i) i) i))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const j I)\n(declare-const e E)\n(assert (=> (not (= i j)) (= (select (store a i e) j) (select a j))))\n",
        ("theory-behavior:read-over-write", "theory-behavior:select-store"),
    ),
    array_symbol(
        "write-over-write",
        "behavior",
        "write-over-write",
        ("store",),
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const e1 E)\n(declare-const e2 E)\n(assert (= (store (store a i e1) i e2) (store a i e2)))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const e1 E)\n(declare-const e2 E)\n(assert (not (= (store (store a i e1) i e2) (store a i e2))))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(assert (= (store (store a i i) i i) a))\n",
        "(declare-sort I 0)\n(declare-sort E 0)\n(declare-const a (Array I E))\n(declare-const i I)\n(declare-const j I)\n(declare-const e1 E)\n(declare-const e2 E)\n(assert (= (select (store (store a i e1) j e2) j) e2))\n",
        ("theory-behavior:write-over-write", "theory-behavior:select-store"),
    ),
    array_symbol(
        "extensionality",
        "behavior",
        "extensionality",
        ("Array", "select"),
        "(declare-const a (Array Int Bool))\n(declare-const b (Array Int Bool))\n(assert (forall ((i Int)) (= (select a i) (select b i))))\n(assert (= a b))\n",
        "(declare-const a (Array Int Bool))\n(declare-const b (Array Int Bool))\n(assert (forall ((i Int)) (= (select a i) (select b i))))\n(assert (not (= a b)))\n",
        "(declare-const a (Array Int Bool))\n(assert (forall ((i Bool)) (= (select a i) true)))\n",
        "(declare-const a (Array Int Bool))\n(declare-const b (Array Int Bool))\n(declare-const i Int)\n(assert (not (= a b)))\n(assert (not (= (select a i) (select b i))))\n",
        ("theory-behavior:array-extensionality",),
        logic="AUFLIA",
    ),
    array_symbol(
        "mixed-index-value-sorts",
        "behavior",
        "mixed-index-value-sorts",
        ("Array", "select", "store"),
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 4)))\n(assert (= (select (store a #x00 #b1010) #x00) #b1010))\n",
        "(declare-const a (Array (_ BitVec 8) (_ BitVec 4)))\n(assert (not (= (select (store a #x00 #b1010) #x00) #b1010)))\n",
        "(declare-const a (Array (_ BitVec 8) Bool))\n(assert (= (select a true) true))\n",
        "(declare-const a (Array (_ BitVec 1) (_ BitVec 16)))\n(assert (= (select (store a #b0 #x0001) #b0) #x0001))\n",
        ("theory-behavior:mixed-index-value-sorts", "theory-behavior:bitvector-index"),
        logic="QF_AUFBV",
    ),
)


BITVECTOR_WIDTHS = (1, 2, 3, 4, 8, 16, 32, 64, 128)


def bv_body(
    assertion: str,
    *,
    width: int = 8,
    declarations: str | None = None,
) -> str:
    default_declarations = (
        f"(declare-const a (_ BitVec {width}))\n"
        f"(declare-const b (_ BitVec {width}))\n"
    )
    return (default_declarations if declarations is None else declarations) + f"(assert {assertion})\n"


def bv_self_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(or {term} (not {term}))"
    return f"(= {term} {term})"


def bv_unsat_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(and {term} (not {term}))"
    return f"(not (= {term} {term}))"


def bv_type_error_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(= {term} a)"
    return term


def bitvector_width_boundary_body(extra_assertions: str = "") -> str:
    declarations = "".join(
        f"(declare-const w{width} (_ BitVec {width}))\n"
        for width in BITVECTOR_WIDTHS
    )
    assertions = "".join(f"(assert (= w{width} w{width}))\n" for width in BITVECTOR_WIDTHS)
    return (
        declarations
        + assertions
        + "(assert (= (bvshl #x01 #x08) (bvshl #x01 #x08)))\n"
        + "(assert (= (bvlshr #x80 #x08) (bvlshr #x80 #x08)))\n"
        + "(assert (= (bvashr #x80 #x08) (bvashr #x80 #x08)))\n"
        + "(assert (= (bvudiv #xff #x00) (bvudiv #xff #x00)))\n"
        + "(assert (= (bvurem #xff #x00) (bvurem #xff #x00)))\n"
        + "(assert (= (bvsdiv #x80 #xff) (bvsdiv #x80 #xff)))\n"
        + "(assert (= (concat ((_ extract 7 4) #xab) ((_ extract 3 0) #xab)) #xab))\n"
        + "(assert (= ((_ repeat 2) #b10) #b1010))\n"
        + "(assert (= ((_ zero_extend 2) #b10) #b0010))\n"
        + "(assert (= ((_ sign_extend 2) #b10) #b1110))\n"
        + "(assert (= ((_ rotate_left 1) #b1001) #b0011))\n"
        + "(assert (= ((_ rotate_right 1) #b1001) #b1100))\n"
        + extra_assertions
    )


def bv_symbol(
    slug_name: str,
    name: str,
    declarations: tuple[str, ...],
    term: str,
    result_sort: str,
    behavior_features: tuple[str, ...],
    *,
    kind: str = "term",
    sat_declarations: str | None = None,
    type_error_assertion: str | None = None,
    boundary_assertion: str | None = None,
) -> TheorySymbol:
    features = (
        "theory-behavior:bitvector",
        *(f"theory-width:{width}" for width in BITVECTOR_WIDTHS),
        *behavior_features,
    )
    if name in Z3_UNSUPPORTED_BITVECTOR_OPERATORS:
        features = (*features, "theory-behavior:z3-unsupported")
    sat_body = bv_body(
        bv_self_assertion(term, result_sort),
        declarations=sat_declarations,
    )
    unsat_body = bv_body(
        bv_unsat_assertion(term, result_sort),
        declarations=sat_declarations,
    )
    type_error_body = bv_body(
        type_error_assertion
        if type_error_assertion is not None
        else bv_type_error_assertion(term, result_sort),
        declarations=sat_declarations,
    )
    boundary_body = bitvector_width_boundary_body(
        "" if boundary_assertion is None else f"(assert {boundary_assertion})\n"
    )
    return TheorySymbol(
        "Fixed_Size_BitVectors",
        slug_name,
        kind,
        name,
        "QF_BV",
        declarations,
        check_sat_script("QF_BV", sat_body),
        proof_script("QF_BV", unsat_body),
        check_sat_script("QF_BV", type_error_body),
        check_sat_script("QF_BV", boundary_body),
        features,
    )


BITVECTOR_THEORY_SYMBOLS: tuple[TheorySymbol, ...] = (
    TheorySymbol(
        "Fixed_Size_BitVectors",
        "bitvec",
        "sort",
        "BitVec",
        "QF_BV",
        ("((_ BitVec m) 0)",),
        check_sat_script("QF_BV", "(declare-const a (_ BitVec 8))\n(assert (= a a))\n"),
        proof_script("QF_BV", "(declare-const a (_ BitVec 8))\n(assert (not (= a a)))\n"),
        check_sat_script("QF_BV", "(declare-const bad (_ BitVec 0))\n(assert (= bad bad))\n"),
        check_sat_script("QF_BV", bitvector_width_boundary_body()),
        (
            "theory-behavior:bitvector",
            "theory-behavior:indexed-sort",
            *(f"theory-width:{width}" for width in BITVECTOR_WIDTHS),
        ),
    ),
    bv_symbol(
        "binary-hex-literal",
        "_",
        ("#b<binary>", "#x<hexadecimal>"),
        "#x0f",
        "BitVec",
        ("theory-behavior:literal", "theory-behavior:binary-literal", "theory-behavior:hex-literal"),
        sat_declarations="",
        type_error_assertion="(= #b1 #b00)",
        boundary_assertion="(and (= #b1 #b1) (= #b10 #b10) (= #xffffffffffffffffffffffffffffffff #xffffffffffffffffffffffffffffffff))",
    ),
    bv_symbol(
        "decimal-literal",
        "_",
        ("((_ bv<numeral> m) (_ BitVec m))",),
        "(_ bv15 8)",
        "BitVec",
        ("theory-behavior:literal", "theory-behavior:decimal-literal"),
        sat_declarations="",
        type_error_assertion="(_ bv1 0)",
        boundary_assertion="(and (= (_ bv1 1) #b1) (= (_ bv255 8) #xff) (= (_ bv0 128) (_ bv0 128)))",
    ),
    bv_symbol("concat", "concat", ("(par (m n) (concat (_ BitVec m) (_ BitVec n) (_ BitVec (+ m n))))",), "(concat #b1010 #b0101)", "BitVec", ("theory-behavior:concat",), sat_declarations="", boundary_assertion="(= (concat #b1 #b0) #b10)"),
    bv_symbol("extract", "extract", ("((_ extract i j) (_ BitVec m) (_ BitVec (- i j -1)))",), "((_ extract 3 0) a)", "BitVec", ("theory-behavior:extract", "theory-behavior:indexed"), type_error_assertion="((_ extract 8 0) a)", boundary_assertion="(= ((_ extract 0 0) #b1) #b1)"),
    bv_symbol("bvnot", "bvnot", ("(bvnot (_ BitVec m) (_ BitVec m))",), "(bvnot a)", "BitVec", ("theory-behavior:bitwise", "theory-behavior:unary")),
    bv_symbol("bvneg", "bvneg", ("(bvneg (_ BitVec m) (_ BitVec m))",), "(bvneg a)", "BitVec", ("theory-behavior:arithmetic", "theory-behavior:signed-min-value")),
    bv_symbol("bvand", "bvand", ("(bvand (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)",), "(bvand a b)", "BitVec", ("theory-behavior:bitwise", "theory-behavior:left-associative")),
    bv_symbol("bvor", "bvor", ("(bvor (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)",), "(bvor a b)", "BitVec", ("theory-behavior:bitwise", "theory-behavior:left-associative")),
    bv_symbol("bvxor", "bvxor", ("(bvxor (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)",), "(bvxor a b)", "BitVec", ("theory-behavior:bitwise", "theory-behavior:left-associative")),
    bv_symbol("bvxnor", "bvxnor", ("(bvxnor (_ BitVec m) (_ BitVec m) (_ BitVec m))",), "(bvxnor a b)", "BitVec", ("theory-behavior:bitwise",)),
    bv_symbol("bvadd", "bvadd", ("(bvadd (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)",), "(bvadd a b)", "BitVec", ("theory-behavior:arithmetic", "theory-behavior:left-associative", "theory-behavior:overflow")),
    bv_symbol("bvmul", "bvmul", ("(bvmul (_ BitVec m) (_ BitVec m) (_ BitVec m) :left-assoc)",), "(bvmul a b)", "BitVec", ("theory-behavior:arithmetic", "theory-behavior:left-associative", "theory-behavior:overflow")),
    bv_symbol("bvudiv", "bvudiv", ("(bvudiv (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit",), "(bvudiv a b)", "BitVec", ("theory-behavior:division", "theory-behavior:division-by-zero", "theory-behavior:soundness-audit"), boundary_assertion="(= (bvudiv #xff #x00) (bvudiv #xff #x00))"),
    bv_symbol("bvurem", "bvurem", ("(bvurem (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit",), "(bvurem a b)", "BitVec", ("theory-behavior:remainder", "theory-behavior:division-by-zero", "theory-behavior:soundness-audit"), boundary_assertion="(= (bvurem #xff #x00) (bvurem #xff #x00))"),
    bv_symbol("bvsub", "bvsub", ("(bvsub (_ BitVec m) (_ BitVec m) (_ BitVec m))",), "(bvsub a b)", "BitVec", ("theory-behavior:arithmetic", "theory-behavior:overflow")),
    bv_symbol("bvnand", "bvnand", ("(bvnand (_ BitVec m) (_ BitVec m) (_ BitVec m))",), "(bvnand a b)", "BitVec", ("theory-behavior:bitwise",)),
    bv_symbol("bvnor", "bvnor", ("(bvnor (_ BitVec m) (_ BitVec m) (_ BitVec m))",), "(bvnor a b)", "BitVec", ("theory-behavior:bitwise",)),
    bv_symbol("bvcomp", "bvcomp", ("(bvcomp (_ BitVec m) (_ BitVec m) (_ BitVec 1))",), "(bvcomp a b)", "BitVec", ("theory-behavior:comparison",)),
    bv_symbol("bvsdiv", "bvsdiv", ("(bvsdiv (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit",), "(bvsdiv a b)", "BitVec", ("theory-behavior:division", "theory-behavior:signed", "theory-behavior:division-by-zero", "theory-behavior:signed-min-value", "theory-behavior:soundness-audit"), boundary_assertion="(= (bvsdiv #x80 #xff) (bvsdiv #x80 #xff))"),
    bv_symbol("bvsrem", "bvsrem", ("(bvsrem (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit",), "(bvsrem a b)", "BitVec", ("theory-behavior:remainder", "theory-behavior:signed", "theory-behavior:division-by-zero", "theory-behavior:soundness-audit"), boundary_assertion="(= (bvsrem #x80 #x00) (bvsrem #x80 #x00))"),
    bv_symbol("bvsmod", "bvsmod", ("(bvsmod (_ BitVec m) (_ BitVec m) (_ BitVec m)); division-by-zero semantics require soundness audit",), "(bvsmod a b)", "BitVec", ("theory-behavior:remainder", "theory-behavior:signed", "theory-behavior:division-by-zero", "theory-behavior:soundness-audit"), boundary_assertion="(= (bvsmod #x80 #x00) (bvsmod #x80 #x00))"),
    bv_symbol("bvshl", "bvshl", ("(bvshl (_ BitVec m) (_ BitVec m) (_ BitVec m))",), "(bvshl a b)", "BitVec", ("theory-behavior:shift", "theory-behavior:boundary-shift"), boundary_assertion="(= (bvshl #x01 #x08) (bvshl #x01 #x08))"),
    bv_symbol("bvlshr", "bvlshr", ("(bvlshr (_ BitVec m) (_ BitVec m) (_ BitVec m))",), "(bvlshr a b)", "BitVec", ("theory-behavior:shift", "theory-behavior:boundary-shift"), boundary_assertion="(= (bvlshr #x80 #x08) (bvlshr #x80 #x08))"),
    bv_symbol("bvashr", "bvashr", ("(bvashr (_ BitVec m) (_ BitVec m) (_ BitVec m))",), "(bvashr a b)", "BitVec", ("theory-behavior:shift", "theory-behavior:boundary-shift", "theory-behavior:signed"), boundary_assertion="(= (bvashr #x80 #x08) (bvashr #x80 #x08))"),
    bv_symbol("repeat", "repeat", ("((_ repeat i) (_ BitVec m) (_ BitVec (* i m)))",), "((_ repeat 2) #b10)", "BitVec", ("theory-behavior:repeat", "theory-behavior:indexed"), sat_declarations="", boundary_assertion="(= ((_ repeat 4) #b1) #b1111)"),
    bv_symbol("zero-extend", "zero_extend", ("((_ zero_extend i) (_ BitVec m) (_ BitVec (+ m i)))",), "((_ zero_extend 2) #b10)", "BitVec", ("theory-behavior:extend", "theory-behavior:zero-extend", "theory-behavior:indexed"), sat_declarations="", boundary_assertion="(= ((_ zero_extend 0) #b1) #b1)"),
    bv_symbol("sign-extend", "sign_extend", ("((_ sign_extend i) (_ BitVec m) (_ BitVec (+ m i)))",), "((_ sign_extend 2) #b10)", "BitVec", ("theory-behavior:extend", "theory-behavior:sign-extend", "theory-behavior:indexed"), sat_declarations="", boundary_assertion="(= ((_ sign_extend 3) #b1) #b1111)"),
    bv_symbol("rotate-left", "rotate_left", ("((_ rotate_left i) (_ BitVec m) (_ BitVec m))",), "((_ rotate_left 1) a)", "BitVec", ("theory-behavior:rotate", "theory-behavior:indexed"), boundary_assertion="(= ((_ rotate_left 4) #xab) #xab)"),
    bv_symbol("rotate-right", "rotate_right", ("((_ rotate_right i) (_ BitVec m) (_ BitVec m))",), "((_ rotate_right 1) a)", "BitVec", ("theory-behavior:rotate", "theory-behavior:indexed"), boundary_assertion="(= ((_ rotate_right 4) #xab) #xab)"),
    bv_symbol("bvult", "bvult", ("(bvult (_ BitVec m) (_ BitVec m) Bool)",), "(bvult a b)", "Bool", ("theory-behavior:comparison", "theory-behavior:unsigned")),
    bv_symbol("bvule", "bvule", ("(bvule (_ BitVec m) (_ BitVec m) Bool)",), "(bvule a b)", "Bool", ("theory-behavior:comparison", "theory-behavior:unsigned")),
    bv_symbol("bvugt", "bvugt", ("(bvugt (_ BitVec m) (_ BitVec m) Bool)",), "(bvugt a b)", "Bool", ("theory-behavior:comparison", "theory-behavior:unsigned")),
    bv_symbol("bvuge", "bvuge", ("(bvuge (_ BitVec m) (_ BitVec m) Bool)",), "(bvuge a b)", "Bool", ("theory-behavior:comparison", "theory-behavior:unsigned")),
    bv_symbol("bvslt", "bvslt", ("(bvslt (_ BitVec m) (_ BitVec m) Bool)",), "(bvslt a b)", "Bool", ("theory-behavior:comparison", "theory-behavior:signed")),
    bv_symbol("bvsle", "bvsle", ("(bvsle (_ BitVec m) (_ BitVec m) Bool)",), "(bvsle a b)", "Bool", ("theory-behavior:comparison", "theory-behavior:signed")),
    bv_symbol("bvsgt", "bvsgt", ("(bvsgt (_ BitVec m) (_ BitVec m) Bool)",), "(bvsgt a b)", "Bool", ("theory-behavior:comparison", "theory-behavior:signed")),
    bv_symbol("bvsge", "bvsge", ("(bvsge (_ BitVec m) (_ BitVec m) Bool)",), "(bvsge a b)", "Bool", ("theory-behavior:comparison", "theory-behavior:signed")),
    bv_symbol("ubv-to-int", "ubv_to_int", ("(ubv_to_int (_ BitVec m) Int)",), "(ubv_to_int a)", "Int", ("theory-behavior:conversion", "theory-behavior:unsigned")),
    bv_symbol("sbv-to-int", "sbv_to_int", ("(sbv_to_int (_ BitVec m) Int)",), "(sbv_to_int a)", "Int", ("theory-behavior:conversion", "theory-behavior:signed")),
    bv_symbol("int-to-bv", "int_to_bv", ("((_ int_to_bv m) Int (_ BitVec m))",), "((_ int_to_bv 8) 3)", "BitVec", ("theory-behavior:conversion", "theory-behavior:indexed"), sat_declarations="", boundary_assertion="(= ((_ int_to_bv 1) 3) #b1)"),
    bv_symbol("bvnego", "bvnego", ("(bvnego (_ BitVec m) Bool)",), "(bvnego a)", "Bool", ("theory-behavior:overflow", "theory-behavior:signed-min-value")),
    bv_symbol("bvuaddo", "bvuaddo", ("(bvuaddo (_ BitVec m) (_ BitVec m) Bool)",), "(bvuaddo a b)", "Bool", ("theory-behavior:overflow", "theory-behavior:unsigned")),
    bv_symbol("bvsaddo", "bvsaddo", ("(bvsaddo (_ BitVec m) (_ BitVec m) Bool)",), "(bvsaddo a b)", "Bool", ("theory-behavior:overflow", "theory-behavior:signed")),
    bv_symbol("bvumulo", "bvumulo", ("(bvumulo (_ BitVec m) (_ BitVec m) Bool)",), "(bvumulo a b)", "Bool", ("theory-behavior:overflow", "theory-behavior:unsigned")),
    bv_symbol("bvsmulo", "bvsmulo", ("(bvsmulo (_ BitVec m) (_ BitVec m) Bool)",), "(bvsmulo a b)", "Bool", ("theory-behavior:overflow", "theory-behavior:signed")),
    bv_symbol("bvusubo", "bvusubo", ("(bvusubo (_ BitVec m) (_ BitVec m) Bool)",), "(bvusubo a b)", "Bool", ("theory-behavior:overflow", "theory-behavior:unsigned")),
    bv_symbol("bvssubo", "bvssubo", ("(bvssubo (_ BitVec m) (_ BitVec m) Bool)",), "(bvssubo a b)", "Bool", ("theory-behavior:overflow", "theory-behavior:signed")),
    bv_symbol("bvsdivo", "bvsdivo", ("(bvsdivo (_ BitVec m) (_ BitVec m) Bool)",), "(bvsdivo a b)", "Bool", ("theory-behavior:overflow", "theory-behavior:signed", "theory-behavior:division")),
)


FLOATINGPOINT_WIDTHS = ((5, 11), (8, 24), (11, 53), (15, 113))


def fp_body(
    assertion: str,
    *,
    declarations: str | None = None,
) -> str:
    default_declarations = (
        "(declare-const x Float32)\n"
        "(declare-const y Float32)\n"
        "(declare-const z Float32)\n"
    )
    return (default_declarations if declarations is None else declarations) + f"(assert {assertion})\n"


def fp_self_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(or {term} (not {term}))"
    return f"(= {term} {term})"


def fp_unsat_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(and {term} (not {term}))"
    return f"(not (= {term} {term}))"


def fp_type_error_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(= {term} x)"
    return term


def floatingpoint_boundary_body(extra_assertions: str = "") -> str:
    declarations = "".join(
        f"(declare-const f{eb}_{sb} (_ FloatingPoint {eb} {sb}))\n"
        for eb, sb in FLOATINGPOINT_WIDTHS
    )
    assertions = "".join(
        f"(assert (= f{eb}_{sb} f{eb}_{sb}))\n"
        for eb, sb in FLOATINGPOINT_WIDTHS
    )
    return (
        declarations
        + assertions
        + "(assert (= (_ +zero 8 24) (_ +zero 8 24)))\n"
        + "(assert (= (_ -zero 8 24) (_ -zero 8 24)))\n"
        + "(assert (fp.isInfinite (_ +oo 8 24)))\n"
        + "(assert (fp.isInfinite (_ -oo 8 24)))\n"
        + "(assert (fp.isNaN (_ NaN 8 24)))\n"
        + "(assert (= (fp #b0 #xff #b00000000000000000000000) (_ +oo 8 24)))\n"
        + "(assert (= ((_ to_fp 8 24) RNE #x3f800000) ((_ to_fp 8 24) RNE #x3f800000)))\n"
        + extra_assertions
    )


def fp_symbol(
    slug_name: str,
    name: str,
    declarations: tuple[str, ...],
    term: str,
    result_sort: str,
    behavior_features: tuple[str, ...],
    *,
    kind: str = "term",
    sat_declarations: str | None = None,
    type_error_assertion: str | None = None,
    boundary_assertion: str | None = None,
) -> TheorySymbol:
    sat_body = fp_body(
        fp_self_assertion(term, result_sort),
        declarations=sat_declarations,
    )
    unsat_body = fp_body(
        fp_unsat_assertion(term, result_sort),
        declarations=sat_declarations,
    )
    type_error_body = fp_body(
        type_error_assertion
        if type_error_assertion is not None
        else fp_type_error_assertion(term, result_sort),
        declarations=sat_declarations,
    )
    boundary_body = floatingpoint_boundary_body(
        "" if boundary_assertion is None else f"(assert {boundary_assertion})\n"
    )
    return TheorySymbol(
        "FloatingPoint",
        slug_name,
        kind,
        name,
        "QF_FP",
        declarations,
        check_sat_script("QF_FP", sat_body),
        proof_script("QF_FP", unsat_body),
        check_sat_script("QF_FP", type_error_body),
        check_sat_script("QF_FP", boundary_body),
        (
            "theory-behavior:floatingpoint",
            "theory-behavior:z3-unsupported",
            *behavior_features,
        ),
    )


def fp_sort(slug_name: str, name: str, declaration: str, sat_decl: str) -> TheorySymbol:
    return TheorySymbol(
        "FloatingPoint",
        slug_name,
        "sort",
        name,
        "QF_FP",
        (declaration,),
        check_sat_script("QF_FP", f"{sat_decl}\n(assert (= fpv fpv))\n"),
        proof_script("QF_FP", f"{sat_decl}\n(assert (not (= fpv fpv)))\n"),
        check_sat_script("QF_FP", "(declare-const bad (FloatingPoint))\n"),
        check_sat_script("QF_FP", floatingpoint_boundary_body()),
        (
            "theory-behavior:floatingpoint",
            "theory-behavior:z3-unsupported",
            "theory-behavior:sort-arity",
            "theory-behavior:indexed-sort" if name == "FloatingPoint" else "theory-behavior:standard-sort",
        ),
    )


def fp_constant(slug_name: str, name: str, term: str, extra_features: tuple[str, ...]) -> TheorySymbol:
    return fp_symbol(
        slug_name,
        name,
        (f"((_ {name} eb sb) (_ FloatingPoint eb sb))",),
        term,
        "Float32",
        ("theory-behavior:indexed", "theory-behavior:special-value", *extra_features),
        sat_declarations="",
        type_error_assertion=f"((_ {name} 8))",
        boundary_assertion=f"(= {term} {term})",
    )


FLOATINGPOINT_THEORY_SYMBOLS: tuple[TheorySymbol, ...] = (
    fp_sort("roundingmode", "RoundingMode", "(RoundingMode 0)", "(declare-const fpv RoundingMode)"),
    fp_sort(
        "floatingpoint",
        "FloatingPoint",
        "((_ FloatingPoint eb sb) 0)",
        "(declare-const fpv (_ FloatingPoint 8 24))",
    ),
    fp_sort("float16", "Float16", "(Float16 0)", "(declare-const fpv Float16)"),
    fp_sort("float32", "Float32", "(Float32 0)", "(declare-const fpv Float32)"),
    fp_sort("float64", "Float64", "(Float64 0)", "(declare-const fpv Float64)"),
    fp_sort("float128", "Float128", "(Float128 0)", "(declare-const fpv Float128)"),
    *(
        fp_symbol(
            name.lower().replace("_", "-"),
            name,
            (f"({name} RoundingMode)",),
            name,
            "RoundingMode",
            ("theory-behavior:rounding-mode",),
            sat_declarations="",
            type_error_assertion=f"({name})",
            boundary_assertion=f"(= {name} {name})",
        )
        for name in (
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
        )
    ),
    fp_constant("positive-zero", "+zero", "(_ +zero 8 24)", ("theory-behavior:signed-zero",)),
    fp_constant("negative-zero", "-zero", "(_ -zero 8 24)", ("theory-behavior:signed-zero",)),
    fp_constant("positive-infinity", "+oo", "(_ +oo 8 24)", ("theory-behavior:infinity",)),
    fp_constant("negative-infinity", "-oo", "(_ -oo 8 24)", ("theory-behavior:infinity",)),
    fp_constant("nan", "NaN", "(_ NaN 8 24)", ("theory-behavior:nan",)),
    fp_symbol(
        "fp",
        "fp",
        ("(fp (_ BitVec 1) (_ BitVec eb) (_ BitVec (- sb 1)) (_ FloatingPoint eb sb))",),
        "(fp #b0 #x7f #b00000000000000000000000)",
        "Float32",
        ("theory-behavior:constructor", "theory-behavior:bitvector-encoding"),
        sat_declarations="",
        type_error_assertion="(fp #b0 #x7f #b0)",
        boundary_assertion="(= (fp #b1 #x00 #b00000000000000000000000) (_ -zero 8 24))",
    ),
    fp_symbol("fp.add", "fp.add", ("(fp.add RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.add RNE x y)", "Float32", ("theory-behavior:arithmetic", "theory-behavior:rounding-mode")),
    fp_symbol("fp.sub", "fp.sub", ("(fp.sub RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.sub RNE x y)", "Float32", ("theory-behavior:arithmetic", "theory-behavior:rounding-mode")),
    fp_symbol("fp.mul", "fp.mul", ("(fp.mul RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.mul RNE x y)", "Float32", ("theory-behavior:arithmetic", "theory-behavior:rounding-mode")),
    fp_symbol("fp.div", "fp.div", ("(fp.div RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.div RNE x y)", "Float32", ("theory-behavior:arithmetic", "theory-behavior:division", "theory-behavior:rounding-mode")),
    fp_symbol("fp.fma", "fp.fma", ("(fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.fma RNE x y z)", "Float32", ("theory-behavior:arithmetic", "theory-behavior:fused", "theory-behavior:rounding-mode"), type_error_assertion="(fp.fma RNE x y)"),
    fp_symbol("fp.sqrt", "fp.sqrt", ("(fp.sqrt RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.sqrt RNE x)", "Float32", ("theory-behavior:arithmetic", "theory-behavior:rounding-mode")),
    fp_symbol("fp.roundtointegral", "fp.roundToIntegral", ("(fp.roundToIntegral RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.roundToIntegral RNE x)", "Float32", ("theory-behavior:rounding-mode",)),
    fp_symbol("fp.rem", "fp.rem", ("(fp.rem (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.rem x y)", "Float32", ("theory-behavior:arithmetic", "theory-behavior:remainder")),
    fp_symbol("fp.min", "fp.min", ("(fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.min x y)", "Float32", ("theory-behavior:min-max", "theory-behavior:nan")),
    fp_symbol("fp.max", "fp.max", ("(fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.max x y)", "Float32", ("theory-behavior:min-max", "theory-behavior:nan")),
    fp_symbol("fp.abs", "fp.abs", ("(fp.abs (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.abs x)", "Float32", ("theory-behavior:unary", "theory-behavior:signed-zero")),
    fp_symbol("fp.neg", "fp.neg", ("(fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))",), "(fp.neg x)", "Float32", ("theory-behavior:unary", "theory-behavior:signed-zero")),
    fp_symbol("fp.leq", "fp.leq", ("(fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)",), "(fp.leq x y)", "Bool", ("theory-behavior:comparison", "theory-behavior:chainable"), boundary_assertion="(fp.leq (_ -zero 8 24) (_ +zero 8 24) (_ +oo 8 24))"),
    fp_symbol("fp.lt", "fp.lt", ("(fp.lt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)",), "(fp.lt x y)", "Bool", ("theory-behavior:comparison", "theory-behavior:chainable"), boundary_assertion="(fp.lt (_ -oo 8 24) (_ +oo 8 24))"),
    fp_symbol("fp.geq", "fp.geq", ("(fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)",), "(fp.geq x y)", "Bool", ("theory-behavior:comparison", "theory-behavior:chainable"), boundary_assertion="(fp.geq (_ +oo 8 24) (_ -zero 8 24) (_ +zero 8 24))"),
    fp_symbol("fp.gt", "fp.gt", ("(fp.gt (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)",), "(fp.gt x y)", "Bool", ("theory-behavior:comparison", "theory-behavior:chainable"), boundary_assertion="(fp.gt (_ +oo 8 24) (_ -oo 8 24))"),
    fp_symbol("fp.eq", "fp.eq", ("(fp.eq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool)",), "(fp.eq x y)", "Bool", ("theory-behavior:comparison", "theory-behavior:signed-zero", "theory-behavior:nan")),
    *(
        fp_symbol(
            name.lower(),
            name,
            (f"({name} (_ FloatingPoint eb sb) Bool)",),
            f"({name} x)",
            "Bool",
            ("theory-behavior:predicate", *features),
            boundary_assertion=boundary,
        )
        for name, features, boundary in (
            ("fp.isNormal", ("theory-behavior:classification",), "(not (fp.isNormal (_ NaN 8 24)))"),
            ("fp.isSubnormal", ("theory-behavior:classification",), "(not (fp.isSubnormal (_ +oo 8 24)))"),
            ("fp.isZero", ("theory-behavior:signed-zero",), "(and (fp.isZero (_ +zero 8 24)) (fp.isZero (_ -zero 8 24)))"),
            ("fp.isInfinite", ("theory-behavior:infinity",), "(and (fp.isInfinite (_ +oo 8 24)) (fp.isInfinite (_ -oo 8 24)))"),
            ("fp.isNaN", ("theory-behavior:nan",), "(fp.isNaN (_ NaN 8 24))"),
            ("fp.isNegative", ("theory-behavior:signed-zero",), "(fp.isNegative (_ -zero 8 24))"),
            ("fp.isPositive", ("theory-behavior:signed-zero",), "(fp.isPositive (_ +zero 8 24))"),
        )
    ),
    fp_symbol("to-fp", "to_fp", ("((_ to_fp eb sb) ... (_ FloatingPoint eb sb))",), "((_ to_fp 8 24) RNE 1.0)", "Float32", ("theory-behavior:conversion", "theory-behavior:indexed", "theory-behavior:rounding-mode"), sat_declarations="", type_error_assertion="((_ to_fp 8 24) true)", boundary_assertion="(= ((_ to_fp 8 24) RNE #x3f800000) ((_ to_fp 8 24) RNE #x3f800000))"),
    fp_symbol("to-fp-unsigned", "to_fp_unsigned", ("((_ to_fp_unsigned eb sb) ... (_ FloatingPoint eb sb))",), "((_ to_fp_unsigned 8 24) RNE #x00000001)", "Float32", ("theory-behavior:conversion", "theory-behavior:indexed", "theory-behavior:rounding-mode", "theory-behavior:unsigned"), sat_declarations="", type_error_assertion="((_ to_fp_unsigned 8 24) RNE 1.0)", boundary_assertion="(= ((_ to_fp_unsigned 8 24) RNE #xff) ((_ to_fp_unsigned 8 24) RNE #xff))"),
    fp_symbol("fp.to-ubv", "fp.to_ubv", ("((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))",), "((_ fp.to_ubv 8) RNE x)", "BitVec", ("theory-behavior:conversion", "theory-behavior:indexed", "theory-behavior:rounding-mode", "theory-behavior:unsigned"), type_error_assertion="((_ fp.to_ubv 8) x)"),
    fp_symbol("fp.to-sbv", "fp.to_sbv", ("((_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m))",), "((_ fp.to_sbv 8) RNE x)", "BitVec", ("theory-behavior:conversion", "theory-behavior:indexed", "theory-behavior:rounding-mode", "theory-behavior:signed"), type_error_assertion="((_ fp.to_sbv 8) x)"),
    fp_symbol("fp.to-real", "fp.to_real", ("(fp.to_real (_ FloatingPoint eb sb) Real)",), "(fp.to_real x)", "Real", ("theory-behavior:conversion",), boundary_assertion="(= (fp.to_real (_ +zero 8 24)) 0.0)"),
)


def string_body(
    assertion: str,
    declarations: str = "",
) -> str:
    return declarations + f"(assert {assertion})\n"


def string_self_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(or {term} (not {term}))"
    return f"(= {term} {term})"


def string_unsat_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(and {term} (not {term}))"
    return f"(not (= {term} {term}))"


def string_type_error_assertion(term: str, result_sort: str) -> str:
    if result_sort == "String":
        return term
    return f"(= {term} \"type-error\")"


def string_boundary_body(extra_assertion: str = "") -> str:
    return (
        "(declare-const s String)\n"
        "(assert (= (str.++ \"\" \"abc\") \"abc\"))\n"
        "(assert (= (str.len \"abc\") 3))\n"
        "(assert (str.prefixof \"a\" \"abc\"))\n"
        "(assert (str.in_re \"aa\" ((_ re.loop 1 3) (str.to_re \"a\"))))\n"
        + ("" if not extra_assertion else f"(assert {extra_assertion})\n")
    )


def string_symbol(
    slug_name: str,
    name: str,
    declarations: tuple[str, ...],
    term: str,
    result_sort: str,
    behavior_features: tuple[str, ...],
    *,
    kind: str = "term",
    sat_declarations: str = "",
    type_error_assertion: str | None = None,
    boundary_assertion: str | None = None,
    frontend_gap: bool = True,
) -> TheorySymbol:
    gap_features = (
        ("theory-behavior:translation-gap", "theory-behavior:proof-gap")
        if frontend_gap
        else ()
    )
    return TheorySymbol(
        "UnicodeStrings",
        slug_name,
        kind,
        name,
        "QF_SLIA",
        declarations,
        check_sat_script(
            "QF_SLIA",
            string_body(string_self_assertion(term, result_sort), sat_declarations),
        ),
        proof_script(
            "QF_SLIA",
            string_body(string_unsat_assertion(term, result_sort), sat_declarations),
        ),
        check_sat_script(
            "QF_SLIA",
            string_body(
                type_error_assertion
                if type_error_assertion is not None
                else string_type_error_assertion(term, result_sort),
                sat_declarations,
            ),
        ),
        check_sat_script(
            "QF_SLIA",
            string_boundary_body("" if boundary_assertion is None else boundary_assertion),
        ),
        (
            "theory-behavior:string",
            *gap_features,
            *behavior_features,
        ),
    )


def string_sort(slug_name: str, name: str, declaration: str, sat_decl: str) -> TheorySymbol:
    return TheorySymbol(
        "UnicodeStrings",
        slug_name,
        "sort",
        name,
        "QF_SLIA",
        (declaration,),
        check_sat_script("QF_SLIA", f"{sat_decl}\n(assert (= x x))\n"),
        proof_script("QF_SLIA", f"{sat_decl}\n(assert (not (= x x)))\n"),
        check_sat_script("QF_SLIA", f"(declare-const bad ({name} Bool))\n"),
        check_sat_script("QF_SLIA", string_boundary_body()),
        (
            "theory-behavior:string",
            "theory-behavior:translation-gap",
            "theory-behavior:proof-gap",
            "theory-behavior:sort-arity",
        ),
    )


UNICODE_STRING_THEORY_SYMBOLS: tuple[TheorySymbol, ...] = (
    string_sort("string", "String", "(String 0)", "(declare-const x String)"),
    string_sort("reglan", "RegLan", "(RegLan String)", "(declare-const x (RegLan String))"),
    string_symbol(
        "string-literal",
        "<string literal>",
        ("<string literal token>",),
        "\"abc\"",
        "String",
        ("theory-behavior:literal",),
        kind="literal",
        type_error_assertion="(= \"abc\" 3)",
        boundary_assertion="(= \"line\" \"line\")",
        frontend_gap=False,
    ),
    string_symbol("str-concat", "str.++", ("(str.++ String String String :left-assoc)",), "(str.++ \"a\" \"b\")", "String", ("theory-behavior:left-associative", "theory-behavior:concat")),
    string_symbol("str.len", "str.len", ("(str.len String Int)",), "(str.len \"abc\")", "Int", ("theory-behavior:length", "theory-behavior:string-int")),
    string_symbol("str-lt", "str.<", ("(str.< String String Bool :chainable)",), "(str.< \"a\" \"b\")", "Bool", ("theory-behavior:comparison", "theory-behavior:chainable")),
    string_symbol("str-le", "str.<=", ("(str.<= String String Bool :chainable)",), "(str.<= \"a\" \"b\")", "Bool", ("theory-behavior:comparison", "theory-behavior:chainable")),
    string_symbol("str.at", "str.at", ("(str.at String Int String)",), "(str.at \"abc\" 1)", "String", ("theory-behavior:indexing", "theory-behavior:string-int")),
    string_symbol("str.substr", "str.substr", ("(str.substr String Int Int String)",), "(str.substr \"abc\" 0 2)", "String", ("theory-behavior:substring", "theory-behavior:string-int")),
    string_symbol("str.prefixof", "str.prefixof", ("(str.prefixof String String Bool)",), "(str.prefixof \"a\" \"abc\")", "Bool", ("theory-behavior:predicate", "theory-behavior:prefix")),
    string_symbol("str.suffixof", "str.suffixof", ("(str.suffixof String String Bool)",), "(str.suffixof \"c\" \"abc\")", "Bool", ("theory-behavior:predicate", "theory-behavior:suffix")),
    string_symbol("str.contains", "str.contains", ("(str.contains String String Bool)",), "(str.contains \"abc\" \"b\")", "Bool", ("theory-behavior:predicate", "theory-behavior:contains")),
    string_symbol("str.indexof", "str.indexof", ("(str.indexof String String Int Int)",), "(str.indexof \"abc\" \"b\" 0)", "Int", ("theory-behavior:indexing", "theory-behavior:string-int")),
    string_symbol("str.replace", "str.replace", ("(str.replace String String String String)",), "(str.replace \"abc\" \"b\" \"x\")", "String", ("theory-behavior:replace",)),
    string_symbol("str.replace-all", "str.replace_all", ("(str.replace_all String String String String)",), "(str.replace_all \"aba\" \"a\" \"x\")", "String", ("theory-behavior:replace", "theory-behavior:global-replace")),
    string_symbol("str.is-digit", "str.is_digit", ("(str.is_digit String Bool)",), "(str.is_digit \"7\")", "Bool", ("theory-behavior:predicate", "theory-behavior:code-conversion")),
    string_symbol("str.to-code", "str.to_code", ("(str.to_code String Int)",), "(str.to_code \"A\")", "Int", ("theory-behavior:code-conversion", "theory-behavior:string-int")),
    string_symbol("str.from-code", "str.from_code", ("(str.from_code Int String)",), "(str.from_code 65)", "String", ("theory-behavior:code-conversion", "theory-behavior:string-int")),
    string_symbol("str.to-int", "str.to_int", ("(str.to_int String Int)",), "(str.to_int \"123\")", "Int", ("theory-behavior:int-conversion", "theory-behavior:string-int")),
    string_symbol("str.from-int", "str.from_int", ("(str.from_int Int String)",), "(str.from_int 123)", "String", ("theory-behavior:int-conversion", "theory-behavior:string-int")),
    string_symbol("str.to-re", "str.to_re", ("(str.to_re String (RegLan String))",), "(str.to_re \"a\")", "RegLan", ("theory-behavior:regex", "theory-behavior:conversion")),
    string_symbol("str.in-re", "str.in_re", ("(str.in_re String (RegLan String) Bool)",), "(str.in_re \"a\" (str.to_re \"a\"))", "Bool", ("theory-behavior:regex", "theory-behavior:membership")),
    string_symbol("str.replace-re", "str.replace_re", ("(str.replace_re String (RegLan String) String String)",), "(str.replace_re \"abc\" (str.to_re \"b\") \"x\")", "String", ("theory-behavior:regex", "theory-behavior:replace")),
    string_symbol("str.replace-re-all", "str.replace_re_all", ("(str.replace_re_all String (RegLan String) String String)",), "(str.replace_re_all \"aba\" (str.to_re \"a\") \"x\")", "String", ("theory-behavior:regex", "theory-behavior:replace", "theory-behavior:global-replace")),
    string_symbol("re.none", "re.none", ("(re.none (RegLan String))",), "re.none", "RegLan", ("theory-behavior:regex", "theory-behavior:regex-constant")),
    string_symbol("re.all", "re.all", ("(re.all (RegLan String))",), "re.all", "RegLan", ("theory-behavior:regex", "theory-behavior:regex-constant")),
    string_symbol("re.allchar", "re.allchar", ("(re.allchar (RegLan String))",), "re.allchar", "RegLan", ("theory-behavior:regex", "theory-behavior:regex-constant")),
    string_symbol("re-concat", "re.++", ("(re.++ (RegLan String) (RegLan String) (RegLan String))",), "(re.++ (str.to_re \"a\") (str.to_re \"b\"))", "RegLan", ("theory-behavior:regex", "theory-behavior:concat")),
    string_symbol("re.union", "re.union", ("(re.union (RegLan String) (RegLan String) (RegLan String) :left-assoc)",), "(re.union (str.to_re \"a\") (str.to_re \"b\"))", "RegLan", ("theory-behavior:regex", "theory-behavior:left-associative", "theory-behavior:union")),
    string_symbol("re.inter", "re.inter", ("(re.inter (RegLan String) (RegLan String) (RegLan String) :left-assoc)",), "(re.inter (str.to_re \"a\") re.all)", "RegLan", ("theory-behavior:regex", "theory-behavior:left-associative", "theory-behavior:intersection")),
    string_symbol("re.diff", "re.diff", ("(re.diff (RegLan String) (RegLan String) (RegLan String))",), "(re.diff re.all (str.to_re \"a\"))", "RegLan", ("theory-behavior:regex", "theory-behavior:difference")),
    string_symbol("re-star", "re.*", ("(re.* (RegLan String) (RegLan String))",), "(re.* (str.to_re \"a\"))", "RegLan", ("theory-behavior:regex", "theory-behavior:kleene-star")),
    string_symbol("re-plus", "re.+", ("(re.+ (RegLan String) (RegLan String))",), "(re.+ (str.to_re \"a\"))", "RegLan", ("theory-behavior:regex", "theory-behavior:kleene-plus")),
    string_symbol("re.opt", "re.opt", ("(re.opt (RegLan String) (RegLan String))",), "(re.opt (str.to_re \"a\"))", "RegLan", ("theory-behavior:regex", "theory-behavior:option")),
    string_symbol("re.range", "re.range", ("(re.range String String (RegLan String))",), "(re.range \"a\" \"z\")", "RegLan", ("theory-behavior:regex", "theory-behavior:range")),
    string_symbol("re-power", "re.^", ("((_ re.^ n) (RegLan String) (RegLan String))",), "((_ re.^ 2) (str.to_re \"a\"))", "RegLan", ("theory-behavior:regex", "theory-behavior:indexed", "theory-behavior:power")),
    string_symbol("re.loop", "re.loop", ("((_ re.loop lo hi) (RegLan String) (RegLan String))",), "((_ re.loop 1 3) (str.to_re \"a\"))", "RegLan", ("theory-behavior:regex", "theory-behavior:indexed", "theory-behavior:loop")),
)


def extension_body(assertion: str, declarations: str = "") -> str:
    return declarations + f"(assert {assertion})\n"


def extension_self_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(or {term} (not {term}))"
    return f"(= {term} {term})"


def extension_unsat_assertion(term: str, result_sort: str) -> str:
    if result_sort == "Bool":
        return f"(and {term} (not {term}))"
    return f"(not (= {term} {term}))"


def extension_type_error_assertion(term: str, result_sort: str) -> str:
    if result_sort in {"Seq", "Set", "Bag"}:
        return term
    return f"(= {term} true)"


def extension_boundary_body(extra_assertion: str = "") -> str:
    return (
        "(declare-const xs (Seq Int))\n"
        "(declare-const ys (Seq Int))\n"
        "(declare-const s (Set Int))\n"
        "(declare-const b (Bag Int))\n"
        "(assert (= (seq.++ xs ys) (seq.++ xs ys)))\n"
        "(assert (= (set.insert 1 s) (set.insert 1 s)))\n"
        "(assert (= (bag.count 1 b) (bag.count 1 b)))\n"
        + ("" if not extra_assertion else f"(assert {extra_assertion})\n")
    )


def extension_symbol(
    slug_name: str,
    name: str,
    declarations: tuple[str, ...],
    term: str,
    result_sort: str,
    behavior_features: tuple[str, ...],
    *,
    kind: str = "term",
    sat_declarations: str = "",
    type_error_assertion: str | None = None,
    boundary_assertion: str | None = None,
) -> TheorySymbol:
    return TheorySymbol(
        "Z3_Extensions",
        slug_name,
        kind,
        name,
        "ALL",
        declarations,
        check_sat_script(
            "ALL",
            extension_body(extension_self_assertion(term, result_sort), sat_declarations),
        ),
        proof_script(
            "ALL",
            extension_body(extension_unsat_assertion(term, result_sort), sat_declarations),
        ),
        check_sat_script(
            "ALL",
            extension_body(
                type_error_assertion
                if type_error_assertion is not None
                else extension_type_error_assertion(term, result_sort),
                sat_declarations,
            ),
        ),
        check_sat_script(
            "ALL",
            extension_boundary_body("" if boundary_assertion is None else boundary_assertion),
        ),
        (
            "theory-behavior:z3-extension",
            "theory-behavior:translation-gap",
            "theory-behavior:proof-gap",
            *behavior_features,
        ),
    )


def extension_sort(slug_name: str, name: str, declaration: str, sat_decl: str) -> TheorySymbol:
    return TheorySymbol(
        "Z3_Extensions",
        slug_name,
        "sort",
        name,
        "ALL",
        (declaration,),
        check_sat_script("ALL", f"{sat_decl}\n(assert (= x x))\n"),
        proof_script("ALL", f"{sat_decl}\n(assert (not (= x x)))\n"),
        check_sat_script("ALL", f"(declare-const bad ({name}))\n"),
        check_sat_script("ALL", extension_boundary_body()),
        (
            "theory-behavior:z3-extension",
            "theory-behavior:translation-gap",
            "theory-behavior:proof-gap",
            "theory-behavior:parametric-sort",
        ),
    )


Z3_EXTENSION_THEORY_SYMBOLS: tuple[TheorySymbol, ...] = (
    extension_sort("seq", "Seq", "(Seq Element)", "(declare-const x (Seq Int))"),
    extension_sort("set", "Set", "(Set Element)", "(declare-const x (Set Int))"),
    extension_sort("bag", "Bag", "(Bag Element)", "(declare-const x (Bag Int))"),
    extension_symbol("seq-concat", "seq.++", ("(seq.++ (Seq A) (Seq A) (Seq A) :left-assoc)",), "(seq.++ xs ys)", "Seq", ("theory-behavior:sequence", "theory-behavior:left-associative", "theory-behavior:concat"), sat_declarations="(declare-const xs (Seq Int))\n(declare-const ys (Seq Int))\n"),
    extension_symbol("seq.len", "seq.len", ("(seq.len (Seq A) Int)",), "(seq.len xs)", "Int", ("theory-behavior:sequence", "theory-behavior:length"), sat_declarations="(declare-const xs (Seq Int))\n"),
    extension_symbol("seq.extract", "seq.extract", ("(seq.extract (Seq A) Int Int (Seq A))",), "(seq.extract xs 0 1)", "Seq", ("theory-behavior:sequence", "theory-behavior:extract"), sat_declarations="(declare-const xs (Seq Int))\n"),
    extension_symbol("seq.contains", "seq.contains", ("(seq.contains (Seq A) (Seq A) Bool)",), "(seq.contains xs ys)", "Bool", ("theory-behavior:sequence", "theory-behavior:contains"), sat_declarations="(declare-const xs (Seq Int))\n(declare-const ys (Seq Int))\n"),
    extension_symbol("set.member", "set.member", ("(set.member A (Set A) Bool)",), "(set.member 1 s)", "Bool", ("theory-behavior:set", "theory-behavior:membership"), sat_declarations="(declare-const s (Set Int))\n"),
    extension_symbol("set.insert", "set.insert", ("(set.insert A (Set A) (Set A))",), "(set.insert 1 s)", "Set", ("theory-behavior:set", "theory-behavior:insert"), sat_declarations="(declare-const s (Set Int))\n"),
    extension_symbol("set.union", "set.union", ("(set.union (Set A) (Set A) (Set A) :left-assoc)",), "(set.union s t)", "Set", ("theory-behavior:set", "theory-behavior:left-associative", "theory-behavior:union"), sat_declarations="(declare-const s (Set Int))\n(declare-const t (Set Int))\n"),
    extension_symbol("set.intersect", "set.intersect", ("(set.intersect (Set A) (Set A) (Set A) :left-assoc)",), "(set.intersect s t)", "Set", ("theory-behavior:set", "theory-behavior:left-associative", "theory-behavior:intersection"), sat_declarations="(declare-const s (Set Int))\n(declare-const t (Set Int))\n"),
    extension_symbol("set.minus", "set.minus", ("(set.minus (Set A) (Set A) (Set A))",), "(set.minus s t)", "Set", ("theory-behavior:set", "theory-behavior:difference"), sat_declarations="(declare-const s (Set Int))\n(declare-const t (Set Int))\n"),
    extension_symbol("set.subset", "set.subset", ("(set.subset (Set A) (Set A) Bool)",), "(set.subset s t)", "Bool", ("theory-behavior:set", "theory-behavior:subset"), sat_declarations="(declare-const s (Set Int))\n(declare-const t (Set Int))\n"),
    extension_symbol("bag.union-disjoint", "bag.union_disjoint", ("(bag.union_disjoint (Bag A) (Bag A) (Bag A) :left-assoc)",), "(bag.union_disjoint b c)", "Bag", ("theory-behavior:bag", "theory-behavior:left-associative", "theory-behavior:union"), sat_declarations="(declare-const b (Bag Int))\n(declare-const c (Bag Int))\n"),
    extension_symbol("bag.union-max", "bag.union_max", ("(bag.union_max (Bag A) (Bag A) (Bag A) :left-assoc)",), "(bag.union_max b c)", "Bag", ("theory-behavior:bag", "theory-behavior:left-associative", "theory-behavior:union"), sat_declarations="(declare-const b (Bag Int))\n(declare-const c (Bag Int))\n"),
    extension_symbol("bag.inter-min", "bag.inter_min", ("(bag.inter_min (Bag A) (Bag A) (Bag A) :left-assoc)",), "(bag.inter_min b c)", "Bag", ("theory-behavior:bag", "theory-behavior:left-associative", "theory-behavior:intersection"), sat_declarations="(declare-const b (Bag Int))\n(declare-const c (Bag Int))\n"),
    extension_symbol("bag.difference-subtract", "bag.difference_subtract", ("(bag.difference_subtract (Bag A) (Bag A) (Bag A))",), "(bag.difference_subtract b c)", "Bag", ("theory-behavior:bag", "theory-behavior:difference"), sat_declarations="(declare-const b (Bag Int))\n(declare-const c (Bag Int))\n"),
    extension_symbol("bag.count", "bag.count", ("(bag.count A (Bag A) Int)",), "(bag.count 1 b)", "Int", ("theory-behavior:bag", "theory-behavior:count"), sat_declarations="(declare-const b (Bag Int))\n"),
)


DATATYPE_THEORY_CASES: tuple[ScriptedCase, ...] = (
    ScriptedCase(
        slug="simple-constructors-selectors-testers",
        script=(
            "(set-logic ALL)\n"
            "(declare-datatype Pair ((mk-pair (left Int) (right Bool))))\n"
            "(declare-const p Pair)\n"
            "(assert (= (left (mk-pair 7 true)) 7))\n"
            "(assert ((_ is mk-pair) p))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only", "z3-oracle"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
        },
        features=(
            "theory:Datatypes",
            "theory-entry:Datatypes:simple-constructors-selectors-testers",
            "theory-case:sat",
            "theory-behavior:constructor",
            "theory-behavior:selector",
            "theory-behavior:tester",
        ),
        logic="ALL",
        source_reference="SMT-LIB 2.7 Datatypes theory constructors, selectors, and testers",
    ),
    ScriptedCase(
        slug="constructor-disjointness-replay",
        script=proof_script(
            "ALL",
            "(declare-datatype Color ((red) (blue)))\n"
            "(assert (= red blue))\n",
        ),
        modes=("parser-only", "typecheck-only", "z3-oracle", "proof-parse", "proof-replay", "z3-tac"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
            "proof-parse": expected_result(
                "red",
                diagnostic="datatype disjointness proof parsing evidence is incomplete",
                failure_phase="proof-parse",
                proof_rule_histogram={"th-lemma[datatype]": 1},
            ),
            "proof-replay": expected_result(
                "red",
                diagnostic="datatype constructor disjointness replay is incomplete",
                failure_phase="proof-replay",
                proof_rule_histogram={"th-lemma[datatype]": 1},
            ),
            "z3-tac": expected_result(
                "red",
                diagnostic="checked Z3_TAC reconstruction for datatype disjointness is incomplete",
                failure_phase="proof-replay",
                theorem_shape="closed theorem without oracle tags",
            ),
        },
        features=(
            "theory:Datatypes",
            "theory-entry:Datatypes:constructor-disjointness",
            "theory-case:unsat-proof",
            "theory-behavior:constructor",
            "theory-behavior:disjointness",
            "theory-behavior:proof-gap",
        ),
        implementation_feature="datatypes-reconstruction:constructor-disjointness",
        implementation_files=("src/HolSmt/SmtLib_Datatypes.sml", "src/HolSmt/Z3_ProofReplay.sml"),
        implementation_phase="proof-replay",
        logic="ALL",
        source_reference="SMT-LIB 2.7 Datatypes theory constructor disjointness",
    ),
    ScriptedCase(
        slug="selector-theorem-replay",
        script=proof_script(
            "ALL",
            "(declare-datatype Pair ((mk-pair (left Int) (right Bool))))\n"
            "(assert (not (= (left (mk-pair 7 true)) 7)))\n",
        ),
        modes=("parser-only", "typecheck-only", "z3-oracle", "proof-parse", "proof-replay", "z3-tac"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
            "proof-parse": expected_result(
                "red",
                diagnostic="datatype selector proof parsing evidence is incomplete",
                failure_phase="proof-parse",
                proof_rule_histogram={"th-lemma[datatype]": 1},
            ),
            "proof-replay": expected_result(
                "red",
                diagnostic="datatype selector theorem replay is incomplete",
                failure_phase="proof-replay",
                proof_rule_histogram={"th-lemma[datatype]": 1},
            ),
            "z3-tac": expected_result(
                "red",
                diagnostic="checked Z3_TAC reconstruction for datatype selector theorem is incomplete",
                failure_phase="proof-replay",
                theorem_shape="closed theorem without oracle tags",
            ),
        },
        features=(
            "theory:Datatypes",
            "theory-entry:Datatypes:selector-theorem",
            "theory-case:unsat-proof",
            "theory-behavior:selector",
            "theory-behavior:proof-gap",
        ),
        implementation_feature="datatypes-reconstruction:selector-theorem",
        implementation_files=("src/HolSmt/SmtLib_Datatypes.sml", "src/HolSmt/Z3_ProofReplay.sml"),
        implementation_phase="proof-replay",
        logic="ALL",
        source_reference="SMT-LIB 2.7 Datatypes theory selector theorem",
    ),
    ScriptedCase(
        slug="recursive-datatype",
        script=(
            "(set-logic ALL)\n"
            "(declare-datatype List ((nil) (cons (head Int) (tail List))))\n"
            "(declare-const xs List)\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
        },
        features=(
            "theory:Datatypes",
            "theory-entry:Datatypes:recursive-datatype",
            "theory-case:sat",
            "theory-behavior:recursive-datatype",
        ),
        logic="ALL",
        source_reference="SMT-LIB 2.7 Datatypes theory recursive datatype",
    ),
    ScriptedCase(
        slug="mutual-datatypes",
        script=(
            "(set-logic ALL)\n"
            "(declare-datatypes ((Tree 0) (Forest 0))\n"
            "  (((leaf) (node (children Forest)))\n"
            "   ((nilF) (consF (head Tree) (tail Forest)))))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
        },
        features=(
            "theory:Datatypes",
            "theory-entry:Datatypes:mutual-datatypes",
            "theory-case:sat",
            "theory-behavior:mutual-datatype",
        ),
        logic="ALL",
        source_reference="SMT-LIB 2.7 Datatypes theory mutual datatypes",
    ),
    ScriptedCase(
        slug="parametric-datatype",
        script=(
            "(set-logic ALL)\n"
            "(declare-datatype Box (par (T) ((box (value T)))))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
        },
        features=(
            "theory:Datatypes",
            "theory-entry:Datatypes:parametric-datatype",
            "theory-case:sat",
            "theory-behavior:parametric-datatype",
        ),
        logic="ALL",
        source_reference="SMT-LIB 2.7 Datatypes theory parametric datatype",
    ),
)


HOCORE_THEORY_CASES: tuple[ScriptedCase, ...] = (
    ScriptedCase(
        slug="function-valued-array-declaration",
        script=(
            "(set-logic QF_AUFLIA)\n"
            "(declare-const f (Array Int Bool))\n"
            "(assert (= f f))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only", "z3-oracle", "z3-tac"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
            "z3-tac": expected_result("pass"),
        },
        features=(
            "theory:HO_Core",
            "theory-entry:HO_Core:function-valued-array-declaration",
            "theory-case:sat",
            "theory-behavior:higher-order",
            "theory-behavior:function-sort",
            "higher-order/function-sort",
        ),
        logic="QF_AUFLIA",
        source_reference="SMT-LIB HO-Core function-valued declaration represented by HOL Array/function sort",
    ),
    ScriptedCase(
        slug="function-argument-sort",
        script=(
            "(set-logic QF_AUFLIA)\n"
            "(declare-fun H ((Array Int Bool)) Bool)\n"
            "(declare-const f (Array Int Bool))\n"
            "(assert (H f))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only", "z3-oracle", "z3-tac"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
            "z3-tac": expected_result("pass"),
        },
        features=(
            "theory:HO_Core",
            "theory-entry:HO_Core:function-argument-sort",
            "theory-case:sat",
            "theory-behavior:function-argument",
            "theory-behavior:function-sort",
            "higher-order/function-sort",
        ),
        logic="QF_AUFLIA",
        source_reference="SMT-LIB HO-Core function argument sort",
    ),
    ScriptedCase(
        slug="function-result-sort",
        script=(
            "(set-logic QF_AUFLIA)\n"
            "(declare-fun make () (Array Int Bool))\n"
            "(assert (= make make))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only", "z3-oracle", "z3-tac"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
            "z3-tac": expected_result("pass"),
        },
        features=(
            "theory:HO_Core",
            "theory-entry:HO_Core:function-result-sort",
            "theory-case:sat",
            "theory-behavior:function-result",
            "theory-behavior:function-sort",
            "higher-order/function-sort",
        ),
        logic="QF_AUFLIA",
        source_reference="SMT-LIB HO-Core function result sort",
    ),
    ScriptedCase(
        slug="higher-order-equality",
        script=(
            "(set-logic QF_AUFLIA)\n"
            "(declare-const f (Array Int Bool))\n"
            "(declare-const g (Array Int Bool))\n"
            "(assert (= f g))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only", "z3-oracle", "z3-tac"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
            "z3-tac": expected_result("pass"),
        },
        features=(
            "theory:HO_Core",
            "theory-entry:HO_Core:higher-order-equality",
            "theory-case:sat",
            "theory-behavior:higher-order-equality",
            "theory-behavior:function-sort",
            "higher-order/function-sort",
        ),
        logic="QF_AUFLIA",
        source_reference="SMT-LIB HO-Core higher-order equality",
    ),
    ScriptedCase(
        slug="lambda-like-universal-encoding",
        script=(
            "(set-logic AUFLIA)\n"
            "(declare-fun lam (Int) Bool)\n"
            "(assert (forall ((x Int)) (= (lam x) (> x 0))))\n"
            "(assert (lam 1))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only", "z3-oracle"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
        },
        features=(
            "theory:HO_Core",
            "theory-entry:HO_Core:lambda-like-universal-encoding",
            "theory-case:boundary",
            "theory-behavior:lambda-like-encoding",
            "theory-behavior:first-order-encoding",
        ),
        logic="AUFLIA",
        source_reference="SMT-LIB HO-Core lambda-like behavior encoded with first-order function and universal axiom",
    ),
    ScriptedCase(
        slug="native-function-sort",
        script=(
            "(set-logic ALL)\n"
            "(declare-const f (-> Int Bool))\n"
            "(assert (= f f))\n"
            "(check-sat)\n"
        ),
        modes=("parser-only", "typecheck-only"),
        expected={
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
        },
        features=(
            "theory:HO_Core",
            "theory-entry:HO_Core:native-function-sort",
            "theory-case:type-error",
            "theory-behavior:hocore-native-function-sort",
            "theory-behavior:function-sort",
            "higher-order/function-sort",
        ),
        logic="ALL",
        standard="SMT-LIB-3",
        source_reference="SMT-LIB 3 HO-Core native function sort",
    ),
)


ALL_THEORY_SYMBOLS = (
    *CORE_ARITHMETIC_THEORY_SYMBOLS,
    *UNICODE_STRING_THEORY_SYMBOLS,
    *ARRAY_THEORY_SYMBOLS,
    *BITVECTOR_THEORY_SYMBOLS,
    *FLOATINGPOINT_THEORY_SYMBOLS,
    *Z3_EXTENSION_THEORY_SYMBOLS,
)


def theory_features(symbol: TheorySymbol, kind: str) -> list[str]:
    return [
        f"theory:{symbol.theory}",
        f"theory-kind:{symbol.kind}",
        f"theory-operator:{symbol.theory}:{symbol.name}",
        f"theory-entry:{symbol.theory}:{symbol.slug}",
        f"theory-case:{kind}",
        *(f"theory-declaration:{symbol.theory}:{declaration}" for declaration in symbol.declarations),
        *symbol.behavior_features,
    ]


def theory_obligation(symbol: TheorySymbol, kind: str, case_id: str, failure_phase: str) -> dict[str, object]:
    files = ("src/HolSmt/SmtLib_Theories.sml", "src/HolSmt/Z3_ProofReplay.sml")
    if symbol.theory == "ArraysEx":
        files = ARRAY_RECONSTRUCTION_FILES
    elif symbol.theory == "Fixed_Size_BitVectors":
        files = BITVECTOR_RECONSTRUCTION_FILES
    elif symbol.theory == "FloatingPoint":
        files = FLOATINGPOINT_RECONSTRUCTION_FILES
    elif symbol.theory == "UnicodeStrings":
        files = STRING_RECONSTRUCTION_FILES
    elif symbol.theory == "Z3_Extensions":
        files = Z3_EXTENSION_RECONSTRUCTION_FILES
    return implementation_obligation(
        files=files,
        feature=f"theory-symbol:{symbol.theory}:{symbol.slug}:{kind}",
        test_ids=[case_id],
        failure_phase=failure_phase,
        notes=GENERATED_OBLIGATION_NOTES,
    )


def theory_case_file(symbol: TheorySymbol, case_id: str) -> str:
    if symbol.theory == "UnicodeStrings":
        return f"cases/theories/strings/{slug(case_id)}.smt2"
    if symbol.theory == "Z3_Extensions":
        return f"cases/theories/z3_extensions/{slug(case_id)}.smt2"
    return deterministic_case_file("theory", case_id)


def theory_standard(symbol: TheorySymbol) -> str:
    if symbol.theory == "Z3_Extensions":
        return "Z3-extension"
    return "SMT-LIB-2.7"


def theory_source(symbol: TheorySymbol) -> dict[str, object]:
    if symbol.theory == "Z3_Extensions":
        return source("Z3-extension", f"Z3 sequence/set/bag extension: {symbol.name}")
    return source("SMT-LIB-theory", f"SMT-LIB 2.7 {symbol.theory} theory: {symbol.name}")


ARRAY_TYPE_ERROR_DIAGNOSTICS = {
    "array": "ArraysEx Array sort arity mismatch",
    "select": "ArraysEx select index sort mismatch",
    "store": "ArraysEx store value sort mismatch",
    "read-over-write": "ArraysEx store value sort mismatch",
    "write-over-write": "ArraysEx store value sort mismatch",
    "extensionality": "ArraysEx select index sort mismatch",
    "mixed-index-value-sorts": "ArraysEx select index sort mismatch",
}


def scripted_theory_case_file(theory: str, case_id: str) -> str:
    directory = {
        "Datatypes": "datatypes",
        "HO_Core": "hocore",
    }[theory]
    return f"cases/theories/{directory}/{slug(case_id)}.smt2"


def scripted_theory_case(theory: str, case: ScriptedCase) -> GeneratedCase:
    case_id = f"theory:{theory}:{case.slug}"
    entry = manifest_entry(
        case_id=case_id,
        file=scripted_theory_case_file(theory, case_id),
        logic=case.logic,
        standard=case.standard,
        row_class="theory",
        features=case.features,
        modes=case.modes,
        versions=SUPPORTED_Z3_VERSIONS,
        expected=case.expected,
        implementation_obligation=scripted_obligation(case, case_id),
        source=source(case.source_kind, case.source_reference),
    )
    return GeneratedCase(entry=entry, script=case.script)


def theory_case(symbol: TheorySymbol, kind: str, script: str) -> GeneratedCase:
    case_id = f"theory:{symbol.theory}:{symbol.slug}:{kind}"
    z3_unsupported = "theory-behavior:z3-unsupported" in symbol.behavior_features
    parser_gap = "theory-behavior:parser-gap" in symbol.behavior_features
    translation_gap = "theory-behavior:translation-gap" in symbol.behavior_features
    proof_gap = "theory-behavior:proof-gap" in symbol.behavior_features
    blocked_by_parser = (
        "SMT-LIB string literal tokenization lacks token-kind metadata for this coverage row"
    )
    if kind == "sat":
        modes = ("parser-only", "typecheck-only", "z3-oracle", "z3-tac")
        front_end_gap = parser_gap or z3_unsupported or translation_gap
        expected = {
            "parser-only": expected_result(
                "red" if parser_gap else "pass",
                diagnostic=blocked_by_parser if parser_gap else None,
                failure_phase="parser" if parser_gap else None,
            ),
            "typecheck-only": expected_result(
                "red" if front_end_gap else "pass",
                diagnostic=blocked_by_parser
                if parser_gap else "SMT-LIB 2.7 theory front-end support is incomplete"
                if front_end_gap else None,
                failure_phase="parser" if parser_gap else "typecheck" if front_end_gap else None,
            ),
            "z3-oracle": expected_result(
                "red" if z3_unsupported or parser_gap else "pass",
                diagnostic="Z3 oracle support for this SMT-LIB 2.7 theory symbol is incomplete"
                if z3_unsupported else blocked_by_parser if parser_gap else None,
                failure_phase="solver" if z3_unsupported else "parser" if parser_gap else None,
            ),
            "z3-tac": expected_result(
                "red" if z3_unsupported or parser_gap or translation_gap else "pass",
                diagnostic="checked Z3_TAC cannot reach SAT no-theorem diagnostic until solver support exists"
                if z3_unsupported else blocked_by_parser
                if parser_gap else "SMT-LIB string/regex or Z3-extension translation is incomplete"
                if translation_gap else None,
                failure_phase="solver" if z3_unsupported else "parser"
                if parser_gap else "translation" if translation_gap else None,
            ),
        }
        if z3_unsupported or parser_gap or translation_gap:
            phase = "solver" if z3_unsupported else "parser" if parser_gap else "translation"
            implementation = theory_obligation(symbol, kind, case_id, phase)
        else:
            implementation = None
    elif kind == "unsat-proof":
        modes = ("parser-only", "typecheck-only", "z3-oracle", "proof-parse", "proof-replay", "z3-tac")
        proof_modes_reconstructed = (
            not parser_gap
            and case_id not in UNSAT_PROOF_MODE_BLOCKED_THEORY_CASES
        )
        z3_tac_reconstructed = case_id in RECONSTRUCTED_THEORY_Z3_TAC_UNSAT_PROOFS
        front_end_gap = parser_gap or z3_unsupported or translation_gap
        expected = {
            "parser-only": expected_result(
                "red" if parser_gap else "pass",
                diagnostic=blocked_by_parser if parser_gap else None,
                failure_phase="parser" if parser_gap else None,
            ),
            "typecheck-only": expected_result(
                "red" if front_end_gap else "pass",
                diagnostic=blocked_by_parser
                if parser_gap else "SMT-LIB 2.7 theory front-end support is incomplete"
                if front_end_gap else None,
                failure_phase="parser" if parser_gap else "typecheck" if front_end_gap else None,
            ),
            "z3-oracle": expected_result(
                "red" if z3_unsupported or parser_gap else "pass",
                diagnostic="Z3 oracle support for this SMT-LIB 2.7 theory symbol is incomplete"
                if z3_unsupported else blocked_by_parser if parser_gap else None,
                failure_phase="solver" if z3_unsupported else "parser" if parser_gap else None,
            ),
            "proof-parse": expected_result(
                "pass" if proof_modes_reconstructed else "red",
                diagnostic="Z3 proof is unavailable until solver support for this theory symbol exists"
                if case_id in UNSAT_PROOF_MODE_BLOCKED_THEORY_CASES else blocked_by_parser
                if parser_gap else None
                if proof_modes_reconstructed else "theory proof parsing evidence is incomplete",
                failure_phase="solver" if z3_unsupported else "parser"
                if parser_gap else None
                if proof_modes_reconstructed else "proof-parse",
                proof_rule_histogram=None if proof_modes_reconstructed else {"asserted": 1},
            ),
            "proof-replay": expected_result(
                "pass" if proof_modes_reconstructed else "red",
                diagnostic="Z3 proof replay is unavailable until solver support for this theory symbol exists"
                if case_id in UNSAT_PROOF_MODE_BLOCKED_THEORY_CASES else blocked_by_parser
                if parser_gap else None
                if proof_modes_reconstructed else "theory proof replay evidence is incomplete",
                failure_phase="solver" if z3_unsupported else "parser"
                if parser_gap else None
                if proof_modes_reconstructed else "proof-replay",
                proof_rule_histogram=None if proof_modes_reconstructed else {"asserted": 1},
            ),
            "z3-tac": expected_result(
                "pass" if z3_tac_reconstructed else "red",
                diagnostic=None
                if z3_tac_reconstructed else "checked Z3_TAC reconstruction is blocked by missing solver support"
                if z3_unsupported else blocked_by_parser
                if parser_gap else "SMT-LIB string/regex or Z3-extension translation is incomplete"
                if translation_gap else "checked Z3_TAC reconstruction for theory symbol is incomplete",
                failure_phase=None
                if z3_tac_reconstructed else "solver" if z3_unsupported else "parser"
                if parser_gap else "translation" if translation_gap else "proof-replay",
                theorem_shape=None if z3_tac_reconstructed else "closed theorem without oracle tags",
            ),
        }
        if not any(result["status"] == "red" for result in expected.values()):
            implementation = None
        else:
            phase = first_red_failure_phase(expected)
            implementation = theory_obligation(symbol, kind, case_id, phase)
    elif kind == "type-error":
        modes = ("parser-only", "typecheck-only", "z3-tac")
        if symbol.theory == "ArraysEx":
            diagnostic = ARRAY_TYPE_ERROR_DIAGNOSTICS[symbol.slug]
            expected = {
                "parser-only": expected_result("pass"),
                "typecheck-only": expected_result(
                    "fail",
                    diagnostic=diagnostic,
                    failure_phase="typecheck",
                ),
                "z3-tac": expected_result(
                    "fail",
                    diagnostic=diagnostic,
                    failure_phase="typecheck",
                ),
            }
            implementation = None
        elif symbol.theory == "UnicodeStrings" and symbol.slug == "string-literal":
            expected = {
                "parser-only": expected_result("pass"),
                "typecheck-only": expected_result(
                    "fail",
                    diagnostic="actual sorts [:string, :int]",
                    failure_phase="typecheck",
                ),
                "z3-tac": expected_result(
                    "fail",
                    diagnostic="actual sorts [:string, :int]",
                    failure_phase="typecheck",
                ),
            }
            implementation = None
        else:
            expected = {
                "parser-only": expected_result(
                    "red" if parser_gap else "pass",
                    diagnostic=blocked_by_parser if parser_gap else None,
                    failure_phase="parser" if parser_gap else None,
                ),
                "typecheck-only": expected_result(
                    "red",
                    diagnostic=blocked_by_parser
                    if parser_gap else "negative theory sort/type diagnostics are incomplete",
                    failure_phase="parser" if parser_gap else "typecheck",
                ),
                "z3-tac": expected_result(
                    "red",
                    diagnostic=blocked_by_parser
                    if parser_gap else "negative theory sort/type diagnostics are incomplete",
                    failure_phase="parser" if parser_gap else "typecheck",
                ),
            }
            implementation = theory_obligation(symbol, kind, case_id, "parser" if parser_gap else "typecheck")
    elif kind == "boundary":
        modes = (
            ("parser-only", "typecheck-only", "z3-oracle", "z3-tac")
            if parser_gap or translation_gap
            else ("parser-only", "typecheck-only", "z3-oracle")
        )
        front_end_gap = parser_gap or z3_unsupported or translation_gap
        expected = {
            "parser-only": expected_result(
                "red" if parser_gap else "pass",
                diagnostic=blocked_by_parser if parser_gap else None,
                failure_phase="parser" if parser_gap else None,
            ),
            "typecheck-only": expected_result(
                "red" if front_end_gap else "pass",
                diagnostic=blocked_by_parser
                if parser_gap else "SMT-LIB 2.7 theory front-end support is incomplete"
                if front_end_gap else None,
                failure_phase="parser" if parser_gap else "typecheck" if front_end_gap else None,
            ),
            "z3-oracle": expected_result(
                "red" if z3_unsupported or parser_gap else "pass",
                diagnostic="Z3 oracle support for this SMT-LIB 2.7 theory boundary case is incomplete"
                if z3_unsupported else blocked_by_parser if parser_gap else None,
                failure_phase="solver" if z3_unsupported else "parser" if parser_gap else None,
            ),
        }
        if parser_gap or translation_gap:
            expected["z3-tac"] = expected_result(
                "red",
                diagnostic=blocked_by_parser
                if parser_gap else "SMT-LIB string/regex or Z3-extension translation is incomplete",
                failure_phase="parser" if parser_gap else "translation",
            )
        if z3_unsupported or parser_gap or translation_gap:
            phase = "solver" if z3_unsupported else "parser" if parser_gap else "translation"
            implementation = theory_obligation(symbol, kind, case_id, phase)
        else:
            implementation = None
    else:
        raise GeneratorError(f"unknown theory case kind: {kind}")

    entry = manifest_entry(
        case_id=case_id,
        file=theory_case_file(symbol, case_id),
        logic=symbol.logic,
        standard=theory_standard(symbol),
        row_class="theory",
        features=theory_features(symbol, kind),
        modes=modes,
        versions=SUPPORTED_Z3_VERSIONS,
        expected=expected,
        implementation_obligation=implementation,
        source=theory_source(symbol),
    )
    return GeneratedCase(entry=entry, script=script)


def theory_cases() -> list[GeneratedCase]:
    cases: list[GeneratedCase] = []
    for symbol in ALL_THEORY_SYMBOLS:
        cases.append(theory_case(symbol, "sat", symbol.sat_script))
        cases.append(theory_case(symbol, "unsat-proof", symbol.unsat_proof_script))
        cases.append(theory_case(symbol, "type-error", symbol.type_error_script))
        cases.append(theory_case(symbol, "boundary", symbol.boundary_script))
    cases.extend(scripted_theory_case("Datatypes", case) for case in DATATYPE_THEORY_CASES)
    cases.extend(scripted_theory_case("HO_Core", case) for case in HOCORE_THEORY_CASES)
    return cases


def logic_features(logic: str, kind: str) -> list[str]:
    features = [f"logic:{logic}", f"logic-case:{kind}"]
    if logic in UNDERREPRESENTED_LOGICS:
        features.append("logic-inventory:underrepresented-v1")
    if logic in SPARSE_LOGICS:
        features.append("logic-inventory:sparse-v1")
    return features


def logic_source(logic: str) -> dict[str, object]:
    return source("SMT-LIB-logic", f"SMT-LIB 2.7 logic packet: {logic}")


def logic_has_uninterpreted_functions(logic: str) -> bool:
    return "UF" in logic.removeprefix("QF_")


def logic_allows_int_real_coercion_case_in_checked_modes(logic: str) -> bool:
    stem = logic.removeprefix("QF_")
    return logic_has_uninterpreted_functions(logic) or stem.startswith("A")


def logic_obligation(logic: str, kind: str, case_id: str, failure_phase: str) -> dict[str, object]:
    return implementation_obligation(
        files=("src/HolSmt/SmtLib_Logics.sml", "src/HolSmt/Z3_ProofReplay.sml"),
        feature=f"logic-packet:{logic}:{kind}",
        test_ids=[case_id],
        failure_phase=failure_phase,
        notes=GENERATED_OBLIGATION_NOTES,
    )


def logic_case(
    *,
    logic: str,
    kind: str,
    script: str,
    modes: Sequence[str],
    expected: Mapping[str, Mapping[str, object]],
    implementation: Mapping[str, object] | None = None,
) -> GeneratedCase:
    case_id = f"logic:{logic}:{kind}"
    entry = manifest_entry(
        case_id=case_id,
        file=deterministic_case_file("logic", case_id),
        logic=logic,
        standard="SMT-LIB-2.7",
        row_class="logic",
        features=logic_features(logic, kind),
        modes=modes,
        versions=SUPPORTED_Z3_VERSIONS,
        expected=expected,
        implementation_obligation=implementation,
        source=logic_source(logic),
    )
    return GeneratedCase(entry=entry, script=script)


def logic_fragment_violation_script(logic: str) -> str:
    def script(*body: str) -> str:
        return f"(set-logic {logic})\n" + "".join(
            f"{line}\n" for line in body
        ) + "(check-sat)\n"

    stem = logic.removeprefix("QF_")

    # Difference logics permit only difference atoms such as x - y <= c.
    # Use x + y <= c even for QF_IDL/RDL so these rows exercise the
    # difference-atom restriction, not just quantifier-freeness.
    if stem.endswith("IDL"):
        return script(
            "(declare-const x Int)",
            "(declare-const y Int)",
            "(assert (<= (+ x y) 1))",
        )
    if stem.endswith("RDL"):
        return script(
            "(declare-const x Real)",
            "(declare-const y Real)",
            "(assert (<= (+ x y) 1.0))",
        )

    # Every QF_* logic excludes quantified formulas.
    if logic.startswith("QF_"):
        return script("(assert (forall ((p Bool)) p))")

    # Linear arithmetic logics exclude products of two non-constant terms.
    if stem.endswith(("LIA", "LRA", "LIRA")):
        sort = "Real" if stem.endswith(("LRA", "LIRA")) else "Int"
        one = "1.0" if sort == "Real" else "1"
        return script(
            f"(declare-const x {sort})",
            f"(declare-const y {sort})",
            f"(assert (= (* x y) {one}))",
        )

    # Nonlinear arithmetic logics still restrict the available theories:
    # Int-only NIA excludes Real terms, Real-only NRA excludes Int terms,
    # mixed NIRA without UF excludes uninterpreted functions.  For array
    # NIRA logics, use bit-vectors instead: HolSmt represents ArraysEx
    # select as function application, so a function-shaped witness would be
    # ambiguous after parsing.
    if stem.endswith("NIA"):
        return script(
            "(declare-const outside_fragment Real)",
            "(assert (= outside_fragment 0.0))",
        )
    if stem.endswith("NRA"):
        return script(
            "(declare-const outside_fragment Int)",
            "(assert (= outside_fragment 0))",
        )
    if stem.endswith("NIRA"):
        if "UF" not in stem and not stem.startswith("A"):
            return script(
                "(declare-fun outside_fragment (Int) Int)",
                "(assert (= (outside_fragment 0) 0))",
            )
        return script(
            "(declare-const outside_fragment (_ BitVec 1))",
            "(assert (= outside_fragment #b0))",
        )

    # Pure UF/BV/FP/String/etc. logics that reach this fallback do not
    # include integer arithmetic, so an Int-sorted constant is outside
    # the logic fragment.
    return script(
        "(declare-const outside_fragment Int)",
        "(assert (= outside_fragment 0))",
    )


def logic_fragment_violation_diagnostic(logic: str) -> str:
    stem = logic.removeprefix("QF_")
    if stem.endswith(("IDL", "RDL")):
        prefix = "difference logic atom shape"
    elif logic.startswith("QF_"):
        prefix = "quantified formula"
    elif stem.endswith(("LIA", "LRA", "LIRA")):
        prefix = "nonlinear arithmetic product"
    elif stem.endswith("NIA"):
        prefix = "real term sort"
    elif stem.endswith("NRA"):
        prefix = "integer term sort"
    elif stem.endswith("NIRA"):
        if "UF" not in stem and not stem.startswith("A"):
            prefix = "uninterpreted function application"
        else:
            prefix = "bit-vector term sort"
    elif "BV" in stem or "FP" in stem:
        return f"integer atom is outside bit-vector logic fragment {logic}"
    else:
        prefix = "integer term sort"
    return f"{prefix} is outside logic fragment {logic}"


def logic_nonlinear_replay_script(logic: str) -> str:
    if logic == "QF_NIA":
        body = (
            "(declare-const x Int)\n"
            "(declare-const y Int)\n"
            "(assert (not (=> (and (>= x 0) (>= y 0)) (>= (* x y) 0))))\n"
        )
    elif logic == "NIA":
        body = (
            "(declare-const x Int)\n"
            "(declare-const y Int)\n"
            "(assert (not (=> (and (>= x 5) (>= y 5)) (>= (* x y) 25))))\n"
        )
    elif logic == "QF_NRA":
        body = (
            "(declare-const x Real)\n"
            "(declare-const y Real)\n"
            "(assert (not (< 0.0 (+ 1.0 (* 2.0 x x x x) (* 2.0 x x x y) (- (* x x y y)) (* 5.0 y y y y)))))\n"
        )
    elif logic == "NRA":
        body = (
            "(declare-const x Real)\n"
            "(assert (not (>= (* x x) 0.0)))\n"
        )
    else:
        raise GeneratorError(f"no nonlinear replay script for logic {logic}")
    return (
        "(set-option :produce-proofs true)\n"
        f"(set-logic {logic})\n"
        f"{body}"
        "(check-sat)\n"
        "(get-proof)\n"
    )


def logic_int_real_user_function_coercion_script(logic: str) -> str:
    return (
        f"(set-logic {logic})\n"
        "(declare-const x Int)\n"
        "(declare-fun p (Real) Bool)\n"
        "(assert (p x))\n"
        "(check-sat)\n"
    )


def logic_packet_cases(
    logic_source_path: Path = DEFAULT_LOGIC_SOURCE,
) -> list[GeneratedCase]:
    cases: list[GeneratedCase] = []
    for logic in logic_packet_logics(logic_source_path):
        sat_script = (
            f"(set-logic {logic})\n"
            "(declare-const p Bool)\n"
            "(assert p)\n"
            "(check-sat)\n"
        )
        cases.append(
            logic_case(
                logic=logic,
                kind="sat",
                script=sat_script,
                modes=("parser-only", "typecheck-only", "z3-oracle", "z3-tac"),
                expected={
                    "parser-only": expected_result("pass"),
                    "typecheck-only": expected_result("pass"),
                    "z3-oracle": expected_result("pass"),
                    "z3-tac": expected_result("pass"),
                },
            )
        )

        if logic in INT_REAL_COERCION_LOGICS:
            expected = {"parser-only": expected_result("pass")}
            if logic_allows_int_real_coercion_case_in_checked_modes(logic):
                expected["typecheck-only"] = expected_result("pass")
                expected["z3-tac"] = expected_result("pass")
            else:
                expected["typecheck-only"] = expected_result(
                    "fail",
                    diagnostic=(
                        "uninterpreted function application is outside "
                        f"logic fragment {logic}"
                    ),
                    failure_phase="typecheck",
                )
                expected["z3-tac"] = expected_result(
                    "fail",
                    diagnostic=(
                        "uninterpreted function application is outside "
                        f"logic fragment {logic}"
                    ),
                    failure_phase="typecheck",
                )
            cases.append(
                logic_case(
                    logic=logic,
                    kind="int-real-user-function-coercion",
                    script=logic_int_real_user_function_coercion_script(logic),
                    modes=("parser-only", "typecheck-only", "z3-tac"),
                    expected=expected,
                )
            )

        unsat_case_id = f"logic:{logic}:unsat-proof"
        cases.append(
            logic_case(
                logic=logic,
                kind="unsat-proof",
                script=(
                    "(set-option :produce-proofs true)\n"
                    f"(set-logic {logic})\n"
                    "(assert false)\n"
                    "(check-sat)\n"
                    "(get-proof)\n"
                ),
                modes=(
                    "parser-only",
                    "typecheck-only",
                    "z3-oracle",
                    "proof-parse",
                    "proof-replay",
                    "z3-tac",
                ),
                expected={
                    "parser-only": expected_result("pass"),
                    "typecheck-only": expected_result("pass"),
                    "z3-oracle": expected_result("pass"),
                    "proof-parse": expected_result(
                        "pass",
                    ),
                    "proof-replay": expected_result(
                        "pass",
                    ),
                    "z3-tac": expected_result(
                        "pass",
                    ),
                },
            )
        )

        if logic in {"QF_NIA", "QF_NRA", "NIA", "NRA"}:
            cases.append(
                logic_case(
                    logic=logic,
                    kind="nonlinear-proof",
                    script=logic_nonlinear_replay_script(logic),
                    modes=(
                        "parser-only",
                        "typecheck-only",
                        "z3-oracle",
                        "proof-parse",
                        "proof-replay",
                        "z3-tac",
                    ),
                    expected={
                        "parser-only": expected_result("pass"),
                        "typecheck-only": expected_result("pass"),
                        "z3-oracle": expected_result("pass"),
                        "proof-parse": expected_result("pass"),
                        "proof-replay": expected_result(
                            "pass",
                            theorem_shape="closed theorem without oracle tags",
                        ),
                        "z3-tac": expected_result(
                            "pass",
                            theorem_shape="closed theorem without oracle tags",
                        ),
                    },
                )
            )

        cases.append(
            logic_case(
                logic=logic,
                kind="type-error",
                script=(
                    f"(set-logic {logic})\n"
                    "(declare-fun f (Bool) Bool)\n"
                    "(assert (f true false))\n"
                    "(check-sat)\n"
                ),
                modes=("parser-only", "typecheck-only", "z3-tac"),
                expected={
                    "parser-only": expected_result("pass"),
                    "typecheck-only": expected_result(
                        "fail",
                        diagnostic="function arity mismatch",
                        failure_phase="typecheck",
                    ),
                    "z3-tac": expected_result(
                        "fail",
                        diagnostic="function arity mismatch",
                        failure_phase="typecheck",
                    ),
                },
            )
        )

        cases.append(
            logic_case(
                logic=logic,
                kind="malformed",
                script=f"(set-logic {logic}\n(check-sat)\n",
                modes=("parser-only",),
                expected={
                    "parser-only": expected_result(
                        "fail",
                        diagnostic="missing ')'",
                        failure_phase="parser",
                    )
                },
            )
        )

        fragment_diagnostic = logic_fragment_violation_diagnostic(logic)
        cases.append(
            logic_case(
                logic=logic,
                kind="fragment-violation",
                script=logic_fragment_violation_script(logic),
                modes=("parser-only", "typecheck-only", "z3-tac"),
                expected={
                    "parser-only": expected_result("pass"),
                    "typecheck-only": expected_result(
                        "fail",
                        diagnostic=fragment_diagnostic,
                        failure_phase="typecheck",
                    ),
                    "z3-tac": expected_result(
                        "fail",
                        diagnostic=fragment_diagnostic,
                        failure_phase="typecheck",
                    ),
                },
            )
        )

        cases.append(
            logic_case(
                logic=logic,
                kind="boundary",
                script=(
                    f"(set-logic {logic})\n"
                    "(push 1)\n"
                    "(assert true)\n"
                    "(pop 1)\n"
                    "(check-sat)\n"
                ),
                modes=("parser-only", "typecheck-only", "z3-oracle"),
                expected={
                    "parser-only": expected_result("pass"),
                    "typecheck-only": expected_result("pass"),
                    "z3-oracle": expected_result("pass"),
                },
            )
        )
    return cases


def sample_cases(classes: Iterable[str] = CASE_CLASSES) -> list[GeneratedCase]:
    requested = tuple(classes)
    for row_class in requested:
        require_choice(row_class, "class", CASE_CLASSES)

    samples = [
        red_sample(
            row_class="command",
            feature="command:set-logic",
            logic="QF_UF",
            standard="SMT-LIB-2.7",
            modes=("parser-only",),
            files=("src/HolSmt/SmtLib_Parser.sml",),
            failure_phase="parser",
            source_info=source("SMT-LIB-standard", "SMT-LIB 2.7 set-logic command"),
            script="(set-logic QF_UF)\n(check-sat)\n",
            diagnostic="complete command corpus row is still an implementation obligation",
        ),
        red_sample(
            row_class="theory",
            feature="theory:Core:distinct",
            logic="QF_UF",
            standard="SMT-LIB-2.7",
            modes=("typecheck-only",),
            files=("src/HolSmt/SmtLib_Theories.sml", "src/HolSmt/SmtLib_TypeCheck.sml"),
            failure_phase="typecheck",
            source_info=source("SMT-LIB-theory", "SMT-LIB 2.7 Core theory"),
            script="(set-logic QF_UF)\n(declare-const a Bool)\n(assert (distinct a true))\n(check-sat)\n",
            diagnostic="complete theory corpus row is still an implementation obligation",
        ),
        red_sample(
            row_class="logic",
            feature="logic:QF_LIA:boundary",
            logic="QF_LIA",
            standard="SMT-LIB-2.7",
            modes=("z3-oracle",),
            files=("src/HolSmt/SmtLib_Logics.sml", "src/HolSmt/SmtLib_Translate.sml"),
            failure_phase="translation",
            source_info=source("SMT-LIB-logic", "SMT-LIB 2.7 QF_LIA logic"),
            script="(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n",
            diagnostic="complete logic packet row is still an implementation obligation",
        ),
        th_lemma_proof_rule_case(TH_LEMMA_PROOF_RULE_OBLIGATIONS[0]),
        red_sample(
            row_class="soundness-audit",
            feature="soundness:oracle-tag-boundary",
            logic="QF_UF",
            standard="Z3-extension",
            modes=("z3-tac",),
            files=(
                "src/HolSmt/Z3_ProofReplay.sml",
                "src/HolSmt/z3_tac_driver.sml",
                "src/HolSmt/tools/audit_complete_conformance.py",
            ),
            failure_phase="theorem-shape",
            source_info=source("HolSmt-internal", "checked Z3_TAC oracle-tag boundary"),
            script="(set-logic QF_UF)\n(assert false)\n(check-sat)\n",
            diagnostic="checked theorem-shape evidence for the oracle-tag boundary is still an implementation obligation",
            theorem_shape="closed theorem without oracle tags",
        ),
        red_sample(
            row_class="external-benchmark",
            feature="external:missing-pinned-benchmark-evidence",
            logic="QF_UF",
            standard="SMT-LIB-2.7",
            modes=("parser-only", "z3-oracle"),
            files=("src/HolSmt/tools/import_external_benchmarks.py", "src/HolSmt/tools/external-benchmarks/pinned/manifest.json"),
            failure_phase="solver",
            source_info=source("external-benchmark", "pinned external benchmark importer missing evidence seed"),
            script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n",
            diagnostic="pinned external benchmark evidence is still an implementation obligation",
        ),
    ]
    return [case for case in samples if str(case.entry["class"]) in requested]


def cases_for_domain(domain: str) -> list[GeneratedCase]:
    if domain == "commands":
        return command_cases()
    if domain == "theories":
        return theory_cases()
    if domain == "logics":
        return logic_packet_cases()
    if domain == "proof-rules":
        return proof_rule_cases()
    return sample_cases((DOMAIN_CLASSES[domain],))


def manifest_for_cases(cases: Sequence[GeneratedCase]) -> dict[str, object]:
    entries = sorted((case.entry for case in cases), key=lambda entry: str(entry["id"]))
    return {"schema_version": MANIFEST_SCHEMA_VERSION, "cases": entries}


def load_manifest(path: Path) -> dict[str, object]:
    if not path.exists():
        return {"schema_version": MANIFEST_SCHEMA_VERSION, "cases": []}
    with path.open(encoding="utf-8") as infile:
        data = json.load(infile)
    if not isinstance(data, dict):
        raise GeneratorError(f"{path} must contain a JSON object")
    if data.get("schema_version") != MANIFEST_SCHEMA_VERSION:
        raise GeneratorError(f"{path} must use schema_version {MANIFEST_SCHEMA_VERSION}")
    if not isinstance(data.get("cases"), list):
        raise GeneratorError(f"{path} must contain a cases array")
    return data


def merge_manifest(existing: Mapping[str, object], generated: Sequence[GeneratedCase]) -> dict[str, object]:
    existing_cases = existing.get("cases", [])
    if not isinstance(existing_cases, list):
        raise GeneratorError("existing manifest cases must be a list")
    generated_by_id = {case.case_id: case.entry for case in generated}
    generated_classes = {str(case.entry["class"]) for case in generated}
    retained = []
    for case in existing_cases:
        if not isinstance(case, Mapping):
            retained.append(case)
            continue
        if str(case.get("id")) in generated_by_id:
            continue
        obligation = case.get("implementation_obligation")
        if (
            isinstance(obligation, Mapping)
            and obligation.get("notes") == GENERATED_OBLIGATION_NOTES
            and str(case.get("class")) in generated_classes
        ):
            continue
        retained.append(case)
    merged = retained + list(generated_by_id.values())
    merged.sort(key=lambda case: str(case["id"]))
    return {"schema_version": MANIFEST_SCHEMA_VERSION, "cases": merged}


def validate_manifest(manifest: Mapping[str, object]) -> None:
    sys.path.insert(0, str(TOOLS_DIR))
    import audit_complete_conformance as audit

    audit.validate_v2_manifest(dict(manifest))


def write_json(path: Path, value: Mapping[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=False) + "\n", encoding="utf-8")


def write_generated_cases(case_root: Path, cases: Sequence[GeneratedCase]) -> None:
    for case in sorted(cases, key=lambda item: item.file):
        relative = Path(case.file)
        if relative.parts[0] != "cases":
            raise GeneratorError(f"generated file must start with cases/: {case.file}")
        output = case_root.parent / relative
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(case.script, encoding="utf-8")


def write_logics_json(path: Path, logic_source: Path) -> None:
    write_json(path, logics_manifest(logic_source))


def generate(classes: Iterable[str], manifest_path: Path, *, write: bool) -> dict[str, object]:
    requested = tuple(classes)
    if requested == ("command",):
        cases = command_cases()
    elif requested == ("theory",):
        cases = theory_cases()
    elif requested == ("logic",):
        cases = logic_packet_cases()
    else:
        cases = sample_cases(requested)
    manifest = manifest_for_cases(cases)
    if write:
        manifest = merge_manifest(load_manifest(manifest_path), cases)
        validate_manifest(manifest)
        write_generated_cases(manifest_path.parent / "cases", cases)
        write_json(manifest_path, manifest)
    else:
        validate_manifest(manifest)
    return manifest


def render_manifest(manifest: Mapping[str, object]) -> str:
    return json.dumps(manifest, indent=2, sort_keys=False) + "\n"


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate or audit the HolSmt complete conformance corpus skeleton."
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=DEFAULT_MANIFEST,
        help="manifest path (default: v2/manifest.json)",
    )
    parser.add_argument(
        "--logic-source",
        type=Path,
        default=DEFAULT_LOGIC_SOURCE,
        help="SmtLib_Logics.sml path used to generate logic packets",
    )
    parser.add_argument(
        "--logics-json",
        type=Path,
        default=DEFAULT_LOGICS_JSON,
        help="logic inventory JSON path written by the logics generator",
    )
    subparsers = parser.add_subparsers(dest="command")

    def add_generation_options(subparser: argparse.ArgumentParser) -> None:
        subparser.add_argument(
            "--write",
            action="store_true",
            help="write generated manifest entries and SMT-LIB scripts; default is dry-run JSON output",
        )

    samples = subparsers.add_parser("samples", help="generate one sample entry for every corpus class")
    add_generation_options(samples)

    for domain in DOMAIN_CLASSES:
        subparser = subparsers.add_parser(domain, help=f"generate {domain} sample entries")
        add_generation_options(subparser)

    subparsers.add_parser("audit", help="validate the manifest without generating files")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(list(argv) if argv is not None else sys.argv[1:])
    command = args.command or "samples"

    try:
        if command == "audit":
            manifest = load_manifest(args.manifest)
            validate_manifest(manifest)
            print(f"manifest ok: {len(manifest['cases'])} case(s)")
            return 0

        if command == "samples":
            cases = sample_cases(CASE_CLASSES)
        elif command == "logics":
            cases = logic_packet_cases(args.logic_source)
        else:
            cases = cases_for_domain(command)
        if getattr(args, "write", False):
            manifest = merge_manifest(load_manifest(args.manifest), cases)
            validate_manifest(manifest)
            write_generated_cases(args.manifest.parent / "cases", cases)
            write_json(args.manifest, manifest)
            if command == "logics":
                write_logics_json(args.logics_json, args.logic_source)
        else:
            manifest = manifest_for_cases(cases)
            validate_manifest(manifest)
        if getattr(args, "write", False):
            print(f"wrote {len(cases)} generated case(s) into {args.manifest}")
        else:
            sys.stdout.write(render_manifest(manifest))
        return 0
    except (GeneratorError, OSError, json.JSONDecodeError) as exc:
        print(f"generate_complete_corpus.py: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
