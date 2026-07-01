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
EXPECTED_STATUSES = ("pass", "fail", "red")
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
        reconstruction_diagnostic="get-info/get-option response semantics are not reconstructed",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/tools/conformance-corpus"),
    ),
    CommandGroup(
        slug="declare-sort",
        commands=("declare-sort",),
        positive_script="(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(declare-sort U 1)\n",
        state_script="(set-logic QF_UF)\n(declare-sort U 0)\n(push 1)\n(declare-const a U)\n(pop 1)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(declare-sort U 0)\n(declare-const a U)\n(assert (= a a))\n(check-sat)\n",
        negative_diagnostic="declare-sort arity",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="abstract sort reconstruction coverage is incomplete",
        reconstruction_phase="translation",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/SmtLib_Translate.sml"),
    ),
    CommandGroup(
        slug="define-sort",
        commands=("define-sort",),
        positive_script="(set-logic QF_UF)\n(define-sort UAlias () Bool)\n(declare-const p UAlias)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(define-sort Bad () Bad)\n",
        state_script="(set-logic QF_UF)\n(define-sort Pair (A B) Bool)\n(declare-const p Bool)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(define-sort UAlias () Bool)\n(assert true)\n(check-sat)\n",
        negative_diagnostic="recursive sort alias",
        negative_phase="typecheck",
        reconstruction_applies=False,
        reconstruction_diagnostic="define-sort alias replay evidence is incomplete",
        reconstruction_phase="translation",
        obligation_files=("src/HolSmt/SmtLib_TypeCheck.sml", "src/HolSmt/SmtLib_Translate.sml"),
    ),
    CommandGroup(
        slug="declare-const",
        commands=("declare-const",),
        positive_script="(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const i Int)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(declare-const p Bool)\n(declare-const p Int)\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert (not p))\n(check-sat)\n",
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
        state_script="(set-logic QF_UF)\n(declare-fun pred (Int) Bool)\n(declare-const x Int)\n(assert (pred x))\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(declare-fun h ((-> Bool Bool)) Bool)\n(check-sat)\n",
        negative_diagnostic="function arity mismatch",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="function-sort and higher-order command replay is incomplete",
        reconstruction_phase="translation",
        obligation_files=("src/HolSmt/SmtLib_TypeCheck.sml", "src/HolSmt/SmtLib_Translate.sml"),
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
        obligation_files=("src/HolSmt/SmtLib_TypeCheck.sml", "src/HolSmt/Z3_ProofReplay.sml"),
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
        obligation_files=("src/HolSmt/SmtLib_TypeCheck.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="define-fun-rec-define-funs-rec",
        commands=("define-fun-rec", "define-funs-rec"),
        positive_script="(set-logic QF_UF)\n(define-fun-rec f ((p Bool)) Bool p)\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(define-funs-rec ((f ((p Bool)) Bool)) ())\n",
        state_script="(set-logic QF_UF)\n(define-funs-rec ((f ((p Bool)) Bool)) ((not p)))\n(assert (f false))\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(define-fun-rec f ((p Bool)) Bool (f p))\n(check-sat)\n",
        negative_diagnostic="malformed recursive definition block",
        negative_phase="parser",
        reconstruction_applies=True,
        reconstruction_diagnostic="recursive definition semantics are not implemented for checked replay",
        reconstruction_phase="translation",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/SmtLib_Translate.sml"),
    ),
    CommandGroup(
        slug="declare-datatype-declare-datatypes",
        commands=("declare-datatype", "declare-datatypes"),
        positive_script="(set-logic QF_UF)\n(declare-datatype Color ((red) (blue)))\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(declare-datatypes ((Tree 0)) (((node (left Tree) (right Tree)))))\n",
        state_script="(set-logic QF_UF)\n(declare-datatypes ((Color 0)) (((red) (blue))))\n(declare-const c Color)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(declare-datatype Color ((red) (blue)))\n(assert (not (= red blue)))\n(check-sat)\n",
        negative_diagnostic="recursive datatype",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="datatype constructor replay is incomplete",
        reconstruction_phase="translation",
        obligation_files=("src/HolSmt/SmtLib_Datatypes.sml", "src/HolSmt/Z3_ProofReplay.sml"),
    ),
    CommandGroup(
        slug="assert",
        commands=("assert",),
        positive_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert (! p :named named_p))\n(check-sat)\n",
        negative_script="(set-logic QF_UF)\n(declare-const x Int)\n(assert x)\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(push 1)\n(assert p)\n(pop 1)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(assert false)\n(check-sat)\n(get-proof)\n",
        negative_diagnostic="assert term must have Bool sort",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="assertion replay coverage for command corpus is incomplete",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_TypeCheck.sml", "src/HolSmt/Z3_ProofReplay.sml"),
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
        negative_script="(set-logic QF_UF)\n(declare-const x Int)\n(check-sat-assuming (x))\n",
        state_script="(set-logic QF_UF)\n(declare-const p Bool)\n(push 1)\n(check-sat-assuming (p))\n(pop 1)\n(check-sat)\n",
        reconstruction_script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert (! p :named p_name))\n(check-sat-assuming ((not p)))\n",
        negative_diagnostic="assumption literal must have Bool sort",
        negative_phase="typecheck",
        reconstruction_applies=True,
        reconstruction_diagnostic="checked theorem reconstruction with assumptions is not implemented",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_TypeCheck.sml", "src/HolSmt/Z3_ProofReplay.sml"),
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
        reconstruction_script="(set-option :produce-unsat-cores true)\n(set-logic QF_UF)\n(assert (! false :named bad))\n(check-sat)\n(get-unsat-core)\n",
        negative_diagnostic="unsat core requested before unsat result",
        negative_phase="solver",
        reconstruction_applies=True,
        reconstruction_diagnostic="unsat-core and unsat-assumption extraction is not implemented",
        reconstruction_phase="proof-replay",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/Z3_ProofReplay.sml"),
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
        reconstruction_diagnostic="model/value response objects are not produced by checked reconstruction",
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
        reconstruction_script="(set-logic QF_UF)\n(assert false)\n(reset-assertions)\n(check-sat)\n",
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
        reconstruction_script="(set-logic QF_UF)\n(assert false)\n(exit)\n(check-sat)\n",
        negative_diagnostic="malformed exit",
        negative_phase="parser",
        reconstruction_applies=False,
        reconstruction_diagnostic="exit finalization behavior is not represented in theorem reconstruction",
        reconstruction_phase="theorem-shape",
        obligation_files=("src/HolSmt/SmtLib_Parser.sml", "src/HolSmt/tools/conformance-corpus"),
    ),
)


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
        cases.append(
            command_case(
                group,
                "state",
                group.state_script,
                ("typecheck-only", "z3-oracle"),
                {
                    "typecheck-only": expected_result(
                        "pass",
                        notes=f"theorem reconstruction applies: {str(group.reconstruction_applies).lower()}",
                    ),
                    "z3-oracle": expected_result(
                        "pass",
                        notes=f"theorem reconstruction applies: {str(group.reconstruction_applies).lower()}",
                    ),
                },
            )
        )
        reconstruction_case_id = f"command:{group.slug}:reconstruction"
        cases.append(
            command_case(
                group,
                "reconstruction",
                group.reconstruction_script,
                ("z3-tac",),
                {
                    "z3-tac": expected_result(
                        "red",
                        diagnostic=group.reconstruction_diagnostic,
                        failure_phase=group.reconstruction_phase,
                        notes=f"theorem reconstruction applies: {str(group.reconstruction_applies).lower()}",
                    )
                },
                implementation=implementation_obligation(
                    files=group.obligation_files,
                    feature=f"command-reconstruction:{group.slug}",
                    test_ids=[reconstruction_case_id],
                    failure_phase=group.reconstruction_phase,
                    notes=GENERATED_OBLIGATION_NOTES,
                ),
            )
        )
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


ALL_THEORY_SYMBOLS = (
    *CORE_ARITHMETIC_THEORY_SYMBOLS,
    *ARRAY_THEORY_SYMBOLS,
    *BITVECTOR_THEORY_SYMBOLS,
    *FLOATINGPOINT_THEORY_SYMBOLS,
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
    return implementation_obligation(
        files=files,
        feature=f"theory-symbol:{symbol.theory}:{symbol.slug}:{kind}",
        test_ids=[case_id],
        failure_phase=failure_phase,
        notes=GENERATED_OBLIGATION_NOTES,
    )


def theory_case(symbol: TheorySymbol, kind: str, script: str) -> GeneratedCase:
    case_id = f"theory:{symbol.theory}:{symbol.slug}:{kind}"
    z3_unsupported = "theory-behavior:z3-unsupported" in symbol.behavior_features
    if kind == "sat":
        modes = ("parser-only", "typecheck-only", "z3-oracle", "z3-tac")
        expected = {
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result(
                "red" if z3_unsupported else "pass",
                diagnostic="Z3 oracle support for this SMT-LIB 2.7 theory symbol is incomplete"
                if z3_unsupported else None,
                failure_phase="solver" if z3_unsupported else None,
            ),
            "z3-tac": expected_result(
                "red" if z3_unsupported else "fail",
                diagnostic="checked Z3_TAC cannot reach SAT no-theorem diagnostic until solver support exists"
                if z3_unsupported else "SAT result has no HOL theorem to reconstruct",
                failure_phase="solver" if z3_unsupported else "theorem-shape",
            ),
        }
        implementation = theory_obligation(symbol, kind, case_id, "solver") if z3_unsupported else None
    elif kind == "unsat-proof":
        modes = ("parser-only", "typecheck-only", "z3-oracle", "proof-parse", "proof-replay", "z3-tac")
        expected = {
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result(
                "red" if z3_unsupported else "pass",
                diagnostic="Z3 oracle support for this SMT-LIB 2.7 theory symbol is incomplete"
                if z3_unsupported else None,
                failure_phase="solver" if z3_unsupported else None,
            ),
            "proof-parse": expected_result(
                "red",
                diagnostic="Z3 proof is unavailable until solver support for this theory symbol exists"
                if z3_unsupported else "theory proof parsing evidence is incomplete",
                failure_phase="solver" if z3_unsupported else "proof-parse",
                proof_rule_histogram={"asserted": 1},
            ),
            "proof-replay": expected_result(
                "red",
                diagnostic="Z3 proof replay is unavailable until solver support for this theory symbol exists"
                if z3_unsupported else "theory proof replay evidence is incomplete",
                failure_phase="solver" if z3_unsupported else "proof-replay",
                proof_rule_histogram={"asserted": 1},
            ),
            "z3-tac": expected_result(
                "red",
                diagnostic="checked Z3_TAC reconstruction is blocked by missing solver support"
                if z3_unsupported else "checked Z3_TAC reconstruction for theory symbol is incomplete",
                failure_phase="solver" if z3_unsupported else "proof-replay",
                theorem_shape="closed theorem without oracle tags",
            ),
        }
        implementation = theory_obligation(symbol, kind, case_id, "solver" if z3_unsupported else "proof-replay")
    elif kind == "type-error":
        modes = ("parser-only", "typecheck-only", "z3-tac")
        expected = {
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result(
                "fail",
                diagnostic="theory symbol arity or sort mismatch",
                failure_phase="typecheck",
            ),
            "z3-tac": expected_result(
                "fail",
                diagnostic="theory symbol arity or sort mismatch",
                failure_phase="typecheck",
            ),
        }
        implementation = None
    elif kind == "boundary":
        modes = ("parser-only", "typecheck-only", "z3-oracle")
        expected = {
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result(
                "red" if z3_unsupported else "pass",
                diagnostic="Z3 oracle support for this SMT-LIB 2.7 theory boundary case is incomplete"
                if z3_unsupported else None,
                failure_phase="solver" if z3_unsupported else None,
            ),
        }
        implementation = theory_obligation(symbol, kind, case_id, "solver") if z3_unsupported else None
    else:
        raise GeneratorError(f"unknown theory case kind: {kind}")

    entry = manifest_entry(
        case_id=case_id,
        file=deterministic_case_file("theory", case_id),
        logic=symbol.logic,
        standard="SMT-LIB-2.7",
        row_class="theory",
        features=theory_features(symbol, kind),
        modes=modes,
        versions=SUPPORTED_Z3_VERSIONS,
        expected=expected,
        implementation_obligation=implementation,
        source=source("SMT-LIB-theory", f"SMT-LIB 2.7 {symbol.theory} theory: {symbol.name}"),
    )
    return GeneratedCase(entry=entry, script=script)


def theory_cases() -> list[GeneratedCase]:
    cases: list[GeneratedCase] = []
    for symbol in ALL_THEORY_SYMBOLS:
        cases.append(theory_case(symbol, "sat", symbol.sat_script))
        cases.append(theory_case(symbol, "unsat-proof", symbol.unsat_proof_script))
        cases.append(theory_case(symbol, "type-error", symbol.type_error_script))
        cases.append(theory_case(symbol, "boundary", symbol.boundary_script))
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
    if logic.startswith("QF_"):
        return (
            f"(set-logic {logic})\n"
            "(assert (forall ((p Bool)) p))\n"
            "(check-sat)\n"
        )
    if any(token in logic for token in ("LIA", "IDL", "NIA")):
        return (
            f"(set-logic {logic})\n"
            "(declare-const x Int)\n"
            "(declare-const y Int)\n"
            "(assert (= (* x y) 1))\n"
            "(check-sat)\n"
        )
    if any(token in logic for token in ("LRA", "NRA", "LIRA", "NIRA")):
        return (
            f"(set-logic {logic})\n"
            "(declare-const x Real)\n"
            "(declare-const y Real)\n"
            "(assert (= (* x y) 1.0))\n"
            "(check-sat)\n"
        )
    return (
        f"(set-logic {logic})\n"
        "(declare-const outside_fragment Int)\n"
        "(assert (= outside_fragment 0))\n"
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
                    "z3-tac": expected_result(
                        "fail",
                        diagnostic="SAT result has no HOL theorem to reconstruct",
                        failure_phase="theorem-shape",
                    ),
                },
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
                        "red",
                        diagnostic="logic proof parsing evidence is incomplete",
                        failure_phase="proof-parse",
                        proof_rule_histogram={"asserted": 1},
                    ),
                    "proof-replay": expected_result(
                        "red",
                        diagnostic="logic proof replay evidence is incomplete",
                        failure_phase="proof-replay",
                        proof_rule_histogram={"asserted": 1},
                    ),
                    "z3-tac": expected_result(
                        "red",
                        diagnostic="checked Z3_TAC reconstruction for logic packet is incomplete",
                        failure_phase="proof-replay",
                        theorem_shape="closed theorem without oracle tags",
                    ),
                },
                implementation=logic_obligation(logic, "unsat-proof", unsat_case_id, "proof-replay"),
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
                        diagnostic="malformed set-logic command",
                        failure_phase="parser",
                    )
                },
            )
        )

        fragment_case_id = f"logic:{logic}:fragment-violation"
        cases.append(
            logic_case(
                logic=logic,
                kind="fragment-violation",
                script=logic_fragment_violation_script(logic),
                modes=("parser-only", "typecheck-only", "z3-tac"),
                expected={
                    "parser-only": expected_result("pass"),
                    "typecheck-only": expected_result(
                        "red",
                        diagnostic="logic fragment restrictions are not completely enforced",
                        failure_phase="typecheck",
                    ),
                    "z3-tac": expected_result(
                        "red",
                        diagnostic="checked mode must reject logic fragment violations before reconstruction",
                        failure_phase="typecheck",
                    ),
                },
                implementation=logic_obligation(
                    logic,
                    "fragment-violation",
                    fragment_case_id,
                    "typecheck",
                ),
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
        red_sample(
            row_class="proof-rule",
            feature="proof-rule:asserted",
            logic="QF_UF",
            standard="Z3-extension",
            modes=("proof-parse", "proof-replay"),
            files=("src/HolSmt/Z3_ProofParser.sml", "src/HolSmt/Z3_ProofReplay.sml"),
            failure_phase="proof-replay",
            source_info=source("Z3-proof", "Z3 proof rule asserted"),
            script="(set-option :produce-proofs true)\n(set-logic QF_UF)\n(assert false)\n(check-sat)\n(get-proof)\n",
            diagnostic="complete proof-rule row is still an implementation obligation",
            proof_rule_histogram={"asserted": 1},
        ),
        red_sample(
            row_class="soundness-audit",
            feature="soundness:oracle-tag-boundary",
            logic="QF_UF",
            standard="Z3-extension",
            modes=("z3-tac",),
            files=("src/HolSmt/Z3.sml", "src/HolSmt/Z3_ProofReplay.sml"),
            failure_phase="oracle-tag",
            source_info=source("HolSmt-internal", "checked Z3_TAC oracle-tag boundary"),
            script="(set-logic QF_UF)\n(assert false)\n(check-sat)\n",
            diagnostic="complete soundness audit row is still an implementation obligation",
            theorem_shape="closed theorem without oracle tags",
        ),
        red_sample(
            row_class="external-benchmark",
            feature="external:reduced-qf-uf-smoke",
            logic="QF_UF",
            standard="SMT-LIB-2.7",
            modes=("parser-only", "z3-oracle"),
            files=("src/HolSmt/tools/external-benchmarks",),
            failure_phase="solver",
            source_info=source("external-benchmark", "pinned reduced QF_UF benchmark smoke"),
            script="(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n",
            diagnostic="complete external benchmark row is still an implementation obligation",
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
