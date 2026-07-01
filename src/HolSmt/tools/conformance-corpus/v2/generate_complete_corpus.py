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
    return implementation_obligation(
        files=("src/HolSmt/SmtLib_Theories.sml", "src/HolSmt/Z3_ProofReplay.sml"),
        feature=f"theory-symbol:{symbol.theory}:{symbol.slug}:{kind}",
        test_ids=[case_id],
        failure_phase=failure_phase,
        notes=GENERATED_OBLIGATION_NOTES,
    )


def theory_case(symbol: TheorySymbol, kind: str, script: str) -> GeneratedCase:
    case_id = f"theory:{symbol.theory}:{symbol.slug}:{kind}"
    if kind == "sat":
        modes = ("parser-only", "typecheck-only", "z3-oracle", "z3-tac")
        expected = {
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
            "z3-tac": expected_result(
                "fail",
                diagnostic="SAT result has no HOL theorem to reconstruct",
                failure_phase="theorem-shape",
            ),
        }
        implementation = None
    elif kind == "unsat-proof":
        modes = ("parser-only", "typecheck-only", "z3-oracle", "proof-parse", "proof-replay", "z3-tac")
        expected = {
            "parser-only": expected_result("pass"),
            "typecheck-only": expected_result("pass"),
            "z3-oracle": expected_result("pass"),
            "proof-parse": expected_result(
                "red",
                diagnostic="theory proof parsing evidence is incomplete",
                failure_phase="proof-parse",
                proof_rule_histogram={"asserted": 1},
            ),
            "proof-replay": expected_result(
                "red",
                diagnostic="theory proof replay evidence is incomplete",
                failure_phase="proof-replay",
                proof_rule_histogram={"asserted": 1},
            ),
            "z3-tac": expected_result(
                "red",
                diagnostic="checked Z3_TAC reconstruction for theory symbol is incomplete",
                failure_phase="proof-replay",
                theorem_shape="closed theorem without oracle tags",
            ),
        }
        implementation = theory_obligation(symbol, kind, case_id, "proof-replay")
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
            "z3-oracle": expected_result("pass"),
        }
        implementation = None
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
    for symbol in CORE_ARITHMETIC_THEORY_SYMBOLS:
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
