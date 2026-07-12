#!/usr/bin/env python3
"""Import pinned external SMT-LIB benchmark cases into the v2 corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, Sequence


TOOLS_DIR = Path(__file__).resolve().parent
DEFAULT_PINNED_MANIFEST = TOOLS_DIR / "external-benchmarks" / "pinned" / "manifest.json"
DEFAULT_SOURCES_LOCK = TOOLS_DIR / "external-benchmarks" / "pinned" / "sources.lock.json"
DEFAULT_CORPUS_ROOT = TOOLS_DIR / "conformance-corpus" / "v2"
DEFAULT_CORPUS_MANIFEST = DEFAULT_CORPUS_ROOT / "manifest.json"
MANIFEST_SCHEMA_VERSION = "2"
PINNED_SCHEMA_VERSION = "holsmt-external-benchmarks-pinned-v1"
LOCK_SCHEMA_VERSION = "holsmt-external-benchmark-sources-lock-v1"
SUPPORTED_Z3_VERSIONS = (
    "2.19.1",
    "4.11.2",
    "4.12.4",
    "4.13.0",
    "4.14.1",
    "4.15.3",
)
MODE_ORDER = (
    "parser-only",
    "typecheck-only",
    "z3-oracle",
    "proof-parse",
    "proof-replay",
    "z3-tac",
)

CURATED_REDUCED_CASES = {
    "curated-reduced/qf_uf_sat.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_UF)
(set-info :status sat)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)
(assert (distinct a b))
(check-sat)
""",
    "curated-reduced/qf_uf_unsat_proof.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_UF)
(set-info :status unsat)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-fun f (U) U)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
(get-proof)
""",
    "curated-reduced/qf_lia_sat.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(assert (<= 0 x))
(assert (<= x 3))
(check-sat)
""",
    "curated-reduced/qf_lia_unsat_proof.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (< x 0))
(assert (<= 0 x))
(check-sat)
(get-proof)
""",
    "curated-reduced/qf_lra_sat.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_LRA)
(set-info :status sat)
(declare-const x Real)
(assert (< 0.0 x))
(assert (< x 1.0))
(check-sat)
""",
    "curated-reduced/qf_lra_unsat_proof.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const x Real)
(assert (< x 0.0))
(assert (<= 0.0 x))
(check-sat)
(get-proof)
""",
    "curated-reduced/qf_bv_sat.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_BV)
(set-info :status sat)
(declare-const x (_ BitVec 4))
(assert (= (bvand x #b1111) x))
(check-sat)
""",
    "curated-reduced/qf_bv_unsat_proof.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_BV)
(set-info :status unsat)
(declare-const x (_ BitVec 4))
(assert (= x #b0000))
(assert (not (= (bvadd x #b0001) #b0001)))
(check-sat)
(get-proof)
""",
    "curated-reduced/qf_auflia_sat.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_AUFLIA)
(set-info :status sat)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select (store a i 7) i) 7))
(check-sat)
""",
    "curated-reduced/qf_auflia_unsat_proof.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const v Int)
(assert (not (= (select (store a i v) i) v)))
(check-sat)
(get-proof)
""",
    "curated-reduced/qf_s_sat.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_S)
(set-info :status sat)
(declare-const s String)
(assert (= (str.++ s "b") "ab"))
(check-sat)
""",
    "curated-reduced/qf_s_unsat_proof.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_S)
(set-info :status unsat)
(assert (not (= (str.++ "a" "b") "ab")))
(check-sat)
(get-proof)
""",
    "curated-reduced/qf_dt_sat.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_DT)
(set-info :status sat)
(declare-datatype Color ((red) (blue)))
(declare-const c Color)
(assert (or (= c red) (= c blue)))
(check-sat)
""",
    "curated-reduced/qf_dt_unsat_proof.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_DT)
(set-info :status unsat)
(declare-datatype Color ((red) (blue)))
(assert (= red blue))
(check-sat)
(get-proof)
""",
    "curated-reduced/qf_ufdt_sat.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_UFDT)
(set-info :status sat)
(declare-sort U 0)
(declare-datatype Color ((red) (blue)))
(declare-fun paint (U) Color)
(declare-const u U)
(assert (= (paint u) red))
(check-sat)
""",
    "curated-reduced/qf_ufdt_unsat_proof.smt2": """(set-info :smt-lib-version 2.7)
(set-logic QF_UFDT)
(set-info :status unsat)
(declare-sort U 0)
(declare-datatype Color ((red) (blue)))
(declare-fun paint (U) Color)
(declare-const u U)
(assert (= (paint u) red))
(assert (= (paint u) blue))
(check-sat)
(get-proof)
""",
}


class ImportErrorWithContext(ValueError):
    pass


@dataclass(frozen=True)
class PinnedEntry:
    raw: Mapping[str, object]

    @property
    def case_id(self) -> str:
        return require_string(self.raw.get("id"), "entry.id")

    @property
    def target_file(self) -> str:
        return require_string(self.raw.get("target_file"), f"{self.case_id}.target_file")

    @property
    def source_url(self) -> str:
        return require_string(self.raw.get("source_url"), f"{self.case_id}.source_url")

    @property
    def sha256(self) -> str:
        value = require_string(self.raw.get("sha256"), f"{self.case_id}.sha256")
        if len(value) != 64 or any(char not in "0123456789abcdef" for char in value):
            raise ImportErrorWithContext(f"{self.case_id}.sha256 must be a lowercase SHA256 hex digest")
        return value


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ImportErrorWithContext(message)


def require_string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise ImportErrorWithContext(f"{label} must be a non-empty string")
    return value


def require_string_list(value: object, label: str) -> list[str]:
    if not isinstance(value, list) or not value:
        raise ImportErrorWithContext(f"{label} must be a non-empty list")
    result = [require_string(item, f"{label} item") for item in value]
    if len(set(result)) != len(result):
        raise ImportErrorWithContext(f"{label} must not contain duplicates")
    return result


def load_json(path: Path) -> object:
    with path.open(encoding="utf-8") as infile:
        return json.load(infile)


def write_json(path: Path, value: Mapping[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=False) + "\n", encoding="utf-8")


def read_pinned_content(entry: PinnedEntry) -> bytes:
    content = entry.raw.get("content")
    if isinstance(content, str):
        return content.encode("utf-8")
    if entry.raw.get("source_id") == "curated-reduced":
        source_path = require_string(entry.raw.get("source_path"), f"{entry.case_id}.source_path")
        if source_path not in CURATED_REDUCED_CASES:
            raise ImportErrorWithContext(f"{entry.case_id} has unknown curated source_path: {source_path}")
        return CURATED_REDUCED_CASES[source_path].encode("utf-8")
    with urllib.request.urlopen(entry.source_url, timeout=60) as response:
        return response.read()


def verify_sha256(entry: PinnedEntry, data: bytes) -> None:
    actual = hashlib.sha256(data).hexdigest()
    if actual != entry.sha256:
        raise ImportErrorWithContext(
            f"{entry.case_id} hash mismatch: expected {entry.sha256}, got {actual}"
        )


def validate_sources_lock(data: object) -> Mapping[str, object]:
    require(isinstance(data, dict), "sources lock must be an object")
    require(data.get("schema_version") == LOCK_SCHEMA_VERSION, "sources lock schema_version is invalid")
    sources = data.get("sources")
    require(isinstance(sources, list) and sources, "sources lock must contain a non-empty sources list")
    for index, source in enumerate(sources, 1):
        require(isinstance(source, dict), f"sources lock source {index} must be an object")
        for field in ("id", "kind", "url", "pin", "pin_type"):
            require_string(source.get(field), f"sources lock source {index}.{field}")
    return data


def validate_pinned_manifest(data: object, sources_lock: Mapping[str, object]) -> list[PinnedEntry]:
    require(isinstance(data, dict), "pinned manifest must be an object")
    require(data.get("schema_version") == PINNED_SCHEMA_VERSION, "pinned manifest schema_version is invalid")
    source_ids = {
        require_string(source.get("id"), "sources lock source.id")
        for source in sources_lock.get("sources", [])
        if isinstance(source, dict)
    }
    families = set(require_string_list(data.get("supported_logic_families"), "supported_logic_families"))
    entries = data.get("entries")
    require(isinstance(entries, list) and entries, "pinned manifest entries must be a non-empty list")
    result = [PinnedEntry(entry) for entry in entries if isinstance(entry, dict)]
    require(len(result) == len(entries), "every pinned manifest entry must be an object")
    seen_ids: set[str] = set()
    for entry in result:
        require(entry.case_id not in seen_ids, f"duplicate pinned entry id: {entry.case_id}")
        seen_ids.add(entry.case_id)
        require_string(entry.raw.get("source_id"), f"{entry.case_id}.source_id")
        require(str(entry.raw["source_id"]) in source_ids, f"{entry.case_id}.source_id is not in sources.lock.json")
        require_string(entry.raw.get("source_path"), f"{entry.case_id}.source_path")
        require_string(entry.raw.get("commit_or_release"), f"{entry.case_id}.commit_or_release")
        require_string(entry.raw.get("logic"), f"{entry.case_id}.logic")
        if entry.raw.get("logic_family") is not None:
            require_string(entry.raw.get("logic_family"), f"{entry.case_id}.logic_family")
        require_string_list(entry.raw.get("features"), f"{entry.case_id}.features")
        modes = require_string_list(entry.raw.get("expected_modes"), f"{entry.case_id}.expected_modes")
        invalid_modes = sorted(set(modes) - set(MODE_ORDER))
        require(not invalid_modes, f"{entry.case_id}.expected_modes contains invalid modes: {', '.join(invalid_modes)}")
        expected = entry.raw.get("expected_status")
        require(isinstance(expected, dict) and expected, f"{entry.case_id}.expected_status must be an object")
        require(set(expected) == set(modes), f"{entry.case_id}.expected_status keys must match expected_modes")
        for mode, value in expected.items():
            require(isinstance(value, dict), f"{entry.case_id}.expected_status[{mode}] must be an object")
            require(value.get("status") in {"pass", "fail", "red"}, f"{entry.case_id}.expected_status[{mode}].status is invalid")
        if any(isinstance(value, dict) and value.get("status") == "red" for value in expected.values()):
            require(isinstance(entry.raw.get("implementation_obligation"), dict), f"{entry.case_id} red rows require implementation_obligation")
        else:
            require(entry.raw.get("implementation_obligation") is None, f"{entry.case_id} must use null implementation_obligation without red rows")
        require(entry.target_file.startswith("cases/external/"), f"{entry.case_id}.target_file must be under cases/external/")
        require(entry.target_file.endswith(".smt2"), f"{entry.case_id}.target_file must end with .smt2")
    validate_family_evidence(families, result)
    return result


def validate_family_evidence(families: set[str], entries: Sequence[PinnedEntry]) -> None:
    missing: dict[str, list[str]] = {}
    for family in sorted(families):
        family_entries = [
            entry for entry in entries
            if entry.raw.get("logic_family") == family and entry.raw.get("include_in_v2", True) is not False
        ]
        kinds = {
            feature
            for entry in family_entries
            for feature in entry.raw.get("features", [])
            if isinstance(feature, str)
        }
        family_missing = []
        if "external-status:sat" not in kinds:
            family_missing.append("sat")
        if "external-status:unsat-proof" not in kinds:
            family_missing.append("unsat-proof")
        if family_missing:
            has_obligation = any(
                "external-obligation:missing-benchmark-evidence" in entry.raw.get("features", [])
                for entry in family_entries
            )
            if not has_obligation:
                missing[family] = family_missing
    if missing:
        details = ", ".join(f"{family}: {', '.join(kinds)}" for family, kinds in missing.items())
        raise ImportErrorWithContext(f"missing external SAT/UNSAT proof evidence or red obligation for {details}")


def ordered_modes(modes: Sequence[str]) -> list[str]:
    return sorted(modes, key=MODE_ORDER.index)


def v2_case_for_entry(entry: PinnedEntry) -> dict[str, object]:
    modes = ordered_modes(require_string_list(entry.raw.get("expected_modes"), f"{entry.case_id}.expected_modes"))
    expected = entry.raw["expected_status"]
    assert isinstance(expected, dict)
    expected_by_mode = {mode: dict(expected[mode]) for mode in modes}
    source = {
        "kind": require_string(entry.raw.get("v2_source_kind", "external-benchmark"), f"{entry.case_id}.v2_source_kind"),
        "reference": require_string(entry.raw.get("source_reference"), f"{entry.case_id}.source_reference"),
        "url": entry.source_url,
        "notes": (
            f"pinned source_path={entry.raw['source_path']}; "
            f"pin={entry.raw['commit_or_release']}; sha256={entry.sha256}"
        ),
    }
    return {
        "id": entry.case_id,
        "file": entry.target_file,
        "logic": require_string(entry.raw.get("logic"), f"{entry.case_id}.logic"),
        "standard": require_string(entry.raw.get("standard", "SMT-LIB-2.7"), f"{entry.case_id}.standard"),
        "class": "external-benchmark",
        "features": sorted(require_string_list(entry.raw.get("features"), f"{entry.case_id}.features")),
        "modes": modes,
        "versions": list(SUPPORTED_Z3_VERSIONS),
        "expected": expected_by_mode,
        "implementation_obligation": (
            dict(entry.raw["implementation_obligation"])
            if isinstance(entry.raw.get("implementation_obligation"), dict)
            else None
        ),
        "source": source,
    }


def load_corpus_manifest(path: Path) -> dict[str, object]:
    if not path.exists():
        return {"schema_version": MANIFEST_SCHEMA_VERSION, "cases": []}
    data = load_json(path)
    require(isinstance(data, dict), "v2 manifest must be an object")
    require(data.get("schema_version") == MANIFEST_SCHEMA_VERSION, "v2 manifest schema_version is invalid")
    require(isinstance(data.get("cases"), list), "v2 manifest cases must be a list")
    return data


def merge_v2_manifest(existing: Mapping[str, object], imported_cases: Sequence[dict[str, object]]) -> dict[str, object]:
    imported_by_id = {str(case["id"]): case for case in imported_cases}
    retained = []
    for case in existing.get("cases", []):
        if not isinstance(case, dict):
            retained.append(case)
            continue
        case_id = str(case.get("id"))
        if case_id in imported_by_id:
            continue
        if case.get("class") == "external-benchmark":
            source = case.get("source")
            obligation = case.get("implementation_obligation")
            if (
                isinstance(source, dict)
                and str(source.get("reference", "")).startswith("pinned reduced QF_UF benchmark smoke")
            ):
                continue
            if (
                isinstance(obligation, dict)
                and obligation.get("notes") == "Generated red seed row; keep red until executable evidence is added."
            ):
                continue
        retained.append(case)
    merged = retained + list(imported_by_id.values())
    merged.sort(key=lambda item: str(item.get("id")))
    return {"schema_version": MANIFEST_SCHEMA_VERSION, "cases": merged}


def validate_v2_manifest(manifest: Mapping[str, object]) -> None:
    sys.path.insert(0, str(TOOLS_DIR))
    import audit_complete_conformance as audit

    audit.validate_v2_manifest(dict(manifest))


def import_entries(
    *,
    entries: Sequence[PinnedEntry],
    corpus_root: Path,
    corpus_manifest: Path,
    write: bool,
) -> dict[str, object]:
    verified_payloads: dict[str, bytes] = {}
    imported_cases: list[dict[str, object]] = []
    for entry in entries:
        if entry.raw.get("include_in_v2", True) is False:
            continue
        payload = read_pinned_content(entry)
        verify_sha256(entry, payload)
        verified_payloads[entry.target_file] = payload
        imported_cases.append(v2_case_for_entry(entry))

    manifest = merge_v2_manifest(load_corpus_manifest(corpus_manifest), imported_cases)
    validate_v2_manifest(manifest)
    if write:
        for target_file, payload in sorted(verified_payloads.items()):
            path = corpus_root / target_file
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
        write_json(corpus_manifest, manifest)
    return manifest


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pinned-manifest", type=Path, default=DEFAULT_PINNED_MANIFEST)
    parser.add_argument("--sources-lock", type=Path, default=DEFAULT_SOURCES_LOCK)
    parser.add_argument("--corpus-root", type=Path, default=DEFAULT_CORPUS_ROOT)
    parser.add_argument("--corpus-manifest", type=Path, default=DEFAULT_CORPUS_MANIFEST)
    parser.add_argument("--check", action="store_true", help="verify and print merged manifest without writing files")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        sources_lock = validate_sources_lock(load_json(args.sources_lock))
        entries = validate_pinned_manifest(load_json(args.pinned_manifest), sources_lock)
        manifest = import_entries(
            entries=entries,
            corpus_root=args.corpus_root,
            corpus_manifest=args.corpus_manifest,
            write=not args.check,
        )
    except ImportErrorWithContext as err:
        print(f"import_external_benchmarks: {err}", file=sys.stderr)
        return 1
    if args.check:
        print(json.dumps(manifest, indent=2, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
