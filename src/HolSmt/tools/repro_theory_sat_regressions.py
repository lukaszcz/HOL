#!/usr/bin/env python3
"""Usage: repro_theory_sat_regressions.py [--timeout SECONDS]."""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys
from dataclasses import dataclass


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
DEFAULT_CORPUS_ROOT = SCRIPT_DIR / "conformance-corpus" / "v2"
DEFAULT_MANIFEST = DEFAULT_CORPUS_ROOT / "manifest.json"
DEFAULT_DRIVER = REPO_ROOT / "src" / "HolSmt" / "holsmt-z3-tac"


# TASK_01 pins the 29 num-bridge divergence rows.  The v2 manifest also
# has theory:Reals:decimal:sat; that decimal-literal smoke is deliberately
# not part of this regression set.
EXPECTED_IDS = (
    "theory:Ints:abs:sat",
    "theory:Ints:div:sat",
    "theory:Ints:divisible:sat",
    "theory:Ints:ge:sat",
    "theory:Ints:gt:sat",
    "theory:Ints:int:sat",
    "theory:Ints:le:sat",
    "theory:Ints:lt:sat",
    "theory:Ints:mod:sat",
    "theory:Ints:neg:sat",
    "theory:Ints:numeral:sat",
    "theory:Ints:plus:sat",
    "theory:Ints:pow:sat",
    "theory:Ints:sub:sat",
    "theory:Ints:times:sat",
    "theory:Reals:div:sat",
    "theory:Reals:ge:sat",
    "theory:Reals:gt:sat",
    "theory:Reals:le:sat",
    "theory:Reals:lt:sat",
    "theory:Reals:neg:sat",
    "theory:Reals:numeral:sat",
    "theory:Reals:plus:sat",
    "theory:Reals:real:sat",
    "theory:Reals:sub:sat",
    "theory:Reals:times:sat",
    "theory:Reals_Ints:is-int:sat",
    "theory:Reals_Ints:to-int:sat",
    "theory:Reals_Ints:to-real:sat",
)

EXPECTED_ARITHMETIC_EXTRA_IDS = frozenset({
    "theory:Reals:decimal:sat",
})


@dataclass(frozen=True)
class Case:
    case_id: str
    logic: str
    path: pathlib.Path


def die(message: str) -> None:
    print(f"repro_theory_sat_regressions.py: {message}", file=sys.stderr)
    raise SystemExit(2)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Run the checked z3-tac repro gate for the 29 theory:*:sat "
            "num-bridge regression cases."
        )
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=2.0,
        help="hard wall-clock timeout per case in seconds (default: 2)",
    )
    parser.add_argument(
        "--driver",
        type=pathlib.Path,
        default=DEFAULT_DRIVER,
        help=f"checked z3-tac driver (default: {DEFAULT_DRIVER})",
    )
    parser.add_argument(
        "--corpus-root",
        type=pathlib.Path,
        default=DEFAULT_CORPUS_ROOT,
        help=f"v2 conformance corpus root (default: {DEFAULT_CORPUS_ROOT})",
    )
    parser.add_argument(
        "--manifest",
        type=pathlib.Path,
        default=DEFAULT_MANIFEST,
        help=f"v2 conformance manifest (default: {DEFAULT_MANIFEST})",
    )
    return parser.parse_args(argv)


def load_manifest(path: pathlib.Path) -> dict[str, object]:
    try:
        with path.open(encoding="utf-8") as infile:
            manifest = json.load(infile)
    except OSError as exc:
        die(f"cannot read manifest {path}: {exc}")
    except json.JSONDecodeError as exc:
        die(f"invalid manifest JSON {path}: {exc}")

    if not isinstance(manifest, dict) or manifest.get("schema_version") != "2":
        die(f"{path}: expected v2 conformance manifest")
    cases = manifest.get("cases")
    if not isinstance(cases, list):
        die(f"{path}: expected non-empty cases list")
    return manifest


def manifest_case_map(
    manifest: dict[str, object],
) -> dict[str, dict[str, object]]:
    cases = manifest["cases"]
    assert isinstance(cases, list)
    by_id: dict[str, dict[str, object]] = {}
    for index, entry in enumerate(cases, start=1):
        if not isinstance(entry, dict):
            die(f"manifest cases[{index}]: expected object")
        case_id = entry.get("id")
        if not isinstance(case_id, str) or not case_id:
            die(f"manifest cases[{index}]: expected non-empty id")
        if case_id in by_id:
            die(f"manifest cases[{index}]: duplicate id {case_id}")
        by_id[case_id] = entry
    return by_id


def arithmetic_sat_ids(by_id: dict[str, dict[str, object]]) -> set[str]:
    families = {"Ints", "Reals", "Reals_Ints"}
    ids: set[str] = set()
    for case_id in by_id:
        parts = case_id.split(":")
        if (
            len(parts) == 4
            and parts[0] == "theory"
            and parts[1] in families
            and parts[3] == "sat"
        ):
            ids.add(case_id)
    return ids


def expected_z3_tac_sat(entry: dict[str, object], case_id: str) -> None:
    expected = entry.get("expected")
    if not isinstance(expected, dict):
        die(f"{case_id}: manifest expected field is missing or invalid")
    z3_tac = expected.get("z3-tac")
    if not isinstance(z3_tac, dict) or z3_tac.get("status") != "pass":
        die(f"{case_id}: manifest z3-tac expectation is not pass")
    modes = entry.get("modes")
    if not isinstance(modes, list) or "z3-tac" not in modes:
        die(f"{case_id}: manifest modes do not include z3-tac")


def load_cases(
    by_id: dict[str, dict[str, object]],
    corpus_root: pathlib.Path,
) -> list[Case]:
    expected = set(EXPECTED_IDS)
    if len(expected) != len(EXPECTED_IDS):
        die("internal error: duplicate EXPECTED_IDS entry")
    if len(EXPECTED_IDS) != 29:
        die(
            "internal error: expected 29 pinned ids, "
            f"found {len(EXPECTED_IDS)}"
        )

    missing_ids = sorted(expected - set(by_id))
    if missing_ids:
        die("manifest is missing pinned ids: " + ", ".join(missing_ids))

    extras = arithmetic_sat_ids(by_id) - expected
    if extras != EXPECTED_ARITHMETIC_EXTRA_IDS:
        die(
            "manifest arithmetic theory:*:sat set drifted; unexpected extras: "
            + ", ".join(sorted(extras))
        )

    cases: list[Case] = []
    for case_id in EXPECTED_IDS:
        entry = by_id[case_id]
        expected_z3_tac_sat(entry, case_id)
        logic = entry.get("logic")
        file_name = entry.get("file")
        if not isinstance(logic, str) or not logic:
            die(f"{case_id}: manifest logic is missing or invalid")
        if not isinstance(file_name, str) or not file_name:
            die(f"{case_id}: manifest file is missing or invalid")
        path = (corpus_root / file_name).resolve()
        if not path.is_file():
            die(f"{case_id}: case file is missing: {path}")
        cases.append(Case(case_id=case_id, logic=logic, path=path))
    return cases


def output_field(stdout: str, stderr: str, field: str) -> str | None:
    prefix = field + "="
    for line in stdout.splitlines() + stderr.splitlines():
        if line.startswith(prefix):
            return line[len(prefix):]
    return None


def short_reason(text: str) -> str:
    for line in text.splitlines():
        line = line.strip()
        if line:
            return line[:160]
    return "no diagnostic output"


def run_case(
    driver: pathlib.Path,
    case: Case,
    timeout: float,
) -> tuple[bool, str]:
    command = [str(driver), str(case.path), case.logic]
    try:
        completed = subprocess.run(
            command,
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except OSError as exc:
        return False, f"FAIL cannot execute driver: {exc}"

    result = output_field(completed.stdout, completed.stderr, "result")
    combined = completed.stdout + "\n" + completed.stderr
    if (
        completed.returncode == 0
        and "Z3_TAC_PASS" in combined
        and result == "sat"
    ):
        return True, "PASS result=sat"
    if completed.returncode == 0 and result:
        return False, f"FAIL result={result}"
    return False, f"FAIL exit={completed.returncode} {short_reason(combined)}"


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    if args.timeout <= 0:
        die("--timeout must be positive")

    manifest = load_manifest(args.manifest)
    cases = load_cases(manifest_case_map(manifest), args.corpus_root)

    passed = 0
    failed = 0
    timed_out = 0
    for case in cases:
        ok, verdict = run_case(args.driver, case, args.timeout)
        if ok:
            passed += 1
        else:
            failed += 1
            if verdict == "TIMEOUT":
                timed_out += 1
        print(f"{case.case_id}: {verdict}")

    total = len(cases)
    print(
        "summary: "
        f"total={total} pass={passed} fail={failed - timed_out} "
        f"timeout={timed_out}"
    )
    return 0 if passed == total else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
