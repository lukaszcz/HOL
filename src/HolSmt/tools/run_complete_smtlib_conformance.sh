#!/usr/bin/env bash

set -u -o pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd "$script_dir/../../.." && pwd)

out_dir="src/HolSmt/tools/complete-conformance-out"
timeout_seconds=30
z3_executable="${HOL4_Z3_EXECUTABLE:-z3}"
declare -a selected_modes=()
declare -a selected_logics=()
declare -a selected_versions=()

all_modes=(
  parser-only
  typecheck-only
  z3-oracle
  proof-parse
  proof-replay
  z3-tac
)

usage() {
  cat <<'EOF'
Usage: src/HolSmt/tools/run_complete_smtlib_conformance.sh [options]

Build HolSmt test drivers, regenerate and validate the v2 SMT-LIB corpus, run
complete conformance/proof/external benchmark checks, and write one report
directory.

Options:
  --out-dir DIR         Report directory. Default: src/HolSmt/tools/complete-conformance-out
  --timeout SECONDS     Per-case solver/driver timeout. Default: 30
  --z3 PATH             Z3 executable for non-versioned conformance modes.
  --mode MODE           Limit conformance to one mode. Repeatable.
  --logic LOGIC         Limit conformance to one HolSmt logic. Repeatable.
  --z3-version VERSION  Limit per-version proof corpus checks. Repeatable.
  -h, --help            Show this help.

Per-version proof checks use HOLSMT_Z3_<version> environment variables first
(dots replaced by underscores), then z3-<version> on PATH, then --z3 if it
reports the requested version. Missing versions are recorded as skipped.
EOF
}

die() {
  printf 'run_complete_smtlib_conformance.sh: %s\n' "$*" >&2
  exit 2
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --out-dir)
      [ "$#" -ge 2 ] || die "--out-dir requires an argument"
      out_dir=$2
      shift 2
      ;;
    --timeout)
      [ "$#" -ge 2 ] || die "--timeout requires an argument"
      timeout_seconds=$2
      shift 2
      ;;
    --z3)
      [ "$#" -ge 2 ] || die "--z3 requires an argument"
      z3_executable=$2
      shift 2
      ;;
    --mode)
      [ "$#" -ge 2 ] || die "--mode requires an argument"
      selected_modes+=("$2")
      shift 2
      ;;
    --logic)
      [ "$#" -ge 2 ] || die "--logic requires an argument"
      selected_logics+=("$2")
      shift 2
      ;;
    --z3-version)
      [ "$#" -ge 2 ] || die "--z3-version requires an argument"
      selected_versions+=("$2")
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

cd "$repo_root" || exit 2

if ! [[ "$timeout_seconds" =~ ^[0-9]+$ ]] || [ "$timeout_seconds" -le 0 ]; then
  die "--timeout must be a positive integer"
fi

if [ "${#selected_modes[@]}" -eq 0 ]; then
  selected_modes=("${all_modes[@]}")
fi

report_dir=$(python3 -c 'import pathlib,sys; print(pathlib.Path(sys.argv[1]).resolve())' "$out_dir")
logs_dir="$report_dir/logs"
steps_file="$report_dir/steps.jsonl"
mkdir -p "$logs_dir" "$report_dir/conformance" "$report_dir/proofs" \
  "$report_dir/external" "$report_dir/audits" "$report_dir/minimized-repros"
: > "$steps_file"

json_string() {
  python3 -c 'import json,sys; print(json.dumps(sys.argv[1]))' "$1"
}

record_step() {
  local name=$1 kind=$2 exit_code=$3 stdout_path=$4 stderr_path=$5 status=$6
  python3 - "$steps_file" "$name" "$kind" "$exit_code" "$stdout_path" "$stderr_path" "$status" <<'PY'
import json
import pathlib
import sys

path, name, kind, exit_code, stdout_path, stderr_path, status = sys.argv[1:]
entry = {
    "name": name,
    "kind": kind,
    "exit_code": int(exit_code),
    "stdout": stdout_path,
    "stderr": stderr_path,
    "status": status,
}
with pathlib.Path(path).open("a", encoding="utf-8") as outfile:
    outfile.write(json.dumps(entry, sort_keys=True) + "\n")
PY
}

run_step() {
  local name=$1 kind=$2
  shift 2
  local stdout_path="$logs_dir/$name.stdout"
  local stderr_path="$logs_dir/$name.stderr"
  printf '[complete-conformance] %s\n' "$name"
  "$@" >"$stdout_path" 2>"$stderr_path"
  local exit_code=$?
  local status=pass
  if [ "$exit_code" -ne 0 ]; then
    status=fail
  fi
  record_step "$name" "$kind" "$exit_code" "$stdout_path" "$stderr_path" "$status"
  return 0
}

write_skipped_step() {
  local name=$1 kind=$2 reason=$3
  local stdout_path="$logs_dir/$name.stdout"
  local stderr_path="$logs_dir/$name.stderr"
  printf '%s\n' "$reason" >"$stdout_path"
  : >"$stderr_path"
  record_step "$name" "$kind" 0 "$stdout_path" "$stderr_path" skipped
}

version_of_z3() {
  local executable=$1
  "$executable" -version 2>/dev/null | python3 -c 'import re,sys; text=sys.stdin.read(); m=re.search(r"([0-9]+(?:\.[0-9]+)+)", text); print(m.group(1) if m else "")'
}

z3_for_version() {
  local version=$1
  local env_name="HOLSMT_Z3_${version//./_}"
  local env_value="${!env_name:-}"
  if [ -n "$env_value" ] && [ -x "$env_value" ]; then
    printf '%s\n' "$env_value"
    return 0
  fi
  if command -v "z3-$version" >/dev/null 2>&1; then
    command -v "z3-$version"
    return 0
  fi
  if command -v "$z3_executable" >/dev/null 2>&1 || [ -x "$z3_executable" ]; then
    if [ "$(version_of_z3 "$z3_executable")" = "$version" ]; then
      printf '%s\n' "$z3_executable"
      return 0
    fi
  fi
  return 1
}

logic_args=()
for logic in "${selected_logics[@]}"; do
  logic_args+=(--logic "$logic")
done

v2_generator="$script_dir/conformance-corpus/v2/generate_complete_corpus.py"
v2_root="$report_dir/generated-v2-corpus"
v2_manifest="$v2_root/manifest.json"
v2_logics_json="$v2_root/logics.json"
proof_manifest="src/HolSmt/tools/proof-corpus/complete/manifest.json"

holmake=Holmake
if [ -x "bin/Holmake" ]; then
  holmake="$repo_root/bin/Holmake"
fi

rm -rf "$v2_root"

run_step build-holsmt-drivers build "$holmake" -C src/HolSmt selftest.exe holsmt-typecheck holsmt-z3-tac
run_step generate-v2-commands generation python3 "$v2_generator" --manifest "$v2_manifest" --logics-json "$v2_logics_json" commands --write
run_step generate-v2-theories generation python3 "$v2_generator" --manifest "$v2_manifest" --logics-json "$v2_logics_json" theories --write
run_step generate-v2-logics generation python3 "$v2_generator" --manifest "$v2_manifest" --logics-json "$v2_logics_json" logics --write
run_step generate-v2-proof-rules generation python3 "$v2_generator" --manifest "$v2_manifest" --logics-json "$v2_logics_json" proof-rules --write
run_step generate-v2-soundness generation python3 "$v2_generator" --manifest "$v2_manifest" --logics-json "$v2_logics_json" soundness --write
run_step generate-v2-external generation python3 "$v2_generator" --manifest "$v2_manifest" --logics-json "$v2_logics_json" external --write
run_step import-external-benchmarks external-import python3 "$script_dir/import_external_benchmarks.py" \
  --corpus-root "$v2_root" \
  --corpus-manifest "$v2_manifest" \
  --check
run_step validate-v2-manifest validation python3 "$v2_generator" --manifest "$v2_manifest" audit

for mode in "${selected_modes[@]}"; do
  mode_out="$report_dir/conformance/$mode"
  mkdir -p "$mode_out"
  run_step "conformance-$mode" conformance python3 "$script_dir/run_conformance_suite.py" \
    --out "$mode_out" \
    --no-default-suite \
    --corpus-dir "$v2_root" \
    --mode "$mode" \
    --timeout "$timeout_seconds" \
    --z3 "$z3_executable" \
    "${logic_args[@]}" \
    --json-report "conformance-$mode.json" \
    --markdown-report "CONFORMANCE-$mode.md"
done

for mode in "${selected_modes[@]}"; do
  external_out="$report_dir/external/$mode"
  mkdir -p "$external_out"
  run_step "external-$mode" external-conformance python3 "$script_dir/run_conformance_suite.py" \
    --out "$external_out" \
    --no-default-suite \
    --benchmark-dir "$script_dir/external-benchmarks/curated-small" \
    --regression-dir "$script_dir/external-benchmarks/local-regressions" \
    --mode "$mode" \
    --timeout "$timeout_seconds" \
    --z3 "$z3_executable" \
    "${logic_args[@]}" \
    --json-report "external-$mode.json" \
    --markdown-report "EXTERNAL-$mode.md"
done

if [ "${#selected_versions[@]}" -eq 0 ]; then
  read -r -a selected_versions <<<"$(python3 - "$proof_manifest" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as infile:
    manifest = json.load(infile)
print(" ".join(manifest.get("supported_z3_versions", [])))
PY
)"
fi

for version in "${selected_versions[@]}"; do
  proof_out="$report_dir/proofs/z3-$version"
  mkdir -p "$proof_out"
  if z3_path=$(z3_for_version "$version"); then
    proof_cases=()
    proof_requirements=(
      --require-rule-occurrence th-lemma-array
      --require-rule-occurrence th-lemma-arith
      --require-rule-occurrence th-lemma-nonlinear-arith
    )
    case "$version" in
      4.11.2)
        proof_cases+=(
          --case-id minimal_bool_unsat
          --case-id theory:ArraysEx:extensionality:unsat-proof
          --case-id logic:NIA:nonlinear-proof
          --case-id logic:QF_NRA:nonlinear-proof
        )
        ;;
      4.12.4|4.13.0|4.14.1|4.15.3)
        proof_requirements+=(
          --require-rule-occurrence def-axiom
          --require-rule-occurrence hypothesis
          --require-rule-occurrence lemma
        )
        ;;
    esac
    run_step "proof-z3-$version" proof-version python3 "$script_dir/record_z3_proof_corpus.py" \
      --z3 "$z3_path" \
      --z3-version "$version" \
      --out "$proof_out" \
      --timeout "$timeout_seconds" \
      --complete-corpus-manifest "$proof_manifest" \
      "${proof_cases[@]}" \
      --gate-report rule-gate.json \
      --fail-on-unknown-rules \
      "${proof_requirements[@]}" \
      --require-theory-subkind 'array:<none>' \
      --minimized-repro-dir "$report_dir/minimized-repros/proofs/z3-$version"
  else
    cat >"$proof_out/proof-version-report.json" <<EOF
{
  "schema": "holsmt-complete-proof-version-report-v1",
  "version": $(json_string "$version"),
  "status": "skipped",
  "reason": "no matching Z3 executable available"
}
EOF
    write_skipped_step "proof-z3-$version" proof-version "no matching Z3 executable available for $version"
  fi
done

run_step audit-complete-conformance audit python3 "$script_dir/audit_complete_conformance.py" \
  --manifest "$v2_manifest" \
  --format json \
  --json-output "$report_dir/audits/complete-conformance-audit.json"

run_step audit-proof-completeness audit python3 "$script_dir/audit_proof_completeness.py" \
  --manifest "$v2_manifest" \
  --proof-summary "$script_dir/proof-corpus/complete/summary.json" \
  --fail-on-red-obligations \
  --format json \
  --json-output "$report_dir/audits/proof-completeness-audit.json"

python3 - "$report_dir" "$steps_file" "$v2_manifest" <<'PY'
import collections
import glob
import json
import pathlib
import sys

report_dir = pathlib.Path(sys.argv[1])
steps_file = pathlib.Path(sys.argv[2])
manifest_path = pathlib.Path(sys.argv[3])
repo_root = pathlib.Path.cwd().resolve()

def display_path(path: object) -> str:
    value = pathlib.Path(str(path))
    try:
        return value.resolve().relative_to(repo_root).as_posix()
    except ValueError:
        return str(path)

def display_entry_paths(entry: dict[str, object]) -> dict[str, object]:
    for key in ("report", "stdout", "stderr", "summary", "missing_report"):
        if isinstance(entry.get(key), str):
            entry[key] = display_path(entry[key])
    return entry

def load_json(path: pathlib.Path):
    with path.open(encoding="utf-8") as infile:
        return json.load(infile)

steps = []
if steps_file.exists():
    for line in steps_file.read_text(encoding="utf-8").splitlines():
        if line.strip():
            steps.append(display_entry_paths(json.loads(line)))

manifest = load_json(manifest_path)
manifest_red = []
for case in manifest.get("cases", []):
    expected = case.get("expected", {})
    if not isinstance(expected, dict):
        continue
    for mode, result in expected.items():
        if isinstance(result, dict) and result.get("status") == "red":
            manifest_red.append(
                {
                    "case": case.get("id"),
                    "mode": mode,
                    "class": case.get("class"),
                    "logic": case.get("logic"),
                    "features": case.get("features", []),
                    "diagnostic": result.get("diagnostic"),
                    "implementation_obligation": case.get("implementation_obligation"),
                }
            )

def load_optional(path: pathlib.Path):
    return load_json(path) if path.exists() else None

complete_audit = load_optional(report_dir / "audits" / "complete-conformance-audit.json")
proof_audit = load_optional(report_dir / "audits" / "proof-completeness-audit.json")

complete_audit_red = []
if isinstance(complete_audit, dict):
    for issue in complete_audit.get("issues", []):
        if isinstance(issue, dict) and issue.get("code") == "red_implementation_obligation":
            complete_audit_red.append(issue)

proof_audit_red = []
if isinstance(proof_audit, dict):
    for issue in proof_audit.get("issues", []):
        if isinstance(issue, dict) and issue.get("severity") == "red":
            proof_audit_red.append(issue)

conformance_reports = []
unexpected_results = []
classification_counts = collections.Counter()
for pattern in (
    str(report_dir / "conformance" / "*" / "conformance-*.json"),
    str(report_dir / "external" / "*" / "external-*.json"),
):
    for name in sorted(glob.glob(pattern)):
        path = pathlib.Path(name)
        try:
            report = load_json(path)
        except (OSError, json.JSONDecodeError) as exc:
            unexpected_results.append(
                {
                    "report": display_path(path),
                    "kind": "report-read-error",
                    "detail": str(exc),
                }
            )
            continue
        conformance_reports.append(
            {
                "path": display_path(path),
                "case_count": report.get("case_count"),
                "result_count": report.get("result_count"),
                "status_counts": report.get("status_counts", {}),
                "conformance_status_counts": report.get("conformance_status_counts", {}),
                "classification_counts": report.get("classification_counts", {}),
            }
        )
        classification_counts.update(report.get("classification_counts", {}))
        for result in report.get("results", []):
            if isinstance(result, dict) and result.get("conformance_status") == "fail":
                unexpected_results.append(
                    {
                        "report": display_path(path),
                        "case": result.get("case"),
                        "logic": result.get("logic"),
                        "mode": result.get("mode"),
                        "classification": result.get("classification"),
                        "detail": result.get("detail"),
                    }
                )
        metamorphic = report.get("metamorphic_groups", {})
        if isinstance(metamorphic, dict):
            counts = metamorphic.get("status_counts", {})
            if isinstance(counts, dict) and counts.get("fail"):
                unexpected_results.append(
                    {
                        "report": display_path(path),
                        "kind": "metamorphic-failure",
                        "count": counts.get("fail"),
                    }
                )

proof_reports = []
for proof_dir in sorted((report_dir / "proofs").glob("z3-*")):
    if not proof_dir.is_dir():
        continue
    summary_path = proof_dir / "summary.json"
    skipped_path = proof_dir / "proof-version-report.json"
    if summary_path.exists():
        summary = load_json(summary_path)
        proof_reports.append(
            {
                "version": proof_dir.name.removeprefix("z3-"),
                "status": "recorded",
                "summary": display_path(summary_path),
                "entry_count": summary.get("entry_count"),
                "proof_count": summary.get("proof_count"),
                "malformed_fragment_count": summary.get("malformed_fragment_count"),
            }
        )
    elif skipped_path.exists():
        proof_reports.append(load_json(skipped_path))

infra_kinds = {"build", "generation", "validation", "external-import"}
infrastructure_errors = []
for step in steps:
    code = int(step.get("exit_code", 0))
    kind = step.get("kind")
    if code == 2 or (code != 0 and kind in infra_kinds):
        infrastructure_errors.append(step)
    if code == 2 and kind in {"conformance", "external-conformance", "proof-version", "audit"}:
        infrastructure_errors.append(step)
    if code != 0 and kind == "conformance":
        mode = str(step.get("name", "")).removeprefix("conformance-")
        expected = report_dir / "conformance" / mode / f"conformance-{mode}.json"
        if not expected.exists():
            infrastructure_errors.append({**step, "missing_report": display_path(expected)})
    if code != 0 and kind == "external-conformance":
        mode = str(step.get("name", "")).removeprefix("external-")
        expected = report_dir / "external" / mode / f"external-{mode}.json"
        if not expected.exists():
            infrastructure_errors.append({**step, "missing_report": display_path(expected)})

audit_blocking = []
if isinstance(proof_audit, dict):
    for issue in proof_audit.get("issues", []):
        if (
            isinstance(issue, dict)
            and issue.get("blocking")
            and issue.get("severity") != "red"
        ):
            audit_blocking.append(issue)

def obligation_search_text(item: dict[str, object]) -> str:
    values: list[str] = []

    def visit(value: object) -> None:
        if isinstance(value, str):
            values.append(value)
        elif isinstance(value, dict):
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(item)
    return " ".join(values).lower()

def first_red_category_counts(
    manifest_items: list[dict[str, object]],
    proof_items: list[dict[str, object]],
) -> dict[str, int]:
    all_items = manifest_items + proof_items
    categories: dict[str, tuple[str, ...]] = {
        "function sorts": ("function-sort", "function-valued"),
        "arrays": ("array", "arraysex"),
        "FP": ("floatingpoint", "fp.", "float16", "float32", "float64", "float128", "th-lemma-fp"),
        "strings/regex": ("unicodestrings", "string", "regex", "regexp", "str.", "re."),
        "datatypes": ("datatype",),
        "seq/set/bag": ("seq", "set.", "bag", "z3_extensions"),
        "th-lemma-basic": ("th-lemma-basic",),
        "advanced theory lemmas": (
            "th-lemma-array",
            "th-lemma-bv",
            "th-lemma-datatype",
            "th-lemma-fp",
            "th-lemma-nonlinear-arith",
            "th-lemma-regexp",
            "th-lemma-seq",
            "th-lemma-string",
        ),
        "check-sat-assuming": ("check-sat-assuming",),
        "unsat core/assumptions": ("get-unsat-assumptions", "get-unsat-core", "unsat-assumptions", "unsat-core"),
        "missing logic packets": ("logic-packet",),
        "real proof occurrences": ("real-proof-occurrence", "missing_real_proof_occurrence"),
        "external benchmarks": ("external-benchmark", "external:"),
    }
    counts: dict[str, int] = {}
    for category, needles in categories.items():
        count = 0
        for item in all_items:
            text = obligation_search_text(item)
            if any(needle in text for needle in needles):
                count += 1
        counts[category] = count
    return counts

first_red_counts = first_red_category_counts(manifest_red, proof_audit_red)

def manifest_obligation_row(item: dict[str, object]) -> dict[str, object]:
    obligation = item.get("implementation_obligation")
    if not isinstance(obligation, dict):
        obligation = {}
    return {
        "source": "manifest",
        "case": item.get("case"),
        "mode": item.get("mode"),
        "class": item.get("class"),
        "logic": item.get("logic"),
        "missing_feature": obligation.get("feature"),
        "failure_phase": obligation.get("failure_phase"),
        "implementation_files": obligation.get("files", []),
        "test_ids": obligation.get("test_ids", []),
    }

def proof_audit_obligation_row(item: dict[str, object]) -> dict[str, object]:
    details = item.get("details")
    if not isinstance(details, dict):
        details = {}
    test_ids = details.get("test_ids", details.get("case_ids", []))
    files = details.get("files", details.get("implementation_files", []))
    return {
        "source": "proof-audit",
        "case": item.get("subject"),
        "mode": "proof-corpus",
        "class": item.get("category"),
        "logic": "ALL",
        "missing_feature": details.get("feature", item.get("subject")),
        "failure_phase": details.get("failure_phase"),
        "implementation_files": files,
        "test_ids": test_ids,
    }

flat_obligations = [
    *(manifest_obligation_row(item) for item in manifest_red),
    *(proof_audit_obligation_row(item) for item in proof_audit_red),
]
flat_obligations.sort(
    key=lambda item: (
        str(item.get("source")),
        str(item.get("case")),
        str(item.get("mode")),
        str(item.get("missing_feature")),
    )
)

red_summary = {
    "schema": "holsmt-red-obligation-summary-v1",
    "manifest_red_count": len(manifest_red),
    "complete_audit_red_count": len(complete_audit_red),
    "proof_audit_red_count": len(proof_audit_red),
    "required_first_red_category_counts": first_red_counts,
    "obligations": flat_obligations,
    "manifest_red_obligations": manifest_red,
    "complete_audit_red_obligations": complete_audit_red,
    "proof_audit_red_obligations": proof_audit_red,
}

red_summary_path = report_dir / "red-obligations.json"
with red_summary_path.open("w", encoding="utf-8") as outfile:
    json.dump(red_summary, outfile, indent=2, sort_keys=True)
    outfile.write("\n")

def md_cell(value: object) -> str:
    text = "" if value is None else str(value)
    return text.replace("|", "\\|").replace("\n", " ")

def md_list(values: object) -> str:
    if isinstance(values, list):
        return ", ".join(str(value) for value in values)
    return "" if values is None else str(values)

red_md = [
    "# HolSmt Red Obligation Summary",
    "",
    f"- Manifest red rows: {len(manifest_red)}",
    f"- Complete-audit red rows: {len(complete_audit_red)}",
    f"- Proof-audit red rows: {len(proof_audit_red)}",
    "- Full machine-readable obligation rows are in `red-obligations.json`.",
    "",
    "## Required First Red Categories",
    "",
    "| Category | Red rows |",
    "| --- | ---: |",
]
for category, count in first_red_counts.items():
    red_md.append(f"| {md_cell(category)} | {count} |")
red_md.extend([
    "",
    "## Red Rows",
    "",
    "| Source | Case | Mode | Class | Logic | Missing feature | Failure phase | Files | Test IDs |",
    "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
])
for item in flat_obligations[:300]:
    red_md.append(
        f"| `{md_cell(item.get('source'))}` | `{md_cell(item.get('case'))}` | `{md_cell(item.get('mode'))}` | `{md_cell(item.get('class'))}` | `{md_cell(item.get('logic'))}` | `{md_cell(item.get('missing_feature'))}` | `{md_cell(item.get('failure_phase'))}` | {md_cell(md_list(item.get('implementation_files')))} | {md_cell(md_list(item.get('test_ids')))} |"
    )
if len(flat_obligations) > 300:
    red_md.append(f"| ... | ... | ... | ... | ... | ... | ... | ... | {len(flat_obligations) - 300} more in JSON |")
(report_dir / "RED_OBLIGATIONS.md").write_text("\n".join(red_md) + "\n", encoding="utf-8")

red_count = len(manifest_red) + len(proof_audit_red)
summary = {
    "schema": "holsmt-complete-conformance-run-v1",
    "report_dir": display_path(report_dir),
    "status": "pass",
    "red_obligation_count": red_count,
    "unexpected_regression_count": len(unexpected_results) + len(audit_blocking),
    "infrastructure_error_count": len(infrastructure_errors),
    "step_count": len(steps),
    "classification_counts": dict(sorted(classification_counts.items())),
}
nonzero_exit_reasons = []
if red_count:
    nonzero_exit_reasons.append("red-obligations")
if unexpected_results or audit_blocking:
    nonzero_exit_reasons.append("unexpected-regressions")
if infrastructure_errors:
    nonzero_exit_reasons.append("infrastructure-errors")
summary["nonzero_exit_reasons"] = nonzero_exit_reasons
if summary["infrastructure_error_count"]:
    summary["status"] = "infrastructure-error"
elif summary["red_obligation_count"]:
    summary["status"] = "red-obligations"
elif summary["unexpected_regression_count"]:
    summary["status"] = "unexpected-regression"

complete = {
    "schema": "holsmt-complete-conformance-report-v1",
    "summary": summary,
    "steps": steps,
    "conformance_reports": conformance_reports,
    "proof_reports": proof_reports,
    "audits": {
        "complete_conformance": display_path(report_dir / "audits" / "complete-conformance-audit.json"),
        "proof_completeness": display_path(report_dir / "audits" / "proof-completeness-audit.json"),
    },
    "red_obligations": red_summary,
    "unexpected_regressions": unexpected_results,
    "audit_blocking_issues": audit_blocking,
    "infrastructure_errors": infrastructure_errors,
    "minimized_repros": display_path(report_dir / "minimized-repros"),
}
with (report_dir / "complete-conformance.json").open("w", encoding="utf-8") as outfile:
    json.dump(complete, outfile, indent=2, sort_keys=True)
    outfile.write("\n")

md = [
    "# HolSmt Complete SMT-LIB Conformance",
    "",
    f"- Status: `{summary['status']}`",
    f"- Red obligations: {summary['red_obligation_count']}",
    f"- Unexpected regressions: {summary['unexpected_regression_count']}",
    f"- Infrastructure errors: {summary['infrastructure_error_count']}",
    f"- Nonzero exit reasons: {', '.join(summary['nonzero_exit_reasons']) or 'none'}",
    f"- Steps: {summary['step_count']}",
    "",
    "## Artifacts",
    "",
    "- `complete-conformance.json`",
    "- `RED_OBLIGATIONS.md` and `red-obligations.json`",
    "- `conformance/<mode>/conformance-<mode>.json`",
    "- `external/<mode>/external-<mode>.json`",
    "- `proofs/z3-<version>/summary.json` or `proof-version-report.json`",
    "- `minimized-repros/`",
    "",
    "## Step Status",
    "",
    "| Step | Kind | Status | Exit |",
    "| --- | --- | --- | ---: |",
]
for step in steps:
    md.append(
        f"| `{step.get('name')}` | `{step.get('kind')}` | `{step.get('status')}` | {step.get('exit_code')} |"
    )
if unexpected_results:
    md.extend(["", "## Unexpected Regressions", "", "| Report | Case | Mode | Detail |", "| --- | --- | --- | --- |"])
    for item in unexpected_results[:100]:
        detail = str(item.get("detail", "")).replace("\n", " ")[:160]
        md.append(f"| `{item.get('report')}` | `{item.get('case', item.get('kind', ''))}` | `{item.get('mode', '')}` | {detail} |")
if infrastructure_errors:
    md.extend(["", "## Infrastructure Errors", "", "| Step | Kind | Exit | stdout | stderr |", "| --- | --- | ---: | --- | --- |"])
    for step in infrastructure_errors:
        md.append(
            f"| `{step.get('name')}` | `{step.get('kind')}` | {step.get('exit_code')} | `{step.get('stdout')}` | `{step.get('stderr')}` |"
        )
(report_dir / "COMPLETE_CONFORMANCE.md").write_text("\n".join(md) + "\n", encoding="utf-8")

exit_code = 0
if summary["status"] != "pass":
    exit_code = 1
(report_dir / "exit-code.txt").write_text(str(exit_code) + "\n", encoding="utf-8")
print(f"wrote complete conformance report to {report_dir / 'complete-conformance.json'}")
print(f"wrote complete conformance markdown to {report_dir / 'COMPLETE_CONFORMANCE.md'}")
print(f"complete conformance status: {summary['status']}")
PY

exit "$(cat "$report_dir/exit-code.txt")"
