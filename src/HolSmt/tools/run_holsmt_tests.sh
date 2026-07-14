#!/usr/bin/env bash

set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd "$script_dir/../../.." && pwd)
out_dir=".holsmt-ci"
include_docker=false
clean_first=true
allow_unsupported_z3=false
supported_z3_versions="4.11.2 through 4.15.x"

usage() {
  cat <<'EOF'
Usage: src/HolSmt/tools/run_holsmt_tests.sh [options]

Runs the local HolSmt test contract from the repository root.

Options:
  --out-dir DIR       Write conformance outputs under DIR (default: .holsmt-ci)
  --no-clean          Do not run Holmake cleanAll before building test targets
  --allow-unsupported-z3
                      Run even when z3 is outside the supported version matrix
  --include-docker   Also run the Docker selftest matrix from src/HolSmt/README
  -h, --help         Show this help

If HOL4_Z3_EXECUTABLE is unset or names a command without a slash, the script
resolves z3 from PATH and exports HOL4_Z3_EXECUTABLE before running any tests.
EOF
}

die() {
  printf 'run_holsmt_tests.sh: %s\n' "$*" >&2
  exit 1
}

is_supported_z3_version() {
  local output=$1
  local major minor patch

  if [[ "$output" =~ Z3[[:space:]]version[[:space:]]([0-9]+)\.([0-9]+)\.([0-9]+) ]]; then
    major=${BASH_REMATCH[1]}
    minor=${BASH_REMATCH[2]}
    patch=${BASH_REMATCH[3]}

    if (( major == 4 && minor >= 11 && minor <= 15 )); then
      if (( minor == 11 && patch < 2 )); then
        return 1
      fi
      return 0
    fi
  fi

  return 1
}

z3_version_number() {
  local output=$1
  if [[ "$output" =~ Z3[[:space:]]version[[:space:]]([0-9]+\.[0-9]+\.[0-9]+) ]]; then
    printf '%s\n' "${BASH_REMATCH[1]}"
    return 0
  fi
  return 1
}

resolve_executable() {
  local name=$1
  local value=$2
  local resolved

  if [[ "$value" == */* ]]; then
    [ -x "$value" ] || die "$name is not executable: $value"
    printf '%s\n' "$value"
    return 0
  fi

  resolved=$(command -v "$value" || true)
  [ -n "$resolved" ] || die "$name is not on PATH or executable: $value"
  [ -x "$resolved" ] || die "$name resolved to a non-executable path: $resolved"
  printf '%s\n' "$resolved"
}

discover_z3_versions() {
  local candidate existing output path_dir search_dir version
  local -a candidates=() path_dirs=() search_dirs=()

  add_z3_search_dir() {
    local dir=$1
    [ -n "$dir" ] || return 0
    [ -d "$dir" ] || return 0
    for existing in "${search_dirs[@]}"; do
      [ "$existing" = "$dir" ] && return 0
    done
    search_dirs+=("$dir")
  }

  detected_z3_matrix_versions=()
  z3_matrix_args=()

  add_z3_search_dir "$HOME/.local/bin"
  IFS=: read -r -a path_dirs <<< "${PATH:-}"
  for path_dir in "${path_dirs[@]}"; do
    add_z3_search_dir "$path_dir"
  done

  for search_dir in "${search_dirs[@]}"; do
    while IFS= read -r candidate; do
      candidates+=("$candidate")
    done < <(find "$search_dir" -maxdepth 1 -type f -executable \
      -name 'z3-[0-9]*' | sort)
  done

  for candidate in "${candidates[@]}"; do
    output=$("$candidate" -version 2>&1 || true)
    version=$(z3_version_number "$output" || true)
    [ -n "$version" ] || continue
    is_supported_z3_version "$output" || continue
    if [[ " ${detected_z3_matrix_versions[*]} " == *" $version "* ]]; then
      continue
    fi
    detected_z3_matrix_versions+=("$version")
    z3_matrix_args+=(--z3 "$version:$candidate")
  done
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --out-dir)
      [ "$#" -ge 2 ] || die "--out-dir requires an argument"
      out_dir=$2
      shift 2
      ;;
    --include-docker)
      include_docker=true
      shift
      ;;
    --no-clean)
      clean_first=false
      shift
      ;;
    --allow-unsupported-z3)
      allow_unsupported_z3=true
      shift
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

cd "$repo_root"

[ -x bin/Holmake ] || die "bin/Holmake is missing or not executable; build HOL first"
[ -x bin/hol ] || die "bin/hol is missing or not executable; build HOL first"

if [ -n "${HOL4_Z3_EXECUTABLE:-}" ]; then
  HOL4_Z3_EXECUTABLE=$(resolve_executable HOL4_Z3_EXECUTABLE "$HOL4_Z3_EXECUTABLE")
  export HOL4_Z3_EXECUTABLE
else
  HOL4_Z3_EXECUTABLE=$(resolve_executable z3 z3)
  export HOL4_Z3_EXECUTABLE
fi

z3_version_output=$("$HOL4_Z3_EXECUTABLE" -version 2>&1 || true)
z3_version=$(z3_version_number "$z3_version_output" || true)
if ! is_supported_z3_version "$z3_version_output"; then
  if "$allow_unsupported_z3"; then
    printf 'Warning: unsupported Z3 version for HolSmt checked proof tests: %s\n' "$z3_version_output" >&2
  else
    die "unsupported Z3 version for HolSmt checked proof tests: ${z3_version_output:-unknown}. Supported versions are ${supported_z3_versions}. Set HOL4_Z3_EXECUTABLE to a supported z3 or pass --allow-unsupported-z3."
  fi
fi

run() {
  printf '\n==> %s\n' "$1"
  local name=$1
  shift
  if "$@"; then
    printf 'PASS: %s\n' "$name"
  else
    local exit_code=$?
    printf 'FAIL: %s (exit %s)\n' "$name" "$exit_code" >&2
    failed_steps+=("$name (exit $exit_code)")
    overall_status=1
  fi
}

run_in_dir() {
  printf '\n==> %s\n' "$1"
  local name=$1
  shift
  local dir=$1
  shift
  if (cd "$dir" && "$@"); then
    printf 'PASS: %s\n' "$name"
  else
    local exit_code=$?
    printf 'FAIL: %s (exit %s)\n' "$name" "$exit_code" >&2
    failed_steps+=("$name (exit $exit_code)")
    overall_status=1
  fi
}

parser_out="$out_dir/conformance/parser"
z3_out="$out_dir/conformance/z3"
typecheck_out="$out_dir/conformance/typecheck"
z3_tac_out="$out_dir/conformance/z3-tac"
complete_out="$out_dir/complete-conformance"
overall_status=0
failed_steps=()

printf 'Using HOL4_Z3_EXECUTABLE=%s\n' "$HOL4_Z3_EXECUTABLE"
printf 'Using %s\n' "$z3_version_output"

if "$clean_first"; then
  run "Clean HolSmt generated targets" \
    bin/Holmake -C src/HolSmt cleanAll
fi

run "Build HolSmt test binaries and conformance drivers" \
  bin/Holmake -C src/HolSmt smtheap selftest.exe holsmt-typecheck holsmt-z3-tac

run "Build real SOS/CSDP selftest" \
  bin/Holmake -C src/real selftest_sos.exe

# Run the functional selftest sharded across fresh, heap-capped processes.
# A single unsharded run reaches >200 GB RSS and is OOM-killed on a
# memory-capped runner (masquerading as a skipped/failed verification), so
# the whole-suite ./selftest.exe is never run here.  --no-build: the build
# step above already produced smtheap + selftest.exe.
run "Run HolSmt SML selftest (sharded)" \
  src/HolSmt/tools/run_selftest.sh --no-build

run_in_dir "Run real SOS/CSDP selftest" src/real \
  ./selftest_sos.exe

run "Run HolSmt Python tool unit tests" \
  python3 -m unittest \
    src/HolSmt/tools/tests/test_audit_proof_completeness.py \
    src/HolSmt/tools/tests/test_audit_coverage_manifest.py \
    src/HolSmt/tools/tests/test_generate_complete_corpus.py \
    src/HolSmt/tools/tests/test_generate_smtlib_coverage.py \
    src/HolSmt/tools/tests/test_record_z3_proof_corpus.py \
    src/HolSmt/tools/tests/test_run_conformance_suite.py

run "Regenerate release coverage report" \
  python3 src/HolSmt/tools/coverage/generate_smtlib_coverage.py --release

run "Check generated coverage files are committed" \
  git diff --exit-code -- \
    src/HolSmt/tools/coverage/smtlib_coverage.json \
    src/HolSmt/tools/coverage/SMTLIB_COVERAGE.md

run "Audit coverage manifest" \
  python3 src/HolSmt/tools/coverage/audit_coverage_manifest.py --enforce

run "Run parser conformance corpus" \
  python3 src/HolSmt/tools/run_conformance_suite.py \
    --out "$parser_out" \
    --no-default-suite \
    --corpus-dir src/HolSmt/tools/conformance-corpus/v1 \
    --mode parser-only

run "Run Z3 oracle/proof conformance slice" \
  python3 src/HolSmt/tools/run_conformance_suite.py \
    --out "$z3_out" \
    --no-default-suite \
    --corpus-dir src/HolSmt/tools/conformance-corpus/v1 \
    --logic QF_UF \
    --logic QF_LIA \
    --mode z3-oracle \
    --mode proof-parse \
    --mode proof-replay \
    --timeout 20

run "Validate checked-in Z3 proof corpus manifest" \
  python3 src/HolSmt/tools/record_z3_proof_corpus.py \
    --validate-corpus-manifest

run "Run live Z3 proof rule gate" \
  python3 src/HolSmt/tools/record_z3_proof_corpus.py \
    --out /tmp/holsmt-proof-corpus \
    --expected-rules src/HolSmt/tools/proof-corpus/minimal_expected_rules.json \
    --fail-on-unseen-rules \
    --fail-on-unknown-rules \
    src/HolSmt/tools/proof-corpus/minimal_bool_unsat.smt2

run "Run full Z3 verifier for configured executable" \
  src/HolSmt/tools/verify_z3_versions.sh \
    --versions "$z3_version" \
    --z3 "$z3_version:$HOL4_Z3_EXECUTABLE" \
    --out-dir "$out_dir/z3-version-current"

run "Run HOL typecheck driver conformance" \
  python3 src/HolSmt/tools/run_conformance_suite.py \
    --out "$typecheck_out" \
    --no-default-suite \
    --benchmark-dir src/HolSmt/tools/tests/conformance/typecheck \
    --mode typecheck-only

run "Run checked Z3_TAC driver conformance" \
  python3 src/HolSmt/tools/run_conformance_suite.py \
    --out "$z3_tac_out" \
    --no-default-suite \
    --benchmark-dir src/HolSmt/tools/tests/conformance/z3_tac \
    --mode z3-tac

run "Audit coverage manifest against conformance reports" \
  python3 src/HolSmt/tools/coverage/audit_coverage_manifest.py \
    --enforce \
    --conformance-report "$parser_out/conformance.json" \
    --conformance-report "$z3_out/conformance.json" \
    --conformance-report "$typecheck_out/conformance.json" \
    --conformance-report "$z3_tac_out/conformance.json"

run "Run complete SMT-LIB conformance suite" \
  src/HolSmt/tools/run_complete_smtlib_conformance.sh \
    --out-dir "$complete_out" \
    --z3 "$HOL4_Z3_EXECUTABLE"

discover_z3_versions

if [ "${#detected_z3_matrix_versions[@]}" -gt 0 ]; then
  run "Run full Z3 version matrix with local binaries (${detected_z3_matrix_versions[*]})" \
    src/HolSmt/tools/verify_z3_versions.sh \
      "${z3_matrix_args[@]}" \
      --out-dir "$out_dir/z3-version-matrix"
else
  run "Run full Z3 version matrix" \
    src/HolSmt/tools/verify_z3_versions.sh \
      --out-dir "$out_dir/z3-version-matrix"
fi

if "$include_docker"; then
  run "Build no-solver Docker image" \
    docker buildx build \
      --load \
      --tag holsmt-nosolver:ci \
      --build-arg SML=poly \
      --build-arg 'BUILDOPTS=--no-cache --expk -j4' \
      -f developers/docker-ci/Dockerfile .

  run "Run no-solver Docker selftest" \
    docker run --rm \
      -e HOL4_Z3_EXECUTABLE= \
      -e HOL4_CVC_EXECUTABLE= \
      -e HOL4_YICES_EXECUTABLE= \
      holsmt-nosolver:ci \
      sh -lc 'src/HolSmt/selftest.exe'

  for z3_version in 4.12.4 4.13.0; do
    run "Build Docker image for Z3 $z3_version" \
      docker buildx build \
        --load \
        --tag "holsmt-z3:$z3_version" \
        --build-arg SML=poly \
        --build-arg "Z3_VERSION=$z3_version" \
        --build-arg 'BUILDOPTS=--no-cache --expk -j4' \
        -f developers/docker-ci/Dockerfile .

    run "Run Docker selftest for Z3 $z3_version" \
      docker run --rm "holsmt-z3:$z3_version" \
        sh -lc '"$HOL4_Z3_EXECUTABLE" -version && src/HolSmt/selftest.exe'
  done
fi

if [ "$overall_status" -ne 0 ]; then
  printf '\nHolSmt tests failed. Failed steps:\n' >&2
  printf '  - %s\n' "${failed_steps[@]}" >&2
  printf '\nComplete conformance reports, when produced, are under %s\n' "$complete_out" >&2
  exit "$overall_status"
fi

printf '\nHolSmt tests completed successfully.\n'
