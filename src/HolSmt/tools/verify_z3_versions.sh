#!/usr/bin/env bash

set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd "$script_dir/../../.." && pwd)

versions=(4.11.2 4.12.4 4.13.0 4.14.1 4.15.3)
out_dir=".holsmt-z3-version-matrix"
download_dir=""
# Per-shard selftest timeout.  The functional selftest is run sharded (see
# tools/run_selftest.sh), so this bounds a single shard, not the whole
# suite -- generous enough that a healthy shard never trips it.
timeout_seconds=1800
shards=${SHARDS:-8}
jobs=${JOBS:-4}
declare -a local_z3s=()

usage() {
  cat <<'EOF'
Usage: src/HolSmt/tools/verify_z3_versions.sh [options]

Downloads representative Z3 releases, runs HolSmt proof checks against each
available executable, and writes a JSON report recording exactly which versions
were verified.

Options:
  --versions LIST       Space/comma-separated Z3 versions to test
                        (default: 4.11.2 4.12.4 4.13.0 4.14.1 4.15.3).
                        Only Z3 4.x is supported; legacy 2.x is not.
  --z3 VERSION:PATH     Use an existing local Z3 executable for VERSION.
                        Repeatable; useful when GitHub has no binary for the
                        local architecture.
  --out-dir DIR         Output directory (default: .holsmt-z3-version-matrix)
  --download-dir DIR    Download/cache directory (default: OUT_DIR/downloads)
  --timeout SECONDS     Per-shard selftest timeout (default: 1800)
  --shards N            Selftest shards per version (default: 8; env SHARDS)
  --jobs J              Concurrent shards (default: 4; env JOBS)
  -h, --help            Show this help

The report is written to OUT_DIR/report.json.  Per-version stdout/stderr and
proof-corpus outputs are kept under OUT_DIR/results/<version>/.
EOF
}

die() {
  printf 'verify_z3_versions.sh: %s\n' "$*" >&2
  exit 1
}

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || die "missing required command: $1"
}

json_string() {
  jq -Rn --arg s "$1" '$s'
}

split_versions() {
  tr ',:' '  ' <<<"$1"
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --versions)
      [ "$#" -ge 2 ] || die "--versions requires an argument"
      read -r -a versions <<<"$(split_versions "$2")"
      shift 2
      ;;
    --z3)
      [ "$#" -ge 2 ] || die "--z3 requires VERSION:PATH"
      local_z3s+=("$2")
      shift 2
      ;;
    --out-dir)
      [ "$#" -ge 2 ] || die "--out-dir requires an argument"
      out_dir=$2
      shift 2
      ;;
    --download-dir)
      [ "$#" -ge 2 ] || die "--download-dir requires an argument"
      download_dir=$2
      shift 2
      ;;
    --timeout)
      [ "$#" -ge 2 ] || die "--timeout requires seconds"
      timeout_seconds=$2
      shift 2
      ;;
    --shards)
      [ "$#" -ge 2 ] || die "--shards requires a count"
      shards=$2
      shift 2
      ;;
    --jobs)
      [ "$#" -ge 2 ] || die "--jobs requires a count"
      jobs=$2
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

cd "$repo_root"

need_cmd curl
need_cmd jq
need_cmd tar
need_cmd unzip
need_cmd timeout
need_cmd python3

[ -x bin/Holmake ] || die "bin/Holmake is missing or not executable; build HOL first"
[ -x bin/hol ] || die "bin/hol is missing or not executable; build HOL first"

download_dir=${download_dir:-"$out_dir/downloads"}
results_dir="$out_dir/results"
mkdir -p "$download_dir" "$results_dir"

local_z3_for_version() {
  local version=$1 entry entry_version entry_path
  for entry in "${local_z3s[@]}"; do
    entry_version=${entry%%:*}
    entry_path=${entry#*:}
    if [ "$entry_version" = "$version" ]; then
      printf '%s\n' "$entry_path"
      return 0
    fi
  done
  return 1
}

candidate_assets() {
  local version=$1 machine
  machine=$(uname -m)
  case "$machine" in
    x86_64|amd64)
      printf '%s\n' \
        "z3-${version}-x64-glibc-2.35.zip" \
        "z3-${version}-x64-glibc-2.31.zip" \
        "z3-${version}-x64-ubuntu-20.04.zip"
      ;;
    aarch64|arm64)
      printf '%s\n' \
        "z3-${version}-arm64-glibc-2.35.zip" \
        "z3-${version}-arm64-glibc-2.31.zip" \
        "z3-${version}-arm64-ubuntu-20.04.zip"
      ;;
    *)
      return 1
      ;;
  esac
}

find_extracted_z3() {
  local dir=$1
  find "$dir" -path '*/bin/z3' -type f -perm -u+x | sort | head -n 1
}

is_usable_z3() {
  local z3_path=$1
  "$z3_path" -version >/dev/null 2>&1
}

download_z3() {
  local version=$1 version_dir zip asset url z3_path
  version_dir="$download_dir/z3-$version"
  for z3_path in $(find "$version_dir" -path '*/bin/z3' -type f -perm -u+x 2>/dev/null | sort); do
    if is_usable_z3 "$z3_path"; then
      printf '%s\n' "$z3_path"
      return 0
    fi
  done

  z3_path=$(find_extracted_z3 "$version_dir" 2>/dev/null || true)
  if [ -n "$z3_path" ]; then
    printf 'Ignoring unusable cached Z3 binary: %s\n' "$z3_path" >&2
  fi

  mkdir -p "$version_dir"
  while IFS= read -r asset; do
    [ -n "$asset" ] || continue
    url="https://github.com/Z3Prover/z3/releases/download/z3-${version}/${asset}"
    zip="$version_dir/$asset"
    printf 'Trying %s\n' "$url" >&2
    if curl -fL --retry 3 --connect-timeout 20 -o "$zip" "$url"; then
      unzip -q -o "$zip" -d "$version_dir"
      for z3_path in $(find "$version_dir" -path '*/bin/z3' -type f -perm -u+x 2>/dev/null | sort); do
        if is_usable_z3 "$z3_path"; then
          printf '%s\n' "$z3_path"
          return 0
        fi
        printf 'Ignoring unusable downloaded Z3 binary: %s\n' "$z3_path" >&2
      done
    fi
  done < <(candidate_assets "$version" || true)

  return 1
}

write_result() {
  local path=$1 version=$2 status=$3 z3_path=$4 z3_output=$5 phase=$6 detail=$7
  jq -n \
    --arg version "$version" \
    --arg status "$status" \
    --arg z3_path "$z3_path" \
    --arg z3_output "$z3_output" \
    --arg phase "$phase" \
    --arg detail "$detail" \
    --arg timestamp "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    '{
      version: $version,
      status: $status,
      z3_path: $z3_path,
      z3_version_output: $z3_output,
      failed_phase: (if $phase == "" then null else $phase end),
      detail: (if $detail == "" then null else $detail end),
      timestamp_utc: $timestamp
    }' > "$path"
}

run_version() {
  local version=$1 result_dir result_json z3_path z3_output phase detail
  local -a z3_opts
  result_dir="$results_dir/$version"
  result_json="$result_dir/result.json"
  mkdir -p "$result_dir"

  if z3_path=$(local_z3_for_version "$version"); then
    [ -x "$z3_path" ] || {
      write_result "$result_json" "$version" "error" "$z3_path" "" "setup" "configured local Z3 is not executable"
      return 0
    }
  elif ! z3_path=$(download_z3 "$version" 2>"$result_dir/download.log"); then
    write_result "$result_json" "$version" "not-run" "" "" "download" "no compatible official Z3 release binary was downloaded for $(uname -m)"
    return 0
  fi

  z3_output=$("$z3_path" -version 2>&1 || true)
  printf '%s\n' "$z3_output" > "$result_dir/z3-version.txt"

  # Only Z3 4.x is supported; legacy 2.x (PROOF_MODE) has been removed.
  case "$version" in
    4.*) z3_opts=(proof=true pp.simplify_implies=false) ;;
    *)
      write_result "$result_json" "$version" "error" "$z3_path" "$z3_output" \
        "setup" "unsupported Z3 version $version (only 4.x is supported)"
      return 0
      ;;
  esac

  "$z3_path" "${z3_opts[@]}" -smt2 \
    -file:src/HolSmt/tools/proof-corpus/minimal_bool_unsat.smt2 \
    > "$result_dir/minimal-proof.stdout" \
    2> "$result_dir/minimal-proof.stderr" || {
      write_result "$result_json" "$version" "fail" "$z3_path" "$z3_output" "minimal-proof" \
        "Z3 failed to produce output for the minimal proof input"
      return 0
    }

  if ! python3 src/HolSmt/tools/record_z3_proof_corpus.py \
      --z3 "$z3_path" \
      --out "$result_dir/proof-corpus" \
      --expected-rules src/HolSmt/tools/proof-corpus/minimal_expected_rules.json \
      --fail-on-unseen-rules \
      --fail-on-unknown-rules \
      src/HolSmt/tools/proof-corpus/minimal_bool_unsat.smt2 \
      > "$result_dir/proof-corpus.stdout" \
      2> "$result_dir/proof-corpus.stderr"; then
    detail=$(tail -n 40 "$result_dir/proof-corpus.stderr" "$result_dir/proof-corpus.stdout" 2>/dev/null)
    write_result "$result_json" "$version" "fail" "$z3_path" "$z3_output" "proof-corpus" "$detail"
    return 0
  fi

  replay_smoke_script="$result_dir/nonlinear-replay.sml"
  cat > "$replay_smoke_script" <<'EOF'
open HolKernel Parse boolLib bossLib;
val _ = load "HolSmtLib";
val _ = Feedback.set_trace "PP.avoid_unicode" 1;
val _ = Feedback.set_trace "HolSmtLib" 0;
val th = prove(``(x:real) pow 3 = x * x * x``, HolSmtLib.Z3_TAC);
val _ = OS.Process.exit
  (if Thm.concl th ~~ ``(x:real) pow 3 = x * x * x`` then
     OS.Process.success
   else
     OS.Process.failure);
EOF
  replay_smoke_script=$(cd "$(dirname "$replay_smoke_script")" && pwd)/$(basename "$replay_smoke_script")
  if ! (cd src/HolSmt && timeout "$timeout_seconds" env HOL4_Z3_EXECUTABLE="$z3_path" \
      ../../bin/hol < "$replay_smoke_script") \
      > "$result_dir/nonlinear-replay.stdout" \
      2> "$result_dir/nonlinear-replay.stderr"; then
    detail=$(tail -n 80 "$result_dir/nonlinear-replay.stderr" \
      "$result_dir/nonlinear-replay.stdout" 2>/dev/null)
    if grep -q "CSDP not found" "$result_dir/nonlinear-replay.stdout" \
        "$result_dir/nonlinear-replay.stderr"; then
      write_result "$result_json" "$version" "blocked" "$z3_path" "$z3_output" \
        "nonlinear-replay-dependency" "$detail"
    else
      write_result "$result_json" "$version" "fail" "$z3_path" "$z3_output" \
        "nonlinear-replay" "$detail"
    fi
    return 0
  fi

  # Run the functional selftest sharded across fresh, heap-capped processes so
  # a single long-lived run cannot exhaust memory and be OOM-killed (which
  # would masquerade as a skipped verification).  The driver returns nonzero
  # if any shard fails or times out.
  if ! env HOL4_Z3_EXECUTABLE="$z3_path" SHARD_TIMEOUT="$timeout_seconds" \
      src/HolSmt/tools/run_selftest.sh --no-build \
        --shards "$shards" --jobs "$jobs" --out "$result_dir/shards" \
      > "$result_dir/selftest.stdout" \
      2> "$result_dir/selftest.stderr"; then
    phase="selftest"
    # Fold the per-shard output into the aggregate log so CSDP detection and
    # the failure detail see the actual selftest output, not just the summary.
    cat "$result_dir"/shards/shard-*.stdout >> "$result_dir/selftest.stdout" \
      2>/dev/null || true
    detail=$(tail -n 80 "$result_dir/selftest.stderr" "$result_dir/selftest.stdout" 2>/dev/null)
    if grep -q "CSDP not found" "$result_dir/selftest.stdout" "$result_dir/selftest.stderr"; then
      write_result "$result_json" "$version" "blocked" "$z3_path" "$z3_output" \
        "selftest-dependency" "$detail"
    else
      write_result "$result_json" "$version" "fail" "$z3_path" "$z3_output" "$phase" "$detail"
    fi
    return 0
  fi

  write_result "$result_json" "$version" "pass" "$z3_path" "$z3_output" "" ""
}

printf 'Building HolSmt verification targets...\n'
bin/Holmake --no-project -C src/HolSmt selftest.exe holsmt-z3-tac >/dev/null

for version in "${versions[@]}"; do
  printf '\n==> Verifying Z3 %s\n' "$version"
  run_version "$version"
  jq -r '"Z3 \(.version): \(.status)" + (if .failed_phase then " (" + .failed_phase + ")" else "" end)' \
    "$results_dir/$version/result.json"
done

jq -s \
  --arg schema "holsmt-z3-version-verification-v1" \
  --arg generated_at "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg host "$(uname -s)-$(uname -m)" \
  '{schema: $schema, generated_at_utc: $generated_at, host: $host,
    versions: .}' \
  "$results_dir"/*/result.json > "$out_dir/report.json"

printf '\nWrote %s\n' "$out_dir/report.json"

if ! jq -e 'all(.versions[]; .status == "pass")' "$out_dir/report.json" >/dev/null; then
  printf '\nZ3 version matrix failed; non-passing rows:\n' >&2
  jq -r '.versions[] | select(.status != "pass") |
    "Z3 \(.version): \(.status)" +
    (if .failed_phase then " (" + .failed_phase + ")" else "" end)' \
    "$out_dir/report.json" >&2
  exit 1
fi
