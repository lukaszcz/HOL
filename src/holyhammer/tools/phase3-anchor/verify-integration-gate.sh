#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 2 || {
  echo "usage: $0 REPOSITORY_ROOT TOP_PROVENANCE" >&2
  exit 2
}
root=$1
provenance=$2
test -d "$root" && test ! -L "$root"
test -s "$provenance" && test ! -L "$provenance"

sha () { sha256sum "$1" | awk '{print $1}'; }

bound_path () {
  local relative=$1
  case "$relative" in
    /* | *..* | "") return 1 ;;
  esac
  test -s "$root/$relative" && test ! -L "$root/$relative"
  printf '%s\n' "$root/$relative"
}

verify_bound () {
  local relative=$1 expected=$2 file
  test "${#expected}" -eq 64
  case "$expected" in *[!0-9a-f]*) return 1 ;; esac
  file=$(bound_path "$relative")
  test "$(sha "$file")" = "$expected"
}

jq -e '
  .schema == "hh-task10-a-run-v13" and
  (.integration_gate | keys == ["baseline_validation_path",
    "baseline_validation_sha256","corrupt_rejection_path",
    "corrupt_rejection_sha256","first8_equivalence_path",
    "first8_equivalence_sha256","input_inventory_path",
    "input_inventory_sha256","integration_certificate_path",
    "integration_certificate_sha256","model_env_rejection_path",
    "model_env_rejection_sha256","ranking_rejections_path",
    "ranking_rejections_sha256","reservation_selftest_path",
    "reservation_selftest_sha256","result_path","result_sha256",
    "resume_certificate_path","resume_certificate_sha256",
    "run_header_path","run_header_sha256","schema",
    "stale_rejection_path","stale_rejection_sha256",
    "xargs_oom_selftest_path","xargs_oom_selftest_sha256"]) and
  .integration_gate.schema == "hh-task10-a-integration-support-v1" and
  ([.integration_gate[]] | all(type == "string" and length > 0))
' "$provenance" >/dev/null

while IFS=$'\t' read -r relative expected
do
  verify_bound "$relative" "$expected"
done < <(jq -r '
  .integration_gate as $gate |
  [[$gate.input_inventory_path,$gate.input_inventory_sha256],
   [$gate.run_header_path,$gate.run_header_sha256],
   [$gate.result_path,$gate.result_sha256],
   [$gate.baseline_validation_path,$gate.baseline_validation_sha256],
   [$gate.integration_certificate_path,$gate.integration_certificate_sha256],
   [$gate.resume_certificate_path,$gate.resume_certificate_sha256],
   [$gate.model_env_rejection_path,$gate.model_env_rejection_sha256],
   [$gate.ranking_rejections_path,$gate.ranking_rejections_sha256],
   [$gate.stale_rejection_path,$gate.stale_rejection_sha256],
   [$gate.corrupt_rejection_path,$gate.corrupt_rejection_sha256],
   [$gate.first8_equivalence_path,$gate.first8_equivalence_sha256],
   [$gate.xargs_oom_selftest_path,$gate.xargs_oom_selftest_sha256],
   [$gate.reservation_selftest_path,$gate.reservation_selftest_sha256]][] |
  @tsv
' "$provenance")

inventory=$(bound_path "$(jq -r \
  '.integration_gate.input_inventory_path' "$provenance")")
(cd "$(dirname "$inventory")" &&
  sha256sum -c "$(basename "$inventory")" >/dev/null)
certificate=$(bound_path "$(jq -r \
  '.integration_gate.integration_certificate_path' "$provenance")")
jq -e --arg input "$(jq -r \
    '.integration_gate.input_inventory_sha256' "$provenance")" \
  --arg run "$(jq -r \
    '.integration_gate.run_header_sha256' "$provenance")" \
  --arg result "$(jq -r \
    '.integration_gate.result_sha256' "$provenance")" \
  --arg baseline "$(jq -r \
    '.integration_gate.baseline_validation_sha256' "$provenance")" \
  --arg resume "$(jq -r \
    '.integration_gate.resume_certificate_sha256' "$provenance")" \
  --arg model "$(jq -r \
    '.integration_gate.model_env_rejection_sha256' "$provenance")" \
  --arg ranking "$(jq -r \
    '.integration_gate.ranking_rejections_sha256' "$provenance")" \
  --arg stale "$(jq -r \
    '.integration_gate.stale_rejection_sha256' "$provenance")" \
  --arg corrupt "$(jq -r \
    '.integration_gate.corrupt_rejection_sha256' "$provenance")" \
  --arg first8 "$(jq -r \
    '.integration_gate.first8_equivalence_sha256' "$provenance")" \
  --arg oom "$(jq -r \
    '.integration_gate.xargs_oom_selftest_sha256' "$provenance")" \
  --arg reservation "$(jq -r \
    '.integration_gate.reservation_selftest_sha256' "$provenance")" '
    .schema == "hh-task10-a-integration-gate-v4" and
    .status == "complete" and .input_inventory_sha256 == $input and
    .run_header_sha256 == $run and .result_sha256 == $result and
    .baseline_validation_sha256 == $baseline and
    .exact_resume_sha256 == $resume and
    .model_env_rejection_sha256 == $model and
    .ranking_rejections_sha256 == $ranking and
    .stale_rejection_sha256 == $stale and
    .corrupt_rejection_sha256 == $corrupt and
    .first8_equivalence_sha256 == $first8 and
    .xargs_oom_selftest_sha256 == $oom and
    .reservation_selftest_sha256 == $reservation and
    .counters.members == 5 and .counters.goals == 426 and
    .counters.rows == 6816 and .counters.historical_divergences == 0 and
    .counters.current_mismatches == 0 and
    .counters.binding_mismatches == 0 and .counters.prover_spawns == 0
  ' "$certificate" >/dev/null
