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
  .schema == "hh-task10-p-run-v4" and
  (.focused_gates | keys == ["schema","smoke","storage",
    "support_inventory_path","support_inventory_sha256"]) and
  .focused_gates.schema == "hh-task10-p-focused-gates-v3" and
  (.focused_gates.support_inventory_path | type == "string" and
    length > 0) and
  (.focused_gates.support_inventory_sha256 |
    test("^[0-9a-f]{64}$")) and
  (.focused_gates.smoke | keys == ["baseline_validation_path",
    "baseline_validation_sha256","corrupt_rejection_path",
    "corrupt_rejection_sha256","first8_equivalence_path",
    "first8_equivalence_sha256","input_inventory_path",
    "input_inventory_sha256","integration_certificate_path",
    "integration_certificate_sha256","model_env_rejection_path",
    "model_env_rejection_sha256","ranking_rejections_path",
    "ranking_rejections_sha256","result_path","result_sha256",
    "resume_certificate_path","resume_certificate_sha256",
    "run_header_path","run_header_sha256","stale_rejection_path",
    "stale_rejection_sha256","xargs_oom_selftest_path",
    "xargs_oom_selftest_sha256"]) and
  (.focused_gates.storage | keys == ["checkpoint_selftest_path",
    "checkpoint_selftest_sha256","equivalence_path","equivalence_sha256",
    "evidence_inventory_path","evidence_inventory_sha256",
    "profile_equivalence_path",
    "profile_equivalence_sha256","reservation_selftest_path",
    "reservation_selftest_sha256"]) and
  ([.focused_gates.smoke[],.focused_gates.storage[]] |
    all(type == "string" and length > 0))
' "$provenance" >/dev/null

support_inventory=$(bound_path "$(jq -r \
  '.focused_gates.support_inventory_path' "$provenance")")
test "$(sha "$support_inventory")" = "$(jq -r \
  '.focused_gates.support_inventory_sha256' "$provenance")"
(cd "$(dirname "$support_inventory")" &&
  sha256sum -c "$(basename "$support_inventory")" >/dev/null)
support_directory=$(dirname "$support_inventory")
cmp -s \
  <(sed -n 's/^[0-9a-f]\{64\}  //p' "$support_inventory" |
    LC_ALL=C sort) \
  <(cd "$support_directory" && find . -type f \
    ! -path ./SHA256SUMS -print | LC_ALL=C sort)

while IFS=$'\t' read -r relative expected
do
  verify_bound "$relative" "$expected"
done < <(jq -r '
  .focused_gates.smoke as $smoke |
  .focused_gates.storage as $storage |
  [[$smoke.input_inventory_path,$smoke.input_inventory_sha256],
   [$smoke.run_header_path,$smoke.run_header_sha256],
   [$smoke.result_path,$smoke.result_sha256],
   [$smoke.baseline_validation_path,$smoke.baseline_validation_sha256],
   [$smoke.integration_certificate_path,
    $smoke.integration_certificate_sha256],
   [$smoke.resume_certificate_path,$smoke.resume_certificate_sha256],
   [$smoke.model_env_rejection_path,$smoke.model_env_rejection_sha256],
   [$smoke.ranking_rejections_path,$smoke.ranking_rejections_sha256],
   [$smoke.stale_rejection_path,$smoke.stale_rejection_sha256],
   [$smoke.corrupt_rejection_path,$smoke.corrupt_rejection_sha256],
   [$smoke.first8_equivalence_path,$smoke.first8_equivalence_sha256],
   [$smoke.xargs_oom_selftest_path,$smoke.xargs_oom_selftest_sha256],
   [$storage.evidence_inventory_path,$storage.evidence_inventory_sha256],
   [$storage.equivalence_path,$storage.equivalence_sha256],
   [$storage.profile_equivalence_path,$storage.profile_equivalence_sha256],
   [$storage.checkpoint_selftest_path,$storage.checkpoint_selftest_sha256],
   [$storage.reservation_selftest_path,
    $storage.reservation_selftest_sha256]][] | @tsv
' "$provenance")

smoke_inventory=$(bound_path "$(jq -r \
  '.focused_gates.smoke.input_inventory_path' "$provenance")")
storage_inventory=$(bound_path "$(jq -r \
  '.focused_gates.storage.evidence_inventory_path' "$provenance")")
(cd "$(dirname "$smoke_inventory")" &&
  sha256sum -c "$(basename "$smoke_inventory")" >/dev/null)
(cd "$(dirname "$storage_inventory")" &&
  sha256sum -c "$(basename "$storage_inventory")" >/dev/null)

smoke_certificate=$(bound_path "$(jq -r \
  '.focused_gates.smoke.integration_certificate_path' "$provenance")")
jq -e --arg input "$(jq -r \
    '.focused_gates.smoke.input_inventory_sha256' "$provenance")" \
  --arg run "$(jq -r \
    '.focused_gates.smoke.run_header_sha256' "$provenance")" \
  --arg result "$(jq -r \
    '.focused_gates.smoke.result_sha256' "$provenance")" \
  --arg baseline "$(jq -r \
    '.focused_gates.smoke.baseline_validation_sha256' "$provenance")" \
  --arg resume "$(jq -r \
    '.focused_gates.smoke.resume_certificate_sha256' "$provenance")" \
  --arg model "$(jq -r \
    '.focused_gates.smoke.model_env_rejection_sha256' "$provenance")" \
  --arg ranking "$(jq -r \
    '.focused_gates.smoke.ranking_rejections_sha256' "$provenance")" \
  --arg stale "$(jq -r \
    '.focused_gates.smoke.stale_rejection_sha256' "$provenance")" \
  --arg corrupt "$(jq -r \
    '.focused_gates.smoke.corrupt_rejection_sha256' "$provenance")" \
  --arg first8 "$(jq -r \
    '.focused_gates.smoke.first8_equivalence_sha256' "$provenance")" \
  --arg oom "$(jq -r \
    '.focused_gates.smoke.xargs_oom_selftest_sha256' "$provenance")" \
  --arg reservation "$(jq -r \
    '.focused_gates.storage.reservation_selftest_sha256' \
    "$provenance")" '
    (keys == ["baseline_validation_sha256","completed",
      "corrupt_rejection_sha256","counters","exact_resume_sha256",
      "experiment","first8_equivalence_sha256",
      "input_inventory_sha256","model_env_rejection_sha256",
      "ranking_rejections_sha256","reservation_selftest_sha256",
      "result_sha256","run_header_sha256","schema",
      "stale_rejection_sha256","status","xargs_oom_selftest_sha256"]) and
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
    (.completed | type == "string" and length > 0) and
    (.experiment | type == "string" and length > 0) and
    ([.exact_resume_sha256,.model_env_rejection_sha256,
      .ranking_rejections_sha256,.stale_rejection_sha256,
      .corrupt_rejection_sha256,.first8_equivalence_sha256,
      .xargs_oom_selftest_sha256,.reservation_selftest_sha256] |
      all(test("^[0-9a-f]{64}$"))) and
    (.counters | keys == ["binding_mismatches","current_mismatches",
      "goals","historical_divergences","members","prover_spawns",
      "ranking_journals","rows"]) and
    .counters.members == 5 and .counters.goals == 426 and
    .counters.rows == 6816 and .counters.historical_divergences == 0 and
    .counters.current_mismatches == 0 and
    .counters.binding_mismatches == 0 and .counters.prover_spawns == 0 and
    .counters.ranking_journals == 426
  ' "$smoke_certificate" >/dev/null

jq -e '.status == "exact" and .rows_byte_identical == true and
  .rankings_byte_identical == true' "$(bound_path "$(jq -r \
    '.focused_gates.storage.equivalence_path' "$provenance")")" \
  >/dev/null
jq -e '.status == "exact" and .whole_chunks_byte_identical == true' \
  "$(bound_path "$(jq -r \
    '.focused_gates.storage.profile_equivalence_path' "$provenance")")" \
  >/dev/null
jq -e '.status == "complete" and .resume_byte_identical == true and
  .scratch_bounded_after_every_commit == true' \
  "$(bound_path "$(jq -r \
    '.focused_gates.storage.checkpoint_selftest_path' "$provenance")")" \
  >/dev/null
jq -e '.status == "complete" and .configured_cap == 8 and
  .observed_maximum == 8 and .all_reservations_released == true' \
  "$(bound_path "$(jq -r \
    '.focused_gates.storage.reservation_selftest_path' "$provenance")")" \
  >/dev/null
