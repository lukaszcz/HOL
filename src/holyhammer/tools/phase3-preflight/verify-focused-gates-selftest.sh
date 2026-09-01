#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 1 || {
  echo "usage: $0 VERIFY_TOOL" >&2
  exit 2
}
verify_tool=$1
test -x "$verify_tool"
work=$(mktemp -d)
trap 'chmod -R u+w "$work" 2>/dev/null || true; \
  find "$work" -depth -delete 2>/dev/null || true' EXIT HUP INT TERM
support=$work/support
mkdir -p "$support/smoke-input" "$support/smoke-run" \
  "$support/storage"
printf '%s\n' smoke >"$support/smoke-input/member"
(cd "$support/smoke-input" && sha256sum member >SHA256SUMS)
printf '%s\n' storage >"$support/storage/member"
(cd "$support/storage" && sha256sum member >SHA256SUMS)
printf '%s\n' run >"$support/smoke-run/run.json"
printf '%s\n' result >"$support/smoke-run/result.json"
printf '%s\n' baseline >"$support/smoke-run/baseline.json"
for name in resume model ranking stale corrupt first8 oom; do
  printf '%s\n' "$name" >"$support/smoke-run/$name.json"
done
jq -n \
  '{status:"complete",configured_cap:8,observed_maximum:8,
    all_reservations_released:true}' \
  >"$support/storage/reservation.json"

file_sha () { sha256sum "$1" | awk '{print $1}'; }
jq -n --arg input "$(file_sha \
    "$support/smoke-input/SHA256SUMS")" \
  --arg run "$(file_sha "$support/smoke-run/run.json")" \
  --arg result "$(file_sha "$support/smoke-run/result.json")" \
  --arg baseline "$(file_sha "$support/smoke-run/baseline.json")" \
  --arg resume "$(file_sha "$support/smoke-run/resume.json")" \
  --arg model "$(file_sha "$support/smoke-run/model.json")" \
  --arg ranking "$(file_sha "$support/smoke-run/ranking.json")" \
  --arg stale "$(file_sha "$support/smoke-run/stale.json")" \
  --arg corrupt "$(file_sha "$support/smoke-run/corrupt.json")" \
  --arg first8 "$(file_sha "$support/smoke-run/first8.json")" \
  --arg oom "$(file_sha "$support/smoke-run/oom.json")" \
  --arg reservation "$(file_sha "$support/storage/reservation.json")" '
    {schema:"hh-task10-a-integration-gate-v4",status:"complete",
     completed:"2026-08-30T00:00:00Z",experiment:"focused-selftest",
     input_inventory_sha256:$input,run_header_sha256:$run,
     result_sha256:$result,baseline_validation_sha256:$baseline,
     exact_resume_sha256:$resume,model_env_rejection_sha256:$model,
     ranking_rejections_sha256:$ranking,stale_rejection_sha256:$stale,
     corrupt_rejection_sha256:$corrupt,first8_equivalence_sha256:$first8,
     xargs_oom_selftest_sha256:$oom,
     reservation_selftest_sha256:$reservation,
     counters:{members:5,goals:426,rows:6816,historical_divergences:0,
       current_mismatches:0,binding_mismatches:0,prover_spawns:0,
       ranking_journals:426}}
  ' >"$support/smoke-run/integration.json"
jq -n \
  '{status:"exact",rows_byte_identical:true,rankings_byte_identical:true}' \
  >"$support/storage/equivalence.json"
jq -n '{status:"exact",whole_chunks_byte_identical:true}' \
  >"$support/storage/profile.json"
jq -n \
  '{status:"complete",resume_byte_identical:true,
    scratch_bounded_after_every_commit:true}' \
  >"$support/storage/checkpoint.json"

(cd "$support" && find . -type f ! -path ./SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$support/SHA256SUMS"

jq -n \
  --arg support "$(file_sha "$support/SHA256SUMS")" \
  --arg smoke_inventory "$(file_sha \
    "$support/smoke-input/SHA256SUMS")" \
  --arg run "$(file_sha "$support/smoke-run/run.json")" \
  --arg result "$(file_sha "$support/smoke-run/result.json")" \
  --arg baseline "$(file_sha "$support/smoke-run/baseline.json")" \
  --arg integration "$(file_sha "$support/smoke-run/integration.json")" \
  --arg resume "$(file_sha "$support/smoke-run/resume.json")" \
  --arg model "$(file_sha "$support/smoke-run/model.json")" \
  --arg ranking "$(file_sha "$support/smoke-run/ranking.json")" \
  --arg stale "$(file_sha "$support/smoke-run/stale.json")" \
  --arg corrupt "$(file_sha "$support/smoke-run/corrupt.json")" \
  --arg first8 "$(file_sha "$support/smoke-run/first8.json")" \
  --arg oom "$(file_sha "$support/smoke-run/oom.json")" \
  --arg storage_inventory "$(file_sha \
    "$support/storage/SHA256SUMS")" \
  --arg equivalence "$(file_sha "$support/storage/equivalence.json")" \
  --arg profile "$(file_sha "$support/storage/profile.json")" \
  --arg checkpoint "$(file_sha "$support/storage/checkpoint.json")" \
  --arg reservation "$(file_sha "$support/storage/reservation.json")" '
    {schema:"hh-task10-p-run-v4",
     focused_gates:{schema:"hh-task10-p-focused-gates-v3",
       support_inventory_path:"support/SHA256SUMS",
       support_inventory_sha256:$support,
       smoke:{input_inventory_path:"support/smoke-input/SHA256SUMS",
         input_inventory_sha256:$smoke_inventory,
         run_header_path:"support/smoke-run/run.json",
         run_header_sha256:$run,
         result_path:"support/smoke-run/result.json",result_sha256:$result,
         baseline_validation_path:"support/smoke-run/baseline.json",
         baseline_validation_sha256:$baseline,
         integration_certificate_path:"support/smoke-run/integration.json",
         integration_certificate_sha256:$integration,
         resume_certificate_path:"support/smoke-run/resume.json",
         resume_certificate_sha256:$resume,
         model_env_rejection_path:"support/smoke-run/model.json",
         model_env_rejection_sha256:$model,
         ranking_rejections_path:"support/smoke-run/ranking.json",
         ranking_rejections_sha256:$ranking,
         stale_rejection_path:"support/smoke-run/stale.json",
         stale_rejection_sha256:$stale,
         corrupt_rejection_path:"support/smoke-run/corrupt.json",
         corrupt_rejection_sha256:$corrupt,
         first8_equivalence_path:"support/smoke-run/first8.json",
         first8_equivalence_sha256:$first8,
         xargs_oom_selftest_path:"support/smoke-run/oom.json",
         xargs_oom_selftest_sha256:$oom},
       storage:{evidence_inventory_path:"support/storage/SHA256SUMS",
         evidence_inventory_sha256:$storage_inventory,
         equivalence_path:"support/storage/equivalence.json",
         equivalence_sha256:$equivalence,
         profile_equivalence_path:"support/storage/profile.json",
         profile_equivalence_sha256:$profile,
         checkpoint_selftest_path:"support/storage/checkpoint.json",
         checkpoint_selftest_sha256:$checkpoint,
         reservation_selftest_path:"support/storage/reservation.json",
         reservation_selftest_sha256:$reservation}}}
  ' >"$work/top.json"
"$verify_tool" "$work" "$work/top.json"

reject () {
  local name=$1 filter=$2
  jq "$filter" "$work/top.json" >"$work/$name.json"
  if "$verify_tool" "$work" "$work/$name.json" >/dev/null 2>&1; then
    echo "focused-gate verifier accepted invalid case: $name" >&2
    exit 1
  fi
}
reject missing 'del(.focused_gates.smoke.resume_certificate_path)'
reject stale '.focused_gates.storage.equivalence_sha256 =
  "0000000000000000000000000000000000000000000000000000000000000000"'
reject extra '.focused_gates.extra = true'
reject malformed '.focused_gates.storage.reservation_selftest_sha256 = "x"'
reject substitution '.focused_gates.smoke.model_env_rejection_sha256 =
  .focused_gates.smoke.ranking_rejections_sha256'
reject fabricated '.focused_gates.smoke.first8_equivalence_sha256 =
  "1111111111111111111111111111111111111111111111111111111111111111"'

printf '%s\n' changed >"$work/external-history"
"$verify_tool" "$work" "$work/top.json"
chmod u+w "$support/smoke-run/model.json"
printf '%s\n' tampered >"$support/smoke-run/model.json"
if "$verify_tool" "$work" "$work/top.json" >/dev/null 2>&1; then
  echo "focused-gate verifier accepted internal support tamper" >&2
  exit 1
fi
printf '%s\n' "P focused-gate verification: passed"
