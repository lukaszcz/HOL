#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 13 || {
  echo "usage: $0 ROOT INPUTS TEMPLATE P_INPUT P_F30 P_S30 P_PROBES" \
    "SMOKE_INPUT SMOKE_RUN SMOKE_CERTS STORAGE HISTORY OUTPUT" >&2
  exit 2
}
root=$1
inputs=$2
template=$3
p_input=$4
p_f30=$5
p_s30=$6
p_probes=$7
smoke_input=$8
smoke_run=$9
smoke_certificates=${10}
storage=${11}
history=${12}
output=${13}
temporary=$output.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM

sha () { sha256sum "$1" | awk '{print $1}'; }
relative () { realpath --relative-to="$inputs" "$1"; }
support=$inputs/support
test ! -e "$support" || {
  echo "support snapshot must be initially absent" >&2
  exit 2
}
"$inputs/snapshot-support.sh" "$p_input" "$support/preflight/input"
"$inputs/snapshot-support.sh" "$p_f30" "$support/preflight/f30" \
  result.json
"$inputs/snapshot-support.sh" "$p_s30" "$support/preflight/s30v5" \
  result.json export-volume/result.json
"$inputs/snapshot-support.sh" "$p_probes" "$support/preflight/probes" \
  result.json
"$inputs/snapshot-support.sh" "$smoke_input" "$support/smoke/input"
"$inputs/snapshot-support.sh" "$smoke_run" "$support/smoke/run" \
  run.json result.json baseline-validation.json \
  integration-certificate.json current-model-env-rejection.json \
  current-ranking-rejections.json stale-input-rejection.json \
  corrupt-input-rejection.json profile-first8-equivalence.json
"$inputs/snapshot-support.sh" "$smoke_certificates" \
  "$support/smoke/certificates" resume2.json
"$inputs/snapshot-support.sh" "$storage" "$support/storage"
"$inputs/snapshot-support.sh" "$history" "$support/predecessors"
p_input=$support/preflight/input
p_f30=$support/preflight/f30
p_s30=$support/preflight/s30v5
p_probes=$support/preflight/probes
smoke_input=$support/smoke/input
smoke_run=$support/smoke/run
smoke_certificates=$support/smoke/certificates
storage=$support/storage
history=$support/predecessors
(cd "$support" && find . -type f ! -path ./SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$support/SHA256SUMS"
(cd "$support" && sha256sum -c SHA256SUMS >/dev/null)
for required in "$inputs/runtime-origin.tsv" "$template" \
  "$inputs/theory-inventory.tsv" "$inputs/worker-function-manifest.tsv" \
  "$inputs/profile-first8-evidence/SHA256SUMS" \
  "$inputs/profile-first8-selftest.sh" \
  "$inputs/profile-unequal-tail-selftest.sh" \
  "$p_input/SHA256SUMS" "$p_f30/result.json" "$p_s30/result.json" \
  "$p_s30/export-volume/result.json" "$p_probes/result.json" \
  "$smoke_input/SHA256SUMS" "$smoke_run/run.json" \
  "$smoke_run/result.json" "$smoke_run/baseline-validation.json" \
  "$smoke_run/integration-certificate.json" \
  "$smoke_certificates/resume2.json" \
  "$smoke_run/current-model-env-rejection.json" \
  "$smoke_run/current-ranking-rejections.json" \
  "$smoke_run/stale-input-rejection.json" \
  "$smoke_run/corrupt-input-rejection.json" \
  "$smoke_run/profile-first8-equivalence.json" \
  "$inputs/current-xargs-oom-selftest.sh" \
  "$storage/evidence-SHA256SUMS" "$storage/equivalence.json" \
  "$storage/current-checkpoint-evidence.sha256" \
  "$storage/profile-chunk-equivalence.json" \
  "$storage/profile-chunk-evidence.sha256" \
  "$storage/checkpoint-reservation-selftest.json" "$history/SHA256SUMS"
do
  test -s "$required" && test ! -L "$required"
done
(cd "$p_input" && sha256sum -c SHA256SUMS >/dev/null)
(cd "$smoke_input" && sha256sum -c SHA256SUMS >/dev/null)
(cd "$storage" && sha256sum -c evidence-SHA256SUMS >/dev/null)
(cd "$history" && sha256sum -c SHA256SUMS >/dev/null)
test "$(sha "$storage/current-checkpoint-evidence.sha256")" = \
  "$(jq -r '.evidence_inventory_sha256' "$storage/equivalence.json")"
test "$(sha "$storage/profile-chunk-evidence.sha256")" = \
  "$(jq -r '.evidence_inventory_sha256' \
    "$storage/profile-chunk-equivalence.json")"
test "$(sha "$storage/profile-chunk-equivalence.json")" = \
  "$(jq -r '.profile_chunk_equivalence_sha256' \
    "$storage/equivalence.json")"

runtime_json=$(awk -F '\t' '
  NF == 3 {printf "%s\t%s\t%s\n",$1,$2,$3}
' "$inputs/runtime-origin.tsv" | jq -Rn '
  [inputs | split("\t") |
   {(.[0]):{tracked_source:.[1],sha256:.[2]}}] | add
')
integration=$(jq -n \
  --arg inventory_path "$(relative "$smoke_input/SHA256SUMS")" \
  --arg inventory "$(sha "$smoke_input/SHA256SUMS")" \
  --arg run_path "$(relative "$smoke_run/run.json")" \
  --arg run "$(sha "$smoke_run/run.json")" \
  --arg result_path "$(relative "$smoke_run/result.json")" \
  --arg result "$(sha "$smoke_run/result.json")" \
  --arg baseline_path \
    "$(relative "$smoke_run/baseline-validation.json")" \
  --arg baseline "$(sha "$smoke_run/baseline-validation.json")" \
  --arg certificate_path \
    "$(relative "$smoke_run/integration-certificate.json")" \
  --arg certificate "$(sha "$smoke_run/integration-certificate.json")" \
  --arg resume_path "$(relative "$smoke_certificates/resume2.json")" \
  --arg resume "$(sha "$smoke_certificates/resume2.json")" \
  --arg model_path \
    "$(relative "$smoke_run/current-model-env-rejection.json")" \
  --arg model "$(sha "$smoke_run/current-model-env-rejection.json")" \
  --arg ranking_path \
    "$(relative "$smoke_run/current-ranking-rejections.json")" \
  --arg ranking "$(sha "$smoke_run/current-ranking-rejections.json")" \
  --arg stale_path "$(relative "$smoke_run/stale-input-rejection.json")" \
  --arg stale "$(sha "$smoke_run/stale-input-rejection.json")" \
  --arg corrupt_path \
    "$(relative "$smoke_run/corrupt-input-rejection.json")" \
  --arg corrupt "$(sha "$smoke_run/corrupt-input-rejection.json")" \
  --arg first8_path \
    "$(relative "$smoke_run/profile-first8-equivalence.json")" \
  --arg first8 "$(sha "$smoke_run/profile-first8-equivalence.json")" \
  --arg oom_path "$(relative "$inputs/current-xargs-oom-selftest.sh")" \
  --arg oom "$(sha "$inputs/current-xargs-oom-selftest.sh")" \
  --arg reservation_path \
    "$(relative "$storage/checkpoint-reservation-selftest.json")" \
  --arg reservation \
    "$(sha "$storage/checkpoint-reservation-selftest.json")" '
  {schema:"hh-task10-a-integration-support-v1",
   input_inventory_path:$inventory_path,input_inventory_sha256:$inventory,
   run_header_path:$run_path,run_header_sha256:$run,
   result_path:$result_path,result_sha256:$result,
   baseline_validation_path:$baseline_path,
   baseline_validation_sha256:$baseline,
   integration_certificate_path:$certificate_path,
   integration_certificate_sha256:$certificate,
   resume_certificate_path:$resume_path,resume_certificate_sha256:$resume,
   model_env_rejection_path:$model_path,model_env_rejection_sha256:$model,
   ranking_rejections_path:$ranking_path,
   ranking_rejections_sha256:$ranking,
   stale_rejection_path:$stale_path,stale_rejection_sha256:$stale,
   corrupt_rejection_path:$corrupt_path,corrupt_rejection_sha256:$corrupt,
   first8_equivalence_path:$first8_path,first8_equivalence_sha256:$first8,
   xargs_oom_selftest_path:$oom_path,xargs_oom_selftest_sha256:$oom,
   reservation_selftest_path:$reservation_path,
   reservation_selftest_sha256:$reservation}
')
preflight=$(jq -n \
  --arg input_path "$(relative "$p_input/SHA256SUMS")" \
  --arg inventory "$(sha "$p_input/SHA256SUMS")" \
  --arg f30_path "$(relative "$p_f30/result.json")" \
  --arg f30_result "$(sha "$p_f30/result.json")" \
  --arg s30_path "$(relative "$p_s30/result.json")" \
  --arg s30_result "$(sha "$p_s30/result.json")" \
  --arg probes_path "$(relative "$p_probes/result.json")" \
  --arg probe_result "$(sha "$p_probes/result.json")" \
  --arg volume_path \
    "$(relative "$p_s30/export-volume/result.json")" \
  --arg volume_result "$(sha "$p_s30/export-volume/result.json")" '
  {schema:"hh-task10-a-preflight-support-v1",
   input_inventory_path:$input_path,input_inventory_sha256:$inventory,
   f30_result_path:$f30_path,
   f30_result_sha256:$f30_result,s30_result_sha256:$s30_result,
   s30_result_path:$s30_path,probe_result_path:$probes_path,
   probe_result_sha256:$probe_result,
   s30_export_volume_result_path:$volume_path,
   s30_export_volume_result_sha256:$volume_result}
')
history_records=$(awk '{print $2}' "$history/SHA256SUMS" | while read -r name
do
  path="$history/$name"
  printf '%s\t%s\n' "$(relative "$path")" "$(sha "$path")"
done | jq -Rn '[inputs | split("\t") | {path:.[0],sha256:.[1]}]')
predecessors=$(jq -n \
  --arg path "$(relative "$history/SHA256SUMS")" \
  --arg digest "$(sha "$history/SHA256SUMS")" \
  --argjson records "$history_records" '
  {schema:"hh-task10-predecessor-rejections-v1",inventory_path:$path,
   inventory_sha256:$digest,records:$records,
   discarded_raw_diagnostics:true}
')

jq --arg commit "$(git -C "$root" rev-parse HEAD)" \
  --arg diff "$(git -C "$root" diff --binary -- src/holyhammer |
    sha256sum | awk '{print $1}')" \
  --arg started "$(date -u +%FT%TZ)" \
  --arg runtime_inventory "$(sha "$inputs/runtime-origin.tsv")" \
  --arg checkpoint_equivalence "$(sha "$storage/equivalence.json")" \
  --arg checkpoint_inventory \
    "$(sha "$storage/current-checkpoint-evidence.sha256")" \
  --arg profile_equivalence \
    "$(sha "$storage/profile-chunk-equivalence.json")" \
  --arg theory_inventory "$(sha "$inputs/theory-inventory.tsv")" \
  --arg worker_manifest "$(sha "$inputs/worker-function-manifest.tsv")" \
  --arg first8_inventory \
    "$(sha "$inputs/profile-first8-evidence/SHA256SUMS")" \
  --arg first8_selftest "$(sha "$inputs/profile-first8-selftest.sh")" \
  --arg unequal_tail \
    "$(sha "$inputs/profile-unequal-tail-selftest.sh")" \
  --arg support_inventory "$(sha "$support/SHA256SUMS")" \
  --argjson runtime "$runtime_json" --argjson integration "$integration" \
  --argjson preflight "$preflight" --argjson predecessors "$predecessors" '
    .schema = "hh-task10-a-run-v13" |
    .revision = "final-source-v9-offline-verifier-v1" |
    .started = $started |
    .main.commit = $commit | .main.tracked_diff_sha256 = $diff |
    .runtime_tools = {schema:"hh-task10-runtime-tools-v2",
      origin_inventory_sha256:$runtime_inventory,files:$runtime} |
    .theory_inventory_sha256 = $theory_inventory |
    .worker_function_preflight.manifest_sha256 = $worker_manifest |
    del(.worker_function_preflight.integration_certificate_sha256) |
    .current_checkpoint_chain.equivalence_certificate_sha256 =
      $checkpoint_equivalence |
    .current_checkpoint_chain.evidence_inventory_sha256 =
      $checkpoint_inventory |
    .profile_goal_chunking.equivalence_certificate_sha256 =
      $profile_equivalence |
    .profile_goal_chunking.first8_evidence_inventory_sha256 =
      $first8_inventory |
    .profile_goal_chunking.first8_selftest_sha256 = $first8_selftest |
    .profile_goal_chunking.unequal_tail_selftest_sha256 = $unequal_tail |
    .integration_gate = $integration | .preflight = $preflight |
    .predecessor_rejections = $predecessors |
    .support_snapshot = {schema:"hh-task10-support-snapshot-v1",
      inventory_path:"support/SHA256SUMS",
      inventory_sha256:$support_inventory} |
    del(.integration_smoke,.mapped_execution_gate)
  ' "$template" >"$temporary"
mv "$temporary" "$output"
trap - EXIT HUP INT TERM
