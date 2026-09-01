#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 8 || {
  echo "usage: $0 ROOT INPUTS TEMPLATE SMOKE_INPUT SMOKE_RUN" \
    "SMOKE_CERTIFICATES STORAGE OUTPUT" >&2
  exit 2
}
root=$1
inputs=$2
template=$3
smoke_input=$4
smoke_run=$5
smoke_certificates=$6
storage=$7
output=$8
experiment_base=phase3-task10-$(basename "$inputs")
temporary=$output.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM

sha () { sha256sum "$1" | awk '{print $1}'; }
relative () { realpath --relative-to="$inputs" "$1"; }
support=$inputs/support
test ! -e "$support" || {
  echo "support snapshot must be initially absent" >&2
  exit 2
}
"$inputs/snapshot-support.sh" "$smoke_input" "$support/smoke/input"
"$inputs/snapshot-support.sh" "$smoke_run" "$support/smoke/run" \
  run.json result.json baseline-validation.json \
  integration-certificate.json current-model-env-rejection.json \
  current-ranking-rejections.json stale-input-rejection.json \
  corrupt-input-rejection.json profile-first8-equivalence.json
"$inputs/snapshot-support.sh" "$smoke_certificates" \
  "$support/smoke/certificates" resume2.json
"$inputs/snapshot-support.sh" "$storage" "$support/storage"
smoke_input=$support/smoke/input
smoke_run=$support/smoke/run
smoke_certificates=$support/smoke/certificates
storage=$support/storage
(cd "$support" && find . -type f ! -path ./SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$support/SHA256SUMS"
(cd "$support" && sha256sum -c SHA256SUMS >/dev/null)
for required in "$inputs/runtime-origin.tsv" "$template" \
  "$smoke_input/SHA256SUMS" "$smoke_run/run.json" \
  "$smoke_run/result.json" "$smoke_run/baseline-validation.json" \
  "$smoke_run/integration-certificate.json" \
  "$smoke_certificates/resume2.json" \
  "$smoke_run/current-model-env-rejection.json" \
  "$smoke_run/current-ranking-rejections.json" \
  "$smoke_run/stale-input-rejection.json" \
  "$smoke_run/corrupt-input-rejection.json" \
  "$smoke_run/profile-first8-equivalence.json" \
  "$smoke_input/current-xargs-oom-selftest.sh" \
  "$storage/evidence-SHA256SUMS" \
  "$storage/equivalence.json" "$storage/profile-chunk-equivalence.json" \
  "$storage/checkpoint-selftest.json" \
  "$storage/checkpoint-reservation-selftest.json"
do
  test -s "$required" && test ! -L "$required"
done
(cd "$smoke_input" && sha256sum -c SHA256SUMS >/dev/null)
(cd "$storage" && sha256sum -c evidence-SHA256SUMS >/dev/null)

runtime_json=$(awk -F '\t' '
  NF == 3 {printf "%s\t%s\t%s\n",$1,$2,$3}
' "$inputs/runtime-origin.tsv" | jq -Rn '
  [inputs | split("\t") |
   {(.[0]):{tracked_source:.[1],sha256:.[2]}}] | add
')
focused=$(jq -n \
  --arg support_path "support/SHA256SUMS" \
  --arg support "$(sha "$support/SHA256SUMS")" \
  --arg smoke_inventory_path "$(relative "$smoke_input/SHA256SUMS")" \
  --arg smoke_inventory "$(sha "$smoke_input/SHA256SUMS")" \
  --arg smoke_run_path "$(relative "$smoke_run/run.json")" \
  --arg smoke_run "$(sha "$smoke_run/run.json")" \
  --arg smoke_result_path "$(relative "$smoke_run/result.json")" \
  --arg smoke_result "$(sha "$smoke_run/result.json")" \
  --arg smoke_baseline_path \
    "$(relative "$smoke_run/baseline-validation.json")" \
  --arg smoke_baseline "$(sha "$smoke_run/baseline-validation.json")" \
  --arg smoke_certificate_path \
    "$(relative "$smoke_run/integration-certificate.json")" \
  --arg smoke_certificate "$(sha "$smoke_run/integration-certificate.json")" \
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
  --arg oom_path \
    "$(relative "$smoke_input/current-xargs-oom-selftest.sh")" \
  --arg oom "$(sha "$smoke_input/current-xargs-oom-selftest.sh")" \
  --arg storage_inventory_path \
    "$(relative "$storage/evidence-SHA256SUMS")" \
  --arg storage_inventory "$(sha "$storage/evidence-SHA256SUMS")" \
  --arg equivalence_path "$(relative "$storage/equivalence.json")" \
  --arg equivalence "$(sha "$storage/equivalence.json")" \
  --arg profile_path \
    "$(relative "$storage/profile-chunk-equivalence.json")" \
  --arg profile "$(sha "$storage/profile-chunk-equivalence.json")" \
  --arg checkpoint_path \
    "$(relative "$storage/checkpoint-selftest.json")" \
  --arg checkpoint "$(sha "$storage/checkpoint-selftest.json")" \
  --arg reservation_path \
    "$(relative "$storage/checkpoint-reservation-selftest.json")" \
  --arg reservation \
    "$(sha "$storage/checkpoint-reservation-selftest.json")" '
    {schema:"hh-task10-p-focused-gates-v3",
     support_inventory_path:$support_path,
     support_inventory_sha256:$support,
     smoke:{input_inventory_path:$smoke_inventory_path,
       input_inventory_sha256:$smoke_inventory,
       run_header_path:$smoke_run_path,run_header_sha256:$smoke_run,
       result_path:$smoke_result_path,result_sha256:$smoke_result,
       baseline_validation_path:$smoke_baseline_path,
       baseline_validation_sha256:$smoke_baseline,
       integration_certificate_path:$smoke_certificate_path,
       integration_certificate_sha256:$smoke_certificate,
       resume_certificate_path:$resume_path,
       resume_certificate_sha256:$resume,
       model_env_rejection_path:$model_path,
       model_env_rejection_sha256:$model,
       ranking_rejections_path:$ranking_path,
       ranking_rejections_sha256:$ranking,
       stale_rejection_path:$stale_path,stale_rejection_sha256:$stale,
       corrupt_rejection_path:$corrupt_path,
       corrupt_rejection_sha256:$corrupt,
       first8_equivalence_path:$first8_path,
       first8_equivalence_sha256:$first8,
       xargs_oom_selftest_path:$oom_path,xargs_oom_selftest_sha256:$oom},
     storage:{evidence_inventory_path:$storage_inventory_path,
       evidence_inventory_sha256:$storage_inventory,
       equivalence_path:$equivalence_path,equivalence_sha256:$equivalence,
       profile_equivalence_path:$profile_path,
       profile_equivalence_sha256:$profile,
       checkpoint_selftest_path:$checkpoint_path,
       checkpoint_selftest_sha256:$checkpoint,
       reservation_selftest_path:$reservation_path,
       reservation_selftest_sha256:$reservation}}
')

jq --arg commit "$(git -C "$root" rev-parse HEAD)" \
  --arg diff "$(git -C "$root" diff --binary -- src/holyhammer |
    sha256sum | awk '{print $1}')" \
  --arg runtime_inventory "$(sha "$inputs/runtime-origin.tsv")" \
  --arg f30 "$experiment_base-f30" \
  --arg s30 "$experiment_base-s30v5" \
  --arg probes "$experiment_base-probes" \
  --arg volume "$experiment_base-volume" \
  --argjson runtime "$runtime_json" --argjson focused "$focused" '
    .schema = "hh-task10-p-run-v4" |
    .main.commit = $commit | .main.tracked_diff_sha256 = $diff |
    .runtime_tools = {schema:"hh-task10-runtime-tools-v2",
      origin_inventory_sha256:$runtime_inventory,files:$runtime} |
    .experiments = {f30:$f30,s30v5:$s30,probes:$probes,volume:$volume} |
    .focused_gates = $focused |
    with_entries(select(.key == "canonical_gate" or .key == "experiments" or
      .key == "focused_gates" or .key == "main" or .key == "provers" or
      .key == "runtime_tools" or .key == "schema"))
  ' "$template" >"$temporary"
mv "$temporary" "$output"
trap - EXIT HUP INT TERM
