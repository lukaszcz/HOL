#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 5 || {
  echo "usage: $0 INPUTS RUN CERTIFICATES STORAGE OUTPUT" >&2
  exit 2
}
inputs=$1
run=$2
certificates=$3
storage=$4
output=$5
temporary=$output.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM

sha () { sha256sum "$1" | awk '{print $1}'; }
for required in "$inputs/SHA256SUMS" "$run/run.json" \
  "$run/result.json" "$run/baseline-validation.json" \
  "$certificates/resume2.json" "$run/current-model-env-rejection.json" \
  "$run/current-ranking-rejections.json" "$run/stale-input-rejection.json" \
  "$run/corrupt-input-rejection.json" \
  "$run/profile-first8-equivalence.json" \
  "$inputs/current-xargs-oom-selftest.sh" \
  "$storage/checkpoint-reservation-selftest.json"
do
  test -s "$required" && test ! -L "$required"
done
(cd "$inputs" && sha256sum -c SHA256SUMS >/dev/null)

jq -e '
  .status == "complete" and .counters.theories == 5 and
  .counters.goals == 426 and .counters.rows == 6816 and
  .counters.mismatches == 0 and .counters.binding_mismatches == 0 and
  .counters.prover_spawns == 0 and .counters.ranking_journals == 426
' "$run/result.json" >/dev/null
jq -e '.status == "complete" and .counters.premise == 0 and
  .counters.request == 0 and .counters.internal == 0 and
  .counters.prover_spawns == 0' \
  "$run/baseline-validation.json" >/dev/null
jq -e '.status == "exact" and .members == 5 and .goals == 426 and
  .rows == 3408 and .mismatch_binding_spawn_counters == 0' \
  "$run/profile-first8-equivalence.json" >/dev/null
jq -e '.status == "rejected" and .before_after_identical == true and
  .accepted_invocations_unchanged == true' \
  "$run/stale-input-rejection.json" "$run/corrupt-input-rejection.json" \
  >/dev/null
jq -e '.status == "rejected"' \
  "$run/current-model-env-rejection.json" >/dev/null
jq -e '.status == "complete" and .cross_feed_rejected == true and
  .stale_model_digest_rejected == true' \
  "$run/current-ranking-rejections.json" >/dev/null

jq -n --arg completed "$(date -u +%FT%TZ)" \
  --arg experiment "$(basename "$run")" \
  --arg input "$(sha "$inputs/SHA256SUMS")" \
  --arg run "$(sha "$run/run.json")" \
  --arg result "$(sha "$run/result.json")" \
  --arg baseline "$(sha "$run/baseline-validation.json")" \
  --arg resume "$(sha "$certificates/resume2.json")" \
  --arg model "$(sha "$run/current-model-env-rejection.json")" \
  --arg ranking "$(sha "$run/current-ranking-rejections.json")" \
  --arg stale "$(sha "$run/stale-input-rejection.json")" \
  --arg corrupt "$(sha "$run/corrupt-input-rejection.json")" \
  --arg first8 "$(sha "$run/profile-first8-equivalence.json")" \
  --arg xargs "$(sha "$inputs/current-xargs-oom-selftest.sh")" \
  --arg reservation \
    "$(sha "$storage/checkpoint-reservation-selftest.json")" \
  --argjson counters "$(jq '.counters' "$run/result.json")" '
  {schema:"hh-task10-a-integration-gate-v4",status:"complete",
   completed:$completed,experiment:$experiment,
   input_inventory_sha256:$input,run_header_sha256:$run,
   result_sha256:$result,baseline_validation_sha256:$baseline,
   exact_resume_sha256:$resume,model_env_rejection_sha256:$model,
   ranking_rejections_sha256:$ranking,stale_rejection_sha256:$stale,
   corrupt_rejection_sha256:$corrupt,first8_equivalence_sha256:$first8,
   xargs_oom_selftest_sha256:$xargs,
   reservation_selftest_sha256:$reservation,
   counters:{members:$counters.theories,goals:$counters.goals,
     rows:$counters.rows,historical_divergences:0,
     current_mismatches:$counters.mismatches,
     binding_mismatches:$counters.binding_mismatches,
     prover_spawns:$counters.prover_spawns,
     ranking_journals:$counters.ranking_journals}}
' >"$temporary"
mv "$temporary" "$output"
trap - EXIT HUP INT TERM
