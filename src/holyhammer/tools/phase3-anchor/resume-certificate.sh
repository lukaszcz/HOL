#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 5 || {
  echo "usage: $0 RUN_OUTPUT INPUTS RUNNER DIAGNOSTIC CERTIFICATE" >&2
  exit 2
}
output=$1
inputs=$2
runner=$3
diagnostic=$4
certificate=$5
experiment=${output##*/}
state=/run/user/$(id -u)/holyhammer-phase3-task10/$experiment
temporary=$certificate.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM
sha () { sha256sum "$1" | awk '{print $1}'; }
tree () {
  (cd "$1" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum) | sha256sum | awk '{print $1}'
}
test ! -e "$state"
test -s "$output/tmpfs-cleanup.json"
for name in baseline current current-rankings current-checkpoint-chains; do
  before_var=before_${name//-/_}
  printf -v "$before_var" '%s' "$(tree "$output/$name")"
done
run_before=$(sha "$output/run.json")
baseline_before=$(sha "$output/baseline-validation.json")
result_before=$(sha "$output/result.json")
cleanup_before=$(sha "$output/tmpfs-cleanup.json")
invocations_before=$(sha "$output/invocations.jsonl")
env HHEVAL_TASK10_A_INPUTS="$inputs" HHEVAL_TASK10_A_EXP="$experiment" \
  "$runner" > "$diagnostic" 2>&1
test ! -e "$state"
for name in baseline current current-rankings current-checkpoint-chains; do
  before_var=before_${name//-/_}
  test "${!before_var}" = "$(tree "$output/$name")"
done
test "$run_before" = "$(sha "$output/run.json")"
test "$baseline_before" = "$(sha "$output/baseline-validation.json")"
test "$result_before" = "$(sha "$output/result.json")"
test "$cleanup_before" = "$(sha "$output/tmpfs-cleanup.json")"
invocations_after=$(sha "$output/invocations.jsonl")
test "$invocations_before" != "$invocations_after"
jq -s -e --arg run "$run_before" \
  --arg input "$(sha "$inputs/SHA256SUMS")" \
  --arg result "$result_before" '
  .[-2].event == "resume" and .[-2].run_header_sha256 == $run and
  .[-2].input_inventory_sha256 == $input and
  .[-1].event == "complete" and .[-1].result_sha256 == $result' \
  "$output/invocations.jsonl" >/dev/null
jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg experiment "$experiment" --arg input "$(sha "$inputs/SHA256SUMS")" \
  --arg run "$run_before" --arg baseline "$baseline_before" \
  --arg result "$result_before" --arg cleanup "$cleanup_before" \
  --arg baseline_tree "$before_baseline" --arg current_tree "$before_current" \
  --arg rankings_tree "$before_current_rankings" \
  --arg chains_tree "$before_current_checkpoint_chains" \
  --arg before "$invocations_before" --arg after "$invocations_after" \
  --arg runner "$(sha "$runner")" --arg verifier "$(sha "$0")" \
  --arg diagnostic "$(sha "$diagnostic")" '
    {schema:"hh-task10-exact-resume-v1",status:"complete",
     completed:$completed,experiment:$experiment,
     input_inventory_sha256:$input,run_header_sha256:$run,
     baseline_validation_sha256:$baseline,result_sha256:$result,
     tmpfs_cleanup_sha256:$cleanup,
     immutable_trees:{baseline:$baseline_tree,current:$current_tree,
       rankings:$rankings_tree,checkpoint_chains:$chains_tree},
     invocation_log_before_sha256:$before,
     invocation_log_after_sha256:$after,runner_sha256:$runner,
     verifier_sha256:$verifier,diagnostic_sha256:$diagnostic,
     durable_only:true,tmpfs_absent_before_and_after:true,
     immutable_results_byte_identical:true}' > "$temporary"
mv "$temporary" "$certificate"
chmod 0444 "$certificate" "$diagnostic"
trap - EXIT HUP INT TERM
