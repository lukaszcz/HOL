#!/bin/bash
set -Eeuo pipefail

INPUTS=${HHEVAL_TASK10_A_INPUTS:?immutable input directory is required}
EXP=${HHEVAL_TASK10_A_EXP:?experiment is required}
export HHEVAL_TASK10_RUNNER_LIBRARY_ONLY=1
source "$INPUTS/run-a.sh"
verify_live_external_tools

verify_worker_export_boundary
verify_inputs
initialize
trap 'cleanup_staged_signatures' EXIT
trap 'exit 130' HUP INT TERM
pool baseline
validate_baseline
test_current_model_env_rejection
test_current_ranking_rejections
export HHEVAL_CHECKPOINT_TEST_SIGKILL_ONCE_THEORY=real_arith
pool current
unset HHEVAL_CHECKPOINT_TEST_SIGKILL_ONCE_THEORY
validate_current

failure=$(find "$OUT/checkpoint-failures/real_arith" -mindepth 1 \
  -maxdepth 1 -type d -name 'atom-0-status-1.*' -print -quit)
test -n "$failure"
jq -e '
  .schema == "hh-current-checkpoint-failure-classification-v1" and
  .theory == "real_arith" and .start == 0 and .worker_status == 1 and
  .retry_status == 76 and .receipt_accepted == false and
  (.test_sigkill_marker | length) > 0' \
  "$failure/failure-classification.json" >/dev/null
grep -F 'current checkpoint infrastructure-retry theory=real_arith status=76 attempt=1' \
  "$OUT/recycles.log" >/dev/null
test "$(find "$OUT/current" -maxdepth 1 -type f -name '*.tsv' | wc -l)" \
  -eq "$(wc -l <"$INVENTORY")"
test -z "$(find "$OUT" "$STATE" -type f -name '*.partial*' -print -quit)"
test "$(tail -n +2 "$OUT/current-first8/real_arith.tsv" | wc -l)" \
  -eq "$((8 * $(awk -F '\t' '$1 == "real_arith" {print $2}' \
    "$INVENTORY")))"
jq -e '
  .task13_premise_mismatches == 0 and
  .task13_request_key_mismatches == 0 and
  .task13_internal_key_pair_mismatches == 0 and
  .prover_spawns == 0' \
  <(head -1 "$OUT/current-first8/real_arith.tsv" | cut -f2-) >/dev/null
test "$(jq -r 'select(.event == "acquire") | .concurrent_slots' \
  "$OUT/checkpoint-reservations.jsonl" | sort -nr | head -1)" \
  -le "$CHECKPOINT_RESERVATION_SLOTS"
"$INPUTS/checkpoint-reservation-selftest.sh" "$INPUTS" "$EXP"

jq -n --arg result "$(sha "$OUT/result.json")" \
  --arg failure "$(sha "$failure/failure-classification.json")" \
  --arg reservation "$(sha "$OUT/checkpoint-reservation-selftest.json")" \
  '{schema:"hh-current-exported-xargs-oom-selftest-v1",status:"complete",
    scheduler_workers:16,pool_exit_status:0,real_nested_hol_sigkill:true,
    other_workers_continued:true,killed_atom_retry_status:76,
    killed_atom_retried_and_accepted:true,prior_checkpoint_authoritative:true,
    partial_receipt_accepted:false,rows_byte_identical:true,
    result_sha256:$result,failure_classification_sha256:$failure,
    reservation_selftest_sha256:$reservation}' \
  >"$OUT/xargs-oom-selftest.json"
