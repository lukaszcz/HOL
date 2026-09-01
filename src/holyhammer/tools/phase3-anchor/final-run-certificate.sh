#!/bin/sh
set -eu

test "$#" -eq 6 || {
  echo "usage: $0 RUN_OUTPUT INPUTS FOLD RESUME RESOURCE_METRICS OUTPUT" >&2
  exit 2
}
run_output=$1
inputs=$2
fold=$3
resume=$4
resources=$5
output=$6
temporary=$output.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM
sha () { sha256sum "$1" | awk '{print $1}'; }
for path in "$run_output/run.json" "$run_output/baseline-validation.json" \
  "$run_output/result.json" "$run_output/tmpfs-cleanup.json" \
  "$inputs/SHA256SUMS" "$fold" "$resume" "$resources"; do
  test -s "$path" && test ! -L "$path"
done
expected_members=$(jq -er '.corpus.nonempty_theories' \
  "$inputs/top-provenance.json")
expected_goals=$(jq -er '.corpus.goals' "$inputs/top-provenance.json")
expected_rows=$(jq -er '.corpus.rows_per_side' \
  "$inputs/top-provenance.json")
expected_checked=$((expected_goals * 8))
jq -e --argjson members "$expected_members" \
  --argjson goals "$expected_goals" --argjson rows "$expected_rows" \
  --argjson checked "$expected_checked" '
  .schema == "hh-task10-a-independent-fold-v2" and
  (keys == ["baseline","baseline_current_canonical_rows_byte_identical",
    "baseline_inventory_order_body_sha256",
    "baseline_model_binding_inventory_sha256",
    "baseline_validation_sha256","canonical_inventory",
    "canonical_sorted_body_sha256","completed","current",
    "current_model_binding_inventory_sha256","failure_archives",
    "input_inventory_sha256","nonempty_mismatch_journals","partials",
    "provenance_bound_ranges_valid","result_sha256","run_header_sha256",
    "schema","selected_premise_binding_sha256",
    "selected_premise_bindings_byte_identical","status"]) and
  (.canonical_inventory | keys == ["checkpoint_chains",
    "checkpoint_receipts","extension_parts","goals","members",
    "ranking_journals","rows","slices"]) and
  (.baseline | keys == ["checked","chunks","expected","goals",
    "internal","premise","prover_spawns","request","rows","theories"]) and
  (.current | keys == ["binding_mismatches","chunks","goals",
    "mismatches","prover_spawns","ranges_valid","rows","theories"]) and
  ([.schema,.status,.completed,.input_inventory_sha256,
    .run_header_sha256,.baseline_validation_sha256,.result_sha256,
    .baseline_inventory_order_body_sha256,.canonical_sorted_body_sha256,
    .selected_premise_binding_sha256,
    .baseline_model_binding_inventory_sha256,
    .current_model_binding_inventory_sha256] |
    all(type == "string")) and
  ([.baseline_current_canonical_rows_byte_identical,
    .selected_premise_bindings_byte_identical,
    .provenance_bound_ranges_valid] | all(type == "boolean")) and
  ([.partials,.failure_archives,.nonempty_mismatch_journals] |
    all(type == "number")) and
  .status == "complete" and .canonical_inventory.members == $members and
  .canonical_inventory.goals == $goals and
  .canonical_inventory.slices == 16 and
  .canonical_inventory.rows == $rows and
  .canonical_inventory.ranking_journals == $goals and
  .baseline.theories == $members and .baseline.goals == $goals and
  .baseline.rows == $rows and .baseline.checked == $checked and
  .baseline.expected == $checked and
  .current.theories == $members and .current.goals == $goals and
  .current.rows == $rows and
  .baseline.premise == 0 and .baseline.request == 0 and
  .baseline.internal == 0 and .baseline.prover_spawns == 0 and
  .current.mismatches == 0 and
  .current.binding_mismatches == 0 and .current.prover_spawns == 0 and
  ([.canonical_inventory[]] | all(type == "number")) and
  ([.baseline[]] | all(type == "number")) and
  ([.current[]] | all(type == "number" or type == "boolean")) and
  .baseline_current_canonical_rows_byte_identical == true and
  .selected_premise_bindings_byte_identical == true and
  .provenance_bound_ranges_valid == true and .partials == 0 and
  .failure_archives == 0 and .nonempty_mismatch_journals == 0' \
  "$fold" >/dev/null
jq -e '.status == "complete" and .durable_only == true and
  .tmpfs_absent_before_and_after == true and
  .immutable_results_byte_identical == true' "$resume" >/dev/null
jq -e '.schema == "hh-task10-tmpfs-cleanup-v1" and
  .status == "removed" and .state_files >= 0 and .state_symlinks >= 0 and
  .tmpfs_root_absent_after_cleanup == true' \
  "$run_output/tmpfs-cleanup.json" >/dev/null
jq -e '.scheduler_workers == 16 and .cpu_quota_cores == 32 and
  .memory_high_bytes == 133143986176 and
  .memory_max_bytes == 137438953472 and .memory_swap_max_bytes == 0 and
  .hard_atom_timeout_seconds == 600' "$resources" >/dev/null
jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg experiment "$(basename "$run_output")" \
  --arg input "$(sha "$inputs/SHA256SUMS")" \
  --arg run "$(sha "$run_output/run.json")" \
  --arg baseline "$(sha "$run_output/baseline-validation.json")" \
  --arg result "$(sha "$run_output/result.json")" \
  --arg fold "$(sha "$fold")" --arg resume "$(sha "$resume")" \
  --arg cleanup "$(sha "$run_output/tmpfs-cleanup.json")" \
  --arg resources "$(sha "$resources")" \
  --slurpfile folded "$fold" --slurpfile resource "$resources" '
    {schema:"hh-task10-a-final-certificate-v3",status:"complete",
     completed:$completed,experiment:$experiment,
     input_inventory_sha256:$input,run_header_sha256:$run,
     baseline_validation_sha256:$baseline,result_sha256:$result,
     independent_fold_sha256:$fold,exact_resume_sha256:$resume,
     tmpfs_cleanup_sha256:$cleanup,resource_metrics_sha256:$resources,
     canonical_inventory:$folded[0].canonical_inventory,
     historical_first8:{rows_checked:$folded[0].baseline.checked,
       premise_mismatches:$folded[0].baseline.premise,
       request_key_mismatches:$folded[0].baseline.request,
       internal_key_pair_mismatches:$folded[0].baseline.internal,
       prover_spawns:$folded[0].baseline.prover_spawns},
     current:$folded[0].current,
     canonical_sorted_body_sha256:$folded[0].canonical_sorted_body_sha256,
     selected_premise_binding_sha256:
       $folded[0].selected_premise_binding_sha256,
     baseline_model_binding_inventory_sha256:
       $folded[0].baseline_model_binding_inventory_sha256,
     current_model_binding_inventory_sha256:
       $folded[0].current_model_binding_inventory_sha256,
     canonical_rows_byte_identical:true,
     selected_premise_bindings_byte_identical:true,
     models_derived_independently:true,envelope:$resource[0]}' > "$temporary"
mv "$temporary" "$output"
chmod 0444 "$output"
trap - EXIT HUP INT TERM
