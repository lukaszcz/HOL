#!/bin/sh
set -eu

test "$#" -eq 3 || {
  echo "usage: $0 RUN_FINAL_CERT CROSS_TUPLE_CERT OUTPUT" >&2
  exit 2
}
run=$1
cross=$2
output=$3
temporary=$output.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM
sha () { sha256sum "$1" | awk '{print $1}'; }
test -s "$run" && test ! -L "$run"
test -s "$cross" && test ! -L "$cross"
run_sha=$(sha "$run")
cross_sha=$(sha "$cross")

jq -e '
  .schema == "hh-task10-a-final-certificate-v3" and
  .status == "complete" and
  (keys == ["baseline_model_binding_inventory_sha256",
    "baseline_validation_sha256","canonical_inventory",
    "canonical_rows_byte_identical","canonical_sorted_body_sha256",
    "completed","current","current_model_binding_inventory_sha256",
    "envelope","exact_resume_sha256","experiment",
    "historical_first8","independent_fold_sha256",
    "input_inventory_sha256","models_derived_independently",
    "resource_metrics_sha256","result_sha256","run_header_sha256",
    "schema","selected_premise_binding_sha256",
    "selected_premise_bindings_byte_identical","status",
    "tmpfs_cleanup_sha256"]) and
  ([.experiment,.input_inventory_sha256,.run_header_sha256,
    .baseline_validation_sha256,.result_sha256,
    .independent_fold_sha256,.exact_resume_sha256,
    .tmpfs_cleanup_sha256,.resource_metrics_sha256] |
    all(type == "string" and length > 0))
' "$run" >/dev/null
jq -e '
  .schema == "hh-task10-cross-tuple-certificate-v2" and
  .status == "rejected" and .exit_status == 78 and
  .accepted_seal_verified == true and
  .challenger_seal_verified == true and .tuples_distinct == true and
  .before_after_identical == true and
  .invocation_and_state_unchanged == true and
  (keys == ["accepted","accepted_seal_verified",
    "before_after_identical","challenger","challenger_seal_verified",
    "command","command_sha256","completed","exit_status",
    "expected_diagnostic","experiment","invocation_and_state_unchanged",
    "runner_sha256","schema","status","stderr_sha256","stdout_sha256",
    "tuples_distinct","verifier_sha256"]) and
  (.accepted | keys == ["bytes","directory_tree_sha256",
    "files","final_certificate_sha256","input_inventory_sha256",
    "invocation_log_sha256","result_sha256","run_header_sha256",
    "state_tree_sha256","tuple_header_sha256"]) and
  (.challenger | keys == ["input_inventory_sha256",
    "tuple_header_sha256"])
' "$cross" >/dev/null

test "$(jq -r '.experiment' "$run")" = "$(jq -r '.experiment' "$cross")"
test "$(jq -r '.input_inventory_sha256' "$run")" = \
  "$(jq -r '.accepted.input_inventory_sha256' "$cross")"
test "$(jq -r '.run_header_sha256' "$run")" = \
  "$(jq -r '.accepted.run_header_sha256' "$cross")"
test "$(jq -r '.result_sha256' "$run")" = \
  "$(jq -r '.accepted.result_sha256' "$cross")"
test "$(jq -r '.accepted.final_certificate_sha256' "$cross")" = \
  "$run_sha"
test "$(jq -r '.accepted.input_inventory_sha256' "$cross")" != \
  "$(jq -r '.challenger.input_inventory_sha256' "$cross")"
test "$(jq -r '.accepted.tuple_header_sha256' "$cross")" != \
  "$(jq -r '.challenger.tuple_header_sha256' "$cross")"

jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg experiment "$(jq -r '.experiment' "$run")" \
  --arg run "$run_sha" --arg cross "$cross_sha" \
  --arg input "$(jq -r '.input_inventory_sha256' "$run")" \
  --arg header "$(jq -r '.run_header_sha256' "$run")" \
  --arg result "$(jq -r '.result_sha256' "$run")" '
    {schema:"hh-task10-final-acceptance-v2",status:"complete",
     completed:$completed,experiment:$experiment,
     input_inventory_sha256:$input,run_header_sha256:$header,
     result_sha256:$result,run_final_certificate_sha256:$run,
     cross_tuple_certificate_sha256:$cross,
     final_certificate_cross_binding_verified:true}' >"$temporary"
mv "$temporary" "$output"
chmod 0444 "$output"
trap - EXIT HUP INT TERM
