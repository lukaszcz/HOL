#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 3 || {
  echo "usage: $0 FINAL_RUN_TOOL CROSS_TUPLE_TOOL FINAL_ACCEPTANCE_TOOL" >&2
  exit 2
}
run_tool=$1
cross_tool=$2
final_tool=$3
test -x "$run_tool" && test -x "$cross_tool" && test -x "$final_tool"
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM

sha () { sha256sum "$1" | awk '{print $1}'; }

seal_tuple () {
  local tuple=$1
  (cd "$tuple" && find . -type f ! -name SHA256SUMS -print0 |
    LC_ALL=C sort -z | xargs -0 sha256sum >SHA256SUMS)
}

make_runner () {
  local runner=$1 status=$2 diagnostic=$3
  apply_body='#!/bin/sh
if test "${1-}" = VERIFY_INPUTS; then exit 0; fi
printf "%s\\n" "$TASK10_DIAGNOSTIC" >&2
exit "$TASK10_STATUS"'
  printf '%s\n' "$apply_body" >"$runner"
  sed -i "s/\$TASK10_STATUS/$status/; s/\$TASK10_DIAGNOSTIC/$diagnostic/" \
    "$runner"
  chmod 0555 "$runner"
}

make_tuple () {
  local tuple=$1 revision=$2 runner=$3 runner_sha
  mkdir -p "$tuple"
  cp "$runner" "$tuple/run-a.sh"
  runner_sha=$(sha "$tuple/run-a.sh")
  printf 'run-a.sh\tphase3-anchor/run-a.sh\t%s\n' "$runner_sha" \
    >"$tuple/runtime-origin.tsv"
  jq -n --arg revision "$revision" --arg runner "$runner_sha" '
    {schema:"hh-task10-a-run-v13",status:"scheduled",run:"A",
     revision:$revision,prover_free:true,
     corpus:{theories:253,nonempty_theories:229,goals:24721,slices:16,
       rows_per_side:395536},
     runtime_tools:{schema:"hh-task10-runtime-tools-v2",
       origin_inventory_sha256:"test",
       files:{"run-a.sh":{tracked_source:"phase3-anchor/run-a.sh",
         sha256:$runner}}}}
  ' >"$tuple/top-provenance.json"
  seal_tuple "$tuple"
}

make_fold () {
  local output=$1
  jq -n '
    {schema:"hh-task10-a-independent-fold-v2",status:"complete",
     completed:"test",input_inventory_sha256:"input",
     run_header_sha256:"run",baseline_validation_sha256:"baseline",
     result_sha256:"result",
     canonical_inventory:{members:229,goals:24721,slices:16,rows:395536,
       checkpoint_chains:229,checkpoint_receipts:348,extension_parts:348,
       ranking_journals:24721},
     baseline:{theories:229,goals:24721,rows:395536,checked:197768,
       expected:197768,premise:0,request:0,internal:0,prover_spawns:0,
       chunks:348},
     current:{theories:229,goals:24721,rows:395536,mismatches:0,
       binding_mismatches:0,prover_spawns:0,chunks:348,ranges_valid:true},
     baseline_current_canonical_rows_byte_identical:true,
     baseline_inventory_order_body_sha256:"inventory-body",
     canonical_sorted_body_sha256:"body",
     selected_premise_binding_sha256:"premises",
     baseline_model_binding_inventory_sha256:"baseline-model",
     current_model_binding_inventory_sha256:"current-model",
     selected_premise_bindings_byte_identical:true,
     provenance_bound_ranges_valid:true,partials:0,failure_archives:0,
     nonempty_mismatch_journals:0}
  ' >"$output"
}

make_accepted () {
  local accepted=$1 inputs=$2
  mkdir -p "$accepted"
  cp "$inputs/top-provenance.json" "$accepted/run.json"
  printf '%s\n' '{"status":"complete"}' >"$accepted/result.json"
  printf '%s\n' '{"status":"complete"}' \
    >"$accepted/baseline-validation.json"
  printf '%s\n' '{"event":"complete"}' >"$accepted/invocations.jsonl"
  jq -n '
    {schema:"hh-task10-tmpfs-cleanup-v1",status:"removed",state_files:0,
     state_symlinks:0,tmpfs_root_absent_after_cleanup:true}
  ' >"$accepted/tmpfs-cleanup.json"
  "$run_tool" "$accepted" "$inputs" "$work/fold.json" \
    "$work/resume.json" "$work/resources.json" \
    "$accepted/final-certificate.json"
}

reject_cross () {
  local name=$1 accepted=$2 inputs=$3 challenger=$4 runner=$5
  if "$cross_tool" "$accepted" "$inputs" "$challenger" "$runner" \
      "$work/cross-$name.json"; then
    echo "cross-tuple tool accepted invalid case: $name" >&2
    exit 1
  fi
  test ! -e "$work/cross-$name.json"
}

good_runner=$work/good-runner
wrong_runner=$work/wrong-runner
unrelated_runner=$work/unrelated-runner
diagnostic='task10 tuple mismatch: sealed input does not match accepted run header'
make_runner "$good_runner" 78 "$diagnostic"
make_runner "$wrong_runner" 78 'wrong diagnostic'
make_runner "$unrelated_runner" 1 "$diagnostic"
accepted_inputs=$work/accepted-inputs
challenger_inputs=$work/challenger-inputs
make_tuple "$accepted_inputs" accepted "$good_runner"
make_tuple "$challenger_inputs" challenger "$good_runner"

make_fold "$work/fold.json"
jq -n \
  '{status:"complete",durable_only:true,
    tmpfs_absent_before_and_after:true,
    immutable_results_byte_identical:true}' >"$work/resume.json"
jq -n \
  '{scheduler_workers:16,cpu_quota_cores:32,
    memory_high_bytes:133143986176,memory_max_bytes:137438953472,
    memory_swap_max_bytes:0,hard_atom_timeout_seconds:600}' \
  >"$work/resources.json"
accepted=$work/certificate-selftest
make_accepted "$accepted" "$accepted_inputs"

reject_fold () {
  local name=$1 filter=$2
  jq "$filter" "$work/fold.json" >"$work/fold-$name.json"
  if "$run_tool" "$accepted" "$accepted_inputs" \
      "$work/fold-$name.json" "$work/resume.json" \
      "$work/resources.json" "$work/final-$name.json"; then
    echo "final fold accepted invalid schema: $name" >&2
    exit 1
  fi
  test ! -e "$work/final-$name.json"
}
reject_fold missing-current-spawns 'del(.current.prover_spawns)'
reject_fold unknown-current-field '.current.unknown = 0'
reject_fold missing-top-field 'del(.selected_premise_binding_sha256)'
reject_fold unknown-top-field '.unknown = 0'
reject_fold wrong-current-type '.current.prover_spawns = "0"'
reject_fold legacy-current-spawns \
  '.current.spawns = .current.prover_spawns | del(.current.prover_spawns)'
reject_fold legacy-baseline-spawns \
  '.baseline.spawns = .baseline.prover_spawns |
   del(.baseline.prover_spawns)'

before=$(sha "$accepted/invocations.jsonl")
"$cross_tool" "$accepted" "$accepted_inputs" "$challenger_inputs" \
  "$good_runner" "$work/cross.json"
after=$(sha "$accepted/invocations.jsonl")
test "$before" = "$after"
jq -e '
  .schema == "hh-task10-cross-tuple-certificate-v2" and
  .status == "rejected" and .exit_status == 78 and
  .accepted_seal_verified and .challenger_seal_verified and
  .tuples_distinct and .before_after_identical and
  .invocation_and_state_unchanged and
  (.stdout_sha256 | length) == 64 and (.stderr_sha256 | length) == 64
' "$work/cross.json" >/dev/null

missing=$work/missing-challenger
cp -a "$challenger_inputs" "$missing"
rm "$missing/top-provenance.json"
reject_cross missing "$accepted" "$accepted_inputs" "$missing" \
  "$good_runner"
corrupt=$work/corrupt-challenger
cp -a "$challenger_inputs" "$corrupt"
printf '%s\n' corrupt >>"$corrupt/top-provenance.json"
reject_cross corrupt "$accepted" "$accepted_inputs" "$corrupt" \
  "$good_runner"
reject_cross same-tuple "$accepted" "$accepted_inputs" "$accepted_inputs" \
  "$good_runner"

wrong_a=$work/wrong-a
wrong_c=$work/wrong-c
wrong_out=$work/wrong-out
make_tuple "$wrong_a" accepted "$wrong_runner"
make_tuple "$wrong_c" challenger "$wrong_runner"
make_accepted "$wrong_out" "$wrong_a"
reject_cross wrong-diagnostic "$wrong_out" "$wrong_a" "$wrong_c" \
  "$wrong_runner"
unrelated_a=$work/unrelated-a
unrelated_c=$work/unrelated-c
unrelated_out=$work/unrelated-out
make_tuple "$unrelated_a" accepted "$unrelated_runner"
make_tuple "$unrelated_c" challenger "$unrelated_runner"
make_accepted "$unrelated_out" "$unrelated_a"
reject_cross unrelated-nonzero "$unrelated_out" "$unrelated_a" \
  "$unrelated_c" "$unrelated_runner"

"$final_tool" "$accepted/final-certificate.json" "$work/cross.json" \
  "$work/acceptance.json"
jq -e '
  .schema == "hh-task10-final-acceptance-v2" and
  .status == "complete" and .experiment == "certificate-selftest" and
  .final_certificate_cross_binding_verified == true
' "$work/acceptance.json" >/dev/null

jq '.accepted.final_certificate_sha256 = "wrong"' "$work/cross.json" \
  >"$work/cross-wrong-final.json"
if "$final_tool" "$accepted/final-certificate.json" \
    "$work/cross-wrong-final.json" "$work/invalid-acceptance.json"; then
  echo "final acceptance accepted a broken final-certificate chain" >&2
  exit 1
fi
test ! -e "$work/invalid-acceptance.json"
echo "cross-tuple and final certificate selftest: passed"
