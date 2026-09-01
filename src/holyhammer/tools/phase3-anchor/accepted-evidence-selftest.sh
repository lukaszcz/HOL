#!/bin/bash
set -Eeuo pipefail

tools=$(cd "$(dirname "$0")" && pwd)
preflight=$(cd "$tools/../phase3-preflight" && pwd)
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM

"$preflight/verify-focused-gates-selftest.sh" \
  "$preflight/verify-focused-gates.sh" >/dev/null
"$tools/verify-integration-gate-selftest.sh" \
  "$tools/verify-integration-gate.sh" >/dev/null
"$tools/resume-certificate-selftest.sh" \
  "$tools/resume-certificate.sh" >/dev/null

inputs=$work/accepted-inputs
challenger=$work/challenger-inputs
output=$work/accepted-evidence
mkdir -p "$inputs" "$output/baseline" "$output/current" \
  "$output/current-first8" \
  "$output/current-rankings/tiny" \
  "$output/current-checkpoint-chains/tiny/atom-000000" \
  "$output/current-last8-parts/tiny" "$output/mismatch" \
  "$output/checkpoint-failures"
printf 'tiny\t1\n' >"$inputs/theory-inventory.tsv"

runner=$inputs/run-a.sh
cat >"$runner" <<'EOF'
#!/bin/sh
if test "${1-}" = VERIFY_INPUTS; then exit 0; fi
echo 'task10 tuple mismatch: sealed input does not match accepted run header' >&2
exit 78
EOF
chmod 0555 "$runner"
runner_sha=$(sha256sum "$runner" | awk '{print $1}')
printf 'run-a.sh\tphase3-anchor/run-a.sh\t%s\n' "$runner_sha" \
  >"$inputs/runtime-origin.tsv"
jq -n --arg runner "$runner_sha" '
  {schema:"hh-task10-a-run-v13",status:"scheduled",run:"A",
   revision:"accepted-evidence-selftest",prover_free:true,
   corpus:{theories:1,nonempty_theories:1,goals:1,slices:16,
     rows_per_side:16},
   runtime_tools:{schema:"hh-task10-runtime-tools-v2",
     origin_inventory_sha256:"selftest",
     files:{"run-a.sh":{tracked_source:"phase3-anchor/run-a.sh",
       sha256:$runner}}}}
' >"$inputs/top-provenance.json"
(cd "$inputs" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum >SHA256SUMS)

binding='[{"goal_id":"tiny.g","goal_sha1":"goal","ancestry_sha1":'
binding+='"ancestry","fact_inventory_sha1":"facts",'
binding+='"selected_premise_count":1,"selected_premises_sha1":"premises"}]'
baseline_header=$(jq -nc --argjson bindings "$binding" '
  {goals:1,row_count:16,task13_rows_checked:8,
   task13_execution_goals:1,task13_premise_mismatches:0,
   task13_request_key_mismatches:0,task13_internal_key_pair_mismatches:0,
   prover_spawns:0,extension_goal_chunks:{count:1},goal_bindings:$bindings,
   model_current_theory:"tiny",model_ancestry:["tiny"],
   model_feature_rows:1,model_features_sha1:"features",
   model_inventory_sha1:"inventory",model_namespace_count:1,
   model_weights_sha1:"weights"}
')
current_header=$(jq -nc --argjson bindings "$binding" '
  {goals:1,row_count:16,mismatches:0,binding_mismatches:0,
   prover_spawns:0,extension_goal_chunks:{count:1},goal_range_start:0,
   completed_goal_range_start:0,goal_range_length:1,
   completed_goal_range_length:1,goal_bindings:$bindings,
   model_current_theory:"tiny",model_ancestry:["tiny"],
   model_feature_rows:1,model_features_sha1:"current-features",
   model_inventory_sha1:"current-inventory",model_namespace_count:1,
   model_weights_sha1:"current-weights"}
')
printf '#\t%s\n' "$baseline_header" >"$output/baseline/tiny.tsv"
printf '#\t%s\n' "$current_header" >"$output/current/tiny.tsv"
for slice in $(seq 1 16); do
  printf 'tiny.g\t%s\ta\tb\tc\td\te\tf\tg\th\ti\tj\tk\n' "$slice"
done | tee -a "$output/baseline/tiny.tsv" \
  >>"$output/current/tiny.tsv"
head -9 "$output/current/tiny.tsv" >"$output/current-first8/tiny.tsv"
printf '%s\n' ranking >"$output/current-rankings/tiny/tiny.ranking"
(cd "$output/current-rankings/tiny" && \
  sha256sum tiny.ranking >SHA256SUMS)
printf '%s\n' '{"status":"complete"}' \
  >"$output/current-checkpoint-chains/tiny/validation.json"
printf '%s\n' '{"status":"complete"}' \
  >"$output/current-checkpoint-chains/tiny/atom-000000/receipt.json"
printf '%s\n' part \
  >"$output/current-last8-parts/tiny/part-000000.tsv"

cp "$inputs/top-provenance.json" "$output/run.json"
jq -n '
  {status:"complete",counters:{premise:0,request:0,internal:0,
    prover_spawns:0}}
' >"$output/baseline-validation.json"
jq -n '
  {status:"complete",counters:{theories:1,goals:1,rows:16,mismatches:0,
    binding_mismatches:0,prover_spawns:0,ranking_journals:1}}
' >"$output/result.json"
printf '%s\n' '{"event":"complete"}' >"$output/invocations.jsonl"
printf '%s\n' durable-copyback result-validation tmpfs-removal \
  >"$work/teardown-order"
jq -n '
  {schema:"hh-task10-tmpfs-cleanup-v1",status:"removed",state_files:0,
   state_symlinks:0,tmpfs_root_absent_after_cleanup:true}
' >"$output/tmpfs-cleanup.json"
"$tools/first8-equivalence-certificate.sh" "$output" \
  "$work/first8.json"
"$tools/smoke-negative-certificate.sh" "$PWD" "$output" "$inputs" \
  "$runner" stale-runtime "$work/stale.json"
"$tools/smoke-negative-certificate.sh" "$PWD" "$output" "$inputs" \
  "$runner" corrupt-checkpoint "$work/corrupt.json"

"$tools/independent-fold.sh" "$output" "$inputs" "$work/fold.json"
printf '%s\n' independent-fold >>"$work/teardown-order"
jq -n '
  {status:"complete",durable_only:true,
   tmpfs_absent_before_and_after:true,
   immutable_results_byte_identical:true}
' >"$work/resume.json"
jq -n '
  {scheduler_workers:16,cpu_quota_cores:32,
   memory_high_bytes:133143986176,memory_max_bytes:137438953472,
   memory_swap_max_bytes:0,hard_atom_timeout_seconds:600}
' >"$work/resources.json"
"$tools/final-run-certificate.sh" "$output" "$inputs" \
  "$work/fold.json" "$work/resume.json" "$work/resources.json" \
  "$output/final-certificate.json"
printf '%s\n' final-run-certificate >>"$work/teardown-order"

cp -a "$inputs" "$challenger"
chmod u+w "$challenger/top-provenance.json" "$challenger/SHA256SUMS"
jq '.revision = "accepted-evidence-challenger"' \
  "$challenger/top-provenance.json" >"$work/challenger.json"
mv "$work/challenger.json" "$challenger/top-provenance.json"
(cd "$challenger" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum >SHA256SUMS)
"$tools/cross-tuple-certificate.sh" "$output" "$inputs" \
  "$challenger" "$runner" "$work/cross.json"
"$tools/final-acceptance-certificate.sh" \
  "$output/final-certificate.json" "$work/cross.json" \
  "$work/final-acceptance.json"
printf '%s\n' cross-tuple final-acceptance >>"$work/teardown-order"

cmp -s "$work/teardown-order" <(printf '%s\n' durable-copyback \
  result-validation tmpfs-removal independent-fold final-run-certificate \
  cross-tuple final-acceptance)
jq -e '.schema == "hh-task10-final-acceptance-v2" and
  .status == "complete" and .final_certificate_cross_binding_verified' \
  "$work/final-acceptance.json" >/dev/null
echo "accepted evidence end-to-end selftest: passed"
