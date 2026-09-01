#!/bin/bash
set -Eeuo pipefail

INPUTS=${1:?input directory required}
EXP=${2:?experiment name required}
THEORY=ASCIInumbers
COUNT=35
export HHEVAL_TASK10_A_INPUTS=$INPUTS
export HHEVAL_TASK10_A_EXP=$EXP
export HHEVAL_TASK10_RUNNER_LIBRARY_ONLY=1
export HHEVAL_TASK10_STORAGE_REFRESH=1
source "$INPUTS/run-a.sh"
test "$HHEVAL_TASK10_A_INPUTS" = "$INPUTS"
case "$INPUTS" in /*) ;; *) exit 2 ;; esac

verify_inputs
verify_live_execution_envelope
verify_worker_export_boundary
unset HHEVAL_TASK10_STORAGE_REFRESH

copy_tree_once () {
  local source=$1 destination=$2
  if test -e "$destination"; then
    test -d "$destination" && test ! -L "$destination"
    diff -qr "$source" "$destination" >/dev/null
  else
    cp -a "$source" "$destination"
  fi
}

inventory_tree () {
  local directory=$1 output=$2
  test -d "$directory" && test ! -L "$directory"
  (cd "$directory" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum) >"$output"
  test -s "$output"
  (cd "$directory" && sha256sum -c "$output" >/dev/null)
}

initialize
make_invocation "$THEORY" "$COUNT"
baseline_theory_once "$THEORY" "$COUNT"
test "$(wc -l <"$OUT/baseline/$THEORY.tsv")" -eq 561
head -1 "$OUT/baseline/$THEORY.tsv" | cut -f2- | jq -e '
  .task13_premise_mismatches == 0 and
  .task13_request_key_mismatches == 0 and
  .task13_internal_key_pair_mismatches == 0 and .prover_spawns == 0' \
  >/dev/null

export HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE="$OUT/checkpoint-monolithic"
CHECKPOINT_MAX_GOALS=128
export CHECKPOINT_MAX_GOALS
current_checkpoint_chain "$THEORY" "$COUNT" "$OUT/monolithic-first8.tsv"
copy_tree_once "$OUT/current-rankings/$THEORY" "$OUT/monolithic-rankings"
test ! -e "$STATE/current-checkpoint/$THEORY"

unset HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE
CHECKPOINT_MAX_GOALS=10
export CHECKPOINT_MAX_GOALS
current_checkpoint_chain "$THEORY" "$COUNT" \
  "$OUT/current-first8/$THEORY.tsv"
copy_tree_once "$OUT/current-rankings/$THEORY" "$OUT/checkpoint-rankings"
test ! -e "$STATE/current-checkpoint/$THEORY"

tail -n +2 "$OUT/monolithic-first8.tsv" >"$OUT/monolithic-body.tsv"
tail -n +2 "$OUT/current-first8/$THEORY.tsv" >"$OUT/checkpoint-body.tsv"
cmp -s "$OUT/monolithic-body.tsv" "$OUT/checkpoint-body.tsv"
diff -qr "$OUT/monolithic-rankings" "$OUT/checkpoint-rankings" >/dev/null

# Exercise the extension exporter in one process and across four ordered
# process-reset chunks.  Every goal retains the complete profiles 9--16 batch,
# including the translation-memo-sensitive E/Vampire TH0 pair.
names_file=$(theorem_names_file "$THEORY" "$COUNT")
names=$(paste -sd ' ' "$names_file")
mkdir -p "$OUT/profile-last8-parts"
current_part_once "$THEORY" "$COUNT" 8 \
  "$OUT/profile-last8-whole.tsv" "$OUT/profile-last8-whole.log" \
  "$names" storage-profile-whole "$OUT/profile-last8-whole.mismatch" 0
for ((offset=0; offset<COUNT; offset+=10)); do
  length=10
  if ((offset + length > COUNT)); then length=$((COUNT - offset)); fi
  words=$(sed -n "$((offset + 1)),$((offset + length))p" "$names_file" |
    paste -sd ' ' -)
  part=$(printf '%s/part-%06d.tsv' "$OUT/profile-last8-parts" "$offset")
  current_part_once "$THEORY" "$length" 8 "$part" \
    "${part%.tsv}.log" "$words" "storage-profile-$offset" \
    "${part%.tsv}.mismatch.jsonl" "$offset"
done
mapfile -t profile_parts < <(find "$OUT/profile-last8-parts" -type f \
  -name 'part-*.tsv' | LC_ALL=C sort)
HHEVAL_CHUNK_REQUIRE_LOGS=1 "$PROFILE_CHUNK_MERGE" current "$THEORY" \
  "$names_file" "$OUT/profile-last8-merged.tsv" "${profile_parts[@]}"
tail -n +2 "$OUT/profile-last8-whole.tsv" >"$OUT/profile-whole.rows"
tail -n +2 "$OUT/profile-last8-merged.tsv" >"$OUT/profile-chunks.rows"
tail -n +2 "$OUT/baseline-last8/$THEORY.tsv" >"$OUT/profile-baseline.rows"
cmp -s "$OUT/profile-whole.rows" "$OUT/profile-chunks.rows"
cmp -s "$OUT/profile-baseline.rows" "$OUT/profile-whole.rows"

profile_evidence="$OUT/profile-chunk-evidence"
mkdir -p "$profile_evidence/current-parts"
cp "$OUT/baseline-last8/$THEORY.tsv" \
  "$profile_evidence/baseline-last8.tsv"
cp "$OUT/profile-last8-whole.tsv" "$profile_evidence/current-whole.tsv"
cp "$OUT/profile-last8-merged.tsv" "$profile_evidence/current-merged.tsv"
cp "$OUT/profile-last8-parts"/* "$profile_evidence/current-parts/"
inventory_tree "$profile_evidence" "$OUT/profile-chunk-evidence.sha256"
profile_inventory=$(sha "$OUT/profile-chunk-evidence.sha256")
profile_rows=$(sha "$OUT/profile-whole.rows")
jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg runtime "$CHECKPOINT_RUNTIME_SHA" --arg inventory "$profile_inventory" \
  --arg rows "$profile_rows" '
  {schema:"hh-profile-goal-chunk-equivalence-v2",status:"exact",
   completed:$completed,theory:"ASCIInumbers",goals:35,
   profile_start:8,profile_length:8,chunk_goal_limit:10,chunk_count:4,
   all_eight_profiles_atomic:true,process_reset_between_goal_chunks:true,
   formats_covered:["th0","th1","tx0","tx0-","fof"],
   memo_sensitive_pair:{profiles:[12,13],format:"th0",
     e_mono_instances:128,vampire_mono_instances:256,covered:true},
   rows:280,whole_chunks_byte_identical:true,
   baseline_current_byte_identical:true,nonempty_mismatches:0,
   body_sha256:$rows,checkpoint_runtime_sha256:$runtime,
   evidence_inventory_sha256:$inventory}' \
  >"$OUT/profile-chunk-equivalence.json"

HHEVAL_CURRENT_CHECKPOINT_MAX_GOALS=10 \
HHEVAL_CHECKPOINT_SELFTEST_REQUIRE_MULTI=1 \
HHEVAL_CHECKPOINT_SELFTEST_STATE="$STATE/selftest" \
  "$INPUTS/current-checkpoint-selftest.sh" "$INPUTS" "$EXP" \
  "$THEORY" "$COUNT" >"$OUT/checkpoint-selftest.json"
"$INPUTS/checkpoint-reservation-selftest.sh" "$INPUTS" "$EXP"
jq -e '
  .status == "complete" and .storage_atoms >= 2 and
  .scratch_bounded_after_every_commit and
  .maximum_scratch_kib_after_commit == 0 and
  .completed_chain_scratch_pruned and .headroom_guard_rejected and
  .host_memory_guard_rejected and .large_binding_streamed and
  .large_binding_bytes > 523190 and .large_binding_exact_resume and
  .oom_policy_continue_verified and .killed_atom_status == 137 and
  .killed_atom_retry_status == 76 and
  .killed_atom_parent_survived and .killed_atom_not_accepted and
  .killed_atom_prior_checkpoint_authoritative and
  .killed_atom_retry_accepted and
  .resume_byte_identical and .kill_before_commit_recovered and
  .corrupt_heap_rejected and .corrupt_receipt_rejected and
  .stale_model_rejected and .stale_runtime_rejected and
  .gap_rejected and .overlap_branch_rejected and
  .wrong_db_order_rejected and .baseline_cross_feed_rejected' \
  "$OUT/checkpoint-selftest.json" >/dev/null
jq -e '
  .status == "complete" and .configured_cap == 8 and
  .scheduler_contenders == 16 and .observed_maximum == 8 and
  .all_reservations_released and .advisory_flock and .normal_release and
  .double_cleanup_idempotent and .killed_owner_auto_released and
  .stale_owner_metadata_overwritten and .nested_child_fd_closed' \
  "$OUT/checkpoint-reservation-selftest.json" >/dev/null
test ! -e "$STATE/selftest/cases"
test ! -e "$STATE/selftest/kill-before-commit"

# Retain the exact durable material used by the checkpoint equivalence fold.
# Regenerable heaps and per-atom scratch remain in STATE and are deliberately
# excluded; the chain receipts, validations, rows, and rankings are sufficient
# for independent revalidation.
checkpoint_evidence="$OUT/current-checkpoint-evidence"
mkdir -p "$checkpoint_evidence"
for file in checkpoint-body.tsv monolithic-body.tsv \
  checkpoint-selftest.json checkpoint-reservation-selftest.json run.json
do
  cp "$OUT/$file" "$checkpoint_evidence/$file"
done
for directory in checkpoint-monolithic current-checkpoint-chains \
  checkpoint-rankings monolithic-rankings current-first8
do
  copy_tree_once "$OUT/$directory" "$checkpoint_evidence/$directory"
done
inventory_tree "$checkpoint_evidence" \
  "$OUT/current-checkpoint-evidence.sha256"
checkpoint_inventory=$(sha "$OUT/current-checkpoint-evidence.sha256")

mono_validation=$(sha "$OUT/checkpoint-monolithic/$THEORY/validation.json")
checkpoint_validation=$(sha \
  "$OUT/current-checkpoint-chains/$THEORY/validation.json")
rows_sha=$(sha "$OUT/checkpoint-body.tsv")
rankings_sha=$(cd "$OUT/checkpoint-rankings" && \
  find . -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum | \
  sha256sum | awk '{print $1}')
runtime=$CHECKPOINT_RUNTIME_SHA
jq -n --arg runtime "$runtime" --arg rows "$rows_sha" \
  --arg rankings "$rankings_sha" --arg mono_validation "$mono_validation" \
  --arg checkpoint_validation "$checkpoint_validation" \
  --arg evidence_inventory "$checkpoint_inventory" \
  --arg storage "$CHECKPOINT_STORAGE_POLICY" \
  --arg profile "$(sha "$OUT/profile-chunk-equivalence.json")" \
  --slurpfile selftests "$OUT/checkpoint-selftest.json" \
  --slurpfile reservations "$OUT/checkpoint-reservation-selftest.json" '
  $selftests[0] as $selftest |
  {schema:"hh-current-db-checkpoint-equivalence-v1",status:"exact",
   theory:"ASCIInumbers",goals:35,monolithic_atoms:1,checkpoint_atoms:4,
   all_eight_profiles_atomic:true,db_order_preserved:true,
   rows_byte_identical:true,rankings_byte_identical:true,
   canonical_reorder_byte_identical:true,
   checkpoint_runtime_sha256:$runtime,
   storage_policy_version:$storage,
   monolithic_rows_sha256:$rows,checkpoint_rows_sha256:$rows,
   monolithic_rankings_sha256:$rankings,checkpoint_rankings_sha256:$rankings,
   monolithic_validation_sha256:$mono_validation,
   checkpoint_validation_sha256:$checkpoint_validation,
   evidence_inventory_sha256:$evidence_inventory,
   profile_chunk_equivalence_sha256:$profile,selftest:$selftest,
   reservation_selftest:$reservations[0]}' \
  >"$OUT/equivalence.json"

# This manifest is the stable storage-gate boundary consumed by both the P and
# A provenance builders.  It is emitted only after every durable artifact has
# been copied and independently rehashed.
(cd "$OUT" && sha256sum \
  equivalence.json current-checkpoint-evidence.sha256 \
  profile-chunk-equivalence.json profile-chunk-evidence.sha256 \
  checkpoint-selftest.json checkpoint-reservation-selftest.json) \
  >"$OUT/evidence-SHA256SUMS"
(cd "$OUT" && sha256sum -c evidence-SHA256SUMS >/dev/null)
evidence_binding=$(sha "$OUT/evidence-SHA256SUMS")
if test -e "$STATE"; then
  hh_task10_cleanup_tmpfs "$STATE" "$OUT/tmpfs-cleanup.json" \
    "$evidence_binding"
fi
test ! -e "$STATE"
sha256sum "$OUT/equivalence.json"
