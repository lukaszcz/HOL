#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 3 || {
  echo "usage: $0 RUN_OUTPUT IMMUTABLE_INPUTS FOLD_OUTPUT" >&2
  exit 2
}
OUT=$1
INPUTS=$2
FOLD_OUTPUT=$3
INVENTORY="$INPUTS/theory-inventory.tsv"
WORK=$(mktemp -d)
trap 'find "$WORK" -depth -mindepth 1 -delete; rmdir "$WORK"' \
  EXIT HUP INT TERM

: >"$WORK/body.tsv"
: >"$WORK/baseline-bindings.jsonl"
: >"$WORK/current-bindings.jsonl"
: >"$WORK/baseline-models.jsonl"
: >"$WORK/current-models.jsonl"

members=0
expected_goals=0
while IFS=$'\t' read -r theory count rest; do
  baseline="$OUT/baseline/$theory.tsv"
  current="$OUT/current/$theory.tsv"
  test -f "$baseline" -a ! -L "$baseline"
  test -f "$current" -a ! -L "$current"
  tail -n +2 "$baseline" | LC_ALL=C sort >"$WORK/baseline-$theory.rows"
  tail -n +2 "$current" | LC_ALL=C sort >"$WORK/current-$theory.rows"
  cmp -s "$WORK/baseline-$theory.rows" "$WORK/current-$theory.rows"
  for manifest in "$baseline" "$current"; do
    tail -n +2 "$manifest" | awk -F '\t' -v count="$count" '
      NF != 13 || $2 !~ /^[0-9]+$/ || $2 < 1 || $2 > 16 {
        bad=1; next
      }
      { key=$1 SUBSEP $2; if (seen[key]++) bad=1; goals[$1]=1; rows++ }
      END {
        for (goal in goals)
          for (slice=1; slice<=16; slice++)
            if (!seen[goal SUBSEP slice]) bad=1
        if (bad || rows != count*16) exit 1
        n=0; for (goal in goals) n++
        if (n != count) exit 1
      }'
  done
  tail -n +2 "$baseline" >>"$WORK/body.tsv"
  for side in baseline current; do
    header="$OUT/$side/$theory.tsv"
    head -1 "$header" | cut -f2- | jq -cS --arg theory "$theory" '
      .goal_bindings[] |
      [$theory,.goal_id,.goal_sha1,.ancestry_sha1,.fact_inventory_sha1,
       .selected_premise_count,.selected_premises_sha1]' \
      >>"$WORK/$side-bindings.jsonl"
    head -1 "$header" | cut -f2- | jq -cS --arg theory "$theory" '
      [$theory,.model_current_theory,.model_ancestry,.model_feature_rows,
       .model_features_sha1,.model_inventory_sha1,.model_namespace_count,
       .model_weights_sha1]' >>"$WORK/$side-models.jsonl"
  done
  test "$(find "$OUT/current-rankings/$theory" -type f \
    -name '*.ranking' | wc -l)" -eq "$count"
  (cd "$OUT/current-rankings/$theory" && \
    sha256sum -c SHA256SUMS >/dev/null)
  members=$((members+1))
  expected_goals=$((expected_goals+count))
done <"$INVENTORY"

expected_rows=$((expected_goals * 16))
expected_checked=$((expected_goals * 8))
test "$members" -gt 0
test "$expected_goals" -gt 0
LC_ALL=C sort "$WORK/baseline-bindings.jsonl" \
  >"$WORK/baseline-bindings.sorted.jsonl"
LC_ALL=C sort "$WORK/current-bindings.jsonl" \
  >"$WORK/current-bindings.sorted.jsonl"
cmp -s "$WORK/baseline-bindings.sorted.jsonl" \
  "$WORK/current-bindings.sorted.jsonl"
test "$(wc -l <"$WORK/body.tsv")" -eq "$expected_rows"
test "$(awk -F '\t' '!seen[$1]++ {n++} END {print n+0}' \
  "$WORK/body.tsv")" -eq "$expected_goals"

LC_ALL=C sort "$WORK/body.tsv" >"$WORK/body.sorted.tsv"
body_sha=$(sha256sum "$WORK/body.tsv" | awk '{print $1}')
sorted_body_sha=$(sha256sum "$WORK/body.sorted.tsv" | awk '{print $1}')
bindings_sha=$(sha256sum "$WORK/baseline-bindings.sorted.jsonl" |
  awk '{print $1}')
baseline_models_sha=$(sha256sum "$WORK/baseline-models.jsonl" | awk '{print $1}')
current_models_sha=$(sha256sum "$WORK/current-models.jsonl" | awk '{print $1}')

baseline_headers=$(find "$OUT/baseline" -type f -name '*.tsv' -print0 |
  xargs -0 -n1 sed -n '1s/^[^\t]*\t//p' | jq -s '
  {theories:length,goals:map(.goals)|add,rows:map(.row_count)|add,
   checked:map(.task13_rows_checked)|add,
   expected:map(.task13_execution_goals*8)|add,
   premise:map(.task13_premise_mismatches)|add,
   request:map(.task13_request_key_mismatches)|add,
   internal:map(.task13_internal_key_pair_mismatches)|add,
   prover_spawns:map(.prover_spawns)|add,
   chunks:map(.extension_goal_chunks.count)|add}')
current_headers=$(find "$OUT/current" -type f -name '*.tsv' -print0 |
  xargs -0 -n1 sed -n '1s/^[^\t]*\t//p' | jq -s '
  {theories:length,goals:map(.goals)|add,rows:map(.row_count)|add,
   mismatches:map(.mismatches)|add,
   binding_mismatches:map(.binding_mismatches)|add,
   prover_spawns:map(.prover_spawns)|add,
   chunks:map(.extension_goal_chunks.count)|add,
   ranges_valid:map(.goal_range_start==0 and
     .completed_goal_range_start==0 and .goal_range_length==.goals and
     .completed_goal_range_length==.goals)|all}')
jq -e --argjson theories "$members" --argjson goals "$expected_goals" \
  --argjson rows "$expected_rows" --argjson checked "$expected_checked" '
  .theories==$theories and .goals==$goals and .rows==$rows and
  .checked==$checked and .expected==$checked and .premise==0 and
  .request==0 and .internal==0 and .prover_spawns==0 and .chunks > 0' \
  <<<"$baseline_headers" >/dev/null
jq -e --argjson theories "$members" --argjson goals "$expected_goals" \
  --argjson rows "$expected_rows" '
  .theories==$theories and .goals==$goals and .rows==$rows and
  .mismatches==0 and .binding_mismatches==0 and .prover_spawns==0 and
  .chunks > 0 and .ranges_valid' <<<"$current_headers" >/dev/null

checkpoint_chains=$(find "$OUT/current-checkpoint-chains" -type f \
  -name validation.json | wc -l)
checkpoint_receipts=$(find "$OUT/current-checkpoint-chains" -type f \
  -name receipt.json | wc -l)
extension_parts=$(find "$OUT/current-last8-parts" -type f \
  -name 'part-*.tsv' | wc -l)
test "$checkpoint_chains" -eq "$members"
test "$checkpoint_receipts" -eq \
  "$(jq -r '.chunks' <<<"$current_headers")"
test "$extension_parts" -eq "$(jq -r '.chunks' <<<"$current_headers")"
test "$(find "$OUT/current-rankings" -type f \
  -name '*.ranking' | wc -l)" -eq "$expected_goals"
test "$(find "$OUT/mismatch" -type f -size +0c | wc -l)" -eq 0
test "$(find "$OUT" -type f \( -name '*.partial*' -o -name '*.tmp' \) |
  wc -l)" -eq 0
test "$(find "$OUT/checkpoint-failures" -type f 2>/dev/null | wc -l)" -eq 0

jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg input "$(sha256sum "$INPUTS/SHA256SUMS" | awk '{print $1}')" \
  --arg run "$(sha256sum "$OUT/run.json" | awk '{print $1}')" \
  --arg baseline "$(sha256sum "$OUT/baseline-validation.json" | awk '{print $1}')" \
  --arg result "$(sha256sum "$OUT/result.json" | awk '{print $1}')" \
  --arg body "$body_sha" --arg sorted_body "$sorted_body_sha" \
  --arg bindings "$bindings_sha" --arg baseline_models "$baseline_models_sha" \
  --arg current_models "$current_models_sha" \
  --argjson members "$members" --argjson goals "$expected_goals" \
  --argjson rows "$expected_rows" \
  --argjson checkpoint_chains "$checkpoint_chains" \
  --argjson checkpoint_receipts "$checkpoint_receipts" \
  --argjson extension_parts "$extension_parts" \
  --argjson baseline_headers "$baseline_headers" \
  --argjson current_headers "$current_headers" '
  {schema:"hh-task10-a-independent-fold-v2",status:"complete",
   completed:$completed,input_inventory_sha256:$input,run_header_sha256:$run,
   baseline_validation_sha256:$baseline,result_sha256:$result,
   canonical_inventory:{members:$members,goals:$goals,slices:16,rows:$rows,
     checkpoint_chains:$checkpoint_chains,
     checkpoint_receipts:$checkpoint_receipts,
     extension_parts:$extension_parts,ranking_journals:$goals},
   baseline:$baseline_headers,current:$current_headers,
   baseline_current_canonical_rows_byte_identical:true,
   baseline_inventory_order_body_sha256:$body,
   canonical_sorted_body_sha256:$sorted_body,
   selected_premise_binding_sha256:$bindings,
   baseline_model_binding_inventory_sha256:$baseline_models,
   current_model_binding_inventory_sha256:$current_models,
   selected_premise_bindings_byte_identical:true,
   provenance_bound_ranges_valid:true,partials:0,failure_archives:0,
   nonempty_mismatch_journals:0}' > "$FOLD_OUTPUT"
chmod 0444 "$FOLD_OUTPUT"
