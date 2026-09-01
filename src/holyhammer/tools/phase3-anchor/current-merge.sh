#!/bin/sh
set -eu

test "$#" -eq 5 || {
  echo "usage: $0 FIRST8 LAST8 BASELINE OUTPUT RANKING_INVENTORY_SHA256" >&2
  exit 2
}
first=$1
last=$2
baseline=$3
output=$4
ranking_inventory_sha=$5
case "$ranking_inventory_sha" in *[!0-9a-f]* | "") exit 2 ;; esac
test "${#ranking_inventory_sha}" -eq 64

header () {
  awk -F "$(printf '\t')" 'NR == 1 {$1 = ""; sub(/^\t/, ""); print}' \
    OFS="$(printf '\t')" "$1"
}

first_header=$(header "$first")
last_header=$(header "$last")
baseline_sha=$(sha256sum "$baseline" | awk '{print $1}')
first_sha=$(sha256sum "$first" | awk '{print $1}')
last_sha=$(sha256sum "$last" | awk '{print $1}')

for value in "$first_header" "$last_header"
do
  printf '%s\n' "$value" | jq -e \
    --arg baseline "$baseline_sha" '
      .schema == "hh-anchor-current-v1" and
      .goal_digest_schema == "hh-goal-struct-v1" and
      .baseline_manifest_sha256 == $baseline and
      .mismatches == 0 and .binding_mismatches == 0 and
      .prover_spawns == 0 and .model_namespace_count == 0 and
      (.model_inventory_sha1 | test("^[0-9a-f]{40}$")) and
      (.model_features_sha1 | test("^[0-9a-f]{40}$")) and
      (.model_weights_sha1 | test("^[0-9a-f]{40}$")) and
      (.goal_bindings | length) == .goals
    ' >/dev/null
done
printf '%s\n' "$last_header" | jq -e '
  .goal_chunk_schema == "hh-profile-goal-chunks-v1" and
  .goal_chunk_policy_version == "hh-current-goal-bisect-v1" and
  .goal_chunk_count >= 1 and .goal_chunk_max_goals >= 1 and
  (.goal_chunk_range_inventory_sha256 | length) == 64 and
  (.goal_chunk_inventory_sha256 | length) == 64 and
  (.goal_chunk_rows_sha256 | length) == 64
' >/dev/null
printf '%s\n' "$first_header" | jq -e '
  .goal_chunk_schema == "hh-profile-goal-chunks-v1" and
  .goal_chunk_policy_version == "hh-current-goal-bisect-v1" and
  .goal_chunk_count >= 1 and .goal_chunk_max_goals >= 1 and
  (.goal_chunk_range_inventory_sha256 | length) == 64 and
  (.goal_chunk_inventory_sha256 | length) == 64 and
  (.goal_chunk_rows_sha256 | length) == 64 and
  .checkpoint_chain_schema == "hh-current-db-checkpoint-chain-v1" and
  .checkpoint_chain_policy_version ==
    "hh-current-db-soft420-hard600-prune-v2" and
  .checkpoint_storage_policy_version ==
    "hh-current-checkpoint-prune-v1" and
  .checkpoint_atom_headroom_kib == 786432 and
  .checkpoint_heavy_hol_reservation_policy_version ==
    "hh-current-heavy-hol-flock-v2" and
  .checkpoint_heavy_hol_reservation_maximum_concurrent_atoms == 8 and
  .checkpoint_chain_atoms >= 1 and
  (.checkpoint_chain_validation_sha256 | length) == 64 and
  (.checkpoint_chain_inventory_sha256 | length) == 64
' >/dev/null

first_common=$(printf '%s\n' "$first_header" | jq -S -c \
  '.goal_bindings |= sort_by(.goal_id) |
   del(.profile_start,.profile_length,.replay_theory,.profile_set_sha1,
       .row_set_sha1,.row_count)')
last_common=$(printf '%s\n' "$last_header" | jq -S -c \
  '.goal_bindings |= sort_by(.goal_id) |
   del(.profile_start,.profile_length,.replay_theory,.profile_set_sha1,
       .row_set_sha1,.row_count)')
first_common=$(printf '%s\n' "$first_common" | jq -S -c '
  del(.goal_chunk_schema,.goal_chunk_count,.goal_chunk_max_goals,
      .goal_chunk_policy_version,.goal_chunk_range_inventory_sha256,
      .goal_chunk_inventory_sha256,.goal_chunk_rows_sha256,
      .completed_goal_range_start,.completed_goal_range_length,
      .checkpoint_chain_schema,.checkpoint_chain_policy_version,
      .checkpoint_chain_validation_sha256,
      .checkpoint_chain_inventory_sha256,.checkpoint_chain_atoms,
      .checkpoint_storage_policy_version,
      .checkpoint_atom_headroom_kib,
      .checkpoint_heavy_hol_reservation_policy_version,
      .checkpoint_heavy_hol_reservation_maximum_concurrent_atoms,
      .export_model_feature_rows,.export_model_inventory_sha1,
      .export_model_features_sha1,.export_model_weights_sha1,
      .export_model_current_theory,.export_model_ancestry,
      .export_model_namespace_count,.export_target_model_features_sha1)')
last_common=$(printf '%s\n' "$last_common" | jq -S -c '
  del(.goal_chunk_schema,.goal_chunk_count,.goal_chunk_max_goals,
      .goal_chunk_policy_version,.goal_chunk_range_inventory_sha256,
      .goal_chunk_inventory_sha256,.goal_chunk_rows_sha256,
      .completed_goal_range_start,.completed_goal_range_length,
      .checkpoint_chain_schema,.checkpoint_chain_policy_version,
      .checkpoint_chain_validation_sha256,
      .checkpoint_chain_inventory_sha256,.checkpoint_chain_atoms,
      .checkpoint_heavy_hol_reservation_policy_version,
      .checkpoint_heavy_hol_reservation_maximum_concurrent_atoms,
      .export_model_feature_rows,.export_model_inventory_sha1,
      .export_model_features_sha1,.export_model_weights_sha1,
      .export_model_current_theory,.export_model_ancestry,
      .export_model_namespace_count,.export_target_model_features_sha1)')
test "$first_common" = "$last_common"
printf '%s\n' "$first_header" | jq -e '
  .profile_start == 0 and .profile_length == 8 and
  .replay_theory == true and .row_count == 8 * .goals and
  .completed_goal_range_start == 0 and
  .completed_goal_range_length == .goals
' >/dev/null
printf '%s\n' "$last_header" | jq -e '
  .profile_start == 8 and .profile_length == 8 and
  .replay_theory == false and .row_count == 8 * .goals and
  .completed_goal_range_start == 0 and
  .completed_goal_range_length == .goals
' >/dev/null

rows="$output.rows.partial.$$"
tail -n +2 "$first" >"$rows"
tail -n +2 "$last" >>"$rows"
awk -F '\t' '
  {
    key = $1 SUBSEP $2
    if ($1 == "" || $2 !~ /^[0-9]+$/ || $2 < 1 || $2 > 16 || seen[key]++)
      bad = 1
    if (!goals[$1]++) goal_count++
    rows++
  }
  END {
    for (goal in goals)
      for (slice = 1; slice <= 16; slice++)
        if (!seen[goal SUBSEP slice]) bad = 1
    if (bad || rows != 16 * goal_count) exit 1
  }
' "$rows"

baseline_rows="$output.baseline.partial.$$"
tail -n +2 "$baseline" | LC_ALL=C sort -t "$(printf '\t')" -k1,1 -k2,2n \
  >"$baseline_rows"
LC_ALL=C sort -t "$(printf '\t')" -k1,1 -k2,2n "$rows" \
  >"$rows.sorted"
cmp -s "$baseline_rows" "$rows.sorted"

row_set_sha=$(sha256sum "$rows.sorted" | awk '{print $1}')
extension_model=$(printf '%s\n' "$last_header" | jq -c '
  {feature_rows:.export_model_feature_rows,
   inventory_sha1:.export_model_inventory_sha1,
   features_sha1:.export_model_features_sha1,
   weights_sha1:.export_model_weights_sha1}')
first_chunks=$(printf '%s\n' "$first_header" | jq -c '
  {schema:.goal_chunk_schema,count:.goal_chunk_count,
   policy_version:.goal_chunk_policy_version,
   max_goals:.goal_chunk_max_goals,
   range_inventory_sha256:.goal_chunk_range_inventory_sha256,
   inventory_sha256:.goal_chunk_inventory_sha256,
   rows_sha256:.goal_chunk_rows_sha256}')
merged_header=$(printf '%s\n' "$first_header" | jq -c \
  --arg first "$first_sha" --arg last "$last_sha" \
  --arg rows "$row_set_sha" --argjson chunks "$(printf '%s\n' \
    "$last_header" | jq -c '{schema:.goal_chunk_schema,
      count:.goal_chunk_count,policy_version:.goal_chunk_policy_version,
      max_goals:.goal_chunk_max_goals,
      range_inventory_sha256:.goal_chunk_range_inventory_sha256,
      inventory_sha256:.goal_chunk_inventory_sha256,
      rows_sha256:.goal_chunk_rows_sha256}')" \
  --argjson extension_model "$extension_model" \
  --argjson first_chunks "$first_chunks" \
  --arg ranking_inventory "$ranking_inventory_sha" '
    .goal_bindings |= sort_by(.goal_id) |
    .schema = "hh-anchor-current-merged-v1" |
    .profile_start = 0 | .profile_length = 16 |
    .replay_theory = true | .row_count = 16 * .goals |
    .profile_set_sha1 = "dd90fee8ca476562d146037768de2f129dd408c1" |
    del(.row_set_sha1) |
    .first8_sha256 = $first | .last8_sha256 = $last |
    .row_inventory_sha256 = $rows | .extension_goal_chunks = $chunks |
    .derivation_goal_chunks = $first_chunks |
    .extension_export_model = $extension_model |
    .ranking_inventory_sha256 = $ranking_inventory
  ')
{
  printf '#hh-anchor-current-merged-v1\t%s\n' "$merged_header"
  cat "$rows.sorted"
} >"$output.partial.$$"
mv "$output.partial.$$" "$output"
rm -f "$rows" "$rows.sorted" "$baseline_rows"
