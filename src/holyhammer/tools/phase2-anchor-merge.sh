#!/bin/sh
set -eu

test "$#" -eq 5 || test "$#" -eq 6 || {
  echo "usage: $0 FIRST8 LAST8 OUTPUT INVOCATION_SHA256"\
" EXTENSION_SCHEDULER_SHA256 PREMISE_INVENTORY_SHA256" >&2
  exit 2
}

first=$1
last=$2
output=$3
invocation_sha=$4
extension_scheduler_sha=$5
premise_inventory_sha=${6-}
profile_sha=dd90fee8ca476562d146037768de2f129dd408c1

case "$invocation_sha" in
  *[!0-9a-f]* | "")
    echo "invalid merge invocation SHA-256" >&2
    exit 2
    ;;
esac
test "${#invocation_sha}" -eq 64 || {
  echo "invalid merge invocation SHA-256 length" >&2
  exit 2
}
case "$extension_scheduler_sha" in
  *[!0-9a-f]* | "")
    echo "invalid extension scheduler SHA-256" >&2
    exit 2
    ;;
esac
test "${#extension_scheduler_sha}" -eq 64 || {
  echo "invalid extension scheduler SHA-256 length" >&2
  exit 2
}
case "$premise_inventory_sha" in
  "") ;;
  *[!0-9a-f]*)
    echo "invalid premise inventory SHA-256" >&2
    exit 2
    ;;
esac
test -z "$premise_inventory_sha" || \
test "${#premise_inventory_sha}" -eq 64 || {
  echo "invalid premise inventory SHA-256 length" >&2
  exit 2
}

header () {
  first_line=$(sed -n '1p' "$1")
  marker=$(printf '#hh-anchor-manifest-v2\t')
  case "$first_line" in
    "$marker"*) printf '%s\n' "${first_line#"$marker"}" ;;
    *) echo "manifest has no v2 header: $1" >&2; exit 2 ;;
  esac
}

first_json=$(header "$first")
last_json=$(header "$last")

jq -e '
  .schema == "hh-anchor-manifest-v2" and
  .goal_digest_schema == "hh-goal-struct-v1" and
  .profile_start == 0 and .profile_length == 8 and
  .profiles == 16 and .row_count == (.goals * 8) and
  .task13_rows_checked == (.task13_execution_goals * 8) and
  .task13_execution_goals >= .goals and
  .task13_internal_key_pair_mismatches == 0 and
  .task13_premise_mismatches == 0 and
  .task13_request_key_mismatches == 0 and .prover_spawns == 0 and
  (.model_inventory_sha1 | test("^[0-9a-f]{40}$")) and
  (.model_features_sha1 | test("^[0-9a-f]{40}$")) and
  (.model_weights_sha1 | test("^[0-9a-f]{40}$"))
' >/dev/null <<EOF
$first_json
EOF
jq -e '
  .schema == "hh-anchor-manifest-v2" and
  .goal_digest_schema == "hh-goal-struct-v1" and
  .profile_start == 8 and .profile_length == 8 and
  .profiles == 16 and .row_count == (.goals * 8) and
  .task13_rows_checked == 0 and
  .task13_internal_key_pair_mismatches == 0 and
  .task13_premise_mismatches == 0 and
  .task13_request_key_mismatches == 0 and .prover_spawns == 0 and
  .goal_chunk_schema == "hh-profile-goal-chunks-v1" and
  .goal_chunk_count >= 1 and .goal_chunk_max_goals >= 1 and
  (.goal_chunk_inventory_sha256 | length) == 64 and
  (.goal_chunk_rows_sha256 | length) == 64 and
  (.model_inventory_sha1 | test("^[0-9a-f]{40}$")) and
  (.model_features_sha1 | test("^[0-9a-f]{40}$")) and
  (.model_weights_sha1 | test("^[0-9a-f]{40}$"))
' >/dev/null <<EOF
$last_json
EOF

common='.goal_bindings |= sort_by(.goal_id) |
  del(.invocation_provenance_sha256, .task13_rows_checked,
  .task13_execution_goals, .profile_start, .profile_length,
  .profile_set_sha1, .row_count, .behavior_source_commit,
  .baseline_provenance_sha256, .model_current_theory, .model_ancestry,
  .model_namespace_count, .export_model_inventory_sha1,
  .export_model_features_sha1, .export_model_weights_sha1,
  .export_model_feature_rows)'
common="$common | del(.goal_chunk_schema, .goal_chunk_count,
  .goal_chunk_max_goals, .goal_chunk_inventory_sha256,
  .goal_chunk_rows_sha256)"
first_common=$(jq -S -c "$common" <<EOF
$first_json
EOF
)
last_common=$(jq -S -c "$common" <<EOF
$last_json
EOF
)
test "$first_common" = "$last_common" || {
  echo "manifest headers disagree outside permitted batch fields" >&2
  exit 2
}

temporary=$output.partial.$$
rows=$temporary.rows
trap 'rm -f "$temporary" "$rows"' EXIT HUP INT TERM
tail -n +2 "$first" >"$rows"
tail -n +2 "$last" >>"$rows"

expected=$(jq -r '.goals * 16' <<EOF
$first_json
EOF
)
test "$(wc -l <"$rows")" -eq "$expected" || {
  echo "merged row count differs from header inventory" >&2
  exit 2
}
LC_ALL=C awk -F '\t' '
  NF != 13 { bad = 1; next }
  $2 !~ /^[0-9]+$/ || $2 < 1 || $2 > 16 { bad = 1; next }
  { key = $1 SUBSEP $2; if (seen[key]++) bad = 1; goals[$1] = 1 }
  END {
    for (goal in goals)
      for (slice = 1; slice <= 16; slice++)
        if (!seen[goal SUBSEP slice]) bad = 1
    if (bad) exit 1
  }
' "$rows" || {
  echo "merged rows have duplicates, gaps, or malformed fields" >&2
  exit 2
}

extension_behavior=$(jq -r '.behavior_source_commit' <<EOF
$last_json
EOF
)
extension_provenance=$(jq -r '.baseline_provenance_sha256' <<EOF
$last_json
EOF
)
extension_model=$(jq -c '{current_theory:.model_current_theory,
  ancestry:.model_ancestry,feature_rows:.export_model_feature_rows,
  namespace_count:.model_namespace_count,
  inventory_sha1:.export_model_inventory_sha1,
  features_sha1:.export_model_features_sha1,
  weights_sha1:.export_model_weights_sha1}' <<EOF
$last_json
EOF
)
extension_chunks=$(jq -c '{schema:.goal_chunk_schema,
  count:.goal_chunk_count,max_goals:.goal_chunk_max_goals,
  inventory_sha256:.goal_chunk_inventory_sha256,
  rows_sha256:.goal_chunk_rows_sha256}' <<EOF
$last_json
EOF
)
merged=$(jq -c --arg invocation "$invocation_sha" \
  --arg profile "$profile_sha" \
  --arg extension_behavior "$extension_behavior" \
  --arg extension_provenance "$extension_provenance" \
  --arg extension_scheduler "$extension_scheduler_sha" \
  --argjson extension_model "$extension_model" \
  --argjson extension_chunks "$extension_chunks" \
  --arg premise_inventory "$premise_inventory_sha" '
    .goal_bindings |= sort_by(.goal_id) |
    .first8_behavior_source_commit = .behavior_source_commit |
    .first8_baseline_provenance_sha256 = .baseline_provenance_sha256 |
    .extension_behavior_source_commit = $extension_behavior |
    .extension_baseline_provenance_sha256 = $extension_provenance |
    .extension_scheduler_sha256 = $extension_scheduler |
    .extension_runtime_model = $extension_model |
    .extension_goal_chunks = $extension_chunks |
    (if $premise_inventory == "" then . else
       .premise_inventory_sha256 = $premise_inventory end) |
    .extension_profile_start = 8 |
    .invocation_provenance_sha256 = $invocation |
    .profile_start = 0 | .profile_length = 16 |
    .profile_set_sha1 = $profile | .row_count = (.goals * 16)
  ' <<EOF
$first_json
EOF
)
printf '#hh-anchor-manifest-v2\t%s\n' "$merged" >"$temporary"
cat "$rows" >>"$temporary"
mv "$temporary" "$output"
rm -f "$rows"
trap - EXIT HUP INT TERM
