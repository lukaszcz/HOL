#!/bin/bash
set -Eeuo pipefail

test "$#" -ge 5 || {
  echo "usage: $0 baseline|current THEORY EXPECTED_NAMES OUTPUT PART..." >&2
  exit 2
}
mode=$1
theory=$2
expected_names=$3
output=$4
shift 4
case "$mode" in baseline|current) ;; *) exit 2 ;; esac
test -s "$expected_names"
test ! -L "$expected_names"
test "$#" -ge 1

temporary=$output.partial.$$
rows=$temporary.rows
bindings=$temporary.bindings
inventory=$temporary.inventory
expected=$temporary.expected
actual=$temporary.actual
expected_sorted=$temporary.expected-sorted
actual_sorted=$temporary.actual-sorted
expected_rows=$temporary.expected-rows
actual_rows=$temporary.actual-rows
ranges=$temporary.ranges
trap 'rm -f "$temporary" "$rows" "$bindings" "$inventory" \
  "$expected" "$actual" "$expected_sorted" "$actual_sorted" \
  "$expected_rows" "$actual_rows" "$ranges"' EXIT HUP INT TERM
: >"$rows"
: >"$bindings"
: >"$inventory"
: >"$ranges"
offset=0
part_count=0
max_goals=0
common=
profile_start=

# This is the complete input-header schema for current profile chunks.
# Fields in current_part_fields are range-local and are aggregated below;
# every other field is immutable across chunks and is compared byte-for-byte
# after canonical JSON normalization.  Keeping this classification explicit
# prevents a newly introduced range-local field from silently becoming a
# cross-chunk invariant (or vice versa).
current_part_fields='["completed_goal_range_length",
  "completed_goal_range_start","goal_bindings","goal_range_length",
  "goal_range_start","goals","row_count","row_set_sha1"]'
current_common_fields='["baseline_manifest_sha256","binding_mismatches",
  "export_model_ancestry","export_model_current_theory",
  "export_model_feature_rows","export_model_features_sha1",
  "export_model_inventory_sha1","export_model_namespace_count",
  "export_model_weights_sha1","export_target_model_features_sha1",
  "goal_chunk_policy_version","goal_digest_schema",
  "invocation_provenance_sha256","mismatches","model_ancestry",
  "model_current_theory","model_feature_rows","model_features_sha1",
  "model_inventory_sha1","model_namespace_count","model_weights_sha1",
  "profile_length","profile_set_sha1","profile_start","prover_spawns",
  "replay_theory","schema","target_model_features_sha1","theory"]'
current_input_fields=$(jq -nc --argjson part "$current_part_fields" \
  --argjson common "$current_common_fields" '$part + $common | sort')

for part in "$@"; do
  test -s "$part"
  test ! -L "$part"
  base=${part##*/}
  case "$base" in *[!A-Za-z0-9._-]* | "") exit 2 ;; esac
  awk -F "$(printf '\t')" -v base="$base" \
    '$NF == base {found = 1} END {exit !found}' "$inventory" && exit 2
  case "$mode" in
    baseline) marker='#hh-anchor-manifest-v2' ;;
    current) marker='#hh-anchor-current-v1' ;;
  esac
  test "$(head -1 "$part" | cut -f1)" = "$marker"
  header=$(head -1 "$part" | cut -f2-)
  goals=$(printf '%s\n' "$header" | jq -er '.goals')
  part_start=$(printf '%s\n' "$header" | jq -er '.profile_start')
  test "$goals" -ge 1
  test "$(wc -l <"$part")" -eq "$((goals * 8 + 1))"
  part_rows_sha=$(tail -n +2 "$part" |
    awk '{printf "%d:%s", length($0), $0}' | sha1sum | awk '{print $1}')
  if test "$mode" = current; then
    test "$part_rows_sha" = "$(printf '%s\n' "$header" | jq -er \
      '.row_set_sha1')"
  fi
  if test -z "$profile_start"; then
    profile_start=$part_start
  else
    test "$part_start" -eq "$profile_start"
  fi
  if test "$goals" -gt "$max_goals"; then max_goals=$goals; fi

  if test "$mode" = baseline; then
    printf '%s\n' "$header" | jq -e \
      --argjson goals "$goals" '
        .schema == "hh-anchor-manifest-v2" and
        .goal_digest_schema == "hh-goal-struct-v1" and
        .goals == $goals and .row_count == $goals * 8 and
        .profile_start == 8 and .profile_length == 8 and
        .task13_rows_checked == 0 and
        .task13_execution_goals == $goals and
        .task13_internal_key_pair_mismatches == 0 and
        .task13_premise_mismatches == 0 and
        .task13_request_key_mismatches == 0 and .prover_spawns == 0 and
        (.model_inventory_sha1 | test("^[0-9a-f]{40}$")) and
        (.model_features_sha1 | test("^[0-9a-f]{40}$")) and
        (.model_weights_sha1 | test("^[0-9a-f]{40}$")) and
        (.goal_bindings | length) == $goals' >/dev/null
    candidate=$(printf '%s\n' "$header" | jq -S -c '
      del(.goals,.row_count,.task13_execution_goals,.goal_bindings)')
  else
    printf '%s\n' "$header" | jq -e \
      --argjson goals "$goals" --argjson start "$profile_start" \
      --argjson offset "$offset" --argjson fields "$current_input_fields" '
        (keys | sort) == $fields and
        .schema == "hh-anchor-current-v1" and
        .goal_digest_schema == "hh-goal-struct-v1" and
        .goals == $goals and .row_count == $goals * 8 and
        .profile_start == $start and .profile_length == 8 and
        .goal_range_start == $offset and
        .goal_range_length == $goals and
        .completed_goal_range_start == $offset and
        .completed_goal_range_length == $goals and
        .goal_chunk_policy_version == "hh-current-goal-bisect-v1" and
        (($start == 0 and .replay_theory == true) or
         ($start == 8 and .replay_theory == false)) and
        .mismatches == 0 and
        .binding_mismatches == 0 and .prover_spawns == 0 and
        (.model_inventory_sha1 | test("^[0-9a-f]{40}$")) and
        (.model_features_sha1 | test("^[0-9a-f]{40}$")) and
        (.model_weights_sha1 | test("^[0-9a-f]{40}$")) and
        (.goal_bindings | length) == $goals and
        all(.goal_bindings[];
          (keys | sort) == ["ancestry_sha1","fact_inventory_sha1",
            "goal_id","goal_sha1","selected_premise_count",
            "selected_premises_sha1"] and
          (.goal_id | type) == "string" and
          (.goal_sha1 | test("^[0-9a-f]{40}$")) and
          (.ancestry_sha1 | test("^[0-9a-f]{40}$")) and
          (.fact_inventory_sha1 | test("^[0-9a-f]{40}$")) and
          (.selected_premises_sha1 | test("^[0-9a-f]{40}$")) and
          .selected_premise_count >= 0)' >/dev/null
    candidate=$(printf '%s\n' "$header" | jq -S -c \
      --argjson part "$current_part_fields" \
      'delpaths($part | map([.]))')
    printf '%s\t%s\t%s\n' "$offset" "$goals" \
      "$(sha256sum "$part" | awk '{print $1}')" >>"$ranges"
  fi
  if test -z "$common"; then common=$candidate; else
    test "$candidate" = "$common"
  fi

  sed -n "$((offset + 1)),$((offset + goals))p" "$expected_names" |
    sed "s/^/$theory./" >"$expected"
  test "$(wc -l <"$expected")" -eq "$goals"
  printf '%s\n' "$header" | jq -r '.goal_bindings[].goal_id' >"$actual"
  LC_ALL=C sort "$expected" >"$expected_sorted"
  LC_ALL=C sort "$actual" >"$actual_sorted"
  cmp -s "$expected_sorted" "$actual_sorted"
  awk -v first="$((profile_start + 1))" \
    -v last="$((profile_start + 8))" \
    '{for (slice = first; slice <= last; slice++)
       print $0 "\t" slice}' "$expected" >"$expected_rows"
  tail -n +2 "$part" | cut -f1,2 >"$actual_rows"
  LC_ALL=C sort -t "$(printf '\t')" -k1,1 -k2,2n \
    "$expected_rows" >"$expected_sorted"
  LC_ALL=C sort -t "$(printf '\t')" -k1,1 -k2,2n \
    "$actual_rows" >"$actual_sorted"
  cmp -s "$expected_sorted" "$actual_sorted"

  tail -n +2 "$part" | LC_ALL=C sort -t "$(printf '\t')" \
    -k1,1 -k2,2n >>"$rows"
  printf '%s\n' "$header" | jq -c \
    '.goal_bindings | sort_by(.goal_id)' >>"$bindings"
  printf 'rows\t%s\t%s\n' "$(sha256sum "$part" | awk '{print $1}')" "$base" \
    >>"$inventory"
  if test "${HHEVAL_CHUNK_REQUIRE_LOGS:-0}" = 1; then
    log=${part%.tsv}.log
    test -s "$log"
    test ! -L "$log"
    printf 'log\t%s\t%s\n' "$(sha256sum "$log" | awk '{print $1}')" \
      "${log##*/}" >>"$inventory"
    if test "$mode" = current; then
      mismatch=${part%.tsv}.mismatch.jsonl
      test -f "$mismatch"
      test ! -L "$mismatch"
      test ! -s "$mismatch"
      printf 'mismatch\t%s\t%s\n' \
        "$(sha256sum "$mismatch" | awk '{print $1}')" \
        "${mismatch##*/}" >>"$inventory"
    fi
  fi
  offset=$((offset + goals))
  part_count=$((part_count + 1))
done

test "$offset" -eq "$(wc -l <"$expected_names")"
LC_ALL=C awk -F '\t' '
  NF != 13 || $2 !~ /^[0-9]+$/ {bad = 1}
  {key = $1 SUBSEP $2; if (seen[key]++) bad = 1}
  END {if (bad) exit 1}' "$rows"
awk -F '\t' -v first="$((profile_start + 1))" \
  -v last="$((profile_start + 8))" \
  '$2 < first || $2 > last {exit 1}' "$rows"
inventory_sha=$(sha256sum "$inventory" | awk '{print $1}')
rows_sha=$(sha256sum "$rows" | awk '{print $1}')
range_inventory_sha=$(sha256sum "$ranges" | awk '{print $1}')
first_header=$(head -1 "$1" | cut -f2-)
if test "$mode" = current; then
  row_set_sha=$(LC_ALL=C awk '{printf "%d:%s", length($0), $0}' "$rows" |
    sha1sum | awk '{print $1}')
  merged=$(printf '%s\n' "$first_header" | jq -c \
    --slurpfile binding_arrays "$bindings" \
    --argjson goals "$offset" \
    --argjson chunks "$part_count" --argjson limit "$max_goals" \
    --arg inventory "$inventory_sha" --arg rows "$rows_sha" \
    --arg row_set "$row_set_sha" --arg ranges "$range_inventory_sha" '
      .goals = $goals | .row_count = $goals * 8 |
      .goal_range_start = 0 | .goal_range_length = $goals |
      .completed_goal_range_start = 0 |
      .completed_goal_range_length = $goals |
      .goal_bindings = [$binding_arrays[] | .[]] |
      .row_set_sha1 = $row_set |
      .goal_chunk_schema = "hh-profile-goal-chunks-v1" |
      .goal_chunk_policy_version = "hh-current-goal-bisect-v1" |
      .goal_chunk_count = $chunks | .goal_chunk_max_goals = $limit |
      .goal_chunk_range_inventory_sha256 = $ranges |
      .goal_chunk_inventory_sha256 = $inventory |
      .goal_chunk_rows_sha256 = $rows')
else
  merged=$(printf '%s\n' "$first_header" | jq -c \
    --slurpfile binding_arrays "$bindings" \
    --argjson goals "$offset" \
    --argjson chunks "$part_count" --argjson limit "$max_goals" \
    --arg inventory "$inventory_sha" --arg rows "$rows_sha" '
      .goals = $goals | .row_count = $goals * 8 |
      .task13_execution_goals = $goals |
      .goal_bindings = [$binding_arrays[] | .[]] |
      .goal_chunk_schema = "hh-profile-goal-chunks-v1" |
      .goal_chunk_count = $chunks | .goal_chunk_max_goals = $limit |
      .goal_chunk_inventory_sha256 = $inventory |
      .goal_chunk_rows_sha256 = $rows')
fi
printf '%s\t%s\n' "$marker" "$merged" >"$temporary"
cat "$rows" >>"$temporary"
mv "$temporary" "$output"
rm -f "$rows" "$bindings" "$inventory" "$ranges" "$expected" "$actual"
rm -f "$expected_sorted" "$actual_sorted" "$expected_rows" "$actual_rows"
trap - EXIT HUP INT TERM
