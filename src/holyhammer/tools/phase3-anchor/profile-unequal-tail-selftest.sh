#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 2 || {
  echo "usage: $0 CHUNK_MERGER TEMPLATE_EVIDENCE" >&2
  exit 2
}
merger=$1
evidence=$2
template="$evidence/bag-parts/part-000000.tsv"
test -x "$merger"
test -s "$template"

work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM
parts="$work/parts"
names="$work/unequal_tail.names"
mkdir -p "$parts"

for ((index=0; index<368; index++)); do
  printf 'g%03d\n' "$index"
done >"$names"

template_header=$(head -1 "$template" | cut -f2-)
template_row=$(tail -n +2 "$template" | head -1)
template_binding=$(printf '%s\n' "$template_header" | \
  jq -c '.goal_bindings[0]')

make_part () {
  local offset=$1 length=$2 part rows bindings row_sha header
  part=$(printf '%s/part-%06d.tsv' "$parts" "$offset")
  rows="$part.rows"
  bindings="$part.bindings"
  : >"$rows"
  : >"$bindings"
  for ((index=offset; index<offset+length; index++)); do
    goal=$(printf 'unequal_tail.g%03d' "$index")
    printf '%s\n' "$template_binding" | jq -c --arg goal "$goal" \
      '.goal_id = $goal' >>"$bindings"
    for ((slice=9; slice<=16; slice++)); do
      printf '%s\n' "$template_row" | awk -F '\t' -v OFS='\t' \
        -v goal="$goal" -v slice="$slice" \
        '{$1=goal; $2=slice; print}' >>"$rows"
    done
  done
  row_sha=$(awk '{printf "%d:%s", length($0), $0}' "$rows" | \
    sha1sum | awk '{print $1}')
  header=$(printf '%s\n' "$template_header" | jq -c \
    --argjson bindings "$(jq -s . "$bindings")" \
    --argjson offset "$offset" --argjson length "$length" \
    --arg row_sha "$row_sha" '
      .theory = "unequal_tail" |
      .goals = $length | .row_count = ($length * 8) |
      .profile_start = 8 | .profile_length = 8 |
      .replay_theory = false |
      .goal_range_start = $offset | .goal_range_length = $length |
      .completed_goal_range_start = $offset |
      .completed_goal_range_length = $length |
      .goal_chunk_policy_version = "hh-current-goal-bisect-v1" |
      .goal_bindings = $bindings | .row_set_sha1 = $row_sha')
  printf '#hh-anchor-current-v1\t%s\n' "$header" >"$part"
  cat "$rows" >>"$part"
  printf 'synthetic production-shaped unequal-tail chunk\n' \
    >"${part%.tsv}.log"
  : >"${part%.tsv}.mismatch.jsonl"
  rm -f "$rows" "$bindings"
}

make_part 0 128
make_part 128 128
make_part 256 112
part0="$parts/part-000000.tsv"
part128="$parts/part-000128.tsv"
part256="$parts/part-000256.tsv"

merged="$work/merged.tsv"
HHEVAL_CHUNK_REQUIRE_LOGS=1 "$merger" current unequal_tail "$names" \
  "$merged" "$part0" "$part128" "$part256"
test "$(wc -l <"$merged")" -eq 2945
head -1 "$merged" | cut -f2- | jq -e '
  .schema == "hh-anchor-current-v1" and
  .theory == "unequal_tail" and .goals == 368 and
  .row_count == 2944 and .profile_start == 8 and
  .profile_length == 8 and .goal_range_start == 0 and
  .goal_range_length == 368 and .completed_goal_range_start == 0 and
  .completed_goal_range_length == 368 and
  .goal_chunk_schema == "hh-profile-goal-chunks-v1" and
  .goal_chunk_policy_version == "hh-current-goal-bisect-v1" and
  .goal_chunk_count == 3 and .goal_chunk_max_goals == 128 and
  (.goal_bindings | length) == 368 and
  (.goal_chunk_range_inventory_sha256 | length) == 64 and
  (.goal_chunk_inventory_sha256 | length) == 64 and
  (.goal_chunk_rows_sha256 | length) == 64
' >/dev/null
{
  tail -n +2 "$part0"
  tail -n +2 "$part128"
  tail -n +2 "$part256"
} >"$work/expected.rows"
tail -n +2 "$merged" >"$work/actual.rows"
cmp -s "$work/expected.rows" "$work/actual.rows"

reject () {
  local label=$1
  shift
  local output="$work/reject-$label.tsv"
  if HHEVAL_CHUNK_REQUIRE_LOGS=1 "$merger" current unequal_tail \
      "$names" "$output" "$@"; then
    echo "unequal-tail merger accepted $label" >&2
    exit 1
  fi
  test ! -e "$output"
}

mutate () {
  local source=$1 target=$2 filter=$3 header
  header=$(head -1 "$source" | cut -f2- | jq -c "$filter")
  printf '#hh-anchor-current-v1\t%s\n' "$header" >"$target"
  tail -n +2 "$source" >>"$target"
  cp "${source%.tsv}.log" "${target%.tsv}.log"
  cp "${source%.tsv}.mismatch.jsonl" \
    "${target%.tsv}.mismatch.jsonl"
}

wrong_length="$work/part-000256.tsv"
mutate "$part256" "$wrong_length" \
  '.completed_goal_range_length = 111'
reject wrong-completed-length "$part0" "$part128" "$wrong_length"
reject gap "$part0" "$part256"
reject duplicate "$part0" "$part0" "$part256"
reject reversed "$part128" "$part0" "$part256"

overlap="$work/part-overlap.tsv"
mutate "$part128" "$overlap" \
  '.goal_range_start = 127 | .completed_goal_range_start = 127'
reject overlap "$part0" "$overlap" "$part256"

stale="$work/part-stale.tsv"
mutate "$part128" "$stale" \
  '.model_features_sha1 = "0000000000000000000000000000000000000000"'
reject stale-common-header "$part0" "$stale" "$part256"

stale_ranking="$work/part-stale-ranking.tsv"
mutate "$part128" "$stale_ranking" \
  '.goal_bindings[0].selected_premises_sha1 = "bad"'
reject stale-ranking-binding "$part0" "$stale_ranking" "$part256"

corrupt="$work/part-corrupt.tsv"
cp "$part128" "$corrupt"
awk -F '\t' -v OFS='\t' 'NR == 2 {$13 = "corrupt"} {print}' \
  "$corrupt" >"$corrupt.tmp"
mv "$corrupt.tmp" "$corrupt"
cp "${part128%.tsv}.log" "${corrupt%.tsv}.log"
cp "${part128%.tsv}.mismatch.jsonl" \
  "${corrupt%.tsv}.mismatch.jsonl"
reject corrupt-row "$part0" "$corrupt" "$part256"

printf 'profile-unequal-tail-selftest: OK\n'
