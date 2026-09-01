#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 4 || {
  echo "usage: $0 EVIDENCE_DIRECTORY CHUNK_MERGER RUNNER INPUTS" >&2
  exit 2
}
evidence=$1
merger=$2
runner=$3
inputs=$4
test -s "$runner"
test -d "$inputs"
export HHEVAL_TASK10_A_INPUTS=$inputs
export HHEVAL_TASK10_A_EXP=phase3-task10-subdivision-library-selftest
export HHEVAL_TASK10_RUNNER_LIBRARY_ONLY=1
# shellcheck source=/dev/null
source "$runner"
unset HHEVAL_TASK10_RUNNER_LIBRARY_ONLY
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' EXIT HUP INT TERM
(cd "$evidence" && sha256sum -c SHA256SUMS >/dev/null)

source_parts="$evidence/bag-parts"
parts="$work/bag-parts"
mkdir -p "$parts"
prepare_part () {
  local offset=$1 source target header
  source=$(printf '%s/part-%06d.tsv' "$source_parts" "$offset")
  target=$(printf '%s/part-%06d.tsv' "$parts" "$offset")
  header=$(head -1 "$source" | cut -f2- | jq -c \
    --argjson offset "$offset" '
      .goal_range_start = $offset |
      .goal_range_length = .goals |
      .completed_goal_range_start = $offset |
      .completed_goal_range_length = .goals |
      .goal_chunk_policy_version = "hh-current-goal-bisect-v1"')
  printf '#hh-anchor-current-v1\t%s\n' "$header" >"$target"
  tail -n +2 "$source" >>"$target"
  cp "${source%.tsv}.log" "${target%.tsv}.log"
  cp "${source%.tsv}.mismatch.jsonl" \
    "${target%.tsv}.mismatch.jsonl"
}
prepare_part 0
prepare_part 2
merged="$work/merged.tsv"
HHEVAL_CHUNK_REQUIRE_LOGS=1 "$merger" current bag \
  "$evidence/bag.names" "$merged" \
  "$parts/part-000000.tsv" "$parts/part-000002.tsv"
tail -n +2 "$merged" | LC_ALL=C sort -t "$(printf '\t')" \
  -k1,1 -k2,2n >"$work/merged.sorted"
cmp -s "$evidence/whole-bag.sorted.tsv" "$work/merged.sorted"
head -1 "$merged" | cut -f2- | jq -e '
  .profile_start == 0 and .profile_length == 8 and
  .replay_theory == true and .goals == 3 and .row_count == 24 and
  .completed_goal_range_start == 0 and
  .completed_goal_range_length == 3 and
  .goal_chunk_policy_version == "hh-current-goal-bisect-v1" and
  .goal_chunk_count == 2 and .goal_chunk_max_goals == 2 and
  (.goal_chunk_range_inventory_sha256 | length) == 64 and
  (.goal_chunk_inventory_sha256 | length) == 64 and
  .goal_chunk_rows_sha256 ==
    "7f47c121994939aea085c9f263885372a5e9a1679dd1e7cb719bfae904586078"
' >/dev/null
(cd "$evidence/rankings" && sha256sum -c SHA256SUMS >/dev/null)
test "$(find "$evidence/rankings" -maxdepth 1 -type f \
  -name '*.ranking' | wc -l)" -eq 3

reject () {
  local label=$1
  shift
  local mode=$1 theory=$2 names=$3
  shift 3
  local output="$work/$label.tsv"
  if HHEVAL_CHUNK_REQUIRE_LOGS=1 "$merger" "$mode" "$theory" \
      "$names" "$output" "$@"; then
    echo "chunk merger accepted $label" >&2
    exit 1
  fi
  test ! -e "$output"
}

reject gap current bag "$evidence/bag.names" \
  "$parts/part-000000.tsv"
reject duplicate current bag "$evidence/bag.names" \
  "$parts/part-000000.tsv" "$parts/part-000000.tsv"
reject reversed current bag "$evidence/bag.names" \
  "$parts/part-000002.tsv" "$parts/part-000000.tsv"
reject baseline-cross-feed current bag "$evidence/bag.names" \
  "$evidence/baseline-part.tsv"

parent="$work/part-parent.tsv"
parent_header=$(head -1 "$merged" | cut -f2- | jq -c '
  del(.goal_chunk_schema,.goal_chunk_count,.goal_chunk_max_goals,
      .goal_chunk_range_inventory_sha256,.goal_chunk_inventory_sha256,
      .goal_chunk_rows_sha256) |
  .goal_range_start = 0 | .goal_range_length = .goals |
  .completed_goal_range_start = 0 |
  .completed_goal_range_length = .goals')
printf '#hh-anchor-current-v1\t%s\n' "$parent_header" >"$parent"
tail -n +2 "$merged" >>"$parent"
cp "$parts/part-000000.log" "${parent%.tsv}.log"
: >"${parent%.tsv}.mismatch.jsonl"
reject stale-parent-child-overlap current bag "$evidence/bag.names" \
  "$parent" "$parts/part-000000.tsv"

stale="$work/part-000002.tsv"
{
  printf '#hh-anchor-current-v1\t'
  head -1 "$parts/part-000002.tsv" | cut -f2- | jq -c \
    '.model_features_sha1 = "0000000000000000000000000000000000000000"'
  tail -n +2 "$parts/part-000002.tsv"
} >"$stale"
cp "$parts/part-000002.log" "$work/part-000002.log"
cp "$parts/part-000002.mismatch.jsonl" \
  "$work/part-000002.mismatch.jsonl"
reject stale-model current bag "$evidence/bag.names" \
  "$parts/part-000000.tsv" "$stale"

corrupt="$work/part-000000.tsv"
awk -F '\t' 'BEGIN {OFS="\t"} NR == 2 {$13 = "corrupt"} {print}' \
  "$parts/part-000000.tsv" >"$corrupt"
cp "$parts/part-000000.log" "$work/part-000000.log"
cp "$parts/part-000000.mismatch.jsonl" \
  "$work/part-000000.mismatch.jsonl"
reject corrupt-row current bag "$evidence/bag.names" \
  "$corrupt" "$parts/part-000002.tsv"

# Exercise the real recursive controller with a genuine status-124 result and
# a certified progress marker.  The successful children are deterministic
# slices of the already cross-certified whole-member rows above, so the test
# checks controller scheduling independently of HOL runtime cost.
control="$work/control"
OUT="$control/out"
STATE="$control/state"
GOAL_CHUNK_MIN=1
GOAL_CHUNK_POLICY=hh-current-goal-bisect-v1
INFRA_ATTEMPTS=2
mkdir -p "$OUT/invocations" "$OUT/baseline" "$STATE/current"
printf '%s\n' '{"run":"subdivision-selftest"}' >"$OUT/run.json"
printf '%s\n' '{"invocation":"subdivision-selftest"}' \
  >"$OUT/invocations/bag.json"
printf '%s\n' baseline >"$OUT/baseline/bag.tsv"
control_names="$control/bag.names"
cp "$evidence/bag.names" "$control_names"
control_source="$merged"
CONTROL_MODE=subdivide
field () {
  test "$1" = bag
  test "$2" = 7
  printf '%s\n' 0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
}
current_part_once () {
  local theory=$1 length=$2 start=$3 output=$4 log=$5 names=$6
  local worker_key=$7 mismatch=$8 offset=$9 header rows row_sha
  test "$theory" = bag
  test "$start" -eq 0
  if test "$CONTROL_MODE" = infrastructure && test "$offset" -eq 0 && \
      test "$length" -eq 3; then
    mkdir -p "$STATE/current/$worker_key"
    printf '%s\n' attempt >>"$control/infra-attempts"
    if test "$(wc -l <"$control/infra-attempts")" -eq 1; then
      printf '%s\n' zero-byte-launch-failure >"$log.partial.$$"
      return 125
    fi
  elif test "$offset" -eq 0 && test "$length" -eq 3; then
    mkdir -p "$STATE/current/$worker_key"
    printf '%s\n' genuine-computation-timeout >"$log.partial.$$"
    jq -nc --arg theory "$theory" --argjson offset "$offset" \
      --argjson length "$length" --arg policy "$GOAL_CHUNK_POLICY" \
      --arg invocation "$(sha "$OUT/invocations/$theory.json")" \
      --arg run "$(sha "$OUT/run.json")" \
      --arg baseline "$(sha "$OUT/baseline/$theory.tsv")" \
      --arg member "$(field "$theory" 7)" '
        {schema:"hh-current-computation-progress-v1",theory:$theory,
         profile_start:0,profile_length:8,goal_range_start:$offset,
         goal_range_length:$length,goal_chunk_policy_version:$policy,
         invocation_provenance_sha256:$invocation,run_header_sha256:$run,
         baseline_manifest_sha256:$baseline,
         canonical_journal_member_sha256:$member,
         model_inventory_sha1:"1111111111111111111111111111111111111111",
         model_features_sha1:"2222222222222222222222222222222222222222",
         model_weights_sha1:"3333333333333333333333333333333333333333"}' \
      >"$STATE/current/$worker_key/progress.json"
    return 124
  fi
  rows="$output.rows"
  : >"$rows"
  while read -r name; do
    awk -F '\t' -v goal="bag.$name" '$1 == goal' "$control_source" \
      >>"$rows"
  done < <(sed -n "$((offset + 1)),$((offset + length))p" \
    "$control_names")
  test "$(wc -l <"$rows")" -eq "$((length * 8))"
  row_sha=$(awk '{printf "%d:%s", length($0), $0}' "$rows" | \
    sha1sum | awk '{print $1}')
  header=$(head -1 "$control_source" | cut -f2- | jq -c \
    --argjson offset "$offset" --argjson length "$length" \
    --arg row_sha "$row_sha" '
      del(.goal_chunk_schema,.goal_chunk_count,.goal_chunk_max_goals,
          .goal_chunk_range_inventory_sha256,.goal_chunk_inventory_sha256,
          .goal_chunk_rows_sha256) |
      .goals = $length | .row_count = $length * 8 |
      .goal_range_start = $offset | .goal_range_length = $length |
      .completed_goal_range_start = $offset |
      .completed_goal_range_length = $length |
      .goal_bindings = .goal_bindings[$offset:($offset + $length)] |
      .row_set_sha1 = $row_sha')
  printf '#hh-anchor-current-v1\t%s\n' "$header" >"$output"
  cat "$rows" >>"$output"
  rm -f "$rows"
  printf '%s\n' accepted-child >"$log"
  : >"$mismatch"
}

control_parts="$OUT/current-first8-parts/bag"
mkdir -p "$control_parts"
# Cross the same exported-function boundary used by the xargs pool.  This
# catches a missing transitive helper before a run can create durable output.
export -f field current_part_once
export control control_names control_source CONTROL_MODE
export OUT STATE GOAL_CHUNK_MIN GOAL_CHUNK_POLICY INFRA_ATTEMPTS
export HHEVAL_WORKER_FUNCTIONS
bash --noprofile --norc -Eeuo pipefail -c '
  for function in $HHEVAL_WORKER_FUNCTIONS; do
    declare -F "$function" >/dev/null
  done
  declare -F validate_current_progress_file >/dev/null
  current_first8_range bag "$control_names" "$1" 0 3
' subdivision-worker "$control_parts"
test ! -e "$control_parts/part-000000-000003.tsv"
test "$(find "$control_parts" -maxdepth 1 -type f -name '*.tsv' | \
  wc -l)" -eq 2
test -s "$OUT/subdivisions/bag/events.jsonl"
test "$(wc -l <"$OUT/subdivisions/bag/events.jsonl")" -eq 1
jq -e '
  .event == "subdivide" and .theory == "bag" and .offset == 0 and
  .length == 3 and .policy_version == "hh-current-goal-bisect-v1" and
  (.progress_sha256 | test("^[0-9a-f]{64}$"))' \
  "$OUT/subdivisions/bag/events.jsonl" >/dev/null
test "$(find "$OUT/subdivisions/bag" -type f \
  -name 'compute-timeout-000000-000003-*' | wc -l)" -eq 2
mapfile -t control_part_list < <(find "$control_parts" -maxdepth 1 \
  -type f -name '*.tsv' | LC_ALL=C sort)
control_fold="$control/fold.tsv"
HHEVAL_CHUNK_REQUIRE_LOGS=1 "$merger" current bag "$control_names" \
  "$control_fold" "${control_part_list[@]}"
tail -n +2 "$control_fold" >"$control/fold.rows"
tail -n +2 "$control_source" >"$control/source.rows"
cmp -s "$control/source.rows" "$control/fold.rows"
control_sha=$(sha256sum "$control_fold" | awk '{print $1}')
current_first8_range bag "$control_names" "$control_parts" 0 3
HHEVAL_CHUNK_REQUIRE_LOGS=1 "$merger" current bag "$control_names" \
  "$control/fold.resume.tsv" "${control_part_list[@]}"
test "$control_sha" = "$(sha256sum "$control/fold.resume.tsv" | \
  awk '{print $1}')"
test "$(wc -l <"$OUT/subdivisions/bag/events.jsonl")" -eq 1

negative="$control/negative"
mkdir -p "$negative"
cp -a "$OUT" "$negative/corrupt-progress"
corrupt_progress="$negative/corrupt-progress/subdivisions/bag"
corrupt_progress+="/compute-timeout-000000-000003-progress.json"
jq '.model_features_sha1 = "bad"' "$corrupt_progress" \
  >"$corrupt_progress.new"
mv "$corrupt_progress.new" "$corrupt_progress"
corrupt_sha=$(sha256sum "$corrupt_progress" | awk '{print $1}')
jq --arg sha "$corrupt_sha" \
  'if .offset == 0 and .length == 3 then .progress_sha256 = $sha else . end' \
  "$negative/corrupt-progress/subdivisions/bag/events.jsonl" \
  >"$negative/corrupt-progress/subdivisions/bag/events.jsonl.new"
mv "$negative/corrupt-progress/subdivisions/bag/events.jsonl.new" \
  "$negative/corrupt-progress/subdivisions/bag/events.jsonl"
if (OUT="$negative/corrupt-progress"; STATE="$negative/state-corrupt";
    current_first8_range bag "$control_names" \
      "$OUT/current-first8-parts/bag" 0 3); then
  echo "controller accepted corrupt archived progress" >&2
  exit 1
fi

cp -a "$OUT" "$negative/stale-policy"
jq '.policy_version = "stale-policy"' \
  "$negative/stale-policy/subdivisions/bag/events.jsonl" \
  >"$negative/stale-policy/subdivisions/bag/events.jsonl.new"
mv "$negative/stale-policy/subdivisions/bag/events.jsonl.new" \
  "$negative/stale-policy/subdivisions/bag/events.jsonl"
if (OUT="$negative/stale-policy"; STATE="$negative/state-stale";
    current_first8_range bag "$control_names" \
      "$OUT/current-first8-parts/bag" 0 3); then
  echo "controller accepted stale subdivision policy" >&2
  exit 1
fi

cp -a "$OUT" "$negative/parent-overlap"
cp "$control_fold" \
  "$negative/parent-overlap/current-first8-parts/bag/part-000000-000003.tsv"
if (OUT="$negative/parent-overlap"; STATE="$negative/state-overlap";
    current_first8_range bag "$control_names" \
      "$OUT/current-first8-parts/bag" 0 3); then
  echo "controller accepted stale parent plus children" >&2
  exit 1
fi

# A launch/infrastructure failure has no certified computation marker.  It is
# retried at the identical range and must never create subdivision evidence.
CONTROL_MODE=infrastructure
OUT="$control/infra-out"
STATE="$control/infra-state"
rm -f "$control/infra-attempts"
mkdir -p "$OUT/invocations" "$OUT/baseline" "$STATE/current"
printf '%s\n' '{"run":"subdivision-selftest"}' >"$OUT/run.json"
printf '%s\n' '{"invocation":"subdivision-selftest"}' \
  >"$OUT/invocations/bag.json"
printf '%s\n' baseline >"$OUT/baseline/bag.tsv"
infra_parts="$OUT/current-first8-parts/bag"
mkdir -p "$infra_parts"
current_first8_range bag "$control_names" "$infra_parts" 0 3
test "$(wc -l <"$control/infra-attempts")" -eq 2
test -s "$infra_parts/part-000000-000003.tsv"
test ! -e "$OUT/subdivisions/bag/events.jsonl"
infra_message='current infrastructure-retry theory=bag start=0 chunk=0'
infra_message+=' length=3 attempt=1 status=125'
test "$(grep -c "$infra_message" \
  "$OUT/recycles.log")" -eq 1

printf 'profile-first8-selftest: OK\n'
