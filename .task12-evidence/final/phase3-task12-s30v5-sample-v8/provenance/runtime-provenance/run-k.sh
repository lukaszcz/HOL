#!/usr/bin/env bash
set -Eeuo pipefail
trap 'status=$?; printf "TASK12 K seed failed at line %s\n" \
  "$LINENO" >&2; exit "$status"' ERR

if (($# != 3)); then
  echo "usage: $0 INPUTS SAMPLE_OUTPUT K_RUN" >&2
  exit 2
fi

ROOT=${HHEVAL_TASK12_ROOT:-$(git rev-parse --show-toplevel)}
INPUTS=$(realpath "$1")
SAMPLE=$(realpath "$2")
K_RUN=$3
DEFAULT_STATE_BASE=/run/user/$(id -u)/holyhammer-phase3-task12
STATE_BASE=${HHEVAL_TASK12_STATE_BASE:-$DEFAULT_STATE_BASE}
STATE="$STATE_BASE/k-revised-v3"
HAMMER="$STATE/hammer"
SOURCE_DRIVER="$ROOT/src/holyhammer/tools/phase3-s30v5/task12-driver.sml"
EXPECTED_INPUT=cc793e532c19105a722979a77c328e6391db27645df731b105586edf2cd530d2

[[ ! -e "$K_RUN" && ! -e "$STATE" ]]
[[ "$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)" == \
  "$EXPECTED_INPUT" ]]
[[ "$(wc -l <"$SAMPLE/k-subset.tsv")" == 128 ]]
jq -e '.status == "sample-sealed" and .sample.goals == 3000 and
  .k_subset.goals == 128 and .full_corpus_s30v5_measured == false' \
  "$SAMPLE/sample-certificate.json" >/dev/null

E_PATH=$(awk -F '\t' '$1 == "e" {print $2}' "$INPUTS/provers.tsv")
V_PATH=$(awk -F '\t' '$1 == "vampire" {print $2}' "$INPUTS/provers.tsv")
Z_PATH=$(awk -F '\t' '$1 == "zipperposition" {print $2}' \
  "$INPUTS/provers.tsv")

TEMP=$(mktemp -d)
cleanup() {
  rm -rf "$TEMP"
}
trap cleanup EXIT HUP INT TERM

mkdir -p "$K_RUN" "$STATE/seed" "$HAMMER/cache"
cp "$SOURCE_DRIVER" "$K_RUN/task12-driver.sml"
DRIVER="$K_RUN/task12-driver.sml"
initial_files=$(find "$HAMMER/cache" -type f | wc -l)
[[ "$initial_files" == 0 ]]
cut -f1 "$SAMPLE/k-subset.tsv" | LC_ALL=C sort -u >"$TEMP/theories"

cache_manifest() {
  local directory=$1 output=$2 relative
  : >"$output"
  while IFS= read -r -d '' relative; do
    [[ "$relative" != *$'\t'* && "$relative" != *$'\n'* ]]
    printf '%s\t%s\t%s\n' \
      "$(sha256sum "$directory/$relative" | cut -d' ' -f1)" \
      "$(stat -c %s "$directory/$relative")" "$relative" >>"$output"
  done < <(cd "$directory" && find . -type f -printf '%P\0' |
    LC_ALL=C sort -z)
}

run_pass() {
  local mode=$1 destination=$2 counts=$3 theory relative directory work
  : >"$counts"
  while IFS= read -r theory; do
    relative=$(awk -F '\t' -v theory="$theory" \
      '$1 == theory {print $2}' "$INPUTS/theory-directories.tsv")
    [[ -n "$relative" ]]
    directory="$ROOT/$relative"
    [[ -d "$directory" ]]
    awk -F '\t' -v theory="$theory" '$1 == theory {print}' \
      "$SAMPLE/k-subset.tsv" >"$TEMP/$theory.tsv"
    work="$STATE/$destination/$theory"
    mkdir -p "$work/journal" "$work/out" "$work/pb"
    env HOLDIR="$ROOT" HOL4_HAMMER_DIR="$HAMMER" \
      HOL4_EPROVER_EXECUTABLE="$E_PATH" \
      HOL4_VAMPIRE_EXECUTABLE="$V_PATH" \
      HOL4_ZIPPERPOSITION_EXECUTABLE="$Z_PATH" \
      HHEVAL_EXPDIR="$work" HHEVAL_THEORY="$theory" \
      HHEVAL_THEORY_DIR="$directory" HHEVAL_PART=0 HHEVAL_PARTS=1 \
      HHEVAL_TASK12_MODE="$mode" \
      HHEVAL_GOAL_INVENTORY="$TEMP/$theory.tsv" \
      HHEVAL_SPAWN_OUTPUT="$work/prover-spawns.txt" \
      "$ROOT/bin/hol" repl -b "$ROOT/bin/hol.state" \
      <"$DRIVER" >"$work/worker.log" 2>&1
    printf '%s\t%s\n' "$theory" \
      "$(cat "$work/prover-spawns.txt")" >>"$counts"
  done <"$TEMP/theories"
}

run_pass cache-seed seed "$TEMP/seed-spawns.tsv"
find "$STATE/seed" -path '*/journal/*.jsonl' -print0 |
  LC_ALL=C sort -z | xargs -0 cat >"$TEMP/seed.jsonl"
[[ "$(wc -l <"$TEMP/seed.jsonl")" == 128 ]]
seed_spawns=$(awk -F '\t' '{n += $2} END {print n+0}' \
  "$TEMP/seed-spawns.tsv")
[[ "$seed_spawns" -gt 0 ]]
cache_manifest "$HAMMER/cache" "$TEMP/seed-cache-manifest.tsv"
cache_before=$(sha256sum "$TEMP/seed-cache-manifest.tsv" | cut -d' ' -f1)
cache_files=$(find "$HAMMER/cache" -type f | wc -l)
cache_bytes=$(find "$HAMMER/cache" -type f -printf '%s\n' |
  awk '{n += $1} END {print n+0}')
[[ "$cache_files" -ge 128 ]]

cp "$SAMPLE/k-subset.tsv" "$K_RUN/subset.tsv.partial"
mv "$K_RUN/subset.tsv.partial" "$K_RUN/subset.tsv"
cp "$TEMP/seed.jsonl" "$K_RUN/seed-journal.jsonl.partial"
mv "$K_RUN/seed-journal.jsonl.partial" "$K_RUN/seed-journal.jsonl"
cp "$TEMP/seed-spawns.tsv" "$K_RUN/seed-spawns.tsv"
cp "$TEMP/seed-cache-manifest.tsv" \
  "$K_RUN/seed-cache-manifest.tsv.partial"
mv "$K_RUN/seed-cache-manifest.tsv.partial" \
  "$K_RUN/seed-cache-manifest.tsv"
cp "$ROOT/src/holyhammer/tools/phase3-s30v5/run-k.sh" \
  "$K_RUN/run-k.sh"
jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg input "$EXPECTED_INPUT" \
  --arg sample "$(sha256sum "$SAMPLE/sample-certificate.json" |
    cut -d' ' -f1)" \
  --arg subset "$(sha256sum "$K_RUN/subset.tsv" | cut -d' ' -f1)" \
  --arg seed "$(sha256sum "$K_RUN/seed-journal.jsonl" | cut -d' ' -f1)" \
  --arg cache "$cache_before" --arg state "$STATE" \
  --arg script "$(sha256sum "$K_RUN/run-k.sh" | cut -d' ' -f1)" \
  --argjson seed_spawns "$seed_spawns" \
  --argjson files "$cache_files" --argjson bytes "$cache_bytes" '
  {schema:"hh-task12-k-seed-v2",status:"seeded",
   completed:$completed,input_inventory_sha256:$input,
   sample_certificate_sha256:$sample,subset_goals:128,
   subset_sha256:$subset,seed_journal_sha256:$seed,
   seed_prover_spawns:$seed_spawns,slices_per_goal:24,
   filter_keyed_problem_filters:["knn","mash","mepo","mesh"],
   initial_cache_files:0,seeded_cache_manifest_sha256:$cache,
   cache_files:$files,cache_bytes:$bytes,state_root:$state,
   producing_run_script_sha256:$script,
   state_retained_for_same_process_witness:true,tuning_performed:false}
' >"$K_RUN/seed-certificate.json.partial"
mv "$K_RUN/seed-certificate.json.partial" "$K_RUN/seed-certificate.json"
