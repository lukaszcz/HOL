#!/usr/bin/env bash
set -Eeuo pipefail
trap 'status=$?; printf "TASK12 K replay failed at line %s\n" \
  "$LINENO" >&2; exit "$status"' ERR

if (($# != 4)); then
  echo "usage: $0 INPUTS SAMPLE SEEDED_K STATE" >&2
  exit 2
fi

ROOT=$(git rev-parse --show-toplevel)
INPUTS=$(realpath "$1")
SAMPLE=$(realpath "$2")
K_RUN=$(realpath "$3")
STATE=$(realpath "$4")
HAMMER="$STATE/hammer"
PRIME_ROOT="$STATE/prime-cache-check"
REPLAY_ROOT="$STATE/replay-witness"
DRIVER="$ROOT/src/holyhammer/tools/phase3-s30v5/k-paired-driver.sml"
TEMP=$(mktemp -d)
trap 'rm -rf "$TEMP"' EXIT HUP INT TERM
(cd "$SAMPLE" && sha256sum -c SHA256SUMS >/dev/null)
[[ -s "$K_RUN/seed-certificate.json" ]]
[[ -d "$STATE/seed" && -d "$HAMMER/cache" ]]
[[ ! -e "$PRIME_ROOT" && ! -e "$REPLAY_ROOT" ]]
jq -e --arg subset "$(sha256sum "$SAMPLE/k-subset.tsv" |
  cut -d' ' -f1)" --arg state "$STATE" '
  .schema == "hh-task12-k-seed-v2" and .status == "seeded" and
  .subset_goals == 128 and .subset_sha256 == $subset and
  .initial_cache_files == 0 and .state_root == $state and
  .state_retained_for_same_process_witness == true and
  .tuning_performed == false
' "$K_RUN/seed-certificate.json" >/dev/null
cmp "$SAMPLE/k-subset.tsv" "$K_RUN/subset.tsv"
cut -f1 "$SAMPLE/k-subset.tsv" | LC_ALL=C sort -u >"$TEMP/theories"
E_PATH=$(awk -F '\t' '$1=="e"{print $2}' "$INPUTS/provers.tsv")
V_PATH=$(awk -F '\t' '$1=="vampire"{print $2}' "$INPUTS/provers.tsv")
Z_PATH=$(awk -F '\t' '$1=="zipperposition"{print $2}' \
  "$INPUTS/provers.tsv")

: >"$TEMP/prime-spawns.tsv"
: >"$TEMP/replay-spawns.tsv"
: >"$TEMP/version-spawns.tsv"
: >"$TEMP/resolved-versions.tsv"
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
cache_manifest "$HAMMER/cache" "$TEMP/cache-before.tsv"
cmp "$K_RUN/seed-cache-manifest.tsv" "$TEMP/cache-before.tsv"
cache_before=$(sha256sum "$TEMP/cache-before.tsv" | cut -d' ' -f1)
[[ "$cache_before" == "$(jq -r '.seeded_cache_manifest_sha256' \
  "$K_RUN/seed-certificate.json")" ]]
find "$STATE" -mindepth 1 -maxdepth 1 -printf '%f\n' |
  LC_ALL=C sort >"$TEMP/state-children-before.tsv"
printf '%s\n' hammer seed >"$TEMP/expected-state-children.tsv"
cmp "$TEMP/expected-state-children.tsv" "$TEMP/state-children-before.tsv"
jq -n --arg state "$STATE" --arg prime "$PRIME_ROOT" \
  --arg replay "$REPLAY_ROOT" \
  --arg observed "$(sha256sum "$TEMP/state-children-before.tsv" | \
    cut -d' ' -f1)" --arg started "$(date -u +%Y-%m-%dT%H:%M:%SZ)" '
  {schema:"hh-task12-k-fresh-roots-v1",observed_at:$started,
   state_root:$state,state_children_before_sha256:$observed,
   state_children_before:["hammer","seed"],
   prime_root:$prime,replay_root:$replay,
   prime_root_absent_before_run:true,replay_root_absent_before_run:true,
   resume_allowed:false}
' >"$TEMP/fresh-root-proof.json"
mkdir "$PRIME_ROOT" "$REPLAY_ROOT"
while IFS= read -r theory; do
  relative=$(awk -F '\t' -v theory="$theory" \
    '$1==theory{print $2}' "$INPUTS/theory-directories.tsv")
  awk -F '\t' -v theory="$theory" '$1==theory{print}' \
    "$SAMPLE/k-subset.tsv" >"$TEMP/$theory.tsv"
  prime="$PRIME_ROOT/$theory"
  replay="$REPLAY_ROOT/$theory"
  [[ ! -e "$prime" && ! -e "$replay" ]]
  mkdir "$prime" "$replay"
  mkdir "$prime/journal" "$prime/out" "$prime/pb"
  mkdir "$replay/journal" "$replay/out" "$replay/pb"
  env HOLDIR="$ROOT" HOL4_HAMMER_DIR="$HAMMER" \
    HOL4_EPROVER_EXECUTABLE="$E_PATH" \
    HOL4_VAMPIRE_EXECUTABLE="$V_PATH" \
    HOL4_ZIPPERPOSITION_EXECUTABLE="$Z_PATH" \
    HHEVAL_THEORY="$theory" HHEVAL_THEORY_DIR="$ROOT/$relative" \
    HHEVAL_GOAL_INVENTORY="$TEMP/$theory.tsv" \
    HHEVAL_PRIME_EXPDIR="$prime" HHEVAL_REPLAY_EXPDIR="$replay" \
    HHEVAL_PRIME_SPAWNS="$prime/spawns" \
    HHEVAL_REPLAY_SPAWNS="$replay/spawns" \
    HHEVAL_VERSION_SPAWNS="$prime/version-spawns" \
    HHEVAL_RESOLVED_VERSIONS="$prime/resolved-versions.tsv" \
    "$ROOT/bin/hol" repl -b "$ROOT/bin/hol.state" \
    <"$DRIVER" >"$replay/worker.log" 2>&1
  printf '%s\t%s\n' "$theory" "$(cat "$prime/spawns")" \
    >>"$TEMP/prime-spawns.tsv"
  printf '%s\t%s\n' "$theory" "$(cat "$replay/spawns")" \
    >>"$TEMP/replay-spawns.tsv"
  printf '%s\t%s\n' "$theory" "$(cat "$prime/version-spawns")" \
    >>"$TEMP/version-spawns.tsv"
  awk -F '\t' -v theory="$theory" 'BEGIN {OFS="\t"}
    {print theory,$0}' "$prime/resolved-versions.tsv" \
    >>"$TEMP/resolved-versions.tsv"
done <"$TEMP/theories"

find "$STATE/seed" -path '*/journal/*.jsonl' -print0 |
  LC_ALL=C sort -z | xargs -0 cat >"$TEMP/seed.jsonl"
find "$PRIME_ROOT" -path '*/journal/*.jsonl' -print0 |
  LC_ALL=C sort -z | xargs -0 cat >"$TEMP/prime.jsonl"
find "$REPLAY_ROOT" -path '*/journal/*.jsonl' -print0 |
  LC_ALL=C sort -z | xargs -0 cat >"$TEMP/replay.jsonl"
[[ "$(wc -l <"$TEMP/seed.jsonl")" == 128 ]]
[[ "$(wc -l <"$TEMP/prime.jsonl")" == 128 ]]
[[ "$(wc -l <"$TEMP/replay.jsonl")" == 128 ]]
version_spawns=$(awk -F '\t' '{n+=$2}END{print n+0}' \
  "$TEMP/version-spawns.tsv")
prime_spawns=$(awk -F '\t' '{n+=$2}END{print n+0}' \
  "$TEMP/prime-spawns.tsv")
replay_spawns=$(awk -F '\t' '{n+=$2}END{print n+0}' \
  "$TEMP/replay-spawns.tsv")
[[ "$version_spawns" == 81 && "$prime_spawns" == 0 &&
  "$replay_spawns" == 0 ]]
[[ "$(wc -l <"$TEMP/resolved-versions.tsv")" == 81 ]]
awk -F '\t' 'NF != 5 || $2 !~ /^(e|vampire|zipperposition)$/ ||
  $3 == "" || $4 == "" || $5 !~ /^(true|false)$/ {exit 1}' \
  "$TEMP/resolved-versions.tsv"
jq -s -e 'length==128 and all(.[];(.slices|length)==24 and
  all(.slices[];.cached==true))' "$TEMP/prime.jsonl" >/dev/null
jq -s -e 'length==128 and all(.[];(.slices|length)==24 and
  all(.slices[];.cached==true))' "$TEMP/replay.jsonl" >/dev/null
cache_manifest "$HAMMER/cache" "$TEMP/cache-after.tsv"
cache_after=$(sha256sum "$TEMP/cache-after.tsv" | cut -d' ' -f1)
cmp "$TEMP/cache-before.tsv" "$TEMP/cache-after.tsv"
[[ "$cache_before" == "$cache_after" ]]
cache_files=$(find "$HAMMER/cache" -type f | wc -l)
cache_bytes=$(find "$HAMMER/cache" -type f -printf '%s\n' |
  awk '{n+=$1}END{print n+0}')
seed_spawns=$(find "$STATE/seed" -name prover-spawns.txt -print0 |
  xargs -0 awk '{n+=$1}END{print n+0}')
cp "$SAMPLE/sample-certificate.json" \
  "$K_RUN/source-sample-certificate.json"
cp "$INPUTS/SHA256SUMS" "$K_RUN/input-SHA256SUMS"
cp "$INPUTS/provers.tsv" "$K_RUN/provers.tsv"
cp "$INPUTS/theory-directories.tsv" "$K_RUN/theory-directories.tsv"
cp "$TEMP/seed.jsonl" "$K_RUN/seed-journal.jsonl"
cp "$TEMP/prime.jsonl" "$K_RUN/prime-journal.jsonl"
cp "$TEMP/replay.jsonl" "$K_RUN/replay-journal.jsonl"
cp "$TEMP/fresh-root-proof.json" "$K_RUN/fresh-root-proof.json"
cp "$TEMP/state-children-before.tsv" "$K_RUN/state-children-before.tsv"
cp "$TEMP/prime-spawns.tsv" "$K_RUN/prime-spawns.tsv"
cp "$TEMP/replay-spawns.tsv" "$K_RUN/replay-spawns.tsv"
cp "$TEMP/version-spawns.tsv" "$K_RUN/version-spawns.tsv"
cp "$TEMP/resolved-versions.tsv" "$K_RUN/resolved-versions.tsv"
printf 'initial-seed\t%s\n' "$seed_spawns" >"$K_RUN/seed-spawns.tsv"
cp "$DRIVER" "$K_RUN/k-paired-driver.sml"
seed_script=$(jq -r '.producing_run_script_sha256' \
  "$K_RUN/seed-certificate.json")
[[ "$(sha256sum "$K_RUN/run-k.sh" | cut -d' ' -f1)" == \
  "$seed_script" ]]
mv "$K_RUN/run-k.sh" "$K_RUN/run-k-seed.sh"
cp "$ROOT/src/holyhammer/tools/phase3-s30v5/run-k.sh" "$K_RUN/run-k.sh"
cp "$ROOT/src/holyhammer/tools/phase3-s30v5/finish-k.sh" "$K_RUN/finish-k.sh"
cp "$TEMP/cache-before.tsv" "$K_RUN/cache-before.tsv"
cp "$TEMP/cache-after.tsv" "$K_RUN/cache-after.tsv"
jq -n --arg state "$STATE" \
  --arg sample "$(sha256sum "$K_RUN/source-sample-certificate.json" |
  cut -d' ' -f1)" \
  --arg subset "$(sha256sum "$K_RUN/subset.tsv" | cut -d' ' -f1)" \
  --arg seed "$(sha256sum "$K_RUN/seed-journal.jsonl" | cut -d' ' -f1)" \
  --arg prime "$(sha256sum "$K_RUN/prime-journal.jsonl" | cut -d' ' -f1)" \
  --arg replay "$(sha256sum "$K_RUN/replay-journal.jsonl" |
  cut -d' ' -f1)" --arg cache "$cache_before" \
  --arg fresh "$(sha256sum "$K_RUN/fresh-root-proof.json" |
    cut -d' ' -f1)" \
  --arg seed_script "$(sha256sum "$K_RUN/run-k-seed.sh" |
    cut -d' ' -f1)" \
  --arg run_script "$(sha256sum "$K_RUN/run-k.sh" | cut -d' ' -f1)" \
  --arg finish_script "$(sha256sum "$K_RUN/finish-k.sh" |
    cut -d' ' -f1)" \
  --arg current_script "$(sha256sum "$K_RUN/run-k-current.sh" |
    cut -d' ' -f1)" \
  --arg input_manifest "$(sha256sum "$K_RUN/input-SHA256SUMS" |
    cut -d' ' -f1)" \
  --arg provers "$(sha256sum "$K_RUN/provers.tsv" | cut -d' ' -f1)" \
  --arg theories "$(sha256sum "$K_RUN/theory-directories.tsv" |
    cut -d' ' -f1)" \
  --argjson seed_spawns "$seed_spawns" \
  --argjson version_spawns "$version_spawns" \
  --argjson prime_spawns "$prime_spawns" \
  --argjson replay_spawns "$replay_spawns" \
  --argjson files "$cache_files" --argjson bytes "$cache_bytes" '
  {schema:"hh-task12-k-cache-witness-v6",status:"complete",
   sample_certificate_sha256:$sample,subset_goals:128,
   subset_sha256:$subset,seed_journal_sha256:$seed,
   prime_journal_sha256:$prime,
   replay_journal_sha256:$replay,seed_prover_spawns:$seed_spawns,
   version_resolution_spawns:$version_spawns,
   prime_cache_check_spawns:$prime_spawns,
   replay_prover_spawns:$replay_spawns,
   slices_per_goal:24,cached_slices_per_goal:24,
   filter_keyed_problem_filters:["knn","mash","mepo","mesh"],
   same_cache_for_seed_and_replay:true,
   seeded_cache_manifest_sha256:$cache,
   cache_manifest_before_sha256:$cache,
   cache_manifest_after_sha256:$cache,
   cache_files:$files,cache_bytes:$bytes,
   producing_scripts:{seed_run_k_sha256:$seed_script,
     finish_k_sha256:$finish_script,
     run_k_current_sha256:$current_script},
   maintained_workflow:{run_k_sha256:$run_script},
   producing_inputs:{input_manifest_sha256:$input_manifest,
     provers_sha256:$provers,theory_directories_sha256:$theories},
   state_root:$state,
   fresh_root_proof_sha256:$fresh,
   prime_root:($state+"/prime-cache-check"),
   replay_root:($state+"/replay-witness"),
   prime_and_replay_roots_absent_before_run:true,
   prime_and_replay_non_resume:true,
   cache_decomposition:{requested_cells:3072,cached_replay_cells:3072,
     physical_cache_files:$files,physical_cache_bytes:$bytes,
     filter_cells:{knn:2048,mash:256,mepo:256,mesh:512}},
   cache_unmodified_by_replay:true,state_removed_after_witness:true,
   explicit_version_resolution:{provers:["e","vampire","zipperposition"],
     processes:27,expected_spawns:81,observed_spawns:$version_spawns,
     completed_before_prime_reset:true},
   tuning_performed:false}
' >"$K_RUN/certificate.json"
chmod -R u+w "$STATE"
"$ROOT/src/holyhammer/tools/phase3-s30v5/safe-remove-state.sh" "$STATE"
[[ ! -e "$STATE" ]]
(cd "$K_RUN" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$K_RUN/SHA256SUMS"
chmod -R a-w "$K_RUN"
