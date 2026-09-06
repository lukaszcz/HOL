#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 5)); then
  echo "usage: $0 INPUT STATE OUTPUT WORKER MAX_ATOMS" >&2
  exit 2
fi

input=$(realpath "$1")
state=$2
output=$3
worker=$(realpath "$4")
max_atoms=$5
tools=$(dirname "$(realpath "$0")")
[[ "$max_atoms" =~ ^[1-9][0-9]*$ && ! -e "$output" ]]
base="/run/user/$(id -u)/holyhammer-phase3-task12"
case "$state" in
  "$base"/phase3-task12-reference-*) ;;
  *) echo "reference state is not an exact TASK12 child" >&2; exit 2 ;;
esac
[[ ! -e "$state" && ! -L "$state" ]]
export HHEVAL_REFERENCE_INPUT="$input"

while IFS=$'\t' read -r mode expected path extra; do
  [[ -z "${extra-}" && "$mode" == file ]]
  [[ "$(sha256sum "$input/$path" | cut -d' ' -f1)" == "$expected" ]]
done <"$input/runtime-dependencies.tsv"

temp=$(mktemp -d)
cleanup() {
  rm -rf "$temp"
  "$tools/safe-remove-state.sh" "$state" 2>/dev/null || true
}
trap cleanup EXIT HUP INT TERM
mkdir -p "$state" "$output/journal" "$output/atom-certificates"
mkdir "$state/hammer"
export HHEVAL_REFERENCE_HAMMER_DIR="$state/hammer"
if [[ -f "$input/runtime-root-certificate.json" ]]; then
  root=${HHEVAL_REFERENCE_HOL_ROOT:?HHEVAL_REFERENCE_HOL_ROOT is not set}
  "$input/verify-runtime-root.sh" "$root" "$input"
  validation_path="$state/runtime-root-validated.sha256"
  sha256sum "$input/runtime-root-certificate.json" \
    >"$validation_path"
  export HHEVAL_REFERENCE_RUNTIME_VALIDATION="$validation_path"
fi
jq -Rr '
  def sample_hash:
    reduce (explode[]) as $byte
      (0; ((. * 65599 + $byte) % 2147483647));
  split("\t") as $row | [$row[0],$row[1],($row[1]|sample_hash)]|@tsv
' "$input/canonical-goals.tsv" >"$temp/hashes.tsv"
: >"$output/resume-events.tsv"
: >"$output/atom-inventory.tsv"

count=0
while IFS=$'\t' read -r atom theory part parts directory extra; do
  [[ -z "${extra-}" ]]
  ((count >= max_atoms)) && break
  ((count += 1))
  awk -F '\t' -v theory="$theory" -v part="$part" -v parts="$parts" '
    $1==theory && $3%parts==part {print theory "\t" $2}
  ' "$temp/hashes.tsv" >"$temp/goals.tsv"
  attempt=0
  ((attempt += 1))
  scratch="$state/$atom-attempt-$attempt"
  mkdir "$scratch"
  if [[ ! -s "$temp/goals.tsv" ]]; then
    : >"$scratch/journal.jsonl"
  else
    while :; do
      ((attempt > 1)) && mkdir "$scratch"
      set +e
      timeout --foreground 600 "$worker" "$atom" "$attempt" \
        "$temp/goals.tsv" "$scratch/journal.jsonl"
      status=$?
      set -e
      if ((status == 0)); then
        break
      fi
      printf '%s\t%s\tcause-and-status-unretained\n' "$atom" "$attempt" \
        >>"$output/resume-events.tsv"
      rm -rf "$scratch"
      ((attempt < 3)) || exit 1
      ((attempt += 1))
      scratch="$state/$atom-attempt-$attempt"
    done
  fi
  if [[ -s "$scratch/journal.jsonl" ]]; then
    jq -er --arg theory "$theory" '
      if type == "object" and .thy == $theory and
        (.goal_id|type) == "string"
      then [.thy,.goal_id]|@tsv
      else error("malformed or cross-theory worker row") end
    ' "$scratch/journal.jsonl" >"$temp/actual-goals.tsv"
  else
    : >"$temp/actual-goals.tsv"
  fi
  cut -f2 "$temp/goals.tsv" | LC_ALL=C sort \
    >"$temp/expected-goal-set.tsv"
  cut -f2 "$temp/actual-goals.tsv" | LC_ALL=C sort \
    >"$temp/actual-goal-set.tsv"
  actual_unique=$(LC_ALL=C sort -u "$temp/actual-goal-set.tsv" | wc -l)
  expected_unique=$(LC_ALL=C sort -u "$temp/expected-goal-set.tsv" | wc -l)
  [[ "$(wc -l <"$temp/actual-goal-set.tsv")" == "$actual_unique" ]]
  [[ "$(wc -l <"$temp/expected-goal-set.tsv")" == "$expected_unique" ]]
  cmp "$temp/expected-goal-set.tsv" "$temp/actual-goal-set.tsv"
  cells=$(wc -l <"$scratch/journal.jsonl")
  [[ "$cells" == "$(wc -l <"$temp/actual-goals.tsv")" ]]
  journal_hash=$(sha256sum "$scratch/journal.jsonl" | cut -d' ' -f1)
  goal_set_hash=$(sha256sum "$temp/actual-goal-set.tsv" | cut -d' ' -f1)
  partial="$output/journal/$atom.jsonl.partial.$$"
  cp "$scratch/journal.jsonl" "$partial"
  mv "$partial" "$output/journal/$atom.jsonl"
  certificate_partial="$output/atom-certificates/$atom.json.partial.$$"
  jq -n --arg atom "$atom" --arg theory "$theory" \
    --arg hash "$journal_hash" --arg goal_set "$goal_set_hash" \
    --argjson cells "$cells" \
    --argjson attempt "$attempt" '
    {schema:"hh-task12-reference-atom-v2",status:"complete",atom:$atom,
     theory:$theory,cells:$cells,attempts:$attempt,journal_sha256:$hash,
     expected_goal_set_sha256:$goal_set,
     actual_worker_row_order_sha256:$hash,durable_copyback:"atomic",
     certificate_publish:"output-local-partial-then-rename"}
  ' >"$certificate_partial"
  certificate_hash=$(sha256sum "$certificate_partial" | cut -d' ' -f1)
  mv "$certificate_partial" "$output/atom-certificates/$atom.json"
  printf '%s\t%s\t%s\t%s\t%s\n' "$atom" "$cells" "$attempt" \
    "$journal_hash" "$certificate_hash" >>"$output/atom-inventory.tsv"
  rm -rf "$scratch"
done <"$input/atoms.tsv"
[[ "$count" == "$max_atoms" ]]
if [[ -f "$input/runtime-root-certificate.json" ]]; then
  "$input/verify-runtime-root.sh" "$root" "$input"
fi
"$tools/safe-remove-state.sh" "$state"
inventory_hash=$(sha256sum "$output/atom-inventory.tsv" | cut -d' ' -f1)
resume_hash=$(sha256sum "$output/resume-events.tsv" | cut -d' ' -f1)
dependency_hash=$(sha256sum "$input/runtime-dependencies.tsv" |
  cut -d' ' -f1)
restart_events=$(wc -l <"$output/resume-events.tsv")
jq -n --arg state "$state" --arg inventory "$inventory_hash" \
  --arg resume "$resume_hash" --arg dependencies "$dependency_hash" \
  --argjson atoms "$count" --argjson restarts "$restart_events" '
  {schema:"hh-task12-reference-terminal-v1",status:"complete",
   completed_atoms:$atoms,restart_resume_events:$restarts,
   atom_inventory_sha256:$inventory,resume_events_sha256:$resume,
   runtime_dependencies_sha256:$dependencies,fixed_atom_order:true,
   atomic_copyback:true,state_root:$state,state_root_removed:true}
' >"$output/terminal-certificate.json.partial"
mv "$output/terminal-certificate.json.partial" \
  "$output/terminal-certificate.json"
if [[ -n "${HHEVAL_REFERENCE_SYSTEMD_UNIT-}" ]]; then
  "$tools/capture-systemd-terminal.sh" \
    "$HHEVAL_REFERENCE_SYSTEMD_UNIT" \
    "$output/terminal-systemd.jsonl.partial"
  mv "$output/terminal-systemd.jsonl.partial" \
    "$output/terminal-systemd.jsonl"
fi
trap - EXIT HUP INT TERM
rm -rf "$temp"
chmod -R a-w "$output"
