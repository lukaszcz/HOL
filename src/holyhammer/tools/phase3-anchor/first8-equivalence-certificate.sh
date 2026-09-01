#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 2 || {
  echo "usage: $0 RUN_OUTPUT CERTIFICATE" >&2
  exit 2
}
run=$1
certificate=$2
temporary=$certificate.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM
sha () { sha256sum "$1" | awk '{print $1}'; }

for required in run.json result.json baseline-validation.json
do
  test -s "$run/$required" && test ! -L "$run/$required"
done
counters=$(jq -e '.status == "complete" | select(.)' \
  "$run/result.json" >/dev/null && jq '.counters' "$run/result.json")
members=$(jq -er '.theories' <<<"$counters")
goals=$(jq -er '.goals' <<<"$counters")
rows=$((goals * 8))
test "$(find "$run/current-first8" -type f -name '*.tsv' | wc -l)" \
  -eq "$members"
test "$(find "$run/current-first8" -type f -name '*.tsv' -print0 |
  xargs -0 -n1 tail -n +2 | wc -l)" -eq "$rows"
test "$(find "$run/current-rankings" -type f -name '*.ranking' |
  wc -l)" -eq "$goals"
chains=$(find "$run/current-checkpoint-chains" -type f \
  -name validation.json | wc -l)
atoms=$(find "$run/current-checkpoint-chains" -type f \
  -name receipt.json | wc -l)
test "$chains" -eq "$members"
jq -e '.counters.premise == 0 and .counters.request == 0 and
  .counters.internal == 0 and .counters.prover_spawns == 0' \
  "$run/baseline-validation.json" >/dev/null
jq -e '.mismatches == 0 and .binding_mismatches == 0 and
  .prover_spawns == 0' <<<"$counters" >/dev/null

jq -n --arg completed "$(date -u +%FT%TZ)" \
  --arg experiment "$(basename "$run")" \
  --arg run "$(sha "$run/run.json")" \
  --arg result "$(sha "$run/result.json")" \
  --argjson members "$members" --argjson goals "$goals" \
  --argjson rows "$rows" --argjson chains "$chains" \
  --argjson atoms "$atoms" '
  {schema:"hh-current-first8-checkpoint-equivalence-v2",status:"exact",
   completed:$completed,experiment:$experiment,members:$members,
   goals:$goals,rows:$rows,profiles_per_goal:8,
   checkpoint_chains:$chains,checkpoint_atoms:$atoms,
   ranking_journals:$goals,model_derived_independently:true,
   gap_free_db_order_coverage:true,canonical_fold_complete:true,
   mismatch_binding_spawn_counters:0,run_header_sha256:$run,
   result_sha256:$result}
' >"$temporary"
mv "$temporary" "$certificate"
chmod 0444 "$certificate"
trap - EXIT HUP INT TERM
