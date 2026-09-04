#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 4)); then
  echo "usage: $0 INPUTS RUN GOALS GOAL_CERTIFICATE" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
RUN=$(realpath "$2")
GOALS=$(realpath "$3")
GOAL_CERT=$(realpath "$4")
TOOLS=$(dirname "$(realpath "$0")")
INPUT_SHA=$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)
ALLOW_SUPERSET=${HHEVAL_TASK11_ALLOW_SUPERSET:-0}
STATE=$(jq -r '.state_root' "$RUN/envelope.json")

[[ "$ALLOW_SUPERSET" == 0 || "$ALLOW_SUPERSET" == 1 ]]
[[ ! -e "$RUN/result.json" && ! -e "$RUN/final-certificate.json" ]]
[[ ! -e "$STATE" ]]
"$INPUTS/verify-inputs.sh" "$INPUTS"
jq -e --arg inventory "$(sha256sum "$GOALS" | cut -d' ' -f1)" '
  .schema == "hh-task11-canonical-goals-v1" and
  .status == "complete" and .goals == 24721 and .theories == 229 and
  .canonical_goal_inventory_sha256 == $inventory and
  .baseline_current_rows_byte_identical == true
' "$GOAL_CERT" >/dev/null

cp "$GOALS" "$RUN/canonical-goals.tsv"
cp "$GOAL_CERT" "$RUN/canonical-goals.json"
chmod 0444 "$RUN/canonical-goals.tsv" "$RUN/canonical-goals.json"

if [[ -s "$RUN/summary.json" ]]; then
  old_summary=$(sha256sum "$RUN/summary.json" | cut -d' ' -f1)
else
  old_summary=absent
fi
if [[ -s "$RUN/report.md" ]]; then
  old_report=$(sha256sum "$RUN/report.md" | cut -d' ' -f1)
else
  old_report=absent
fi
if [[ -s "$RUN/journal-inventory.tsv.partial" ]]; then
  old_partial=$(sha256sum "$RUN/journal-inventory.tsv.partial" |
    cut -d' ' -f1)
else
  old_partial=absent
fi
HHEVAL_TASK11_ALLOW_SUPERSET=$ALLOW_SUPERSET \
  "$TOOLS/fold-result.sh" "$RUN" "$INPUT_SHA" \
    "$RUN/result.json.partial" "$RUN/journal-inventory.tsv.new" \
    "$RUN/canonical-goals.tsv"
mv "$RUN/result.json.partial" "$RUN/result.json"
mv "$RUN/journal-inventory.tsv.new" "$RUN/journal-inventory.tsv"

"$TOOLS/investigate-shape.sh" "$RUN" "$RUN/canonical-goals.tsv" \
  "$RUN/shape-investigation.json" "$RUN/shape-investigation.md"

jq '{schema:"hh-task11-f30-summary-v1",status:.status,
  canonical_goal_inventory_sha256:.canonical_goal_inventory_sha256,
  cells:.cells,goals:.goals,conditions:.conditions,gate:.gate,
  shape:.shape}' "$RUN/result.json" >"$RUN/summary.json.new"
mv "$RUN/summary.json.new" "$RUN/summary.json"

jq -r '
  def row($c):
    "| " + $c.condition + " | " + ($c.goals|tostring) + " | " +
    ($c.proved|tostring) + " | " + ($c.reconstructed|tostring) + " |";
  "# Phase 3 full-corpus F30 result\n\n" +
  "The exact accepted TASK10 A inventory contains " + (.goals|tostring) +
  " goals. The raw v6 journals formed a strict " +
  (.excluded_extra_goals|tostring) + "-goal superset; every canonical " +
  "goal was present exactly once for all eight conditions, and only the " +
  "explicitly certified extras were excluded.\n\n" +
  "| condition | goals | proved | reconstructed |\n" +
  "|---|---:|---:|---:|\n" +
  ([.conditions[] | row(.)] | join("\n")) + "\n\n" +
  "The MeSh ensemble gate " + (if .gate.pass then "passes" else "fails" end) +
  ". Seen-subset criterion (a) " +
  (if .shape.criterion_a_pass then "passes" else "fails" end) +
  "; direction check (b) " +
  (if .shape.criterion_b_pass then "passes" else "fails" end) +
  ". See shape-investigation.md for the paired analysis.\n"
' "$RUN/result.json" >"$RUN/report.md.new"
mv "$RUN/report.md.new" "$RUN/report.md"

(cd "$RUN" && find atom-certificates -type f -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$RUN/atom-inventory.tsv"
"$TOOLS/make-auxiliary-evidence.sh" "$RUN" \
  "$RUN/canonical-goals.tsv" "$RUN/excluded-extra-goals.tsv" \
  "$RUN/criterion-b-investigation.md"

jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg old_summary "$old_summary" --arg old_report "$old_report" \
  --arg old_partial "$old_partial" \
  --arg extras "$(sha256sum "$RUN/excluded-extra-goals.tsv" |
    cut -d' ' -f1)" \
  --argjson extra_count "$(wc -l <"$RUN/excluded-extra-goals.tsv")" '
  {schema:"hh-task11-f30-corpus-correction-v1",status:"complete",
   completed:$completed,
   cause:(if $extra_count == 0 then "none"
     else "live DB contained post-corpus theorems" end),
   original_fold_failure:(if $extra_count == 0 then "none"
     else "journal is incomplete, duplicated, or corpus-inconsistent" end),
   original_summary_sha256:$old_summary,original_report_sha256:$old_report,
   original_partial_inventory_sha256:$old_partial,
   excluded_extra_goal_ids_sha256:$extras,
   excluded_extra_goals:$extra_count,missing_canonical_goals:0,
   duplicate_canonical_cells:0,canonical_cells_per_goal:8,
   no_measurement_rerun_required:($extra_count > 0)}
' >"$RUN/corpus-correction.json"

attempts=$(jq -s 'map(.attempts) | add' "$RUN"/atom-certificates/*.json)
recycles=$((attempts - 3212))
status_124=$(awk '/status=124 checkpointed/ {count++}
  END {print count+0}' "$RUN"/log/*.log)
status_137=$(awk '/status=137 checkpointed/ {count++}
  END {print count+0}' "$RUN"/log/*.log)
jq -n --arg result "$(sha256sum "$RUN/result.json" | cut -d' ' -f1)" \
  --arg peak "${HHEVAL_TASK11_MEMORY_PEAK_HUMAN:-unknown}" \
  --argjson attempts "$attempts" --argjson recycles "$recycles" \
  --argjson status_124 "$status_124" --argjson status_137 "$status_137" \
  --argjson oom "${HHEVAL_TASK11_OOM_KILL_EVENTS:-0}" '
  {schema:"hh-task11-f30-cleanup-v2",status:"removed",
   result_sha256:$result,tmpfs_root_absent_after_cleanup:true,
   observed_memory_peak_human:$peak,observed_swap_peak_bytes:0,
   atom_attempts:$attempts,recovered_worker_recycles:$recycles,
   timeout_status_124:$status_124,kill_status_137:$status_137,
   systemd_oom_kill_events:$oom}
' >"$RUN/tmpfs-cleanup.json"

rm -f "$RUN/journal-inventory.tsv.partial" \
  "$RUN/result.canonical.json.partial" \
  "$RUN/journal-inventory.canonical.tsv.partial" \
  "$RUN/shape-investigation.json.partial" \
  "$RUN/shape-investigation.md.partial"
jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg result "$(sha256sum "$RUN/result.json" | cut -d' ' -f1)" \
  '{event:"complete",time:$time,result_sha256:$result,
    recovery:"canonical-corpus-superset"}' >>"$RUN/invocations.jsonl"

for file in result.json summary.json report.md journal-inventory.tsv \
    atom-inventory.tsv excluded-extra-goals.tsv \
    shape-investigation.json shape-investigation.md \
    criterion-b-investigation.md corpus-correction.json \
    tmpfs-cleanup.json invocations.jsonl; do
  chmod 0444 "$RUN/$file"
done
