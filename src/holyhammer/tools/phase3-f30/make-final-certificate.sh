#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 3)); then
  echo "usage: $0 RUN INPUT_SHA OUTPUT" >&2
  exit 2
fi

RUN=$(realpath "$1")
INPUT_SHA=$2
OUTPUT=$3
TOOLS=$(dirname "$(realpath "$0")")
for file in run.json envelope.json envelope-start.json atoms.tsv \
    journal-inventory.tsv atom-inventory.tsv result.json summary.json \
    report.md canonical-goals.tsv canonical-goals.json \
    shape-investigation.json criterion-b-investigation.md \
    excluded-extra-goals.tsv corpus-correction.json tmpfs-cleanup.json \
    terminal-service.json terminal-service.log invocations.jsonl \
    verifier/SHA256SUMS; do
  [[ -s "$RUN/$file" && ! -L "$RUN/$file" ]]
done

jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg input "$INPUT_SHA" \
  --arg run "$(sha256sum "$RUN/run.json" | cut -d' ' -f1)" \
  --arg envelope "$(sha256sum "$RUN/envelope.json" | cut -d' ' -f1)" \
  --arg envelope_start "$(sha256sum "$RUN/envelope-start.json" |
    cut -d' ' -f1)" \
  --arg atoms "$(sha256sum "$RUN/atoms.tsv" | cut -d' ' -f1)" \
  --arg journals "$(sha256sum "$RUN/journal-inventory.tsv" |
    cut -d' ' -f1)" \
  --arg atom_inventory "$(sha256sum "$RUN/atom-inventory.tsv" |
    cut -d' ' -f1)" \
  --arg result "$(sha256sum "$RUN/result.json" | cut -d' ' -f1)" \
  --arg summary "$(sha256sum "$RUN/summary.json" | cut -d' ' -f1)" \
  --arg report "$(sha256sum "$RUN/report.md" | cut -d' ' -f1)" \
  --arg goals "$(sha256sum "$RUN/canonical-goals.tsv" | cut -d' ' -f1)" \
  --arg goal_cert "$(sha256sum "$RUN/canonical-goals.json" |
    cut -d' ' -f1)" \
  --arg shape "$(sha256sum "$RUN/shape-investigation.json" |
    cut -d' ' -f1)" \
  --arg criterion_b "$(sha256sum "$RUN/criterion-b-investigation.md" |
    cut -d' ' -f1)" \
  --arg excluded "$(sha256sum "$RUN/excluded-extra-goals.tsv" |
    cut -d' ' -f1)" \
  --arg correction "$(sha256sum "$RUN/corpus-correction.json" |
    cut -d' ' -f1)" \
  --arg cleanup "$(sha256sum "$RUN/tmpfs-cleanup.json" | cut -d' ' -f1)" \
  --arg terminal "$(sha256sum "$RUN/terminal-service.json" |
    cut -d' ' -f1)" \
  --arg terminal_log "$(sha256sum "$RUN/terminal-service.log" |
    cut -d' ' -f1)" \
  --arg verifier "$(sha256sum "$RUN/verifier/SHA256SUMS" |
    cut -d' ' -f1)" \
  --arg invocations "$(sha256sum "$RUN/invocations.jsonl" |
    cut -d' ' -f1)" \
  --arg maker "$(sha256sum "$0" | cut -d' ' -f1)" \
  --arg fold "$(sha256sum "$TOOLS/fold-result.sh" | cut -d' ' -f1)" \
  --arg investigation "$(sha256sum "$TOOLS/investigate-shape.sh" |
    cut -d' ' -f1)" '
  {schema:"hh-task11-f30-final-v4",status:"complete",
   completed:$completed,input_inventory_sha256:$input,
   run_header_sha256:$run,envelope_sha256:$envelope,
   start_envelope_sha256:$envelope_start,atom_plan_sha256:$atoms,
   journal_inventory_sha256:$journals,
   atom_inventory_sha256:$atom_inventory,result_sha256:$result,
   summary_sha256:$summary,report_sha256:$report,
   canonical_goal_inventory_sha256:$goals,
   canonical_goal_certificate_sha256:$goal_cert,
   shape_investigation_sha256:$shape,
   criterion_b_investigation_sha256:$criterion_b,
   excluded_extra_goal_ids_sha256:$excluded,
   corpus_correction_sha256:$correction,cleanup_sha256:$cleanup,
   terminal_service_sha256:$terminal,
   terminal_service_log_sha256:$terminal_log,
   verifier_inventory_sha256:$verifier,
   invocations_sha256:$invocations,certificate_tool_sha256:$maker,
   fold_tool_sha256:$fold,shape_tool_sha256:$investigation}
' >"$OUTPUT"
chmod 0444 "$OUTPUT"
