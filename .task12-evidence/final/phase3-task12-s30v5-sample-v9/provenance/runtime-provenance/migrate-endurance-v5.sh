#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 2)); then
  echo "usage: $0 SEALED_SAMPLE OUTPUT" >&2
  exit 2
fi

source_sample=$(realpath "$1")
output=$2
[[ ! -e "$output" ]]
mkdir "$output"
cp -a "$source_sample/endurance" "$output/endurance"
cp "$source_sample/canonical-goals.tsv" "$source_sample/schedule.tsv" \
  "$source_sample/s30v3-sample.jsonl" \
  "$source_sample/sample-certificate.json" "$output/"
chmod -R u+w "$output"
terminal="$output/endurance/terminal-certificate.json"
resume="$output/endurance/resume-events.tsv"
awk -F '\t' 'BEGIN {OFS="\t"} NF == 4 {
  print $1,$2,$3,"cause-and-status-unknown"; next} {exit 1}' "$resume" \
  >"$resume.partial"
mv "$resume.partial" "$resume"
jq '{schema:"hh-task12-endurance-terminal-v4",status,unit,invocation_id,
  structured_journal_sha256,atom_plan_sha256,atom_inventory_sha256,
  concatenated_journal_sha256,completed_atoms,completed_cells,empty_atoms,
  attempts,last_atom,fixed_atom_order,atomic_copyback,resume_events,
  start_realtime_usec,stop_realtime_usec,duration_usec,cpu_usage_nsec,
  memory_peak_bytes,memory_swap_peak_bytes,state_root,state_root_removed,
  restart_resume_events,atomic_continuity,
  restart_causes_retained:false,restart_statuses_retained:false,
  restart_cause_and_status:"unknown"}' "$terminal" \
  >"$terminal.partial"
mv "$terminal.partial" "$terminal"
(cd "$output" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$output/SHA256SUMS"
chmod -R a-w "$output"
