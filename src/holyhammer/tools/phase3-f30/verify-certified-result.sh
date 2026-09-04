#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 2)); then
  echo "usage: $0 INPUTS RUN" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
RUN=$(realpath "$2")
TOOLS=$(dirname "$(realpath "$0")")
INPUT_SHA=$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)
TEMP=$(mktemp -d)
trap 'rm -rf "$TEMP"' EXIT HUP INT TERM

[[ -s "$RUN/verifier/SHA256SUMS" && ! -L "$RUN/verifier/SHA256SUMS" ]]
(cd "$RUN/verifier" && sha256sum -c SHA256SUMS >/dev/null)
verifier_inventory_sha=$(sha256sum "$RUN/verifier/SHA256SUMS" |
  cut -d' ' -f1)

"$TOOLS/verify-inputs.sh" "$INPUTS"
for file in run.json envelope.json envelope-start.json atoms.tsv \
    result.json summary.json \
    report.md canonical-goals.tsv canonical-goals.json \
    shape-investigation.json shape-investigation.md \
    criterion-b-investigation.md journal-inventory.tsv \
    atom-inventory.tsv excluded-extra-goals.tsv invocations.jsonl \
    corpus-correction.json tmpfs-cleanup.json terminal-service.json \
    terminal-service.log final-certificate.json; do
  [[ -s "$RUN/$file" && ! -L "$RUN/$file" ]]
done
[[ "$(wc -l <"$RUN/atoms.tsv")" == 3212 ]]
[[ "$(wc -l <"$RUN/canonical-goals.tsv")" == 24721 ]]
extra_count=$(jq -r '.excluded_extra_goals' "$RUN/result.json")
[[ "$(wc -l <"$RUN/excluded-extra-goals.tsv")" == "$extra_count" ]]
[[ "$(sha256sum "$RUN/excluded-extra-goals.tsv" | cut -d' ' -f1)" == \
   "$(jq -r '.excluded_extra_goal_ids_sha256' "$RUN/result.json")" ]]
jq -e --arg goals "$(sha256sum "$RUN/canonical-goals.tsv" |
    cut -d' ' -f1)" '
  .schema == "hh-task11-canonical-goals-v1" and
  .status == "complete" and .goals == 24721 and .theories == 229 and
  .canonical_goal_inventory_sha256 == $goals and
  .task10_final_acceptance_sha256 ==
    "3ddeed2ae8219688e5a59ef66e23c24b5b78aae07beecaf9356fae2e9e3e8313" and
  .task10_final_certificate_sha256 ==
    "4a9f965a6571843a1b36abda51aa973e531ae20ecc42e68eaa9b0e10cf653660" and
  .task10_independent_fold_sha256 ==
    "8b2504def61b2395c59870fa600e2d5ea2986e3824fee0263194ba3aa554757a" and
  .canonical_sorted_anchor_body_sha256 ==
    "424c40478df3fe96dfca9afc0d5db016a9c0c5126b37e2ecf98f93af0213982d"
' "$RUN/canonical-goals.json" >/dev/null
corrected=$(jq -r '.strict_superset_corrected' "$RUN/result.json")
if [[ "$corrected" == true ]]; then
  allow_superset=1
else
  allow_superset=0
fi

HHEVAL_TASK11_ALLOW_SUPERSET=$allow_superset \
  "$TOOLS/fold-result.sh" "$RUN" \
  "$INPUT_SHA" "$TEMP/result.json" "$TEMP/journal-inventory.tsv" \
  "$RUN/canonical-goals.tsv"
cmp "$TEMP/result.json" "$RUN/result.json"
cmp "$TEMP/journal-inventory.tsv" "$RUN/journal-inventory.tsv"
"$TOOLS/investigate-shape.sh" "$RUN" "$RUN/canonical-goals.tsv" \
  "$TEMP/shape.json" "$TEMP/shape.md"
cmp "$TEMP/shape.json" "$RUN/shape-investigation.json"
cmp "$TEMP/shape.md" "$RUN/shape-investigation.md"
"$TOOLS/make-auxiliary-evidence.sh" "$RUN" \
  "$RUN/canonical-goals.tsv" "$TEMP/excluded-extra-goals.tsv" \
  "$TEMP/criterion-b-investigation.md"
cmp "$TEMP/excluded-extra-goals.tsv" "$RUN/excluded-extra-goals.tsv"
cmp "$TEMP/criterion-b-investigation.md" \
  "$RUN/criterion-b-investigation.md"

input_commit=$(jq -r '.main.commit' "$INPUTS/top-provenance.json")
input_diff=$(jq -r '.main.tracked_diff_sha256' \
  "$INPUTS/top-provenance.json")
run_sha=$(sha256sum "$RUN/run.json" | cut -d' ' -f1)
result_sha=$(sha256sum "$RUN/result.json" | cut -d' ' -f1)
start_sha=$(sha256sum "$RUN/envelope-start.json" | cut -d' ' -f1)
terminal_sha=$(sha256sum "$RUN/terminal-service.json" | cut -d' ' -f1)
terminal_log_sha=$(sha256sum "$RUN/terminal-service.log" | cut -d' ' -f1)
cleanup_sha=$(sha256sum "$RUN/tmpfs-cleanup.json" | cut -d' ' -f1)
service_started=$(rg -F 'Started phase3-task11-f30-v6.service' \
  "$RUN/terminal-service.log" | awk '{print $1}')
service_exited=$(rg -F \
  'phase3-task11-f30-v6.service: Main process exited, code=exited,' \
  "$RUN/terminal-service.log" | awk '{print $1}')
[[ "$(printf '%s\n' "$service_started" | wc -l)" == 1 ]]
[[ "$(printf '%s\n' "$service_exited" | wc -l)" == 1 ]]
jq -e --arg input "$INPUT_SHA" --arg run "$run_sha" \
  --arg commit "$input_commit" --arg diff "$input_diff" '
  .schema == "hh-task11-f30-envelope-v1" and .status == "running" and
  .input_inventory_sha256 == $input and .run_header_sha256 == $run and
  .hol_commit == $commit and .tracked_source_patch_sha256 == $diff and
  .initial_cache_files == 0 and .isolated_caches == true and
  .resumable_journals == true and
  .envelope == {cpu_quota_cores:32,memory_high_bytes:133143986176,
    memory_max_bytes:137438953472,memory_swap_max_bytes:0,
    worker_recycle_seconds:600,worker_slots:32,chunk_target_goals:8,
    tmpfs_scratch:true,durable_copyback:true}
' "$RUN/envelope-start.json" >/dev/null
jq -e --arg input "$INPUT_SHA" --arg run "$run_sha" \
  --arg commit "$input_commit" --arg diff "$input_diff" \
  --arg result "$result_sha" --arg terminal "$terminal_sha" \
  --arg terminal_log "$terminal_log_sha" '
  .schema == "hh-task11-f30-envelope-v1" and .status == "complete" and
  .input_inventory_sha256 == $input and .run_header_sha256 == $run and
  .hol_commit == $commit and .tracked_source_patch_sha256 == $diff and
  .result_sha256 == $result and .initial_cache_files == 0 and
  .isolated_caches == true and .resumable_journals == true and
  .envelope == {cpu_quota_cores:32,memory_high_bytes:133143986176,
    memory_max_bytes:137438953472,memory_swap_max_bytes:0,
    worker_recycle_seconds:600,worker_slots:32,chunk_target_goals:8,
    tmpfs_scratch:true,durable_copyback:true} and
  .terminal_service.certificate == "terminal-service.json" and
  .terminal_service.certificate_sha256 == $terminal and
  .terminal_service.log_sha256 == $terminal_log and
  .terminal_service.result == "exit-code" and
  .terminal_service.main_exit_status == 5 and
  .terminal_service.memory_peak_human == "107.3G" and
  .terminal_service.memory_swap_peak_bytes == 0 and
  .terminal_service.journal_oom_notifications == 26 and
  .terminal_service.cgroup_oom_kill_events == 19 and
  .terminal_service.worker_status_137_recycles == 26 and
  .terminal_service.recovered_after_original_fold_rejection == true
' "$RUN/envelope.json" >/dev/null
jq -e --arg log "$terminal_log_sha" --arg start "$start_sha" \
  --arg service_started "$service_started" \
  --arg service_exited "$service_exited" \
  --arg result "$result_sha" --arg cleanup "$cleanup_sha" '
  .schema == "hh-task11-terminal-service-v1" and .status == "complete" and
  .service == "phase3-task11-f30-v6.service" and
  .service_started == $service_started and
  .service_exited == $service_exited and
  .service_result == "exit-code" and .main_exit_status == 5 and
  .original_fold_outcome == "rejected strict corpus superset" and
  .memory_peak_human == "107.3G" and .memory_swap_peak_bytes == 0 and
  .journal_oom_notifications == 26 and .cgroup_oom_kill_events == 19 and
  .worker_status_137_recycles == 26 and .terminal_log_sha256 == $log and
  .start_envelope_sha256 == $start and
  .recovered_result_sha256 == $result and .cleanup_sha256 == $cleanup
' "$RUN/terminal-service.json" >/dev/null
[[ "$(rg -c 'A process of this unit has been killed by the OOM killer' \
  "$RUN/terminal-service.log")" == 26 ]]
[[ "$(rg -c 'journal is incomplete, duplicated, or corpus-inconsistent' \
  "$RUN/terminal-service.log")" == 1 ]]
[[ "$(rg -c 'Main process exited, code=exited, status=5/NOTINSTALLED' \
  "$RUN/terminal-service.log")" == 1 ]]
[[ "$(rg -c "Failed with result 'exit-code'" \
  "$RUN/terminal-service.log")" == 1 ]]
[[ "$(rg -c '107.3G memory peak, 0B memory swap peak' \
  "$RUN/terminal-service.log")" == 1 ]]

(cd "$RUN" && sha256sum -c atom-inventory.tsv >/dev/null)
[[ "$(wc -l <"$RUN/atom-inventory.tsv")" == 3212 ]]
if [[ -d "$RUN/artifacts/atoms" ]]; then
  artifact_count=$(find "$RUN/artifacts/atoms" -mindepth 1 -maxdepth 1 \
    -type d | wc -l)
else
  artifact_count=0
fi
if [[ "$artifact_count" == 3212 ]]; then
  artifacts_present=1
elif [[ "$artifact_count" == 0 && -s "$RUN/evidence-compaction.json" ]]; then
  artifacts_present=0
else
  echo "TASK11 artifact tree is partial or lacks a compaction certificate" >&2
  exit 1
fi

tree_digest() {
  local directory=$1
  (cd "$directory" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
}

while IFS=$'\t' read -r atom theory part parts theory_dir extra; do
  certificate="$RUN/atom-certificates/$atom.json"
  journal="$RUN/journal/$atom.jsonl"
  [[ -s "$certificate" && -f "$journal" && -z "${extra-}" ]]
  journal_sha=$(sha256sum "$journal" | cut -d' ' -f1)
  jq -e --arg atom "$atom" --arg input "$INPUT_SHA" \
    --arg journal "$journal_sha" --arg theory "$theory" \
    --argjson part "$part" --argjson parts "$parts" \
    --arg theory_dir "$theory_dir" '
      .schema == "hh-task11-f30-atom-v1" and .status == "complete" and
      .atom == $atom and .theory == $theory and .part == $part and
      .parts == $parts and .input_inventory_sha256 == $input and
      .theory_directory == $theory_dir and .journal_sha256 == $journal and
      .tmpfs_removed == true
    ' "$certificate" >/dev/null
  if [[ "$artifacts_present" == 1 ]]; then
    artifact="$RUN/artifacts/atoms/$atom"
    [[ -d "$artifact" && ! -L "$artifact" ]]
    tree=$(tree_digest "$artifact")
    jq -e --arg tree "$tree" '.artifact_tree_sha256 == $tree' \
      "$certificate" >/dev/null
  fi
done <"$RUN/atoms.tsv"

if [[ "$artifacts_present" == 0 ]]; then
  LINEAGE="$RUN/lineage/v3"
  if [[ -s "$LINEAGE/SHA256SUMS" ]]; then
    has_lineage=1
    [[ ! -L "$LINEAGE/SHA256SUMS" ]]
    (cd "$LINEAGE" && sha256sum -c SHA256SUMS >/dev/null)
    lineage_sha=$(sha256sum "$LINEAGE/SHA256SUMS" | cut -d' ' -f1)
    predecessor_final_sha=$(sha256sum "$LINEAGE/final-certificate.json" |
      cut -d' ' -f1)
    predecessor_compaction_sha=$(sha256sum \
      "$LINEAGE/evidence-compaction.json" | cut -d' ' -f1)
    jq -e \
      --arg final "$predecessor_final_sha" \
      --arg verifier "$(sha256sum "$LINEAGE/full-artifact-verifier.sh" |
        cut -d' ' -f1)" '
      .schema == "hh-task11-evidence-compaction-v1" and
      .status == "removed" and .artifact_directories_removed == 3212 and
      .artifact_files_removed > 0 and .artifact_bytes_removed > 0 and
      .artifacts_absent_after_cleanup == true and
      .final_certificate_sha256 == $final and
      .full_verifier_sha256 == $verifier and
      .full_verification_before_cleanup == true
    ' "$LINEAGE/evidence-compaction.json" >/dev/null
  else
    has_lineage=0
    lineage_sha=
    predecessor_final_sha=
    predecessor_compaction_sha=
  fi
  jq -e \
    --arg final "$(sha256sum "$RUN/final-certificate.json" | cut -d' ' -f1)" \
    --arg atoms "$(sha256sum "$RUN/atom-inventory.tsv" | cut -d' ' -f1)" \
    --arg verifier "$verifier_inventory_sha" --arg lineage "$lineage_sha" \
    --arg predecessor_final "$predecessor_final_sha" \
    --arg predecessor_compaction "$predecessor_compaction_sha" \
    --argjson has_lineage "$has_lineage" '
    .schema == "hh-task11-evidence-compaction-v2" and
    .status == "removed" and .artifact_directories_removed == 3212 and
    .artifact_files_removed > 0 and .artifact_bytes_removed > 0 and
    .artifacts_absent_after_cleanup == true and
    .final_certificate_sha256 == $final and
    .atom_inventory_sha256 == $atoms and
    .verifier_inventory_sha256 == $verifier and
    (if $has_lineage then
       .predecessor_lineage_inventory_sha256 == $lineage and
       .predecessor_final_certificate_sha256 == $predecessor_final and
       .predecessor_compaction_certificate_sha256 == $predecessor_compaction
     else .predecessor_lineage_inventory_sha256 == null and
       .predecessor_final_certificate_sha256 == null and
       .predecessor_compaction_certificate_sha256 == null
     end) and
    .full_verification_before_cleanup == true and
    .retained_evidence_reverified_after_compaction == true
  ' "$RUN/evidence-compaction.json" >/dev/null
fi

jq -e --arg input "$INPUT_SHA" \
  --arg goals "$(sha256sum "$RUN/canonical-goals.tsv" | cut -d' ' -f1)" '
  .schema == "hh-task11-f30-result-v1" and .status == "complete" and
  .input_inventory_sha256 == $input and
  .canonical_goal_inventory_sha256 == $goals and
  .goals == 24721 and .cells == 197768 and
  .observed_cells == (.cells + 8 * .excluded_extra_goals) and
  (.strict_superset_corrected == (.excluded_extra_goals > 0)) and
  (.conditions | length) == 8 and (.gate.pass | type) == "boolean" and
  (.shape.criterion_a_pass | type) == "boolean" and
  (.shape.criterion_b_pass | type) == "boolean"
' "$RUN/result.json" >/dev/null
jq -e --argjson extra_count "$extra_count" \
  --arg excluded "$(sha256sum "$RUN/excluded-extra-goals.tsv" |
    cut -d' ' -f1)" '
  .schema == "hh-task11-f30-corpus-correction-v1" and
  .status == "complete" and
  .excluded_extra_goals == $extra_count and
  .excluded_extra_goal_ids_sha256 == $excluded and
  .missing_canonical_goals == 0 and .duplicate_canonical_cells == 0 and
  .canonical_cells_per_goal == 8 and
  .no_measurement_rerun_required == ($extra_count > 0)
' "$RUN/corpus-correction.json" >/dev/null
jq -e '
  .schema == "hh-task11-f30-cleanup-v2" and .status == "removed" and
  .tmpfs_root_absent_after_cleanup == true and
  .observed_memory_peak_human == "107.3G" and
  .observed_swap_peak_bytes == 0 and .atom_attempts == 10649 and
  .recovered_worker_recycles == 7437 and .timeout_status_124 == 7411 and
  .kill_status_137 == 26 and .systemd_oom_kill_events == 19
' "$RUN/tmpfs-cleanup.json" >/dev/null
[[ ! -e "$(jq -r '.state_root' "$RUN/envelope.json")" ]]

FINAL="$RUN/final-certificate.json"
jq -e --arg input "$INPUT_SHA" \
  --arg run "$(sha256sum "$RUN/run.json" | cut -d' ' -f1)" \
  --arg envelope "$(sha256sum "$RUN/envelope.json" | cut -d' ' -f1)" \
  --arg envelope_start "$start_sha" \
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
  --arg terminal "$terminal_sha" --arg terminal_log "$terminal_log_sha" \
  --arg verifier "$verifier_inventory_sha" \
  --arg invocations "$(sha256sum "$RUN/invocations.jsonl" |
    cut -d' ' -f1)" \
  --arg maker "$(sha256sum "$TOOLS/make-final-certificate.sh" |
    cut -d' ' -f1)" \
  --arg fold "$(sha256sum "$TOOLS/fold-result.sh" | cut -d' ' -f1)" \
  --arg shape_tool "$(sha256sum "$TOOLS/investigate-shape.sh" |
    cut -d' ' -f1)" '
  .schema == "hh-task11-f30-final-v4" and .status == "complete" and
  .input_inventory_sha256 == $input and .run_header_sha256 == $run and
  .envelope_sha256 == $envelope and
  .start_envelope_sha256 == $envelope_start and
  .atom_plan_sha256 == $atoms and .journal_inventory_sha256 == $journals and
  .atom_inventory_sha256 == $atom_inventory and .result_sha256 == $result and
  .summary_sha256 == $summary and .report_sha256 == $report and
  .canonical_goal_inventory_sha256 == $goals and
  .canonical_goal_certificate_sha256 == $goal_cert and
  .shape_investigation_sha256 == $shape and
  .criterion_b_investigation_sha256 == $criterion_b and
  .excluded_extra_goal_ids_sha256 == $excluded and
  .corpus_correction_sha256 == $correction and .cleanup_sha256 == $cleanup and
  .terminal_service_sha256 == $terminal and
  .terminal_service_log_sha256 == $terminal_log and
  .verifier_inventory_sha256 == $verifier and
  .invocations_sha256 == $invocations and
  .certificate_tool_sha256 == $maker and .fold_tool_sha256 == $fold and
  .shape_tool_sha256 == $shape_tool
' "$FINAL" >/dev/null
