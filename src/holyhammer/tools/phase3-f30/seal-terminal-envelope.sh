#!/usr/bin/env bash
set -Eeuo pipefail

if (($# < 3 || $# > 4)); then
  echo "usage: $0 INPUTS RUN SERVICE [TERMINAL_LOG]" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
RUN=$(realpath "$2")
SERVICE=$3
SOURCE_LOG=${4-}
START="$RUN/envelope.json"
START_COPY="$RUN/envelope-start.json"
LOG="$RUN/terminal-service.log"
TERMINAL="$RUN/terminal-service.json"
INPUT_SHA=$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)

[[ ! -e "$START_COPY" && ! -e "$LOG" && ! -e "$TERMINAL" ]]
if [[ -n "$SOURCE_LOG" ]]; then
  cp "$(realpath "$SOURCE_LOG")" "$LOG.partial"
else
  journalctl --user -u "$SERVICE" --no-pager -o short-iso-precise \
    >"$LOG.partial"
fi
[[ -s "$LOG.partial" ]]

started_line=$(rg -F "Started $SERVICE" "$LOG.partial")
exit_line=$(rg -F "$SERVICE: Main process exited, code=exited," \
  "$LOG.partial")
failure_line=$(rg -F "$SERVICE: Failed with result 'exit-code'." \
  "$LOG.partial")
resource_line=$(rg -F "$SERVICE: Consumed " "$LOG.partial")
[[ "$(printf '%s\n' "$started_line" | wc -l)" == 1 ]]
[[ "$(printf '%s\n' "$exit_line" | wc -l)" == 1 ]]
[[ "$(printf '%s\n' "$failure_line" | wc -l)" == 1 ]]
[[ "$(printf '%s\n' "$resource_line" | wc -l)" == 1 ]]
[[ "$started_line" == *"HHEVAL_TASK11_INPUTS=$INPUTS"* ]]
[[ "$started_line" == \
   *"HHEVAL_TASK11_EXPERIMENT=${SERVICE%.service}"* ]]
[[ "$exit_line" == *"status=5/NOTINSTALLED"* ]]
[[ "$resource_line" == *"107.3G memory peak, 0B memory swap peak."* ]]
[[ "$(rg -c 'journal is incomplete, duplicated, or corpus-inconsistent' \
  "$LOG.partial")" == 1 ]]
journal_oom=$(rg -c \
  'A process of this unit has been killed by the OOM killer' "$LOG.partial")
[[ "$journal_oom" == 26 ]]

started=$(printf '%s\n' "$started_line" | awk '{print $1}')
exited=$(printf '%s\n' "$exit_line" | awk '{print $1}')
log_sha=$(sha256sum "$LOG.partial" | cut -d' ' -f1)
start_sha=$(sha256sum "$START" | cut -d' ' -f1)
run_sha=$(sha256sum "$RUN/run.json" | cut -d' ' -f1)
result_sha=$(sha256sum "$RUN/result.json" | cut -d' ' -f1)
cleanup_sha=$(sha256sum "$RUN/tmpfs-cleanup.json" | cut -d' ' -f1)
cgroup_oom=$(jq -r '.systemd_oom_kill_events' "$RUN/tmpfs-cleanup.json")
worker_137=$(jq -r '.kill_status_137' "$RUN/tmpfs-cleanup.json")
completed=$(jq -sr 'map(select(.event == "complete")) | last.time' \
  "$RUN/invocations.jsonl")

jq -e --arg input "$INPUT_SHA" --arg run "$run_sha" \
  --arg commit "$(jq -r '.main.commit' "$INPUTS/top-provenance.json")" \
  --arg diff "$(jq -r '.main.tracked_diff_sha256' \
    "$INPUTS/top-provenance.json")" '
  .schema == "hh-task11-f30-envelope-v1" and .status == "running" and
  .input_inventory_sha256 == $input and .run_header_sha256 == $run and
  .hol_commit == $commit and .tracked_source_patch_sha256 == $diff and
  .initial_cache_files == 0 and .isolated_caches == true and
  .resumable_journals == true and
  .envelope == {cpu_quota_cores:32,memory_high_bytes:133143986176,
    memory_max_bytes:137438953472,memory_swap_max_bytes:0,
    worker_recycle_seconds:600,worker_slots:32,chunk_target_goals:8,
    tmpfs_scratch:true,durable_copyback:true}
' "$START" >/dev/null
jq -e --arg result "$result_sha" --argjson cgroup_oom "$cgroup_oom" \
  --argjson worker_137 "$worker_137" '
  .schema == "hh-task11-f30-cleanup-v2" and .status == "removed" and
  .result_sha256 == $result and .observed_memory_peak_human == "107.3G" and
  .observed_swap_peak_bytes == 0 and
  .systemd_oom_kill_events == $cgroup_oom and
  .kill_status_137 == $worker_137 and
  .tmpfs_root_absent_after_cleanup == true
' "$RUN/tmpfs-cleanup.json" >/dev/null
[[ "$worker_137" == 26 && "$cgroup_oom" == 19 ]]

jq -n --arg service "$SERVICE" --arg started "$started" \
  --arg exited "$exited" --arg log "$log_sha" --arg start "$start_sha" \
  --arg result "$result_sha" --arg cleanup "$cleanup_sha" \
  --argjson journal_oom "$journal_oom" --argjson cgroup_oom "$cgroup_oom" \
  --argjson worker_137 "$worker_137" '
  {schema:"hh-task11-terminal-service-v1",status:"complete",
   service:$service,service_started:$started,service_exited:$exited,
   service_result:"exit-code",main_exit_status:5,
   original_fold_outcome:"rejected strict corpus superset",
   memory_peak_human:"107.3G",memory_swap_peak_bytes:0,
   journal_oom_notifications:$journal_oom,
   cgroup_oom_kill_events:$cgroup_oom,
   worker_status_137_recycles:$worker_137,
   terminal_log_sha256:$log,start_envelope_sha256:$start,
   recovered_result_sha256:$result,cleanup_sha256:$cleanup}
' >"$TERMINAL.partial"

mv "$LOG.partial" "$LOG"
mv "$TERMINAL.partial" "$TERMINAL"
cp "$START" "$START_COPY"
jq --arg completed "$completed" \
  --arg terminal_sha "$(sha256sum "$TERMINAL" | cut -d' ' -f1)" \
  --arg terminal_log "$log_sha" --arg result "$result_sha" \
  --argjson journal_oom "$journal_oom" \
  --argjson cgroup_oom "$cgroup_oom" --argjson worker_137 "$worker_137" '
  .status = "complete" | .completed = $completed |
  .result_sha256 = $result |
  .terminal_service = {
    certificate:"terminal-service.json",certificate_sha256:$terminal_sha,
    log_sha256:$terminal_log,result:"exit-code",main_exit_status:5,
    memory_peak_human:"107.3G",memory_swap_peak_bytes:0,
    journal_oom_notifications:$journal_oom,
    cgroup_oom_kill_events:$cgroup_oom,
    worker_status_137_recycles:$worker_137,
    recovered_after_original_fold_rejection:true}
' "$START_COPY" >"$START.partial"
mv "$START.partial" "$START"
chmod 0444 "$START" "$START_COPY" "$LOG" "$TERMINAL"
