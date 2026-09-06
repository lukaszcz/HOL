#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 2)); then
  echo "usage: $0 K STRUCTURED_SYSTEMD_JOURNAL" >&2
  exit 2
fi

K=$(realpath "$1")
JOURNAL=$(realpath "$2")
[[ -s "$K/certificate.json" && -s "$K/SHA256SUMS" ]]
(cd "$K" && sha256sum -c SHA256SUMS >/dev/null)
[[ ! -e "$K/terminal-service.json" ]]
jq -s -e '
  length == 2 and (map(.invocation_id)|unique|length) == 1 and
  all(.[];.unit == "phase3-task12-k-v10.service") and
  .[0].job_type == "start" and .[0].job_result == "done" and
  .[1].cpu_usage_nsec != null and .[1].memory_peak_bytes != null and
  .[1].memory_swap_peak_bytes == 0 and
  ([.[]|select(.message|test("Failed|Main process exited"))]|length) == 0
' "$JOURNAL" >/dev/null
invocation=$(jq -sr '.[0].invocation_id' "$JOURNAL")
start=$(jq -sr '.[0].realtime_usec' "$JOURNAL")
completion=$(jq -sr '.[-1].realtime_usec' "$JOURNAL")
cpu=$(jq -sr '.[-1].cpu_usage_nsec' "$JOURNAL")
memory=$(jq -sr '.[-1].memory_peak_bytes' "$JOURNAL")
swap=$(jq -sr '.[-1].memory_swap_peak_bytes' "$JOURNAL")
chmod u+w "$K" "$K/SHA256SUMS"
cp "$JOURNAL" "$K/terminal-systemd.jsonl"
jq -n --arg invocation "$invocation" \
  --arg journal "$(sha256sum "$K/terminal-systemd.jsonl" | cut -d' ' -f1)" \
  --arg result "$(sha256sum "$K/certificate.json" | cut -d' ' -f1)" \
  --argjson start "$start" --argjson completion "$completion" \
  --argjson cpu "$cpu" --argjson memory "$memory" --argjson swap "$swap" '
  {schema:"hh-task12-k-terminal-v5",status:"complete",
   unit:"phase3-task12-k-v10.service",invocation_id:$invocation,
   structured_journal_sha256:$journal,k_certificate_sha256:$result,
   start_realtime_usec:$start,completion_record_realtime_usec:$completion,
   duration_usec:($completion-$start),start_job_result:"done",
   completion_artifact_observed:true,observed_failure_records:0,
   certificate_reconciled_from_sealed_journal:true,
   cpu_usage_nsec:$cpu,memory_peak_bytes:$memory,memory_swap_peak_bytes:$swap,
   requested_envelope:{cpu_quota_percent:3200,
     memory_high_bytes:133143986176,memory_max_bytes:137438953472,
     memory_swap_max_bytes:0,oom_policy:"continue"}}
' >"$K/terminal-service.json"
SUMS=$(mktemp)
trap 'rm -f "$SUMS"' EXIT HUP INT TERM
(cd "$K" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$SUMS"
mv "$SUMS" "$K/SHA256SUMS"
chmod -R a-w "$K"
