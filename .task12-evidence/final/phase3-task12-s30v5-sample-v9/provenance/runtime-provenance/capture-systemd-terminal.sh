#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 2)); then
  echo "usage: $0 USER_UNIT OUTPUT_JSONL" >&2
  exit 2
fi

unit=$1
output=$2
[[ "$unit" == phase3-task12-*.service && ! -e "$output" ]]
journalctl --user -u "$unit" -o json --no-pager | jq -Sc '
  {realtime_usec:(.__REALTIME_TIMESTAMP|tonumber),
   source_realtime_usec:(._SOURCE_REALTIME_TIMESTAMP|tonumber),
   unit:.USER_UNIT,invocation_id:.USER_INVOCATION_ID,
   message_id:.MESSAGE_ID,job_type:.JOB_TYPE,job_result:.JOB_RESULT,
   cpu_usage_nsec:(.CPU_USAGE_NSEC//null|
     if .==null then null else tonumber end),
   memory_peak_bytes:(.MEMORY_PEAK//null|
     if .==null then null else tonumber end),
   memory_swap_peak_bytes:(.MEMORY_SWAP_PEAK//null|
     if .==null then null else tonumber end),message:.MESSAGE}
' >"$output"
[[ -s "$output" ]]
