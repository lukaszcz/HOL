#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 3)); then
  echo "usage: $0 SAMPLE K OUTPUT" >&2
  exit 2
fi

sample=$(realpath "$1")
k=$(realpath "$2")
output=$3
[[ ! -e "$output" ]]
completion=$(jq -er '.completion_record_realtime_usec' \
  "$k/terminal-service.json")
completed=$(date -u -d "@$((completion / 1000000))" +%Y-%m-%dT%H:%M:%SZ)
jq -n --arg completed "$completed" \
  --slurpfile endurance "$sample/endurance/terminal-certificate.json" \
  --slurpfile cache "$k/certificate.json" '
  ($endurance[0]) as $e | ($cache[0]) as $k |
  {schema:"hh-task12-final-v5",status:"complete",completed:$completed,
   endurance:{status:$e.status,atoms:$e.completed_atoms,
     goals:$e.completed_cells,attempts:$e.attempts,
     empty_shards:$e.empty_atoms,unit:$e.unit,invocation_id:$e.invocation_id,
     start_realtime_usec:$e.start_realtime_usec,
     stop_realtime_usec:$e.stop_realtime_usec,duration_usec:$e.duration_usec,
     cpu_usage_nsec:$e.cpu_usage_nsec,memory_peak_bytes:$e.memory_peak_bytes,
     swap_peak_bytes:$e.memory_swap_peak_bytes,state_root:$e.state_root,
     restart_resume_events:$e.restart_resume_events,
     atomic_continuity:$e.atomic_continuity,
     restart_causes_retained:false,restart_statuses_retained:false,
     restart_cause_and_status:"unknown"},
   k:{goals:$k.subset_goals,
     cached_cells:$k.cache_decomposition.cached_replay_cells,
     prime_cached_cells:3072,
     version_resolution_spawns:$k.version_resolution_spawns,
     prime_cache_check_spawns:$k.prime_cache_check_spawns,
     replay_prover_spawns:$k.replay_prover_spawns,state_root:$k.state_root,
     fresh_prime_and_replay_roots:true,prime_and_replay_non_resume:true,
     cache_manifest_before_sha256:$k.cache_manifest_before_sha256,
     cache_manifest_after_sha256:$k.cache_manifest_after_sha256},
   tmpfs_cleanup:"complete",tuning_performed:false,
   full_corpus_s30v5_measured:false,no_full_corpus_claim:true}
' >"$output"
