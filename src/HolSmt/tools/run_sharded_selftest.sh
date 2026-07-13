#!/usr/bin/env bash
#
# Run the HolSmt functional selftest sharded across N fresh processes.
#
# Rationale: the selftest's functional phase runs ~800 solver-backed goals in
# a single long-lived Poly/ML process, so the heap only ever grows -- the
# unbounded whole-suite run reaches >200 GB RSS and is easily OOM-killed on a
# memory-capped runner, which then looks like a skipped/failed verification.
#
# This driver splits the suite into N shards (selected in selftest.sml via
# HOL4_SELFTEST_SHARD="k/N", round-robin by test index) and runs each shard in
# its own fresh process with a hard --maxheap cap.  A fresh process resets the
# heap to a single shard's working set, so peak RSS drops to a few GB per
# shard regardless of whether the whole-suite growth was Poly/ML slack or real
# retention.  Running shards concurrently also collapses wall-clock.
#
# Memory budget: peak RSS is roughly (jobs * per-shard-RSS).  Choose --jobs to
# fit the host/cgroup: a 32 GB runner should use a small --jobs (even 1);
# a large host can run every shard at once.  --shards controls granularity
# (more shards => smaller per-shard working set and finer timeout), --jobs
# controls how many run at the same time.
#
# Usage:
#   tools/run_sharded_selftest.sh [--shards N] [--jobs J] [--maxheap MB]
#                                 [--timeout SECONDS] [--out DIR]
#
# Environment overrides: SHARDS, JOBS, MAXHEAP, SHARD_TIMEOUT, OUT_DIR.
# HOL4_Z3_EXECUTABLE / HOL4_CVC_EXECUTABLE are inherited by every shard.
#
set -u

script_dir=$(cd "$(dirname "$0")" && pwd)
holsmt_dir=$(cd "$script_dir/.." && pwd)          # src/HolSmt
repo_root=$(cd "$holsmt_dir/../.." && pwd)

shards=${SHARDS:-8}
jobs=${JOBS:-4}
maxheap=${MAXHEAP:-16000}
timeout_seconds=${SHARD_TIMEOUT:-3600}
out_dir=${OUT_DIR:-"$holsmt_dir/selftest-shards"}

while [ $# -gt 0 ]; do
  case "$1" in
    --shards)  shards=$2; shift 2 ;;
    --jobs)    jobs=$2; shift 2 ;;
    --maxheap) maxheap=$2; shift 2 ;;
    --timeout) timeout_seconds=$2; shift 2 ;;
    --out)     out_dir=$2; shift 2 ;;
    -h|--help)
      sed -n '2,32p' "$0"; exit 0 ;;
    *) printf 'Unknown argument: %s\n' "$1" >&2; exit 2 ;;
  esac
done

if [ "$shards" -lt 1 ] || [ "$jobs" -lt 1 ]; then
  printf 'shards and jobs must be >= 1\n' >&2; exit 2
fi
[ "$jobs" -gt "$shards" ] && jobs=$shards

hol="$repo_root/bin/hol"
holstate="$holsmt_dir/smtheap"

if [ ! -x "$hol" ]; then
  printf 'hol executable not found: %s\n' "$hol" >&2; exit 2
fi
if [ ! -e "$holstate" ]; then
  printf 'holstate not found: %s (build selftest.exe first)\n' "$holstate" >&2
  exit 2
fi

mkdir -p "$out_dir"
rm -f "$out_dir"/shard-*.stdout "$out_dir"/shard-*.status

printf 'Sharded selftest: %d shards, %d concurrent, --maxheap %s, timeout %ss\n' \
  "$shards" "$jobs" "$maxheap" "$timeout_seconds"

run_shard() {
  local k=$1
  (
    cd "$holsmt_dir" || exit 99
    timeout "$timeout_seconds" env HOL4_SELFTEST_SHARD="$k/$shards" \
      "$hol" --gcthreads=1 --maxheap "$maxheap" run \
      --holstate="$holstate" selftest \
      > "$out_dir/shard-$k.stdout" 2>&1
    echo $? > "$out_dir/shard-$k.status"
  ) &
}

running=0
for ((k = 0; k < shards; k++)); do
  run_shard "$k"
  running=$((running + 1))
  if [ "$running" -ge "$jobs" ]; then
    wait -n 2>/dev/null || wait
    running=$((running - 1))
  fi
done
wait

fail=0
for ((k = 0; k < shards; k++)); do
  rc=$(cat "$out_dir/shard-$k.status" 2>/dev/null || echo "??")
  if [ "$rc" = 0 ] && grep -q "all tests successful" "$out_dir/shard-$k.stdout"; then
    printf 'shard %d/%d: PASS\n' "$k" "$shards"
  else
    fail=1
    case "$rc" in
      124) printf 'shard %d/%d: FAIL (timeout after %ss)\n' \
             "$k" "$shards" "$timeout_seconds" ;;
      ??)  printf 'shard %d/%d: FAIL (no status; never completed)\n' \
             "$k" "$shards" ;;
      *)   printf 'shard %d/%d: FAIL (rc=%s)\n' "$k" "$shards" "$rc" ;;
    esac
    tail -n 15 "$out_dir/shard-$k.stdout" 2>/dev/null | sed 's/^/    /'
  fi
done

if [ "$fail" = 0 ]; then
  printf 'ALL SHARDS PASSED (%d shards)\n' "$shards"
  exit 0
fi
printf 'SHARDED SELFTEST FAILED\n'
exit 1
