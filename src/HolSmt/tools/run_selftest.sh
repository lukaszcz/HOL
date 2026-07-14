#!/usr/bin/env bash
#
# Run the HolSmt functional selftest, sharded across N fresh processes.
#
# Zero-config: `src/HolSmt/tools/run_selftest.sh` with no arguments builds
# whatever is missing, auto-detects z3/cvc5, sizes concurrency to the host,
# and runs the whole suite.  Every knob has an env var and a flag override.
#
# Rationale for sharding: the selftest's functional phase runs ~800
# solver-backed goals in a single long-lived Poly/ML process, so the heap
# only ever grows -- the unbounded whole-suite run reaches >200 GB RSS and is
# easily OOM-killed on a memory-capped runner, which then looks like a
# skipped/failed verification.  This driver splits the suite into N shards
# (selected in selftest.sml via HOL4_SELFTEST_SHARD="k/N", round-robin by
# test index) and runs each in its own fresh process with a hard --maxheap
# cap, so peak RSS drops to a few GB per shard.  Running shards concurrently
# also collapses wall-clock.
#
# Usage:
#   tools/run_selftest.sh [--shards N] [--jobs J] [--maxheap MB]
#                         [--timeout SECONDS] [--out DIR]
#                         [--keep-going] [--no-build]
#
# Defaults (all overridable by the matching env var):
#   --shards   8          (SHARDS)        suite granularity
#   --jobs     auto       (JOBS)          concurrent shards; sized to host
#                                         RAM/cores if unset
#   --maxheap  8000       (MAXHEAP)       hard per-shard heap cap, MB
#   --timeout  1800       (SHARD_TIMEOUT) per-shard wall-clock kill, seconds
#   --out      selftest-shards (OUT_DIR)  per-shard stdout/status directory
#   --keep-going          (HOL4_SELFTEST_KEEP_GOING=1)  run every test and
#                                         report all failures, instead of
#                                         stopping each shard at its first
#   --no-build            (RUN_SELFTEST_BUILD=0)  skip the build/up-to-date
#                                         check and run what is already built
#
# Solver executables: HOL4_Z3_EXECUTABLE / HOL4_CVC_EXECUTABLE are used if
# set; otherwise z3 (preferring z3-4.15.x) and cvc5 are resolved from
# ~/.local/bin and PATH.  A missing solver is not fatal -- its columns are
# simply skipped by the selftest.
#
set -u

script_dir=$(cd "$(dirname "$0")" && pwd)
holsmt_dir=$(cd "$script_dir/.." && pwd)          # src/HolSmt
repo_root=$(cd "$holsmt_dir/../.." && pwd)

shards=${SHARDS:-8}
jobs=${JOBS:-auto}
maxheap=${MAXHEAP:-8000}
timeout_seconds=${SHARD_TIMEOUT:-1800}
out_dir=${OUT_DIR:-"$holsmt_dir/selftest-shards"}
keep_going=${HOL4_SELFTEST_KEEP_GOING:-0}
do_build=${RUN_SELFTEST_BUILD:-1}

while [ $# -gt 0 ]; do
  case "$1" in
    --shards)     shards=$2; shift 2 ;;
    --jobs)       jobs=$2; shift 2 ;;
    --maxheap)    maxheap=$2; shift 2 ;;
    --timeout)    timeout_seconds=$2; shift 2 ;;
    --out)        out_dir=$2; shift 2 ;;
    --keep-going) keep_going=1; shift ;;
    --no-build)   do_build=0; shift ;;
    -h|--help)    sed -n '3,40p' "$0" | sed 's/^#\{0,1\} \{0,1\}//'; exit 0 ;;
    *) printf 'Unknown argument: %s\n' "$1" >&2; exit 2 ;;
  esac
done

if [ "$shards" -lt 1 ]; then
  printf 'shards must be >= 1\n' >&2; exit 2
fi

hol="$repo_root/bin/hol"
holmake="$repo_root/bin/Holmake"
holstate="$holsmt_dir/smtheap"

if [ ! -x "$hol" ]; then
  printf 'hol executable not found: %s (build HOL first)\n' "$hol" >&2; exit 2
fi

# --- resolve solver executables (non-fatal if absent) ----------------------

# Resolve a solver: honour a preset env value if it is executable, else scan
# ~/.local/bin then PATH for the given glob patterns (tried in order).
# Prints the resolved path, or nothing if none found.
resolve_solver() {
  local preset=$1; shift
  if [ -n "$preset" ] && [ -x "$preset" ]; then
    printf '%s\n' "$preset"; return 0
  fi
  local -a dirs=("$HOME/.local/bin") path_dirs=()
  local d pat cand
  IFS=: read -r -a path_dirs <<< "${PATH:-}"
  for d in "${path_dirs[@]}"; do [ -n "$d" ] && dirs+=("$d"); done
  for pat in "$@"; do
    for d in "${dirs[@]}"; do
      [ -d "$d" ] || continue
      for cand in "$d"/$pat; do
        [ -f "$cand" ] && [ -x "$cand" ] && { printf '%s\n' "$cand"; return 0; }
      done
    done
  done
  return 1
}

z3=$(resolve_solver "${HOL4_Z3_EXECUTABLE:-}" 'z3-4.15*' 'z3-4.1*' 'z3-*' 'z3')
if [ -n "$z3" ]; then
  export HOL4_Z3_EXECUTABLE="$z3"
  printf 'z3:   %s\n' "$z3"
else
  printf 'z3:   not found (z3 columns will be skipped)\n'
fi

cvc=$(resolve_solver "${HOL4_CVC_EXECUTABLE:-}" 'cvc5-*' 'cvc5')
if [ -n "$cvc" ]; then
  export HOL4_CVC_EXECUTABLE="$cvc"
  printf 'cvc5: %s\n' "$cvc"
else
  printf 'cvc5: not found (cvc5 columns will be skipped)\n'
fi

# --- build what is missing (incremental; fast when up to date) -------------

if [ "$do_build" = 1 ]; then
  if [ ! -x "$holmake" ]; then
    printf 'Holmake not found: %s (build HOL first)\n' "$holmake" >&2; exit 2
  fi
  printf 'Building smtheap + selftest (incremental)...\n'
  if ! ( cd "$holsmt_dir" && "$holmake" smtheap selftest.exe ); then
    printf 'build failed\n' >&2; exit 2
  fi
elif [ ! -e "$holstate" ]; then
  printf 'holstate not found: %s and --no-build given\n' "$holstate" >&2
  exit 2
fi

# --- size concurrency to the host if --jobs is auto ------------------------

if [ "$jobs" = auto ]; then
  cores=$(nproc 2>/dev/null || echo 4)
  avail_mb=$(awk '/MemAvailable/ {print int($2/1024)}' /proc/meminfo 2>/dev/null)
  [ -n "$avail_mb" ] || avail_mb=$((maxheap * 2))
  # Conservative: assume a shard may use up to its full --maxheap cap, so
  # jobs*maxheap must fit in available RAM.  Also cap by cores and shards.
  by_mem=$(( avail_mb / maxheap ))
  [ "$by_mem" -lt 1 ] && by_mem=1
  jobs=$shards
  [ "$cores" -lt "$jobs" ] && jobs=$cores
  [ "$by_mem" -lt "$jobs" ] && jobs=$by_mem
fi
if [ "$jobs" -lt 1 ]; then jobs=1; fi
[ "$jobs" -gt "$shards" ] && jobs=$shards

mkdir -p "$out_dir"
rm -f "$out_dir"/shard-*.stdout "$out_dir"/shard-*.status

printf 'Selftest: %d shards, %d concurrent, --maxheap %s MB, timeout %ss%s\n' \
  "$shards" "$jobs" "$maxheap" "$timeout_seconds" \
  "$( [ "$keep_going" = 1 ] && printf ', keep-going' )"

run_shard() {
  local k=$1
  (
    cd "$holsmt_dir" || exit 99
    timeout "$timeout_seconds" \
      env HOL4_SELFTEST_SHARD="$k/$shards" \
          HOL4_SELFTEST_KEEP_GOING="$keep_going" \
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
    grep -h "failed on term" "$out_dir/shard-$k.stdout" 2>/dev/null \
      | sed 's/^/    /'
    tail -n 15 "$out_dir/shard-$k.stdout" 2>/dev/null | sed 's/^/    /'
  fi
done

if [ "$fail" = 0 ]; then
  printf 'ALL SHARDS PASSED (%d shards)\n' "$shards"
  exit 0
fi
printf 'SELFTEST FAILED\n'
exit 1
