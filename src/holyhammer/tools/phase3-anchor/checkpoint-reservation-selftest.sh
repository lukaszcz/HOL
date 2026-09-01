#!/bin/bash
set -Eeuo pipefail

INPUTS=${1:?immutable input directory required}
EXP=${2:?experiment required}
export HHEVAL_TASK10_A_INPUTS=$INPUTS
export HHEVAL_TASK10_A_EXP=$EXP
export HHEVAL_TASK10_RUNNER_LIBRARY_ONLY=1
source "$INPUTS/run-a.sh"
verify_live_external_tools

test_root="$STATE/reservation-selftest"
test_out="$OUT/reservation-selftest"
saved_state=$STATE
saved_out=$OUT
STATE=$test_root
OUT=$test_out
find "$test_root" -depth -mindepth 1 -delete 2>/dev/null || true
find "$test_out" -depth -mindepth 1 -delete 2>/dev/null || true
mkdir -p "$STATE" "$OUT"
printf '0\n' >"$STATE/active"
printf '0\n' >"$STATE/maximum"

reservation_test_worker () {
  local label=$1 audit active maximum
  checkpoint_reservation_acquire "$label"
  exec {audit}>"$STATE/audit.lock"
  "$CHECKPOINT_FLOCK_PATH" "$audit"
  active=$(cat "$STATE/active"); active=$((active + 1))
  maximum=$(cat "$STATE/maximum")
  printf '%s\n' "$active" >"$STATE/active"
  if test "$active" -gt "$maximum"; then
    printf '%s\n' "$active" >"$STATE/maximum"
  fi
  "$CHECKPOINT_FLOCK_PATH" -u "$audit"
  exec {audit}>&-
  sleep 1
  exec {audit}>"$STATE/audit.lock"
  "$CHECKPOINT_FLOCK_PATH" "$audit"
  active=$(cat "$STATE/active"); active=$((active - 1))
  test "$active" -ge 0
  printf '%s\n' "$active" >"$STATE/active"
  "$CHECKPOINT_FLOCK_PATH" -u "$audit"
  exec {audit}>&-
  checkpoint_reservation_release "$label" 0
}
reservation_kill_worker () {
  local ready=$1 child_file=$2
  checkpoint_reservation_acquire killed-owner
  (checkpoint_reservation_close_child_fd; exec sleep 60 \
    >/dev/null 2>&1) &
  printf '%s\n' "$!" >"$child_file"
  printf 'ready\n' >"$ready"
  wait
}
export -f reservation_test_worker reservation_kill_worker
export STATE OUT
seq 1 16 | xargs -n 1 -P 16 bash --noprofile --norc -Eeuo pipefail -c \
  'reservation_test_worker "contender-$1"' reservation-worker

test "$(jq -r 'select(.event == "acquire") | .token' \
  "$OUT/checkpoint-reservations.jsonl" | sort -u | wc -l)" -eq 16
maximum=$(cat "$STATE/maximum")
test "$maximum" -eq "$CHECKPOINT_RESERVATION_SLOTS"
test "$(checkpoint_reservation_count_slots \
  "$STATE/checkpoint-reservations")" -eq 0
test "$(cat "$STATE/active")" -eq 0

printf '999999999\t1\tstale-owner\tstale-test\n' \
  >"$STATE/checkpoint-reservations/slot-00.owner.tsv"
checkpoint_reservation_acquire stale-recovery
test "$CHECKPOINT_RESERVATION_SLOT" -eq 0
test "$(cut -f3 "$STATE/checkpoint-reservations/slot-00.owner.tsv")" = \
  "$CHECKPOINT_RESERVATION_OWNER_TOKEN"
checkpoint_reservation_release stale-recovery 0
checkpoint_reservation_release stale-recovery 0

ready="$STATE/killed-owner.ready"; child_file="$STATE/killed-owner.child"
if timeout --signal=KILL 1 bash --noprofile --norc -Eeuo pipefail -c \
  'reservation_kill_worker "$1" "$2"' reservation-kill \
  "$ready" "$child_file"; then
  false
else
  killed_status=$?
fi
test "$killed_status" -eq 137
test -s "$ready" -a -s "$child_file"
checkpoint_reservation_acquire killed-owner-reacquire
test "$CHECKPOINT_RESERVATION_SLOT" -eq 0
checkpoint_reservation_release killed-owner-reacquire 0
kill "$(cat "$child_file")" 2>/dev/null || true

checkpoint_reservation_acquire nested-child
(checkpoint_reservation_close_child_fd; exec sleep 60 \
  >/dev/null 2>&1) &
nested_child=$!
checkpoint_reservation_release nested-child 0
checkpoint_reservation_acquire nested-child-reacquire
test "$CHECKPOINT_RESERVATION_SLOT" -eq 0
checkpoint_reservation_release nested-child-reacquire 0
kill "$nested_child" 2>/dev/null || true
wait "$nested_child" 2>/dev/null || true
test "$(checkpoint_reservation_count_slots \
  "$STATE/checkpoint-reservations")" -eq 0

STATE=$saved_state
OUT=$saved_out
export STATE OUT
jq -n --arg policy "$CHECKPOINT_RESERVATION_POLICY" \
  --argjson cap "$CHECKPOINT_RESERVATION_SLOTS" \
  --argjson maximum "$maximum" \
  --arg flock "$CHECKPOINT_FLOCK_PATH" \
  --arg flock_sha "$CHECKPOINT_FLOCK_SHA256" \
  '{schema:"hh-current-heavy-hol-reservation-selftest-v2",
    status:"complete",policy_version:$policy,configured_cap:$cap,
    scheduler_contenders:16,observed_maximum:$maximum,
    advisory_flock:true,flock_path:$flock,flock_sha256:$flock_sha,
    normal_release:true,double_cleanup_idempotent:true,
    killed_owner_auto_released:true,stale_owner_metadata_overwritten:true,
    nested_child_fd_closed:true,all_reservations_released:true}' \
  >"$OUT/checkpoint-reservation-selftest.json"
