#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 4 || {
  echo "usage: $0 INPUTS EXP THEORY COUNT" >&2
  exit 2
}
inputs=$1
exp=$2
theory=$3
count=$4
export HHEVAL_TASK10_A_INPUTS=$inputs
export HHEVAL_TASK10_A_EXP=$exp
export HHEVAL_TASK10_RUNNER_LIBRARY_ONLY=1
source "$inputs/run-a.sh"
verify_live_external_tools
if test -n "${HHEVAL_CHECKPOINT_SELFTEST_RUNTIME_OVERRIDE:-}"; then
  CHECKPOINT_RUNTIME_SHA=$HHEVAL_CHECKPOINT_SELFTEST_RUNTIME_OVERRIDE
  export CHECKPOINT_RUNTIME_SHA
fi
STATE=${HHEVAL_CHECKPOINT_SELFTEST_STATE:-/tmp/hh-current-checkpoint-selftest}
export STATE
mkdir -p "$STATE/current" "$STATE/launch"
accepted="$OUT/current-checkpoint-chains/$theory"
test -s "$accepted/validation.json"

expect_reject () {
  if checkpoint_validate_chain "$theory" "$count" >/dev/null 2>&1; then
    echo "checkpoint validator accepted negative case: $1" >&2
    exit 1
  fi
}

case_root () {
  local name=$1 root="$STATE/cases/$1"
  find "$root" -depth -mindepth 1 -delete 2>/dev/null || true
  mkdir -p "$root"
  cp -a "$accepted" "$root/$theory"
  find "$root" -type d -exec chmod 0755 {} +
  printf '%s\n' "$root"
}

# Exact resume is a pure validation/fold: rows cannot change.
before=$(sha "$OUT/current-first8/$theory.tsv")
current_checkpoint_chain "$theory" "$count" "$OUT/current-first8/$theory.tsv"
test "$(sha "$OUT/current-first8/$theory.tsv")" = "$before"

root=$(case_root stale-runtime)
HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE=$root
saved_runtime=$CHECKPOINT_RUNTIME_SHA
CHECKPOINT_RUNTIME_SHA=0000000000000000000000000000000000000000000000000000000000000000
expect_reject stale-runtime
CHECKPOINT_RUNTIME_SHA=$saved_runtime

root=$(case_root stale-model)
HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE=$root
receipt=$(find "$root/$theory/atoms" -name receipt.json | sort | sed -n 1p)
jq '.model_inventory_sha1="0000000000000000000000000000000000000000"' \
  "$receipt" >"$receipt.new"
mv -f "$receipt.new" "$receipt"
expect_reject stale-model

root=$(case_root corrupt-heap)
HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE=$root
heap=$(find "$root/$theory" -type f -name '*.heap' -print -quit)
chmod u+w "$heap"
printf x >>"$heap"
expect_reject corrupt-heap

root=$(case_root corrupt-receipt)
HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE=$root
receipt=$(find "$root/$theory/atoms" -name receipt.json | sort | sed -n 1p)
jq '.next_heap_sha256="0000000000000000000000000000000000000000000000000000000000000000"' \
  "$receipt" >"$receipt.new"
mv -f "$receipt.new" "$receipt"
expect_reject corrupt-receipt

root=$(case_root gap)
HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE=$root
victim=$(find "$root/$theory/atoms" -mindepth 1 -maxdepth 1 -type d | sort | sed -n 2p)
find "$victim" -depth -delete
expect_reject gap

root=$(case_root overlap-branch)
HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE=$root
first=$(find "$root/$theory/atoms" -mindepth 1 -maxdepth 1 -type d | \
  sort | sed -n 1p)
cp -a "$first" "$root/$theory/atoms/000005"
find "$root/$theory/atoms/000005" -type d -exec chmod 0755 {} +
expect_reject overlap-branch

root=$(case_root wrong-db-order)
HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE=$root
awk 'NR==1 {a=$0;next} NR==2 {print;print a;next} {print}' \
  "$root/$theory/db-order.txt" >"$root/$theory/db-order.new"
mv -f "$root/$theory/db-order.new" "$root/$theory/db-order.txt"
expect_reject wrong-db-order

root=$(case_root baseline-cross-feed)
HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE=$root
atom=$(find "$root/$theory/atoms" -mindepth 1 -maxdepth 1 -type d | \
  sort | sed -n 1p)
ranking=$(find "$atom/rankings" -name '*.ranking' | sort | sed -n 1p)
premise=$(find "$OUT/baseline-premises/$theory" -name '*.premises' | \
  sort | sed -n 1p)
chmod u+w "$ranking"
cp "$premise" "$ranking"
chmod u+w "$atom/rankings.sha256"
(cd "$atom/rankings" && find . -name '*.ranking' -print0 | LC_ALL=C sort -z | \
  xargs -0 sha256sum) >"$atom/rankings.sha256"
jq --arg digest "$(sha "$atom/rankings.sha256")" \
  '.rankings_inventory_sha256=$digest' "$atom/receipt.json" \
  >"$atom/receipt.new"
mv -f "$atom/receipt.new" "$atom/receipt.json"
expect_reject baseline-cross-feed

# A killed atom has no durable receipt and leaves the prior heap authoritative.
kill_root="$STATE/kill-before-commit"
find "$kill_root" -depth -mindepth 1 -delete 2>/dev/null || true
mkdir -p "$kill_root"
HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE=$kill_root
checkpoint_create_base "$theory" "$count"
checkpoint_validate_chain "$theory" "$count"
base_sha=$CHECKPOINT_CHAIN_PRIOR_SHA
test ! -e "$STATE/current-checkpoint/$theory"
maximum_scratch_kib=0
saved_headroom=$CHECKPOINT_ATOM_HEADROOM_KIB
saved_host_floor=$HOST_MEMORY_MIN_AVAILABLE_KIB
scope_relative=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
test "$(cat "/sys/fs/cgroup$scope_relative/memory.oom.group")" = 0
export HHEVAL_CHECKPOINT_TEST_SIGKILL_CHILD=1
if checkpoint_atom_once "$theory" "$count"; then
  echo "killed atom unexpectedly committed" >&2
  exit 1
else
  test "$?" -eq 76
fi
unset HHEVAL_CHECKPOINT_TEST_SIGKILL_CHILD
kill_failure=$(find "$OUT/checkpoint-failures/$theory" -mindepth 1 \
  -maxdepth 1 -type d -name 'atom-0-status-137.*' | sort | tail -1)
test -n "$kill_failure"
jq -e '
  .worker_status == 137 and .retry_status == 76 and
  .receipt_accepted == false' \
  "$kill_failure/failure-classification.json" >/dev/null
kill -0 $$
test -z "$(find "$kill_root/$theory/atoms" -mindepth 1 -maxdepth 1 \
  -type d -print -quit)"
test "$(sha "$kill_root/$theory/base.heap")" = "$base_sha"
test ! -e "$STATE/current-checkpoint/$theory"
export HHEVAL_HOST_MEMORY_AVAILABLE_OVERRIDE=0
export HHEVAL_SCOPE_MEMORY_CURRENT_OVERRIDE=0
export HHEVAL_HOST_MEMORY_WAIT_OVERRIDE=0
if require_host_memory_headroom; then
  echo "host-memory guard unexpectedly accepted atom" >&2
  exit 1
else
  test "$?" -eq 75
fi
export HHEVAL_HOST_MEMORY_AVAILABLE_OVERRIDE=$saved_host_floor
require_host_memory_headroom
unset HHEVAL_HOST_MEMORY_AVAILABLE_OVERRIDE
unset HHEVAL_SCOPE_MEMORY_CURRENT_OVERRIDE
unset HHEVAL_HOST_MEMORY_WAIT_OVERRIDE
export HHEVAL_CHECKPOINT_TEST_AVAILABLE_KIB=0
if checkpoint_atom_once "$theory" "$count"; then
  echo "headroom guard unexpectedly accepted atom" >&2
  exit 1
else
  test "$?" -eq 75
fi
unset HHEVAL_CHECKPOINT_TEST_AVAILABLE_KIB
test ! -e "$STATE/current-checkpoint/$theory"
export HHEVAL_CHECKPOINT_TEST_KILL_AFTER_CHILD=1
if checkpoint_atom_once "$theory" "$count"; then
  echo "kill-before-commit hook unexpectedly committed" >&2
  exit 1
fi
unset HHEVAL_CHECKPOINT_TEST_KILL_AFTER_CHILD
test -z "$(find "$kill_root/$theory/atoms" -mindepth 1 -maxdepth 1 -type d -print -quit)"
test "$(sha "$kill_root/$theory/base.heap")" = "$base_sha"
test ! -e "$STATE/current-checkpoint/$theory"
checkpoint_atom_once "$theory" "$count"
checkpoint_validate_chain "$theory" "$count"
test "$CHECKPOINT_CHAIN_END" -gt 0
test ! -e "$STATE/current-checkpoint/$theory"
first_end=$CHECKPOINT_CHAIN_END
if test "$first_end" -lt "$count"; then
  checkpoint_atom_once "$theory" "$count"
  checkpoint_validate_chain "$theory" "$count"
  test "$CHECKPOINT_CHAIN_END" -gt "$first_end"
  test ! -e "$STATE/current-checkpoint/$theory"
  storage_atoms=2
else
  storage_atoms=1
fi
if test "${HHEVAL_CHECKPOINT_SELFTEST_REQUIRE_MULTI:-0}" = 1; then
  test "$storage_atoms" -ge 2
fi
accepted_first=$(find "$accepted/atoms" -mindepth 1 -maxdepth 1 -type d | \
  sort | sed -n 1p)
new_first=$(find "$kill_root/$theory/atoms" -mindepth 1 -maxdepth 1 \
  -type d | sort | sed -n 1p)
cmp -s "$accepted_first/rows.tsv" "$new_first/rows.tsv"

# Headers larger than MAX_ARG_STRLEN must be streamed, and exact resume must
# render the same bytes.  This fixture is larger than A21's 523,190-byte
# triggering header and exercises the production fold renderer.
large_root="$STATE/large-binding-fold"
find "$large_root" -depth -mindepth 1 -delete 2>/dev/null || true
mkdir -p "$large_root"
large_count=7000
printf '#hh-anchor-current-v1\t%s\n' \
  '{"schema":"hh-anchor-current-v1","goal_bindings":[]}' \
  >"$large_root/first.tsv"
awk -v count="$large_count" 'BEGIN {
  for (i = 1; i <= count; i++)
    printf ("{\"goal_id\":\"large.%06d\",\"goal_struct_sha256\":" \
      "\"%064d\",\"padding\":\"%080d\"}\n"), i, 0, 0
}' >"$large_root/bindings.jsonl"
jq -s '.' "$large_root/bindings.jsonl" >"$large_root/bindings.json"
large_binding_bytes=$(stat -c %s "$large_root/bindings.json")
test "$large_binding_bytes" -gt 523190
checkpoint_render_fold_header "$large_root/first.tsv" \
  "$large_root/bindings.json" "$large_root/header-1.json" \
  "$(printf chain | sha256sum | awk '{print $1}')" \
  "$(printf inventory | sha256sum | awk '{print $1}')" \
  "$(printf rows | sha256sum | awk '{print $1}')" "$large_count" 55
checkpoint_render_fold_header "$large_root/first.tsv" \
  "$large_root/bindings.json" "$large_root/header-2.json" \
  "$(printf chain | sha256sum | awk '{print $1}')" \
  "$(printf inventory | sha256sum | awk '{print $1}')" \
  "$(printf rows | sha256sum | awk '{print $1}')" "$large_count" 55
cmp -s "$large_root/header-1.json" "$large_root/header-2.json"
jq -e --argjson goals "$large_count" '
  .goals == $goals and .row_count == $goals * 8 and
  (.goal_bindings | length) == $goals and
  .checkpoint_chain_atoms == 55' "$large_root/header-1.json" >/dev/null
large_header_sha=$(sha "$large_root/header-1.json")
if "$RG_PATH" -n -- '--argjson [^ ]+ "\$\(cat' \
    "$INPUTS/current-checkpoint-chain.sh" >/dev/null; then
  echo "checkpoint runtime contains unbounded JSON argv transport" >&2
  exit 1
fi

unset HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE
for cleanup_root in "$STATE/cases" "$kill_root" "$large_root"; do
  case "$cleanup_root" in
    "$STATE/"*) ;;
    *) exit 2 ;;
  esac
  if test -d "$cleanup_root"; then
    find "$cleanup_root" -depth -delete
  fi
done
jq -n --arg theory "$theory" --arg runtime "$CHECKPOINT_RUNTIME_SHA" \
  --arg storage "$CHECKPOINT_STORAGE_POLICY" \
  --argjson headroom "$saved_headroom" --argjson storage_atoms "$storage_atoms" \
  --argjson maximum_scratch_kib "$maximum_scratch_kib" \
  --arg memory_policy "$HOST_MEMORY_POLICY" \
  --argjson host_floor "$saved_host_floor" \
  --argjson scope_headroom "$HOST_MEMORY_SCOPE_HEADROOM_BYTES" \
  --argjson large_binding_bytes "$large_binding_bytes" \
  --arg large_header "$large_header_sha" \
  --arg accepted "$(sha "$accepted/validation.json")" \
  '{schema:"hh-current-db-checkpoint-selftest-v1",status:"complete",
    theory:$theory,checkpoint_runtime_sha256:$runtime,
    accepted_validation_sha256:$accepted,resume_byte_identical:true,
    oom_policy_continue_verified:true,killed_atom_status:137,
    killed_atom_retry_status:76,
    killed_atom_parent_survived:true,killed_atom_not_accepted:true,
    killed_atom_prior_checkpoint_authoritative:true,
    killed_atom_retry_accepted:true,
    kill_before_commit_recovered:true,corrupt_heap_rejected:true,
    storage_policy_version:$storage,atom_headroom_kib:$headroom,
    storage_atoms:$storage_atoms,scratch_bounded_after_every_commit:true,
    maximum_scratch_kib_after_commit:$maximum_scratch_kib,
    host_memory_policy_version:$memory_policy,
    host_memory_minimum_external_available_kib:$host_floor,
    host_memory_minimum_scope_headroom_bytes:$scope_headroom,
    host_memory_guard_rejected:true,
    large_binding_streamed:true,large_binding_bytes:$large_binding_bytes,
    large_binding_exact_resume:true,large_header_sha256:$large_header,
    completed_chain_scratch_pruned:true,headroom_guard_rejected:true,
    corrupt_receipt_rejected:true,stale_model_rejected:true,
    stale_runtime_rejected:true,
    gap_rejected:true,overlap_branch_rejected:true,
    wrong_db_order_rejected:true,baseline_cross_feed_rejected:true}'
