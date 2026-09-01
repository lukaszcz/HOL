#!/bin/bash
set -Eeuo pipefail
GIT_OPTIONAL_LOCKS=0
export GIT_OPTIONAL_LOCKS

BASE_F751=/tmp/holyhammer-anchor-f751
OVERLAY_F751=/tmp/holyhammer-current-overlay-f751
BASE_F258=/tmp/holyhammer-anchor-f258
OVERLAY_F258=/tmp/holyhammer-current-overlay-f258
INPUTS=${HHEVAL_TASK10_A_INPUTS:?immutable input directory is required}
case "$INPUTS" in
  /*) ;;
  *) INPUTS=$(CDPATH= cd -- "$INPUTS" && pwd -P) ;;
esac
HHEVAL_TASK10_A_INPUTS=$INPUTS
export HHEVAL_TASK10_A_INPUTS
CALLER_PATH=$PATH
PATH=$INPUTS/verify-bin
export PATH
EVIDENCE_ROOT=${HHEVAL_TASK10_EVIDENCE_ROOT:-$(
  CDPATH= cd -- "$INPUTS/../.." && pwd -P
)}
ROOT=${HHEVAL_TASK10_ROOT:-${EVIDENCE_ROOT%/.task10-evidence}}
EXP=${HHEVAL_TASK10_A_EXP:-phase3-task10-a}
EVAL="$EVIDENCE_ROOT/runs"
OUT="$EVAL/$EXP"
STATE="/run/user/$(id -u)/holyhammer-phase3-task10/$EXP"
CORPUS="$INPUTS/eval/phase2-s30-v3/journal"
INVENTORY="$INPUTS/theory-inventory.tsv"
PREMISES="$OUT/baseline-premises"
BASELINE_TOOL="$INPUTS/tools/phase2-anchor-manifest.sh"
BASELINE_MERGE="$INPUTS/tools/phase2-anchor-merge.sh"
CURRENT_WRAPPER="$INPUTS/run-current.sh"
CURRENT_DRIVER="$INPUTS/current-driver.sml"
CURRENT_MERGE="$INPUTS/current-merge.sh"
PROFILE_CHUNK_MERGE="$INPUTS/profile-chunk-merge.sh"
WORKER_FUNCTION_MANIFEST="$INPUTS/worker-function-manifest.tsv"
CHECKPOINT_CHAIN_TOOL="$INPUTS/current-checkpoint-chain.sh"
TMPFS_CLEANUP_TOOL="$INPUTS/tmpfs-cleanup.sh"
INTEGRATION_GATE_VERIFIER="$INPUTS/verify-integration-gate.sh"
TIMEOUT=10m
MAX_ATTEMPTS=2
GOAL_CHUNK_LIMIT=$(jq -er '.goal_chunk_limit' \
  "$INPUTS/top-provenance.json")
GOAL_CHUNK_MIN=$(jq -er '.goal_chunk_subdivision.minimum_goals' \
  "$INPUTS/top-provenance.json")
GOAL_CHUNK_POLICY=$(jq -er '.goal_chunk_subdivision.policy_version' \
  "$INPUTS/top-provenance.json")
INFRA_ATTEMPTS=$(jq -er '.goal_chunk_subdivision.infrastructure_attempts' \
  "$INPUTS/top-provenance.json")
CHECKPOINT_POLICY=hh-current-db-soft420-hard600-prune-v2
CHECKPOINT_STORAGE_POLICY=hh-current-checkpoint-prune-v1
CHECKPOINT_MAX_GOALS=${HHEVAL_CURRENT_CHECKPOINT_MAX_GOALS:-128}
test "$CHECKPOINT_MAX_GOALS" -ge 1 -a "$CHECKPOINT_MAX_GOALS" -le 128
CHECKPOINT_ATOM_HEADROOM_KIB=${HHEVAL_CHECKPOINT_ATOM_HEADROOM_KIB:-786432}
test "$CHECKPOINT_ATOM_HEADROOM_KIB" -ge 262144
CHECKPOINT_RESERVATION_POLICY=$(jq -er \
  '.current_checkpoint_chain.heavy_hol_reservation.policy_version' \
  "$INPUTS/top-provenance.json")
CHECKPOINT_RESERVATION_SLOTS=$(jq -er \
  '.current_checkpoint_chain.heavy_hol_reservation.maximum_concurrent_atoms' \
  "$INPUTS/top-provenance.json")
CHECKPOINT_RESERVATION_WAIT_SECONDS=$(jq -er \
  '.current_checkpoint_chain.heavy_hol_reservation.wait_seconds' \
  "$INPUTS/top-provenance.json")
CHECKPOINT_FLOCK_PATH=$(jq -er \
  '.current_checkpoint_chain.heavy_hol_reservation.flock_path' \
  "$INPUTS/top-provenance.json")
CHECKPOINT_FLOCK_SHA256=$(jq -er \
  '.current_checkpoint_chain.heavy_hol_reservation.flock_sha256' \
  "$INPUTS/top-provenance.json")
RG_PATH=$(jq -er \
  '.external_tools.tools[] | select(.name == "rg") | .path' \
  "$INPUTS/top-provenance.json")
test "$CHECKPOINT_RESERVATION_SLOTS" -eq 8
test "$CHECKPOINT_RESERVATION_WAIT_SECONDS" -le 600
HOST_MEMORY_POLICY=$(jq -er \
  '.envelope.host_memory_admission.policy_version' \
  "$INPUTS/top-provenance.json")
HOST_MEMORY_MIN_AVAILABLE_KIB=$(jq -er \
  '.envelope.host_memory_admission.minimum_external_available_kib' \
  "$INPUTS/top-provenance.json")
HOST_MEMORY_SCOPE_HEADROOM_BYTES=$(jq -er \
  '.envelope.host_memory_admission.minimum_scope_headroom_bytes' \
  "$INPUTS/top-provenance.json")
HOST_MEMORY_WAIT_SECONDS=$(jq -er \
  '.envelope.host_memory_admission.wait_seconds' \
  "$INPUTS/top-provenance.json")
CHECKPOINT_RUNTIME_SHA=$(
  for checkpoint_runtime_file in "$CHECKPOINT_CHAIN_TOOL" \
      "$INPUTS/current-checkpoint-base.sml" \
      "$INPUTS/current-controller.sml" "$CURRENT_DRIVER" \
      "$CURRENT_WRAPPER" "$INPUTS/run-a.sh" "$CURRENT_MERGE" \
      "$PROFILE_CHUNK_MERGE" \
      "$INPUTS/current-checkpoint-selftest.sh" \
      "$INPUTS/checkpoint-reservation-selftest.sh" \
      "$INPUTS/current-xargs-oom-selftest.sh" \
      "$INPUTS/profile-unequal-tail-selftest.sh" \
      "$TMPFS_CLEANUP_TOOL" \
      "$INPUTS/tmpfs-cleanup-selftest.sh" \
      "$WORKER_FUNCTION_MANIFEST"; do
    sha256sum "$checkpoint_runtime_file" | awk '{print $1}'
  done | sha256sum | awk '{print $1}')
EXPECTED_THEORIES=$(wc -l <"$INVENTORY")
EXPECTED_GOALS=$(awk -F '\t' '{n += $2} END {print n+0}' "$INVENTORY")
EXPECTED_ROWS=$((EXPECTED_GOALS * 16))
EXPECTED_FIRST8=$((EXPECTED_GOALS * 8))
MEMORY_HIGH=133143986176
MEMORY_MAX=137438953472

. "$CHECKPOINT_CHAIN_TOOL"
. "$TMPFS_CLEANUP_TOOL"

stamp () { printf '%s %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*"; }
sha () { sha256sum "$1" | awk '{print $1}'; }

require_host_memory_headroom () {
  local available current adjusted headroom relative cgroup started wait_seconds
  started=$SECONDS
  wait_seconds=${HHEVAL_HOST_MEMORY_WAIT_OVERRIDE:-$HOST_MEMORY_WAIT_SECONDS}
  relative=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
  cgroup="/sys/fs/cgroup$relative"
  while true; do
    if test -n "${HHEVAL_HOST_MEMORY_AVAILABLE_OVERRIDE:-}"; then
      available=$HHEVAL_HOST_MEMORY_AVAILABLE_OVERRIDE
    else
      available=$(awk '$1 == "MemAvailable:" {print $2}' /proc/meminfo)
    fi
    if test -n "${HHEVAL_SCOPE_MEMORY_CURRENT_OVERRIDE:-}"; then
      current=$HHEVAL_SCOPE_MEMORY_CURRENT_OVERRIDE
    else
      current=$(cat "$cgroup/memory.current")
    fi
    adjusted=$((available + current / 1024))
    headroom=$((MEMORY_HIGH - current))
    if test "$adjusted" -ge "$HOST_MEMORY_MIN_AVAILABLE_KIB" &&
       test "$headroom" -ge "$HOST_MEMORY_SCOPE_HEADROOM_BYTES"; then
      break
    fi
    if test "$((SECONDS - started))" -ge "$wait_seconds"; then
      stamp "host-memory-reject" "external_available_kib=$adjusted" \
        "scope_current_bytes=$current" "scope_headroom_bytes=$headroom" \
        "policy=$HOST_MEMORY_POLICY" >&2
      return 75
    fi
    sleep 5
  done
  if test -d "${OUT:-}" &&
     test "${HHEVAL_MEMORY_ADMISSION_NO_JOURNAL:-0}" != 1; then
    jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      --arg policy "$HOST_MEMORY_POLICY" --argjson host "$available" \
      --argjson scope "$current" --argjson external "$adjusted" \
      --argjson headroom "$headroom" --argjson waited "$((SECONDS - started))" \
      '{time:$time,policy_version:$policy,host_available_kib:$host,
        scope_current_bytes:$scope,external_available_kib:$external,
        scope_headroom_bytes:$headroom,waited_seconds:$waited,
        decision:"admit"}' >>"$OUT/memory-admission.jsonl"
  fi
}

verify_scope () {
  local relative cgroup quota period
  relative=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
  cgroup="/sys/fs/cgroup$relative"
  test "$(cat "$cgroup/memory.high")" = "$MEMORY_HIGH"
  test "$(cat "$cgroup/memory.max")" = "$MEMORY_MAX"
  test "$(cat "$cgroup/memory.swap.max")" = 0
  test "$(cat "$cgroup/memory.oom.group")" = 0
  read -r quota period <"$cgroup/cpu.max"
  test "$quota" != max
  test "$quota" -eq "$((32 * period))"
}

verify_live_external_tools () {
  local name command command_path path resolved digest version
  local version_digest actual count=0
  while IFS="$(printf '\t')" read -r name command_path path digest version \
      version_digest
  do
    case "$path" in /*) ;; *) return 1 ;; esac
    command=${command_path##*/}
    case "$name" in
      prover:* | rg) resolved=$command_path ;;
      *)
        resolved=$(PATH=$CALLER_PATH command -v "$command")
        test "$resolved" = "$command_path"
        ;;
    esac
    test "$(realpath "$resolved")" = "$path"
    test -x "$path" && test ! -L "$path"
    test "$(sha "$path")" = "$digest"
    IFS= read -r actual < <("$path" --version </dev/null 2>&1 || true)
    test -n "$actual"
    test "$actual" = "$version"
    test "$(printf '%s' "$actual" | sha256sum | awk '{print $1}')" = \
      "$version_digest"
    count=$((count + 1))
  done <"$INPUTS/external-tools.tsv"
  test "$count" -eq "$(wc -l <"$INPUTS/external-tools.tsv")"
  PATH=$CALLER_PATH
  export PATH
}

verify_live_source_state () {
  local state base overlay commit patch diff inventory file_path digest
  local signature_theory signature_state signature_target signature_artifact
  local signature_sha implementation_target implementation_artifact
  local implementation_sha data_target data_artifact data_sha
  local signature_overlay
  test "$(git -C "$ROOT" rev-parse HEAD)" = "$(jq -r \
    '.main.commit' "$INPUTS/top-provenance.json")"
  test "$(git -C "$ROOT" diff --binary -- src/holyhammer | sha256sum | \
    awk '{print $1}')" = "$(jq -r '.main.tracked_diff_sha256' \
      "$INPUTS/top-provenance.json")"
  for state in f751 f258; do
    if test "$state" = f751; then
      base=$BASE_F751
      overlay=$OVERLAY_F751
    else
      base=$BASE_F258
      overlay=$OVERLAY_F258
    fi
    commit=$(jq -r --arg state "$state" \
      '.execution_states[$state].base_commit' \
      "$INPUTS/top-provenance.json")
    patch=$(jq -r --arg state "$state" \
      '.execution_states[$state].historical_patch_sha256' \
      "$INPUTS/top-provenance.json")
    diff=$(jq -r --arg state "$state" \
      '.execution_states[$state].current_diff_sha256' \
      "$INPUTS/top-provenance.json")
    inventory=$(jq -r --arg state "$state" \
      '.execution_states[$state].loaded_inventory_sha256' \
      "$INPUTS/top-provenance.json")
    test "$(git -C "$base" rev-parse HEAD)" = "$commit"
    test "$(git -C "$overlay" rev-parse HEAD)" = "$commit"
    test "$(git -C "$base" diff --binary -- \
      src/holyhammer/hhMonomorph.sml | sha256sum | awk '{print $1}')" = \
      "$patch"
    test "$(git -C "$overlay" diff --binary -- src/AI src/holyhammer | \
      sha256sum | awk '{print $1}')" = "$diff"
    sh "$INPUTS/tools/phase2-anchor-check-provenance.sh" \
      "$base" "$INPUTS/loaded-$state.sha256"
    while IFS="$(printf '\t')" read -r file_path digest; do
      test "$(sha "$overlay/$file_path")" = "$digest"
    done < <(jq -r --arg state "$state" '
      .execution_states[$state].current_loaded.sources |
      to_entries[] | [.key, .value] | @tsv
    ' "$INPUTS/top-provenance.json")
    while IFS="$(printf '\t')" read -r file_path digest; do
      test "$(sha "$overlay/$file_path")" = "$digest"
    done < <(jq -r --arg state "$state" '
      .execution_states[$state].current_loaded.objects |
      to_entries[] | [.key, .value] | @tsv
    ' "$INPUTS/top-provenance.json")
    test "$(sha "$INPUTS/loaded-$state.sha256")" = "$inventory"
  done
  test "$(sha "$BASE_F751/bin/hol.state")" = "$(jq -r \
    '.extension_execution.baseline_heap.sha256' \
    "$INPUTS/top-provenance.json")"
  test "$(sha "$OVERLAY_F751/bin/hol.state")" = "$(jq -r \
    '.extension_execution.current_heaps.f751.sha256' \
    "$INPUTS/top-provenance.json")"
  test "$(sha "$OVERLAY_F258/bin/hol.state")" = "$(jq -r \
    '.extension_execution.current_heaps.f258.sha256' \
    "$INPUTS/top-provenance.json")"
  while IFS="$(printf '\t')" read -r signature_theory signature_state \
      signature_target signature_artifact signature_sha \
      implementation_target implementation_artifact implementation_sha \
      data_target data_artifact data_sha; do
    signature_overlay=$(overlay_root "$signature_theory")
    test ! -e "$signature_overlay/$signature_target"
    test ! -e "$signature_overlay/$implementation_target"
    test ! -e "$signature_overlay/$data_target"
  done <"$INPUTS/fallback-current-signatures.tsv"
  test "$(sha "$BASE_F751/src/holyhammer/hhSchedule.sml")" = "$(jq -r \
    '.genuine_f751.schedule_source_sha256' \
    "$INPUTS/extension-scheduler-equivalence.json")"
  while IFS="$(printf '\t')" read -r file_path digest; do
    test "$(sha "$OVERLAY_F258/$file_path")" = "$digest"
    test "$(sha "$ROOT/$file_path")" = "$digest"
  done <"$INPUTS/overlay-f258-allowlisted-files.tsv"
  while IFS="$(printf '\t')" read -r file_path digest; do
    test "$(sha "$OVERLAY_F258/$file_path")" = "$digest"
  done <"$INPUTS/overlay-f258-runtime-objects.tsv"
  while IFS="$(printf '\t')" read -r file_path digest; do
    test "$(sha "$OVERLAY_F258/$file_path")" = "$digest"
  done <"$INPUTS/overlay-f258-runtime-sources.tsv"
  cmp -s <(awk -F '\t' 'FNR > 1 {print $1}' \
      "$INPUTS/phase3-overlay-allowlist.tsv" \
      "$INPUTS/phase3-overlay-support-f258.tsv" | LC_ALL=C sort -u) \
    <(git -C "$OVERLAY_F258" status --porcelain --untracked-files=all -- \
      src/AI src/holyhammer | sed 's/^...//' | LC_ALL=C sort)
}

verify_live_execution_envelope () {
  test -z "${HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE:-}"
  test -z "${HHEVAL_CHECKPOINT_TEST_KILL_AFTER_CHILD:-}"
  test -z "${HHEVAL_CHECKPOINT_TEST_SIGKILL_CHILD:-}"
  test -z "${HHEVAL_CHECKPOINT_TEST_SIGKILL_ONCE_THEORY:-}"
  test -z "${HHEVAL_CHECKPOINT_TEST_AVAILABLE_KIB:-}"
  test -z "${HHEVAL_HOST_MEMORY_AVAILABLE_OVERRIDE:-}"
  test -z "${HHEVAL_SCOPE_MEMORY_CURRENT_OVERRIDE:-}"
  test -z "${HHEVAL_HOST_MEMORY_WAIT_OVERRIDE:-}"
  verify_live_external_tools
  verify_live_source_state
  test "$(findmnt -T "/run/user/$(id -u)" -n -o FSTYPE)" = tmpfs
  test "$(nproc)" -eq 32
  require_host_memory_headroom
  verify_scope
}

verify_sealed_external_tools () {
  local inventory name command_path path digest version version_digest count
  inventory=$(jq -er '.external_tools.inventory_path' \
    "$INPUTS/top-provenance.json")
  test "$inventory" = external-tools.tsv
  test -s "$INPUTS/$inventory" && test ! -L "$INPUTS/$inventory"
  test "$(sha "$INPUTS/$inventory")" = "$(jq -er \
    '.external_tools.inventory_sha256' "$INPUTS/top-provenance.json")"
  count=0
  while IFS="$(printf '\t')" read -r name command_path path digest version \
      version_digest
  do
    test -n "$name" && test -n "$version"
    case "$command_path" in /*) ;; *) return 1 ;; esac
    case "$path" in /*) ;; *) return 1 ;; esac
    case "$digest:$version_digest" in
      *[!0-9a-f:]* | *:*:* | :* | *:) return 1 ;;
    esac
    test "${#digest}" -eq 64 && test "${#version_digest}" -eq 64
    test "$(printf '%s' "$version" | sha256sum | awk '{print $1}')" = \
      "$version_digest"
    count=$((count + 1))
  done <"$INPUTS/$inventory"
  test "$count" -gt 0
  test "$count" -eq "$(cut -f1 "$INPUTS/$inventory" | \
    LC_ALL=C sort -u | wc -l)"
  jq -e --arg inventory "$(sha "$INPUTS/$inventory")" \
    --argjson tools "$(jq -Rn '
      [inputs | split("\t") |
       {name:.[0],command_path:.[1],path:.[2],sha256:.[3],version:.[4],
        version_sha256:.[5]}]
    ' <"$INPUTS/$inventory")" '
      (.external_tools | keys ==
        ["inventory_path","inventory_sha256","schema","tools"]) and
      .external_tools.schema == "hh-task10-external-tools-v1" and
      .external_tools.inventory_path == "external-tools.tsv" and
      .external_tools.inventory_sha256 == $inventory and
      .external_tools.tools == $tools
    ' "$INPUTS/top-provenance.json" >/dev/null
  jq -e '
    . as $root |
    all($root.pinned_provers[];
      . as $prover |
      any($root.external_tools.tools[];
        .name == ("prover:" + $prover.name) and
        .command_path == $prover.path and .sha256 == $prover.sha256 and
        (.version | contains($prover.version)))) and
    ($root.external_tools.tools[] | select(.name == "flock")) as $flock |
    $root.current_checkpoint_chain.heavy_hol_reservation.flock_path ==
      $flock.command_path and
    $root.current_checkpoint_chain.heavy_hol_reservation.flock_sha256 ==
      $flock.sha256
  ' "$INPUTS/top-provenance.json" >/dev/null
}

verify_chunk_equivalence () {
  local evidence="$INPUTS/profile-chunk-evidence"
  local certificate="$INPUTS/profile-chunk-equivalence.json"
  local inventory="$INPUTS/profile-chunk-evidence.sha256"
  local chunk_rows
  test "$(sha "$certificate")" = "$(jq -r \
    '.profile_goal_chunking.equivalence_certificate_sha256' \
    "$INPUTS/top-provenance.json")"
  test "$(sha "$inventory")" = "$(jq -r \
    '.evidence_inventory_sha256' "$certificate")"
  (cd "$evidence" && sha256sum -c "$inventory" >/dev/null)
  jq -e --arg runtime "$CHECKPOINT_RUNTIME_SHA" '
    .schema == "hh-profile-goal-chunk-equivalence-v2" and
    .status == "exact" and .theory == "ASCIInumbers" and .goals == 35 and
    .profile_start == 8 and .profile_length == 8 and
    .chunk_goal_limit == 10 and .chunk_count == 4 and
    .all_eight_profiles_atomic == true and
    .process_reset_between_goal_chunks == true and
    .rows == 280 and .whole_chunks_byte_identical == true and
    .baseline_current_byte_identical == true and
    .nonempty_mismatches == 0 and
    .checkpoint_runtime_sha256 == $runtime and
    (.body_sha256 | test("^[0-9a-f]{64}$")) and
    .memo_sensitive_pair.covered == true and
    .memo_sensitive_pair.e_mono_instances == 128 and
    .memo_sensitive_pair.vampire_mono_instances == 256' \
    "$certificate" >/dev/null
  test "$(find "$evidence/current-parts" -type f \
    -name 'part-*.tsv' | wc -l)" -eq 4
  test "$(find "$evidence/current-parts" -type f \
    -name '*mismatch*' -size +0c | wc -l)" -eq 0
  tail -n +2 "$evidence/current-whole.tsv" | cmp -s - <(
    for part in "$evidence"/current-parts/part-*.tsv; do
      tail -n +2 "$part"
    done)
  tail -n +2 "$evidence/current-merged.tsv" | cmp -s - <(
    for part in "$evidence"/current-parts/part-*.tsv; do
      tail -n +2 "$part"
    done)
  tail -n +2 "$evidence/baseline-last8.tsv" | cmp -s - <(
    for part in "$evidence"/current-parts/part-*.tsv; do
      tail -n +2 "$part"
    done)
  test "$(for part in "$evidence"/current-parts/part-*.tsv; do
    tail -n +2 "$part"
  done | sha256sum | awk '{print $1}')" = \
    "$(jq -r '.body_sha256' "$certificate")"
}

verify_checkpoint_chain_evidence () {
  local evidence="$INPUTS/current-checkpoint-evidence"
  local certificate="$INPUTS/current-checkpoint-equivalence.json"
  local inventory="$INPUTS/current-checkpoint-evidence.sha256"
  test "$(sha "$certificate")" = "$(jq -r \
    '.current_checkpoint_chain.equivalence_certificate_sha256' \
    "$INPUTS/top-provenance.json")"
  test "$(sha "$inventory")" = "$(jq -r \
    '.evidence_inventory_sha256' "$certificate")"
  (cd "$evidence" && sha256sum -c "$inventory" >/dev/null)
  jq -e --arg runtime "$CHECKPOINT_RUNTIME_SHA" '
    .schema == "hh-current-db-checkpoint-equivalence-v1" and
    .status == "exact" and .theory == "ASCIInumbers" and .goals == 35 and
    .monolithic_atoms == 1 and .checkpoint_atoms == 4 and
    .all_eight_profiles_atomic == true and .db_order_preserved == true and
    .rows_byte_identical == true and .rankings_byte_identical == true and
    .canonical_reorder_byte_identical == true and
    .checkpoint_runtime_sha256 == $runtime and
    .selftest.resume_byte_identical == true and
    .selftest.kill_before_commit_recovered == true and
    .selftest.storage_policy_version == "hh-current-checkpoint-prune-v1" and
    .selftest.storage_atoms >= 2 and
    .selftest.scratch_bounded_after_every_commit == true and
    .selftest.maximum_scratch_kib_after_commit == 0 and
    .selftest.completed_chain_scratch_pruned == true and
    .selftest.headroom_guard_rejected == true and
    .selftest.host_memory_policy_version ==
      "hh-external-memory-floor-v2" and
    .selftest.host_memory_guard_rejected == true and
    .selftest.large_binding_streamed == true and
    .selftest.large_binding_bytes > 523190 and
    .selftest.large_binding_exact_resume == true and
    .selftest.oom_policy_continue_verified == true and
    .selftest.killed_atom_status == 137 and
    .selftest.killed_atom_retry_status == 76 and
    .selftest.killed_atom_parent_survived == true and
    .selftest.killed_atom_not_accepted == true and
    .selftest.killed_atom_prior_checkpoint_authoritative == true and
    .selftest.killed_atom_retry_accepted == true and
    .selftest.corrupt_heap_rejected == true and
    .selftest.corrupt_receipt_rejected == true and
    .selftest.stale_model_rejected == true and
    .selftest.stale_runtime_rejected == true and
    .selftest.gap_rejected == true and
    .selftest.overlap_branch_rejected == true and
    .selftest.wrong_db_order_rejected == true and
    .selftest.baseline_cross_feed_rejected == true and
    .reservation_selftest.status == "complete" and
    .reservation_selftest.configured_cap == 8 and
    .reservation_selftest.scheduler_contenders == 16 and
    .reservation_selftest.observed_maximum == 8 and
    .reservation_selftest.all_reservations_released == true and
    .reservation_selftest.advisory_flock == true and
    .reservation_selftest.normal_release == true and
    .reservation_selftest.double_cleanup_idempotent == true and
    .reservation_selftest.killed_owner_auto_released == true and
    .reservation_selftest.stale_owner_metadata_overwritten == true and
    .reservation_selftest.nested_child_fd_closed == true' \
    "$certificate" >/dev/null
}

verify_full_inventory_binding () {
  local theory count corpus_rows
  test -s "$INVENTORY"
  jq -e '.theorem_filter == {}' "$INPUTS/top-provenance.json" \
    >/dev/null
  awk -F '\t' '
    NF != 13 || $1 !~ /^[A-Za-z0-9_]+$/ ||
    $2 !~ /^[1-9][0-9]*$/ || seen[$1]++ {exit 1}
  ' "$INVENTORY"
  while IFS="$(printf '\t')" read -r theory count _; do
    test -f "$CORPUS/$theory.jsonl"
    test ! -L "$CORPUS/$theory.jsonl"
    corpus_rows=$(wc -l <"$CORPUS/$theory.jsonl")
    test "$corpus_rows" -eq "$count"
    jq -e -s --argjson count "$count" '
      length == $count and all(.[]; (.thm | type) == "string" and
        (.thm | length) > 0) and ([.[].thm] | unique | length) == $count
    ' "$CORPUS/$theory.jsonl" >/dev/null
  done <"$INVENTORY"
}

verify_inputs () {
  local main_commit main_diff state base overlay commit diff patch inventory
  local allowlist_sha files_sha file_path digest
  local tool_path tool_digest tool_source predecessor_inventory
  local predecessor_path predecessor_sha support_inventory support_path
  local expected
  if test "${HHEVAL_TASK10_STORAGE_REFRESH:-0}" = 1; then
    test "${HHEVAL_TASK10_RUNNER_LIBRARY_ONLY:-0}" = 1
  else
    test -z "${HHEVAL_TASK10_STORAGE_REFRESH:-}"
  fi
  # Everything in this function is deliberately read-only.  In particular,
  # review-time VERIFY_INPUTS must not depend on, sample, or mutate the live
  # execution scope.  Live admission is performed only after this verifier
  # returns on the normal execution path.
  verify_recorded_run_header_readonly
  jq -e '
    .schema == "hh-task10-a-run-v13" and
    (keys == ["canonical_gate","corpus","current_checkpoint_chain",
      "envelope","execution_state_map","execution_state_mapping",
      "execution_states","extension_execution","external_tools",
      "goal_chunk_limit",
      "goal_chunk_subdivision","goal_digest_schema","initial_cache_files",
      "input_inventory_binding","integration_gate","main",
      "pinned_provers","predecessor_rejections","preflight",
      "profile_goal_chunking","prover_free","ranking_model_provenance",
      "resumable_per_theory_manifests","revision","run","runtime_tools",
      "schema","started","status","support_snapshot","theorem_filter",
      "theory_inventory_sha256","worker_function_preflight"]) and
    (.preflight | keys == ["f30_result_path","f30_result_sha256",
      "input_inventory_path","input_inventory_sha256","probe_result_path",
      "probe_result_sha256","s30_export_volume_result_path",
      "s30_export_volume_result_sha256","s30_result_path",
      "s30_result_sha256","schema"]) and
    .preflight.schema == "hh-task10-a-preflight-support-v1" and
    (.support_snapshot | keys == ["inventory_path","inventory_sha256",
      "schema"]) and
    .support_snapshot.schema == "hh-task10-support-snapshot-v1" and
    (.support_snapshot.inventory_path | type == "string" and length > 0) and
    (.support_snapshot.inventory_sha256 | test("^[0-9a-f]{64}$")) and
    (.runtime_tools | keys == ["files","origin_inventory_sha256",
      "schema"]) and
    (.predecessor_rejections | keys == ["discarded_raw_diagnostics",
      "inventory_path","inventory_sha256","records","schema"]) and
    .predecessor_rejections.schema ==
      "hh-task10-predecessor-rejections-v1" and
    .predecessor_rejections.discarded_raw_diagnostics == true and
    (.predecessor_rejections.records | type == "array" and length > 0) and
    all(.predecessor_rejections.records[];
      keys == ["path","sha256"] and (.path | type == "string") and
      (.sha256 | test("^[0-9a-f]{64}$")))
  ' "$INPUTS/top-provenance.json" >/dev/null
  verify_sealed_external_tools
  support_path=$(jq -r '.support_snapshot.inventory_path' \
    "$INPUTS/top-provenance.json")
  case "$support_path" in /* | *..* | "") return 1 ;; esac
  support_inventory=$INPUTS/$support_path
  test -s "$support_inventory" && test ! -L "$support_inventory"
  test "$(sha "$support_inventory")" = "$(jq -r \
    '.support_snapshot.inventory_sha256' "$INPUTS/top-provenance.json")"
  (cd "$(dirname "$support_inventory")" &&
    sha256sum -c "$(basename "$support_inventory")" >/dev/null)
  cmp -s \
    <(sed -n 's/^[0-9a-f]\{64\}  //p' "$support_inventory" |
      LC_ALL=C sort) \
    <(cd "$(dirname "$support_inventory")" && find . -type f \
      ! -path ./SHA256SUMS -print | LC_ALL=C sort)
  if test "${HHEVAL_TASK10_STORAGE_REFRESH:-0}" != 1; then
    "$INTEGRATION_GATE_VERIFIER" "$INPUTS" \
      "$INPUTS/top-provenance.json"
  fi
  test "$CHECKPOINT_MAX_GOALS" -eq 128
  test "$CHECKPOINT_STORAGE_POLICY" = hh-current-checkpoint-prune-v1
  test "$CHECKPOINT_ATOM_HEADROOM_KIB" -eq 786432
  test "$CHECKPOINT_RESERVATION_POLICY" = hh-current-heavy-hol-flock-v2
  test "$CHECKPOINT_RESERVATION_SLOTS" -eq 8
  test "$CHECKPOINT_RESERVATION_WAIT_SECONDS" -eq 600
  jq -e --arg policy "$CHECKPOINT_STORAGE_POLICY" \
    --argjson headroom "$CHECKPOINT_ATOM_HEADROOM_KIB" \
    --arg reservation "$CHECKPOINT_RESERVATION_POLICY" \
    --argjson slots "$CHECKPOINT_RESERVATION_SLOTS" \
    --argjson reservation_wait "$CHECKPOINT_RESERVATION_WAIT_SECONDS" \
    --arg flock "$CHECKPOINT_FLOCK_PATH" \
    --arg flock_sha "$CHECKPOINT_FLOCK_SHA256" '
      .current_checkpoint_chain.storage_policy_version == $policy and
      .current_checkpoint_chain.atom_headroom_kib == $headroom and
      .current_checkpoint_chain.heavy_hol_reservation.policy_version ==
        $reservation and
      .current_checkpoint_chain.heavy_hol_reservation.maximum_concurrent_atoms ==
        $slots and
      .current_checkpoint_chain.heavy_hol_reservation.wait_seconds ==
        $reservation_wait and
      .current_checkpoint_chain.heavy_hol_reservation.flock_path == $flock and
      .current_checkpoint_chain.heavy_hol_reservation.flock_sha256 ==
        $flock_sha' \
    "$INPUTS/top-provenance.json" >/dev/null
  test "$(sha "$WORKER_FUNCTION_MANIFEST")" = "$(jq -r \
    '.worker_function_preflight.manifest_sha256' \
    "$INPUTS/top-provenance.json")"
  jq -e --arg manifest "$(sha "$WORKER_FUNCTION_MANIFEST")" '
    (.worker_function_preflight | keys == ["children_accepted",
      "children_scheduled","clean_child_declare_f","entrypoints",
      "genuine_timeout_subdivision",
      "infrastructure_failure_retries_same_range","manifest_sha256",
      "parent_range_accepted","resume_byte_identical","schema",
      "stale_corrupt_overlap_cross_feed_rejected","status"]) and
    .worker_function_preflight.schema ==
      "hh-task10-worker-function-preflight-v1" and
    .worker_function_preflight.status == "certified" and
    .worker_function_preflight.manifest_sha256 == $manifest and
    .worker_function_preflight.clean_child_declare_f == true and
    .worker_function_preflight.genuine_timeout_subdivision == true and
    .worker_function_preflight.parent_range_accepted == false and
    .worker_function_preflight.children_scheduled == 2 and
    .worker_function_preflight.children_accepted == 2 and
    .worker_function_preflight.resume_byte_identical == true and
    .worker_function_preflight.entrypoints ==
      ["baseline_theory_once","current_theory_once"] and
    .worker_function_preflight.infrastructure_failure_retries_same_range ==
      true and
    .worker_function_preflight.stale_corrupt_overlap_cross_feed_rejected ==
      true
  ' "$INPUTS/top-provenance.json" >/dev/null
  jq -e '
    (.main | keys == ["commit","tracked_diff_sha256"]) and
    (.main.commit | test("^[0-9a-f]{40}$")) and
    (.main.tracked_diff_sha256 | test("^[0-9a-f]{64}$")) and
    .runtime_tools.schema == "hh-task10-runtime-tools-v2" and
    (.runtime_tools.origin_inventory_sha256 | test("^[0-9a-f]{64}$")) and
    (.runtime_tools.files | keys | length) >= 10 and
    (.runtime_tools.files["run-a.sh"].sha256 |
      test("^[0-9a-f]{64}$")) and
    (.runtime_tools.files["current-driver.sml"].sha256 |
      test("^[0-9a-f]{64}$")) and
    (.runtime_tools.files["current-controller.sml"].sha256 |
      test("^[0-9a-f]{64}$")) and
    (.runtime_tools.files["run-current.sh"].sha256 |
      test("^[0-9a-f]{64}$"))' "$INPUTS/top-provenance.json" >/dev/null
  test "$(sha "$INPUTS/runtime-origin.tsv")" = "$(jq -r \
    '.runtime_tools.origin_inventory_sha256' "$INPUTS/top-provenance.json")"
  while IFS=$'\t' read -r tool_path tool_digest; do
    case "$tool_path" in
      /* | *..* | "") exit 2 ;;
    esac
    test "$(sha "$INPUTS/$tool_path")" = "$tool_digest"
  done < <(jq -r '.runtime_tools.files | to_entries[] |
    [.key,.value.sha256] | @tsv' "$INPUTS/top-provenance.json")
  while IFS=$'\t' read -r tool_path tool_source tool_digest; do
    test "$(jq -r --arg path "$tool_path" \
      '.runtime_tools.files[$path].sha256 // empty' \
      "$INPUTS/top-provenance.json")" = "$tool_digest"
  done <"$INPUTS/runtime-origin.tsv"
  test "$(jq '.runtime_tools.files | length' \
    "$INPUTS/top-provenance.json")" -eq \
    "$(wc -l <"$INPUTS/runtime-origin.tsv")"
  predecessor_inventory=$(jq -r \
    '.predecessor_rejections.inventory_path' \
    "$INPUTS/top-provenance.json")
  case "$predecessor_inventory" in /* | *..* | "") return 1 ;; esac
  test -s "$INPUTS/$predecessor_inventory"
  test "$(sha "$INPUTS/$predecessor_inventory")" = "$(jq -r \
    '.predecessor_rejections.inventory_sha256' \
    "$INPUTS/top-provenance.json")"
  (cd "$(dirname "$INPUTS/$predecessor_inventory")" &&
    sha256sum -c "$(basename "$predecessor_inventory")" >/dev/null)
  while IFS=$'\t' read -r predecessor_path predecessor_sha; do
    case "$predecessor_path" in /* | *..* | "") return 1 ;; esac
    test "$(sha "$INPUTS/$predecessor_path")" = "$predecessor_sha"
  done < <(jq -r '.predecessor_rejections.records[] |
    [.path,.sha256] | @tsv' "$INPUTS/top-provenance.json")
  for state in f751 f258; do
    commit=$(jq -r --arg state "$state" \
      '.execution_states[$state].base_commit' \
      "$INPUTS/top-provenance.json")
    patch=$(jq -r --arg state "$state" \
      '.execution_states[$state].historical_patch_sha256' \
      "$INPUTS/top-provenance.json")
    diff=$(jq -r --arg state "$state" \
      '.execution_states[$state].current_diff_sha256' \
      "$INPUTS/top-provenance.json")
    inventory=$(jq -r --arg state "$state" \
      '.execution_states[$state].loaded_inventory_sha256' \
      "$INPUTS/top-provenance.json")
    case "$commit:$patch:$diff:$inventory" in
      *[!0-9a-f:]* | *:*:*:*:* | :* | *:) return 1 ;;
    esac
    test "${#commit}" -eq 40
    test "${#patch}" -eq 64 && test "${#diff}" -eq 64
    test "${#inventory}" -eq 64
    test "$(sha "$INPUTS/loaded-$state.sha256")" = "$inventory"
    jq -e --arg state "$state" '
      (.execution_states[$state].current_loaded |
        keys == ["objects","sources"]) and
      all(.execution_states[$state].current_loaded.sources | to_entries[];
        (.key | startswith("src/")) and
        (.value | test("^[0-9a-f]{64}$"))) and
      all(.execution_states[$state].current_loaded.objects | to_entries[];
        (.key | startswith("src/")) and
        (.value | test("^[0-9a-f]{64}$")))
    ' "$INPUTS/top-provenance.json" >/dev/null
  done
  allowlist_sha=$(sha "$INPUTS/phase3-overlay-allowlist.tsv")
  test "$allowlist_sha" = "$(jq -r \
    '.execution_state_mapping.overlay_allowlist_sha256' \
    "$INPUTS/top-provenance.json")"
  test "$(sha "$INPUTS/phase3-overlay-support-f258.tsv")" = "$(jq -r \
    '.execution_state_mapping.f258_support_closure_sha256' \
    "$INPUTS/top-provenance.json")"
  test "$(sha "$INPUTS/phase3-overlay-runtime-closure-uos.tsv")" = \
    "$(jq -r '.execution_state_mapping.f258_runtime_closure_sha256' \
      "$INPUTS/top-provenance.json")"
  test "$(sha "$INPUTS/overlay-f258-runtime-objects.tsv")" = \
    "$(jq -r '.execution_state_mapping.f258_runtime_objects_sha256' \
      "$INPUTS/top-provenance.json")"
  test "$(sha "$INPUTS/overlay-f258-runtime-sources.tsv")" = \
    "$(jq -r '.execution_state_mapping.f258_runtime_sources_sha256' \
      "$INPUTS/top-provenance.json")"
  test "$(sha "$INPUTS/fallback-current-signatures.tsv")" = \
    "$(jq -r \
      '.execution_state_mapping.fallback_current_signatures_sha256' \
      "$INPUTS/top-provenance.json")"
  local signature_theory signature_state signature_target signature_artifact
  local signature_sha implementation_target implementation_artifact
  local implementation_sha data_target data_artifact data_sha
  local signature_overlay signature_count=0
  local signature_members
  while IFS=$'\t' read -r signature_theory signature_state \
      signature_target signature_artifact signature_sha \
      implementation_target implementation_artifact implementation_sha \
      data_target data_artifact data_sha; do
    test -n "$signature_theory"
    test "$signature_state" = "$(execution_state "$signature_theory")"
    case "$signature_target" in
      src/*Theory.sig) ;;
      *) return 1 ;;
    esac
    test "$signature_artifact" = \
      "fallback-current-signatures/$signature_target"
    test "$(sha "$INPUTS/$signature_artifact")" = "$signature_sha"
    test "$(awk -F '\t' -v target="$signature_target" \
      -v digest="$signature_sha" \
      '$1 == target && $3 == digest {n++} END {print n+0}' \
      "$INPUTS/fallback-theory-artifacts.tsv")" -eq 1
    test "$implementation_target" = "${signature_target%.sig}.sml"
    test "$implementation_artifact" = \
      "fallback-current-signatures/$implementation_target"
    test "$(sha "$INPUTS/$implementation_artifact")" = \
      "$implementation_sha"
    test "$(awk -F '\t' -v target="$implementation_target" \
      -v digest="$implementation_sha" \
      '$1 == target && $3 == digest {n++} END {print n+0}' \
      "$INPUTS/fallback-theory-artifacts.tsv")" -eq 1
    test "$data_target" = "${signature_target%.sig}.dat"
    test "$data_artifact" = "fallback-current-signatures/$data_target"
    test "$(sha "$INPUTS/$data_artifact")" = "$data_sha"
    test "$(awk -F '\t' -v target="$data_target" -v digest="$data_sha" \
      '$1 == target && $3 == digest {n++} END {print n+0}' \
      "$INPUTS/fallback-theory-artifacts.tsv")" -eq 1
    signature_count=$((signature_count + 1))
  done <"$INPUTS/fallback-current-signatures.tsv"
  test "$(cut -f1 "$INPUTS/fallback-current-signatures.tsv" | \
    LC_ALL=C sort -u | wc -l)" -eq "$signature_count"
  test "$signature_count" -eq "$(jq -r \
    '.execution_state_mapping.fallback_current_signature_count' \
    "$INPUTS/top-provenance.json")"
  signature_members=$(cut -f1 "$INPUTS/fallback-current-signatures.tsv" | \
    LC_ALL=C sort | paste -sd, -)
  test "$signature_members" = "$(jq -r \
    '.execution_state_mapping.fallback_current_signature_members |
      sort | join(",")' "$INPUTS/top-provenance.json")"
  test "$signature_count" -eq 2
  test "$signature_members" = gh224a,gh225a
  test "$(sha "$INPUTS/extension-scheduler-equivalence.json")" = \
    "$(jq -r \
      '.execution_state_mapping.extension_scheduler_equivalence_sha256' \
      "$INPUTS/top-provenance.json")"
  jq -e --arg compatibility \
    "$(sha "$INPUTS/tools/hhSchedule-f751-identity-f258.sml")" '
      .status == "exact" and
      (.genuine_f751.schedule_source_sha256 |
        test("^[0-9a-f]{64}$")) and
      .f258_compatibility_source.schedule_source_sha256 == $compatibility and
      .genuine_f751.rows_sha256 == .f258_compatibility_source.rows_sha256 and
      .genuine_f751.problem_inventory_sha256 ==
        .f258_compatibility_source.problem_inventory_sha256 and
      .checks.row_files_byte_equal == true and
      .checks.complete_problem_inventories_byte_equal == true and
      .checks.memo_sequence_preserved == true and
      .discriminating_collision.distinct == true and
      .discriminating_collision.e.mono_instances == 128 and
      .discriminating_collision.vampire.mono_instances == 256
    ' "$INPUTS/extension-scheduler-equivalence.json" >/dev/null
  files_sha=$(sha "$INPUTS/overlay-f258-allowlisted-files.tsv")
  test "$files_sha" = "$(jq -r \
    '.execution_state_mapping.f258_allowlisted_files_sha256' \
    "$INPUTS/top-provenance.json")"
  (cd "$INPUTS" && sha256sum -c SHA256SUMS >/dev/null)
  if test "${HHEVAL_TASK10_STORAGE_REFRESH:-0}" != 1; then
    verify_chunk_equivalence
    verify_checkpoint_chain_evidence
  fi
  test "$(sha "$INPUTS/profile-first8-evidence/SHA256SUMS")" = \
    "$(jq -r '.profile_goal_chunking.first8_evidence_inventory_sha256' \
      "$INPUTS/top-provenance.json")"
  test "$(sha "$INPUTS/profile-first8-selftest.sh")" = \
    "$(jq -r '.profile_goal_chunking.first8_selftest_sha256' \
      "$INPUTS/top-provenance.json")"
  test "$(sha "$INPUTS/profile-unequal-tail-selftest.sh")" = \
    "$(jq -r '.profile_goal_chunking.unequal_tail_selftest_sha256' \
      "$INPUTS/top-provenance.json")"
  # The two executable regression programs are provenance-bound above.  Their
  # retained results are validated by the sealed integration gate; do not
  # rerun mutating test programs from the read-only tuple verifier.
  test "$(sha "$INVENTORY")" = \
    "$(jq -r '.theory_inventory_sha256' "$INPUTS/top-provenance.json")"
  verify_full_inventory_binding
  while IFS=$'\t' read -r support_path expected; do
    case "$support_path" in /* | *..* | "") return 1 ;; esac
    case "$expected" in *[!0-9a-f]* | "") return 1 ;; esac
    test "${#expected}" -eq 64
    test -s "$INPUTS/$support_path" && test ! -L "$INPUTS/$support_path"
    test "$(sha "$INPUTS/$support_path")" = "$expected"
  done < <(jq -r '
    .preflight as $p |
    [[$p.input_inventory_path,$p.input_inventory_sha256],
     [$p.f30_result_path,$p.f30_result_sha256],
     [$p.s30_result_path,$p.s30_result_sha256],
     [$p.probe_result_path,$p.probe_result_sha256],
     [$p.s30_export_volume_result_path,
      $p.s30_export_volume_result_sha256]][] | @tsv
  ' "$INPUTS/top-provenance.json")
  support_path=$(jq -r '.preflight.input_inventory_path' \
    "$INPUTS/top-provenance.json")
  (cd "$(dirname "$INPUTS/$support_path")" &&
    sha256sum -c "$(basename "$support_path")" >/dev/null)
  test "$(wc -l <"$INVENTORY")" -eq "$EXPECTED_THEORIES"
  awk -F '\t' 'NF != 13 || $1 == "" || $2 !~ /^[1-9][0-9]*$/ ||
    ($8 != "f751" && $8 != "f258") || seen[$1]++ {exit 1}' "$INVENTORY"
  test "$GOAL_CHUNK_LIMIT" -ge 1
  test "$GOAL_CHUNK_LIMIT" -le 128
  test "$GOAL_CHUNK_MIN" -ge 1
  test "$GOAL_CHUNK_MIN" -le "$GOAL_CHUNK_LIMIT"
  test "$GOAL_CHUNK_POLICY" = hh-current-goal-bisect-v1
  test "$INFRA_ATTEMPTS" -ge 1
  test "$HOST_MEMORY_POLICY" = hh-external-memory-floor-v2
  test "$HOST_MEMORY_MIN_AVAILABLE_KIB" -ge 67108864
  test "$HOST_MEMORY_SCOPE_HEADROOM_BYTES" -ge 17179869184
  test "$HOST_MEMORY_WAIT_SECONDS" -le 600
  jq -e --arg policy "$HOST_MEMORY_POLICY" \
    --argjson floor "$HOST_MEMORY_MIN_AVAILABLE_KIB" \
    --argjson headroom "$HOST_MEMORY_SCOPE_HEADROOM_BYTES" \
    --argjson wait "$HOST_MEMORY_WAIT_SECONDS" '
      .envelope.oom_policy == "continue" and
      .envelope.memory_oom_group == 0 and
      (.envelope.host_memory_admission | keys == ["failure_status",
        "formula","minimum_external_available_kib",
        "minimum_scope_headroom_bytes","policy_version","poll_seconds",
        "wait_seconds"]) and
      .envelope.host_memory_admission.policy_version == $policy and
      .envelope.host_memory_admission.formula ==
        "MemAvailable_kib + scope_memory_current_bytes / 1024" and
      .envelope.host_memory_admission.minimum_external_available_kib ==
        $floor and
      .envelope.host_memory_admission.minimum_scope_headroom_bytes ==
        $headroom and .envelope.host_memory_admission.wait_seconds == $wait and
      .envelope.host_memory_admission.poll_seconds == 5 and
      .envelope.host_memory_admission.failure_status == 75' \
    "$INPUTS/top-provenance.json" >/dev/null
}

initialize () {
  local input_sha
  DURABLE_ONLY_RESUME=0
  input_sha=$(sha "$INPUTS/SHA256SUMS")
  if test -e "$OUT" || test -e "$STATE"; then
    test -s "$OUT/run.json"
    if ! cmp -s "$OUT/run.json" "$INPUTS/top-provenance.json"; then
      echo "task10 tuple mismatch: sealed input does not match accepted run header" \
        >&2
      return 78
    fi
    if test ! -e "$STATE"; then
      test -s "$OUT/result.json"
      test -s "$OUT/tmpfs-cleanup.json"
      jq -e '.status == "complete"' "$OUT/result.json" >/dev/null
      jq -e --arg result "$(sha "$OUT/result.json")" '
        .schema == "hh-task10-tmpfs-cleanup-v1" and
        .status == "removed" and .durable_binding_sha256 == $result and
        .tmpfs_root_absent_after_cleanup == true' \
        "$OUT/tmpfs-cleanup.json" >/dev/null
      DURABLE_ONLY_RESUME=1
    else
      test -d "$STATE" && test ! -L "$STATE"
    fi
    jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      --arg event resume --arg run_sha "$(sha "$OUT/run.json")" \
      --arg input_sha "$input_sha" \
      '{time:$time,event:$event,run_header_sha256:$run_sha,
        input_inventory_sha256:$input_sha}' \
      >>"$OUT/invocations.jsonl"
    return
  fi
  test ! -e "$OUT"
  test ! -e "$STATE"
  mkdir -p "$OUT"/{baseline-first8,baseline-last8,baseline,baseline-premises}
  mkdir -p "$OUT"/{current-first8,current-last8,current,current-rankings}
  mkdir -p "$OUT"/{mismatch,log,invocations}
  mkdir -p "$OUT"/{baseline-last8-parts,current-first8-parts}
  mkdir -p "$OUT"/{current-last8-parts,theorem-names}
  mkdir -p "$STATE"/{baseline,current,launch}
  cp "$INPUTS/top-provenance.json" "$OUT/run.json"
  chmod 0444 "$OUT/run.json"
  jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg event start --arg run_sha "$(sha "$OUT/run.json")" \
    --arg input_sha "$input_sha" \
    '{time:$time,event:$event,run_header_sha256:$run_sha,
      input_inventory_sha256:$input_sha}' \
    >"$OUT/invocations.jsonl"
}

cleanup_successful_run () {
  local result_sha
  test -s "$OUT/result.json"
  result_sha=$(sha "$OUT/result.json")
  if test -e "$STATE"; then
    hh_task10_cleanup_tmpfs "$STATE" "$OUT/tmpfs-cleanup.json" \
      "$result_sha"
  else
    test -s "$OUT/tmpfs-cleanup.json"
    jq -e --arg result "$result_sha" '
      .schema == "hh-task10-tmpfs-cleanup-v1" and
      .status == "removed" and .durable_binding_sha256 == $result and
      .tmpfs_root_absent_after_cleanup == true' \
      "$OUT/tmpfs-cleanup.json" >/dev/null
  fi
  test ! -e "$STATE"
}

verify_existing_tuple_readonly () {
  if test -e "$OUT" || test -e "$STATE"; then
    test -s "$OUT/run.json" && test ! -L "$OUT/run.json"
    if ! cmp -s "$OUT/run.json" "$INPUTS/top-provenance.json"; then
      echo "task10 tuple mismatch: sealed input does not match accepted run header" \
        >&2
      return 78
    fi
  fi
}

verify_recorded_run_header_readonly () {
  if test -e "$OUT" || test -e "$STATE"; then
    test -s "$OUT/run.json" && test ! -L "$OUT/run.json"
    cmp -s "$OUT/run.json" "$INPUTS/top-provenance.json"
    jq -e --argjson high "$MEMORY_HIGH" \
      --argjson max "$MEMORY_MAX" \
      --arg policy "$HOST_MEMORY_POLICY" \
      --argjson floor "$HOST_MEMORY_MIN_AVAILABLE_KIB" \
      --argjson headroom "$HOST_MEMORY_SCOPE_HEADROOM_BYTES" \
      --argjson wait "$HOST_MEMORY_WAIT_SECONDS" '
      (.envelope | keys == ["atomic_durable_copyback",
        "atomic_timeout_seconds","cpu_quota_cores",
        "host_memory_admission","memory_high_bytes","memory_max_bytes",
        "memory_oom_group","memory_swap_max_bytes","oom_policy",
        "parallel_hol_workers","tmpfs_scratch"]) and
      .envelope.parallel_hol_workers == 16 and
      .envelope.cpu_quota_cores == 32 and
      .envelope.memory_high_bytes == $high and
      .envelope.memory_max_bytes == $max and
      .envelope.memory_swap_max_bytes == 0 and
      .envelope.oom_policy == "continue" and
      .envelope.memory_oom_group == 0 and
      .envelope.atomic_timeout_seconds == 600 and
      .envelope.tmpfs_scratch == true and
      .envelope.atomic_durable_copyback == true and
      .envelope.host_memory_admission.policy_version == $policy and
      .envelope.host_memory_admission.minimum_external_available_kib ==
        $floor and
      .envelope.host_memory_admission.minimum_scope_headroom_bytes ==
        $headroom and
      .envelope.host_memory_admission.wait_seconds == $wait
    ' "$OUT/run.json" >/dev/null
  fi
}

field () {
  local theory=$1 column=$2
  awk -F '\t' -v theory="$theory" -v column="$column" \
    '$1 == theory {print $column; exit}' "$INVENTORY"
}

execution_state () { field "$1" 8; }

baseline_root () {
  case "$(execution_state "$1")" in
    f751) printf '%s\n' "$BASE_F751" ;;
    f258) printf '%s\n' "$BASE_F258" ;;
    *) return 2 ;;
  esac
}

overlay_root () {
  case "$(execution_state "$1")" in
    f751) printf '%s\n' "$OVERLAY_F751" ;;
    f258) printf '%s\n' "$OVERLAY_F258" ;;
    *) return 2 ;;
  esac
}

make_invocation () {
  local theory=$1 count=$2 path
  path="$OUT/invocations/$theory.json"
  local directory dat ui member member_sha state base overlay heap_relative
  local base_heap_sha overlay_heap_sha object_inventory holmakefile_sha
  local extension_heap_relative extension_base_heap extension_current_heap
  local names_path names_sha signature_binding
  names_path=$(theorem_names_file "$theory" "$count")
  names_sha=$(sha "$names_path")
  directory=$(field "$theory" 3)
  dat=$(field "$theory" 4)
  ui=$(field "$theory" 5)
  member=$(field "$theory" 6)
  member_sha=$(field "$theory" 7)
  state=$(execution_state "$theory")
  heap_relative=$(field "$theory" 9)
  base_heap_sha=$(field "$theory" 10)
  overlay_heap_sha=$(field "$theory" 11)
  object_inventory=$(field "$theory" 12)
  holmakefile_sha=$(field "$theory" 13)
  base=$(baseline_root "$theory")
  overlay=$(overlay_root "$theory")
  extension_heap_relative=$(jq -r \
    '.extension_execution.baseline_heap.relative_path' \
    "$INPUTS/top-provenance.json")
  extension_base_heap=$(jq -r '.extension_execution.baseline_heap.sha256' \
    "$INPUTS/top-provenance.json")
  extension_current_heap=$(jq -r --arg state "$state" \
      '.extension_execution.current_heaps[$state].sha256' \
      "$INPUTS/top-provenance.json")
  signature_binding=$(fallback_signature_binding "$theory")
  test "$(sha "$directory/.hol/objs/${theory}Theory.dat")" = "$dat"
  test "$(sha "$directory/.hol/objs/${theory}Theory.ui")" = "$ui"
  test "$(sha "$CORPUS/$theory.jsonl")" = "$member_sha"
  test "$(sha "$base/$heap_relative")" = "$base_heap_sha"
  test "$(sha "$overlay/$heap_relative")" = "$overlay_heap_sha"
  test "$(sha "$BASE_F751/$extension_heap_relative")" = \
    "$extension_base_heap"
  test "$(sha "$overlay/$extension_heap_relative")" = \
    "$extension_current_heap"
  test "$(cd "$directory/.hol/objs" &&
    find . -maxdepth 1 -type f -print0 | LC_ALL=C sort -z |
      xargs -0 sha256sum | sha256sum | awk '{print $1}')" = \
    "$object_inventory"
  if test "$holmakefile_sha" = -; then
    test ! -e "$directory/Holmakefile"
  else
    test "$(sha "$directory/Holmakefile")" = "$holmakefile_sha"
  fi
  if test -e "$path"; then
    test ! -L "$path"
    jq -e --arg theory "$theory" --argjson goals "$count" \
      --arg state "$state" \
      --arg heap "$heap_relative" --arg base_heap "$base_heap_sha" \
      --arg overlay_heap "$overlay_heap_sha" \
      --arg extension_heap "$extension_heap_relative" \
      --arg extension_base "$extension_base_heap" \
      --arg extension_current "$extension_current_heap" \
      --arg objects "$object_inventory" --arg hmf "$holmakefile_sha" \
      --arg names "$names_sha" --argjson chunk_limit "$GOAL_CHUNK_LIMIT" \
      --arg run_sha "$(sha "$OUT/run.json")" \
      --argjson signature "$signature_binding" \
      '.schema == "hh-task10-a-invocation-v4" and
       .theory == $theory and .goals == $goals and
       .execution_state == $state and
       .nested_heap.relative_path == $heap and
       .nested_heap.baseline_sha256 == $base_heap and
       .nested_heap.current_sha256 == $overlay_heap and
       .extension_heap.relative_path == $extension_heap and
       .extension_heap.baseline_sha256 == $extension_base and
       .extension_heap.current_sha256 == $extension_current and
       .theory_artifact.object_inventory_sha256 == $objects and
       .theory_artifact.source_holmakefile_sha256 == $hmf and
       .fallback_current_signature == $signature and
       .theorem_names_sha256 == $names and
       .goal_chunk_limit == $chunk_limit and
       .run_header_sha256 == $run_sha' "$path" >/dev/null
    return
  fi
  jq -n --arg theory "$theory" --argjson goals "$count" \
    --arg run_sha "$(sha "$OUT/run.json")" \
    --arg input_sha "$(sha "$INPUTS/SHA256SUMS")" \
    --arg directory "$directory" --arg dat "$dat" --arg ui "$ui" \
    --arg member "$member" --arg member_sha "$member_sha" \
    --arg state "$state" --arg base "$base" --arg overlay "$overlay" \
    --arg heap "$heap_relative" --arg base_heap "$base_heap_sha" \
    --arg overlay_heap "$overlay_heap_sha" \
    --arg extension_heap "$extension_heap_relative" \
    --arg extension_base "$extension_base_heap" \
    --arg extension_current "$extension_current_heap" \
    --arg objects "$object_inventory" --arg hmf "$holmakefile_sha" \
    --arg names "$names_sha" --argjson chunk_limit "$GOAL_CHUNK_LIMIT" \
    --argjson signature "$signature_binding" \
    '{schema:"hh-task10-a-invocation-v4",theory:$theory,goals:$goals,
      execution_state:$state,baseline_root:$base,current_root:$overlay,
      run_header_sha256:$run_sha,input_inventory_sha256:$input_sha,
      canonical_journal:{member:$member,member_sha256:$member_sha},
      theory_artifact:{directory:$directory,dat_sha256:$dat,ui_sha256:$ui,
        object_inventory_sha256:$objects,source_holmakefile_sha256:$hmf},
      fallback_current_signature:$signature,
      nested_heap:{relative_path:$heap,baseline_sha256:$base_heap,
        current_sha256:$overlay_heap},
      extension_heap:{baseline_state:"f751",current_state:$state,
        relative_path:$extension_heap,baseline_sha256:$extension_base,
        current_sha256:$extension_current},
      profile_batches:[{start:0,length:8,replay_theory:true},
        {start:8,length:8,replay_theory:false}],
      theorem_names_sha256:$names,goal_chunk_limit:$chunk_limit,
      atomic_timeout_seconds:600}' >"$path"
  chmod 0444 "$path"
}

fallback_signature_binding () {
  local theory=$1 row state target artifact digest implementation_target
  local implementation_artifact implementation_digest object_target
  local implementation_object_target data_target data_artifact data_digest
  local data_object_target
  row=$(awk -F '\t' -v theory="$theory" '$1 == theory {print}' \
    "$INPUTS/fallback-current-signatures.tsv")
  if test -z "$row"; then
    printf 'null\n'
    return
  fi
  IFS=$'\t' read -r _ state target artifact digest implementation_target \
    implementation_artifact implementation_digest data_target data_artifact \
    data_digest <<<"$row"
  object_target="${target%/*}/.hol/objs/${target##*/}"
  implementation_object_target="${implementation_target%/*}/.hol/objs/${implementation_target##*/}"
  data_object_target="${data_target%/*}/.hol/objs/${data_target##*/}"
  jq -nc --arg state "$state" --arg target "$target" \
    --arg object_target "$object_target" --arg artifact "$artifact" \
    --arg digest "$digest" --arg implementation "$implementation_target" \
    --arg implementation_object "$implementation_object_target" \
    --arg implementation_artifact "$implementation_artifact" \
    --arg implementation_digest "$implementation_digest" \
    --arg data "$data_target" --arg data_object "$data_object_target" \
    --arg data_artifact "$data_artifact" --arg data_digest "$data_digest" \
    '{schema:"hh-fallback-current-signature-v1",execution_state:$state,
      interface:{overlay_relative_path:$target,
        poly_object_relative_path:$object_target,
        input_relative_path:$artifact,sha256:$digest},
      implementation:{overlay_relative_path:$implementation,
        poly_object_relative_path:$implementation_object,
        input_relative_path:$implementation_artifact,
        sha256:$implementation_digest},
      data:{overlay_relative_path:$data,
        poly_object_relative_path:$data_object,
        input_relative_path:$data_artifact,sha256:$data_digest}}'
}

stage_current_signature () {
  local theory=$1 worker_key=$2 row state target artifact digest overlay
  local implementation_target implementation_artifact implementation_digest
  local implementation_object_target data_target data_artifact data_digest
  local data_object_target
  local marker lock object_target hol_dir object_dir hol_created=0
  local object_created=0
  row=$(awk -F '\t' -v theory="$theory" '$1 == theory {print}' \
    "$INPUTS/fallback-current-signatures.tsv")
  test -n "$row" || return 0
  IFS=$'\t' read -r _ state target artifact digest implementation_target \
    implementation_artifact implementation_digest data_target data_artifact \
    data_digest <<<"$row"
  test "$state" = "$(execution_state "$theory")"
  overlay=$(overlay_root "$theory")
  artifact="$INPUTS/$artifact"
  target="$overlay/$target"
  implementation_artifact="$INPUTS/$implementation_artifact"
  implementation_target="$overlay/$implementation_target"
  data_artifact="$INPUTS/$data_artifact"
  data_target="$overlay/$data_target"
  hol_dir="${target%/*}/.hol"
  object_dir="$hol_dir/objs"
  object_target="$object_dir/${target##*/}"
  implementation_object_target="$object_dir/${implementation_target##*/}"
  data_object_target="$object_dir/${data_target##*/}"
  marker="$STATE/signature-staging/$worker_key.tsv"
  lock="$STATE/signature-locks/$theory.lock"
  test "$worker_key" = "${worker_key//[^A-Za-z0-9_.-]/}"
  mkdir -p "$STATE/signature-staging" "$STATE/signature-locks"
  mkdir "$lock"
  test ! -e "$target"
  test ! -e "$object_target"
  test ! -e "$implementation_target"
  test ! -e "$implementation_object_target"
  test ! -e "$data_target"
  test ! -e "$data_object_target"
  test "$(sha "$artifact")" = "$digest"
  test "$(sha "$implementation_artifact")" = "$implementation_digest"
  test "$(sha "$data_artifact")" = "$data_digest"
  if test ! -d "$hol_dir"; then mkdir "$hol_dir"; hol_created=1; fi
  if test ! -d "$object_dir"; then
    mkdir "$object_dir"
    object_created=1
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$target" "$object_target" "$artifact" "$digest" "$lock" \
    "$implementation_target" "$implementation_object_target" \
    "$implementation_artifact" "$implementation_digest" \
    "$data_target" "$data_object_target" "$data_artifact" "$data_digest" \
    "$object_created" "$hol_created" >"$marker"
  ln -s "$artifact" "$target" || {
    unstage_current_signature "$worker_key" || true
    return 1
  }
  ln -s "$artifact" "$object_target" || {
    unstage_current_signature "$worker_key" || true
    return 1
  }
  ln -s "$implementation_artifact" "$implementation_target" || {
    unstage_current_signature "$worker_key" || true
    return 1
  }
  ln -s "$implementation_artifact" "$implementation_object_target" || {
    unstage_current_signature "$worker_key" || true
    return 1
  }
  ln -s "$data_artifact" "$data_target" || {
    unstage_current_signature "$worker_key" || true
    return 1
  }
  ln -s "$data_artifact" "$data_object_target" || {
    unstage_current_signature "$worker_key" || true
    return 1
  }
  test -L "$target"
  test -L "$object_target"
  test -L "$implementation_target"
  test -L "$implementation_object_target"
  test -L "$data_target"
  test -L "$data_object_target"
  test "$(readlink "$target")" = "$artifact"
  test "$(readlink "$object_target")" = "$artifact"
  test "$(sha "$target")" = "$digest"
  test "$(sha "$object_target")" = "$digest"
  test "$(sha "$implementation_target")" = "$implementation_digest"
  test "$(sha "$implementation_object_target")" = \
    "$implementation_digest"
  test "$(sha "$data_target")" = "$data_digest"
  test "$(sha "$data_object_target")" = "$data_digest"
}

unstage_current_signature () {
  local worker_key=$1 marker target object_target artifact digest lock
  local implementation_target implementation_object_target
  local implementation_artifact implementation_digest
  local data_target data_object_target data_artifact data_digest
  local object_created hol_created
  marker="$STATE/signature-staging/$worker_key.tsv"
  test -e "$marker" || return 0
  IFS=$'\t' read -r target object_target artifact digest lock \
    implementation_target implementation_object_target \
    implementation_artifact implementation_digest data_target \
    data_object_target data_artifact data_digest object_created hol_created \
    <"$marker"
  if test -L "$target"; then
    test "$(readlink "$target")" = "$artifact"
    test "$(sha "$target")" = "$digest"
    unlink "$target"
  fi
  if test -L "$object_target"; then
    test "$(readlink "$object_target")" = "$artifact"
    test "$(sha "$object_target")" = "$digest"
    unlink "$object_target"
  fi
  if test -L "$implementation_target"; then
    test "$(readlink "$implementation_target")" = "$implementation_artifact"
    test "$(sha "$implementation_target")" = "$implementation_digest"
    unlink "$implementation_target"
  fi
  if test -L "$implementation_object_target"; then
    test "$(readlink "$implementation_object_target")" = \
      "$implementation_artifact"
    test "$(sha "$implementation_object_target")" = \
      "$implementation_digest"
    unlink "$implementation_object_target"
  fi
  if test -L "$data_target"; then
    test "$(readlink "$data_target")" = "$data_artifact"
    test "$(sha "$data_target")" = "$data_digest"
    unlink "$data_target"
  fi
  if test -L "$data_object_target"; then
    test "$(readlink "$data_object_target")" = "$data_artifact"
    test "$(sha "$data_object_target")" = "$data_digest"
    unlink "$data_object_target"
  fi
  if test "$object_created" -eq 1; then rmdir "${object_target%/*}"; fi
  if test "$hol_created" -eq 1; then rmdir "${object_target%/*/*}"; fi
  rmdir "$lock"
  unlink "$marker"
}

cleanup_staged_signatures () {
  local marker worker_key status=0
  test -d "$STATE/signature-staging" || return 0
  while IFS= read -r marker; do
    worker_key=${marker##*/}
    worker_key=${worker_key%.tsv}
    unstage_current_signature "$worker_key" || status=1
  done < <(find "$STATE/signature-staging" -maxdepth 1 -type f \
    -name '*.tsv' -print)
  return "$status"
}

verify_no_staged_signatures () {
  local theory state target artifact digest implementation_target
  local implementation_artifact implementation_digest overlay object_target
  local implementation_object_target data_target data_artifact data_digest
  local data_object_target
  test -z "$(find "$STATE/signature-staging" -maxdepth 1 -type f \
    -print -quit 2>/dev/null)"
  while IFS=$'\t' read -r theory state target artifact digest \
      implementation_target implementation_artifact \
      implementation_digest data_target data_artifact data_digest; do
    overlay=$(overlay_root "$theory")
    object_target="${target%/*}/.hol/objs/${target##*/}"
    implementation_object_target="${implementation_target%/*}/.hol/objs"
    implementation_object_target+="/${implementation_target##*/}"
    data_object_target="${data_target%/*}/.hol/objs/${data_target##*/}"
    test ! -e "$overlay/$target"
    test ! -e "$overlay/$object_target"
    test ! -e "$overlay/$implementation_target"
    test ! -e "$overlay/$implementation_object_target"
    test ! -e "$overlay/$data_target"
    test ! -e "$overlay/$data_object_target"
  done <"$INPUTS/fallback-current-signatures.tsv"
}

theorem_names () {
  local theory=$1 selected
  selected=$(jq -r --arg theory "$theory" \
    '.theorem_filter[$theory][]? // empty' "$INPUTS/top-provenance.json" |
    paste -sd ' ' -)
  if test -z "$selected"; then
    jq -r '.thm' "$CORPUS/$theory.jsonl" | paste -sd ' ' -
    return
  fi
  for theorem in $selected; do
    jq -e --arg theorem "$theorem" \
      'select(.thm == $theorem)' "$CORPUS/$theory.jsonl" >/dev/null
  done
  printf '%s\n' "$selected"
}

theorem_names_file () {
  local theory=$1 count=$2 path
  path="$OUT/theorem-names/$theory.txt"
  if test -e "$path"; then
    test -f "$path"
    test ! -L "$path"
    test "$(wc -l <"$path")" -eq "$count"
    test "$(paste -sd ' ' "$path")" = "$(theorem_names "$theory")"
    printf '%s\n' "$path"
    return
  fi
  theorem_names "$theory" | tr ' ' '\n' >"$path.partial.$$"
  test "$(wc -l <"$path.partial.$$")" -eq "$count"
  mv "$path.partial.$$" "$path"
  chmod 0444 "$path"
  printf '%s\n' "$path"
}

launch_directory () {
  local kind=$1 theory=$2 start=$3 result
  result="$STATE/launch/$kind-$theory-$start"
  local directory state root heap_relative heap heap_sha
  directory=$(field "$theory" 3)
  state=$(execution_state "$theory")
  heap_relative=$(field "$theory" 9)
  case "$kind-$start" in
    baseline-8)
      root=$BASE_F751
      heap_relative=$(jq -r \
        '.extension_execution.baseline_heap.relative_path' \
        "$INPUTS/top-provenance.json")
      heap_sha=$(jq -r '.extension_execution.baseline_heap.sha256' \
        "$INPUTS/top-provenance.json")
      ;;
    current-8)
      root=$(overlay_root "$theory")
      heap_relative=$(jq -r \
        --arg state "$(execution_state "$theory")" \
        '.extension_execution.current_heaps[$state].relative_path' \
        "$INPUTS/top-provenance.json")
      heap_sha=$(jq -r --arg state "$(execution_state "$theory")" \
        '.extension_execution.current_heaps[$state].sha256' \
        "$INPUTS/top-provenance.json")
      ;;
    baseline-0)
      root=$(baseline_root "$theory")
      heap_sha=$(field "$theory" 10)
      ;;
    current-0)
      root=$(overlay_root "$theory")
      heap_sha=$(field "$theory" 11)
      ;;
    *) return 2 ;;
  esac
  heap=$root/$heap_relative
  test "$(sha "$heap")" = "$heap_sha"
  mkdir -p "$result/.hol/objs"
  if ! find "$result/.hol/objs" -mindepth 1 -print -quit | grep -q .; then
    find "$directory/.hol/objs" -maxdepth 1 -type f \
      -exec ln -s -t "$result/.hol/objs" {} +
  fi
  if test -e "$result/Holmakefile"; then
    test ! -L "$result/Holmakefile"
    test "$(sed -n 's/^HOLHEAP = //p' "$result/Holmakefile")" = "$heap"
  else
    printf 'HOLHEAP = %s\n' "$heap" >"$result/Holmakefile"
    chmod 0444 "$result/Holmakefile"
  fi
  printf '%s\n' "$result"
}

baseline_part_once () {
  local theory=$1 count=$2 start=$3 output=$4 log=$5
  local invocation="$OUT/invocations/$theory.json" names launch status base
  local anchor_state behavior provenance runtime runtime_commit runtime_state
  local schedule_source
  local premise_provenance premise_read_only
  local first_header model_inventory model_features model_weights model_rows
  local -a ranking_model_env=()
  schedule_source=
  names=${6-}
  if test -z "$names"; then names=$(theorem_names "$theory"); fi
  test "$(wc -w <<<"$names")" -eq "$count"
  launch=$(launch_directory baseline "$theory" "$start")
  if test "$start" -eq 0; then
    anchor_state=$(execution_state "$theory")
    base=$(baseline_root "$theory")
  else
    # The exact first-eight gate worker writes the maximum-length ranking.
    # The genuine f751 Phase2 exporter then consumes that ranking read-only
    # under its complete heap while retaining the mapped target artifacts.
    anchor_state=f751
    base=$BASE_F751
  fi
  behavior=$(jq -r --arg state "$anchor_state" \
    '.execution_states[$state].base_commit' "$INPUTS/top-provenance.json")
  provenance=$(jq -r --arg state "$anchor_state" \
    '.execution_states[$state].loaded_inventory_sha256' \
    "$INPUTS/top-provenance.json")
  if test "$start" -eq 0; then
    runtime=$(baseline_root "$theory")
    runtime_state=$(execution_state "$theory")
    premise_read_only=0
  else
    runtime=$BASE_F751
    runtime_state=f751
    premise_read_only=1
    test -s "$OUT/baseline-first8/$theory.tsv"
    first_header=$(head -1 "$OUT/baseline-first8/$theory.tsv" | cut -f2-)
    model_inventory=$(jq -er '.model_inventory_sha1' <<<"$first_header")
    model_features=$(jq -er '.model_features_sha1' <<<"$first_header")
    model_weights=$(jq -er '.model_weights_sha1' <<<"$first_header")
    model_rows=$(jq -er '.model_feature_rows' <<<"$first_header")
    ranking_model_env=(
      "HHEVAL_ANCHOR_MODEL_INVENTORY_SHA1=$model_inventory"
      "HHEVAL_ANCHOR_MODEL_FEATURES_SHA1=$model_features"
      "HHEVAL_ANCHOR_MODEL_WEIGHTS_SHA1=$model_weights"
      "HHEVAL_ANCHOR_MODEL_FEATURE_ROWS=$model_rows")
  fi
  runtime_commit=$(jq -r --arg state "$runtime_state" \
    '.execution_states[$state].base_commit' "$INPUTS/top-provenance.json")
  premise_provenance=$(jq -r --arg state "$(execution_state "$theory")" \
    '.execution_states[$state].loaded_inventory_sha256' \
    "$INPUTS/top-provenance.json")
  require_host_memory_headroom || return
  stamp "baseline theory=$theory start=$start invocation=$(sha "$invocation")" \
    >"$log.partial.$$"
  if (cd "$STATE/baseline" && \
    timeout --signal=TERM --kill-after=120s "$TIMEOUT" \
    env PATH="$INPUTS/bin:$PATH" HOLDIR="$base" \
      HHEVAL_PHASE3_TMPFS="$STATE/baseline" \
      HHEVAL_ANCHOR_WORKTREE="$base" \
      HHEVAL_ANCHOR_RUNTIME_WORKTREE="$runtime" \
      HHEVAL_ANCHOR_RUNTIME_COMMIT="$runtime_commit" \
      HHEVAL_ANCHOR_SCHEDULE_SOURCE="$schedule_source" \
      HHEVAL_ANCHOR_EXECUTION_STATE="$anchor_state" \
      HHEVAL_ANCHOR_THEORY_DIR="$launch" \
      HHEVAL_ANCHOR_THEORY="$theory" \
      HHEVAL_ANCHOR_THEOREMS="$names" \
      HHEVAL_ANCHOR_PREMISES_DIRECTORY="$PREMISES/$theory" \
      HHEVAL_ANCHOR_PREMISES_PROVENANCE_SHA256="$premise_provenance" \
      HHEVAL_ANCHOR_PREMISES_READ_ONLY="$premise_read_only" \
      HHEVAL_ANCHOR_PROFILE_START="$start" \
      HHEVAL_ANCHOR_PROFILE_LENGTH=8 \
      HHEVAL_ANCHOR_INVOCATION_PROVENANCE_SHA256="$(sha "$invocation")" \
      HHEVAL_ANCHOR_OUTPUT="$output.partial.$$" \
      "${ranking_model_env[@]}" \
      "$BASELINE_TOOL" >>"$log.partial.$$" 2>&1); then
    status=0
  else
    status=$?
  fi
  if test "$status" -ne 0; then return "$status"; fi
  test "$(wc -l <"$output.partial.$$")" -eq "$((count * 8 + 1))" || \
    return
  head -1 "$output.partial.$$" | cut -f2- | jq -e \
    --argjson goals "$count" --argjson start "$start" \
    --arg invocation "$(sha "$invocation")" \
    --arg behavior "$behavior" --arg provenance "$provenance" '
      .goals == $goals and .row_count == $goals * 8 and
      .goal_digest_schema == "hh-goal-struct-v1" and
      .profile_start == $start and .profile_length == 8 and
      .invocation_provenance_sha256 == $invocation and
      .behavior_source_commit == $behavior and
      .baseline_provenance_sha256 == $provenance and
      .task13_internal_key_pair_mismatches == 0 and
      .task13_premise_mismatches == 0 and
      .task13_request_key_mismatches == 0 and .prover_spawns == 0 and
      (.model_inventory_sha1 | test("^[0-9a-f]{40}$")) and
      (.model_features_sha1 | test("^[0-9a-f]{40}$")) and
      (.model_weights_sha1 | test("^[0-9a-f]{40}$")) and
      (.goal_bindings | length) == $goals and
      (if $start == 0 then
         .task13_execution_goals >= $goals and
         .task13_rows_checked == .task13_execution_goals * 8
       else .task13_rows_checked == 0 end)' >/dev/null || return
  mv "$output.partial.$$" "$output"
  mv "$log.partial.$$" "$log"
}

baseline_chunked_last8 () {
  local theory=$1 count=$2 output=$3 names_file part_dir
  local offset length words part log attempt status merged
  names_file=$(theorem_names_file "$theory" "$count")
  part_dir="$OUT/baseline-last8-parts/$theory"
  mkdir -p "$part_dir"
  for ((offset=0; offset<count; offset+=GOAL_CHUNK_LIMIT)); do
    length=$GOAL_CHUNK_LIMIT
    if ((offset + length > count)); then length=$((count - offset)); fi
    part=$(printf '%s/part-%06d.tsv' "$part_dir" "$offset")
    log=${part%.tsv}.log
    words=$(sed -n "$((offset + 1)),$((offset + length))p" \
      "$names_file" | paste -sd ' ' -)
    if test ! -s "$part"; then
      status=1
      for ((attempt=1; attempt<=MAX_ATTEMPTS; attempt++)); do
        if baseline_part_once "$theory" "$length" 8 "$part" "$log" \
          "$words"; then status=0; break; fi
        stamp "baseline recycle theory=$theory start=8 chunk=$offset attempt=$attempt" \
          >>"$OUT/recycles.log"
      done
      test "$status" -eq 0
    fi
  done
  mapfile -t parts < <(find "$part_dir" -maxdepth 1 -type f \
    -name 'part-*.tsv' | LC_ALL=C sort)
  merged=$output.revalidate.$$
  HHEVAL_CHUNK_REQUIRE_LOGS=1 "$PROFILE_CHUNK_MERGE" baseline "$theory" \
    "$names_file" "$merged" "${parts[@]}"
  if test -e "$output"; then cmp -s "$output" "$merged"; rm -f "$merged"
  else mv "$merged" "$output"
  fi
}

baseline_theory_once () {
  local theory=$1 count=$2 invocation
  invocation="$OUT/invocations/$theory.json"
  local first="$OUT/baseline-first8/$theory.tsv"
  local last="$OUT/baseline-last8/$theory.tsv"
  local merged="$OUT/baseline/$theory.tsv" attempt status extension_scheduler_sha
  local premise_inventory
  make_invocation "$theory" "$count"
  mkdir -p "$PREMISES/$theory"
  for start in 0 8; do
    if test "$start" -eq 0; then output=$first; else output=$last; fi
    if test "$start" -eq 8; then
      baseline_chunked_last8 "$theory" "$count" "$output"
      continue
    fi
    if test -s "$output"; then
      test "$(wc -l <"$output")" -eq "$((count * 8 + 1))"
      if test "$start" -eq 0; then
        anchor_state=$(execution_state "$theory")
      else
        anchor_state=f751
      fi
      behavior=$(jq -r --arg state "$anchor_state" \
        '.execution_states[$state].base_commit' "$INPUTS/top-provenance.json")
      provenance=$(jq -r --arg state "$anchor_state" \
        '.execution_states[$state].loaded_inventory_sha256' \
        "$INPUTS/top-provenance.json")
      head -1 "$output" | cut -f2- | jq -e \
        --argjson goals "$count" --argjson start "$start" \
        --arg invocation "$(sha "$invocation")" \
        --arg behavior "$behavior" --arg provenance "$provenance" '
          .goals == $goals and .row_count == $goals * 8 and
          .goal_digest_schema == "hh-goal-struct-v1" and
          .profile_start == $start and .profile_length == 8 and
          .invocation_provenance_sha256 == $invocation and
          .behavior_source_commit == $behavior and
          .baseline_provenance_sha256 == $provenance and
          .task13_internal_key_pair_mismatches == 0 and
          .task13_premise_mismatches == 0 and
          .task13_request_key_mismatches == 0 and .prover_spawns == 0' \
        >/dev/null
      if test "$start" -eq 8; then
        head -1 "$output" | cut -f2- | jq -e '
          .goal_chunk_schema == "hh-profile-goal-chunks-v1" and
          .goal_chunk_count >= 1 and .goal_chunk_max_goals >= 1 and
          (.goal_chunk_inventory_sha256 | length) == 64 and
          (.goal_chunk_rows_sha256 | length) == 64' >/dev/null
      fi
      continue
    fi
    status=1
    for ((attempt=1; attempt<=MAX_ATTEMPTS; attempt++)); do
      if baseline_part_once "$theory" "$count" "$start" "$output" \
        "$OUT/log/baseline-$theory-$start.log"; then status=0; break; fi
      stamp "baseline recycle theory=$theory start=$start attempt=$attempt" \
        >>"$OUT/recycles.log"
    done
    test "$status" -eq 0
  done
  test "$(find "$PREMISES/$theory" -type f -name '*.premises' | \
    wc -l)" -eq "$count"
  test -z "$(find "$PREMISES/$theory" -type f -name '*.partial' \
    -print -quit)"
  premise_inventory=$(cd "$PREMISES/$theory" && \
    find . -type f -name '*.premises' -print0 | LC_ALL=C sort -z | \
    xargs -0 sha256sum | sha256sum | awk '{print $1}')
  if test -s "$merged"; then
    test "$(head -1 "$merged" | cut -f2- | jq -r \
      '.premise_inventory_sha256')" = "$premise_inventory"
  fi
  extension_scheduler_sha=$(sha "$BASE_F751/src/holyhammer/hhSchedule.sml")
  "$BASELINE_MERGE" "$first" "$last" "$merged" \
    "$(sha "$invocation")" "$extension_scheduler_sha" "$premise_inventory"
}

current_part_once () {
  local theory=$1 count=$2 start=$3 output=$4 log=$5
  local invocation="$OUT/invocations/$theory.json" names launch baseline status overlay
  local current_state worker_key mismatch first_header model_inventory
  local model_features model_weights model_rows producer_sources
  local model_current_theory model_ancestry model_namespace
  local target_model_features producer_objects canonical_member_sha
  local rankings_directory first8_path range_start progress_path
  local -a model_env=()
  names=${6-}
  if test -z "$names"; then names=$(theorem_names "$theory"); fi
  worker_key=${7:-$theory-$start}
  mismatch=${8:-$OUT/mismatch/$theory-$start.jsonl}
  range_start=${9:-0}
  progress_path="$STATE/current/$worker_key/progress.json"
  mkdir -p "${mismatch%/*}"
  launch=$(launch_directory current "$theory" "$start")
  overlay=$(overlay_root "$theory")
  current_state=$(execution_state "$theory")
  baseline="$OUT/baseline/$theory.tsv"
  if test -n "${HHEVAL_CURRENT_RANKINGS_OVERRIDE:-}"; then
    rankings_directory=$HHEVAL_CURRENT_RANKINGS_OVERRIDE
  else
    rankings_directory="$OUT/current-rankings/$theory"
  fi
  if test -n "${HHEVAL_CURRENT_FIRST8_OVERRIDE:-}"; then
    first8_path=$HHEVAL_CURRENT_FIRST8_OVERRIDE
  else
    first8_path="$OUT/current-first8/$theory.tsv"
  fi
  if test "$start" -eq 0; then
    model_inventory=
    model_features=
    model_weights=
    model_rows=-1
    model_current_theory=
    model_ancestry=
    model_namespace=-1
    target_model_features=
    if test "${HHEVAL_CURRENT_NEGATIVE_MODEL_ENV_TEST:-0}" -eq 1; then
      first_header=$(head -1 "$baseline" | cut -f2-)
      model_inventory=$(jq -er '.model_inventory_sha1' <<<"$first_header")
      model_features=$(jq -er '.model_features_sha1' <<<"$first_header")
      model_weights=$(jq -er '.model_weights_sha1' <<<"$first_header")
      model_rows=$(jq -er '.model_feature_rows' <<<"$first_header")
      model_env=(
        "HHEVAL_CURRENT_MODEL_INVENTORY_SHA1=$model_inventory"
        "HHEVAL_CURRENT_MODEL_FEATURES_SHA1=$model_features"
        "HHEVAL_CURRENT_MODEL_WEIGHTS_SHA1=$model_weights"
        "HHEVAL_CURRENT_MODEL_FEATURE_ROWS=$model_rows")
    fi
  else
    first_header=$(head -1 "$first8_path" | cut -f2-)
    model_inventory=$(jq -er '.model_inventory_sha1' <<<"$first_header")
    model_features=$(jq -er '.model_features_sha1' <<<"$first_header")
    model_weights=$(jq -er '.model_weights_sha1' <<<"$first_header")
    model_rows=$(jq -er '.model_feature_rows' <<<"$first_header")
    model_current_theory=$(jq -er '.model_current_theory' <<<"$first_header")
    model_ancestry=$(jq -er '.model_ancestry | join(",")' <<<"$first_header")
    model_namespace=$(jq -er '.model_namespace_count' <<<"$first_header")
    target_model_features=$(jq -er '.target_model_features_sha1' \
      <<<"$first_header")
    model_env=(
      "HHEVAL_CURRENT_MODEL_INVENTORY_SHA1=$model_inventory"
      "HHEVAL_CURRENT_MODEL_FEATURES_SHA1=$model_features"
      "HHEVAL_CURRENT_MODEL_WEIGHTS_SHA1=$model_weights"
      "HHEVAL_CURRENT_MODEL_FEATURE_ROWS=$model_rows"
      "HHEVAL_CURRENT_MODEL_CURRENT_THEORY=$model_current_theory"
      "HHEVAL_CURRENT_MODEL_ANCESTRY=$model_ancestry"
      "HHEVAL_CURRENT_MODEL_NAMESPACE_COUNT=$model_namespace"
      "HHEVAL_CURRENT_TARGET_MODEL_FEATURES_SHA1=$target_model_features")
  fi
  producer_sources=$(jq -S -c --arg state "$current_state" \
    '.execution_states[$state].current_loaded.sources' \
    "$INPUTS/top-provenance.json" | sha256sum | awk '{print $1}')
  producer_objects=$(jq -S -c --arg state "$current_state" \
    '.execution_states[$state].current_loaded.objects' \
    "$INPUTS/top-provenance.json" | sha256sum | awk '{print $1}')
  canonical_member_sha=$(field "$theory" 7)
  mkdir -p "$rankings_directory"
  mkdir -p "$STATE/current/$worker_key"
  find "$STATE/current/$worker_key" -depth -mindepth 1 -delete
  mkdir -p "$STATE/current/$worker_key/scratch"
  require_host_memory_headroom || return
  stamp "current theory=$theory start=$start invocation=$(sha "$invocation")" \
    >"$log.partial.$$"
  if ! stage_current_signature "$theory" "$worker_key"; then
    unstage_current_signature "$worker_key" || true
    return 1
  fi
  if (cd "$STATE/current/$worker_key" && \
    timeout --signal=TERM --kill-after=120s "$TIMEOUT" \
    env HOLDIR="$overlay" HOL4_HAMMER_DIR="$STATE/current/$worker_key/hammer" \
      HHEVAL_CURRENT_OVERLAY="$overlay" \
      HHEVAL_CURRENT_EXECUTION_STATE="$current_state" \
      HHEVAL_THEORY="$theory" HHEVAL_THEORY_DIR="$launch" \
      HHEVAL_ANCHOR_THEOREMS="$names" \
      HHEVAL_ANCHOR_PROFILE_START="$start" \
      HHEVAL_ANCHOR_PROFILE_LENGTH=8 \
      HHEVAL_ANCHOR_REPLAY_THEORY="$((start == 0 ? 1 : 0))" \
      HHEVAL_ANCHOR_BASELINE="$baseline" \
      HHEVAL_ANCHOR_OUTPUT="$output.partial.$$" \
      HHEVAL_ANCHOR_MISMATCHES="$mismatch.partial.$$" \
      HHEVAL_ANCHOR_SCRATCH="$STATE/current/$worker_key/scratch" \
      HHEVAL_CURRENT_INVOCATION_PROVENANCE_SHA256="$(sha "$invocation")" \
      HHEVAL_CURRENT_INVOCATION_PATH="$invocation" \
      HHEVAL_CURRENT_BASELINE_SHA256="$(sha "$baseline")" \
      HHEVAL_CURRENT_RUN_HEADER_SHA256="$(sha "$OUT/run.json")" \
      HHEVAL_CURRENT_CANONICAL_MEMBER_SHA256="$canonical_member_sha" \
      HHEVAL_CURRENT_PRODUCER_SOURCES_SHA256="$producer_sources" \
      HHEVAL_CURRENT_PRODUCER_OBJECTS_SHA256="$producer_objects" \
      HHEVAL_CURRENT_RANKINGS_DIRECTORY="$rankings_directory" \
      HHEVAL_CURRENT_PROGRESS_PATH="$progress_path" \
      HHEVAL_CURRENT_GOAL_RANGE_START="$range_start" \
      HHEVAL_CURRENT_GOAL_RANGE_LENGTH="$count" \
      HHEVAL_CURRENT_GOAL_CHUNK_POLICY_VERSION="$GOAL_CHUNK_POLICY" \
      "${model_env[@]}" \
      HHEVAL_CURRENT_WORKER_ROOT="$STATE/current/$worker_key/worker" \
      HHEVAL_CURRENT_INNER="$CURRENT_DRIVER" \
      HHEVAL_CURRENT_LAUNCH_DIR="$launch" \
      "$CURRENT_WRAPPER" >>"$log.partial.$$" 2>&1); then
    status=0
  else
    status=$?
  fi
  if ! unstage_current_signature "$worker_key"; then status=1; fi
  if test "$status" -ne 0; then return "$status"; fi
  test ! -s "$mismatch.partial.$$" || return
  test "$(wc -l <"$output.partial.$$")" -eq "$((count * 8 + 1))" || \
    return
  head -1 "$output.partial.$$" | cut -f2- | jq -e \
    --argjson goals "$count" --argjson start "$start" \
    --arg invocation "$(sha "$invocation")" \
    --arg baseline "$(sha "$baseline")" \
    --arg model_inventory "$model_inventory" \
    --arg model_features "$model_features" \
    --arg model_weights "$model_weights" \
    --argjson model_rows "$model_rows" \
    --argjson range_start "$range_start" \
    --arg chunk_policy "$GOAL_CHUNK_POLICY" '
      .schema == "hh-anchor-current-v1" and .goals == $goals and
      .goal_digest_schema == "hh-goal-struct-v1" and
      .row_count == $goals * 8 and .profile_start == $start and
      .profile_length == 8 and
      .goal_range_start == $range_start and
      .goal_range_length == $goals and
      .completed_goal_range_start == $range_start and
      .completed_goal_range_length == $goals and
      .goal_chunk_policy_version == $chunk_policy and
      .invocation_provenance_sha256 == $invocation and
      .baseline_manifest_sha256 == $baseline and
      .mismatches == 0 and .binding_mismatches == 0 and
      (($start == 0 and
        (.model_inventory_sha1 | test("^[0-9a-f]{40}$")) and
        (.model_features_sha1 | test("^[0-9a-f]{40}$")) and
        (.model_weights_sha1 | test("^[0-9a-f]{40}$")) and
        .model_feature_rows > 0) or
       ($start != 0 and
        .model_inventory_sha1 == $model_inventory and
        .model_features_sha1 == $model_features and
        .model_weights_sha1 == $model_weights and
        .model_feature_rows == $model_rows)) and
      .prover_spawns == 0 and (.goal_bindings | length) == $goals' \
    >/dev/null || return
  mv "$mismatch.partial.$$" "$mismatch"
  mv "$output.partial.$$" "$output"
  mv "$log.partial.$$" "$log"
  find "$STATE/current/$worker_key" -depth -mindepth 1 -delete || return
}

current_chunked_last8 () {
  local theory=$1 count=$2 output=$3 names_file part_dir
  local offset length words part log mismatch attempt status merged
  names_file=$(theorem_names_file "$theory" "$count")
  part_dir="$OUT/current-last8-parts/$theory"
  mkdir -p "$part_dir"
  for ((offset=0; offset<count; offset+=GOAL_CHUNK_LIMIT)); do
    length=$GOAL_CHUNK_LIMIT
    if ((offset + length > count)); then length=$((count - offset)); fi
    part=$(printf '%s/part-%06d.tsv' "$part_dir" "$offset")
    log=${part%.tsv}.log
    mismatch=${part%.tsv}.mismatch.jsonl
    words=$(sed -n "$((offset + 1)),$((offset + length))p" \
      "$names_file" | paste -sd ' ' -)
    if test ! -s "$part"; then
      status=1
      for ((attempt=1; attempt<=MAX_ATTEMPTS; attempt++)); do
        if current_part_once "$theory" "$length" 8 "$part" "$log" \
          "$words" "$theory-8-$offset" "$mismatch" "$offset"; then
          status=0
          break
        fi
        stamp "current recycle theory=$theory start=8 chunk=$offset attempt=$attempt" \
          >>"$OUT/recycles.log"
      done
      test "$status" -eq 0
    fi
  done
  mapfile -t parts < <(find "$part_dir" -maxdepth 1 -type f \
    -name 'part-*.tsv' | LC_ALL=C sort)
  merged=$output.revalidate.$$
  HHEVAL_CHUNK_REQUIRE_LOGS=1 "$PROFILE_CHUNK_MERGE" current "$theory" \
    "$names_file" "$merged" "${parts[@]}"
  if test -e "$output"; then cmp -s "$output" "$merged"; rm -f "$merged"
  else mv "$merged" "$output"
  fi
  if test -e "$OUT/mismatch/$theory-8.jsonl"; then
    test ! -s "$OUT/mismatch/$theory-8.jsonl"
  else
    : >"$OUT/mismatch/$theory-8.partial.$$"
    mv "$OUT/mismatch/$theory-8.partial.$$" \
      "$OUT/mismatch/$theory-8.jsonl"
  fi
}

validate_current_progress_file () {
  local theory=$1 start=$2 offset=$3 length=$4 marker=$5
  test -s "$marker"
  test ! -L "$marker"
  jq -e --arg theory "$theory" --argjson start "$start" \
    --argjson offset "$offset" --argjson length "$length" \
    --arg policy "$GOAL_CHUNK_POLICY" \
    --arg invocation "$(sha "$OUT/invocations/$theory.json")" \
    --arg run "$(sha "$OUT/run.json")" \
    --arg baseline "$(sha "$OUT/baseline/$theory.tsv")" \
    --arg member "$(field "$theory" 7)" '
      .schema == "hh-current-computation-progress-v1" and
      .theory == $theory and .profile_start == $start and
      .profile_length == 8 and .goal_range_start == $offset and
      .goal_range_length == $length and
      .goal_chunk_policy_version == $policy and
      .invocation_provenance_sha256 == $invocation and
      .run_header_sha256 == $run and
      .baseline_manifest_sha256 == $baseline and
      .canonical_journal_member_sha256 == $member and
      (.model_inventory_sha1 | test("^[0-9a-f]{40}$")) and
      (.model_features_sha1 | test("^[0-9a-f]{40}$")) and
      (.model_weights_sha1 | test("^[0-9a-f]{40}$"))' "$marker" \
    >/dev/null
}

validate_current_progress () {
  local theory=$1 start=$2 offset=$3 length=$4 worker_key=$5
  validate_current_progress_file "$theory" "$start" "$offset" "$length" \
    "$STATE/current/$worker_key/progress.json"
}

archive_current_failure () {
  local theory=$1 offset=$2 length=$3 part=$4 log=$5 mismatch=$6
  local worker_key=$7 kind=$8 archive source
  archive="$OUT/subdivisions/$theory"
  mkdir -p "$archive"
  for source in "$log.partial.$$" \
      "$STATE/current/$worker_key/progress.json" \
      "$part.partial.$$" "$mismatch.partial.$$"; do
    if test -e "$source"; then
      mv "$source" "$archive/${kind}-$(printf '%06d-%06d' \
        "$offset" "$length")-${source##*/}"
    fi
  done
  find "$STATE/current/$worker_key" -depth -mindepth 1 -delete
}

current_first8_range () {
  local theory=$1 names_file=$2 part_dir=$3 offset=$4 length=$5
  local words part log mismatch worker_key status progress infra left right
  local events archived_progress event_count range_event_count event_sha
  local archived_log_count
  part=$(printf '%s/part-%06d-%06d.tsv' "$part_dir" "$offset" "$length")
  log=${part%.tsv}.log
  mismatch=${part%.tsv}.mismatch.jsonl
  worker_key="$theory-0-$offset-$length"
  words=$(sed -n "$((offset + 1)),$((offset + length))p" \
    "$names_file" | paste -sd ' ' -)
  events="$OUT/subdivisions/$theory/events.jsonl"
  if test -e "$events"; then
    test -s "$events" || return
    test ! -L "$events" || return
    range_event_count=$(jq -s --arg theory "$theory" \
      --argjson offset "$offset" --argjson length "$length" '
        [.[] | select(.event == "subdivide" and .theory == $theory and
          .start == 0 and .offset == $offset and .length == $length)] |
        length' "$events")
    event_count=$(jq -s --arg theory "$theory" \
      --argjson offset "$offset" --argjson length "$length" \
      --arg policy "$GOAL_CHUNK_POLICY" '
        [.[] | select(.event == "subdivide" and .theory == $theory and
          .start == 0 and .offset == $offset and .length == $length and
          .policy_version == $policy)] | length' "$events")
    if test "$range_event_count" -gt 0; then
      test "$range_event_count" -eq 1 || return
      test "$event_count" -eq 1 || return
      test ! -e "$part" || return
      test -z "$(find "$part_dir" -maxdepth 1 -type f \
        -name "${part##*/}.partial.*" -print -quit)" || return
      archived_progress=$(printf '%s/compute-timeout-%06d-%06d-progress.json' \
        "$OUT/subdivisions/$theory" "$offset" "$length")
      validate_current_progress_file "$theory" 0 "$offset" "$length" \
        "$archived_progress" || return
      event_sha=$(jq -sr --arg theory "$theory" \
        --argjson offset "$offset" --argjson length "$length" \
        --arg policy "$GOAL_CHUNK_POLICY" '
          [.[] | select(.event == "subdivide" and .theory == $theory and
            .start == 0 and .offset == $offset and .length == $length and
            .policy_version == $policy)][0].progress_sha256' "$events")
      test "$(sha "$archived_progress")" = "$event_sha" || return
      archived_log_count=$(find "$OUT/subdivisions/$theory" -maxdepth 1 \
        -type f -name "$(printf 'compute-timeout-%06d-%06d-part-%06d-%06d.log.partial.*' \
          "$offset" "$length" "$offset" "$length")" | wc -l)
      test "$archived_log_count" -eq 1 || return
      test "$length" -ge "$((GOAL_CHUNK_MIN * 2))" || return
      left=$((length / 2))
      right=$((length - left))
      current_first8_range "$theory" "$names_file" "$part_dir" \
        "$offset" "$left" || return
      current_first8_range "$theory" "$names_file" "$part_dir" \
        "$((offset + left))" "$right" || return
      return
    fi
  fi
  if test -s "$part"; then
    head -1 "$part" | cut -f2- | jq -e \
      --argjson offset "$offset" --argjson length "$length" \
      --arg policy "$GOAL_CHUNK_POLICY" '
        .goal_range_start == $offset and
        .goal_range_length == $length and
        .goal_chunk_policy_version == $policy' >/dev/null || return
    return
  fi
  infra=0
  while :; do
    if current_part_once "$theory" "$length" 0 "$part" "$log" \
        "$words" "$worker_key" "$mismatch" "$offset"; then
      status=0
    else
      status=$?
    fi
    if test "$status" -eq 0; then return; fi
    progress="$STATE/current/$worker_key/progress.json"
    if test -e "$progress" || test -L "$progress"; then
      if ! validate_current_progress "$theory" 0 "$offset" "$length" \
          "$worker_key"; then
        archive_current_failure "$theory" "$offset" "$length" \
          "$part" "$log" "$mismatch" "$worker_key" invalid-progress
        stamp "current invalid-progress" "theory=$theory" "start=0" \
          "chunk=$offset" "length=$length" "status=$status" \
          >>"$OUT/recycles.log"
        return 1
      fi
    fi
    if test "$status" -eq 124 && test -s "$progress"; then
      if test "$length" -lt "$((GOAL_CHUNK_MIN * 2))"; then
        archive_current_failure "$theory" "$offset" "$length" \
          "$part" "$log" "$mismatch" "$worker_key" terminal-timeout
        stamp "current terminal-timeout theory=$theory start=0 chunk=$offset length=$length" \
          >>"$OUT/recycles.log"
        return 124
      fi
      mkdir -p "$OUT/subdivisions/$theory"
      jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
        --arg theory "$theory" --argjson offset "$offset" \
        --argjson length "$length" --arg policy "$GOAL_CHUNK_POLICY" \
        --arg progress_sha "$(sha "$progress")" \
        '{time:$time,event:"subdivide",theory:$theory,start:0,
          offset:$offset,length:$length,policy_version:$policy,
          progress_sha256:$progress_sha}' \
        >>"$OUT/subdivisions/$theory/events.jsonl"
      archive_current_failure "$theory" "$offset" "$length" \
        "$part" "$log" "$mismatch" "$worker_key" compute-timeout
      left=$((length / 2))
      right=$((length - left))
      current_first8_range "$theory" "$names_file" "$part_dir" \
        "$offset" "$left"
      current_first8_range "$theory" "$names_file" "$part_dir" \
        "$((offset + left))" "$right"
      return
    fi
    if test -s "$progress"; then
      archive_current_failure "$theory" "$offset" "$length" \
        "$part" "$log" "$mismatch" "$worker_key" computation-error
      return "$status"
    fi
    infra=$((infra + 1))
    archive_current_failure "$theory" "$offset" "$length" \
      "$part" "$log" "$mismatch" "$worker_key" infrastructure
    stamp "current infrastructure-retry" "theory=$theory" "start=0" \
      "chunk=$offset" "length=$length" "attempt=$infra" \
      "status=$status" \
      >>"$OUT/recycles.log"
    test "$infra" -lt "$INFRA_ATTEMPTS" || return "$status"
  done
}

current_chunked_first8 () {
  current_checkpoint_chain "$1" "$2" "$3"
}

validate_current_rankings () {
  local theory=$1 count=$2 directory inventory partial
  directory="$OUT/current-rankings/$theory"
  inventory="$directory/SHA256SUMS"
  test "$(find "$directory" -maxdepth 1 -type f -name '*.ranking' | wc -l)" \
    -eq "$count"
  test -z "$(find "$directory" -maxdepth 1 -type f -name '*.partial' \
    -print -quit)"
  if test ! -e "$inventory"; then
    partial="$inventory.partial.$$"
    (cd "$directory" && find . -maxdepth 1 -type f -name '*.ranking' \
      -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) >"$partial"
    test "$(wc -l <"$partial")" -eq "$count"
    mv "$partial" "$inventory"
  fi
  test ! -L "$inventory"
  test "$(wc -l <"$inventory")" -eq "$count"
  (cd "$directory" && sha256sum -c SHA256SUMS >/dev/null)
}

current_theory_once () {
  local theory=$1 count=$2 first last merged attempt status ranking_inventory
  first="$OUT/current-first8/$theory.tsv"
  last="$OUT/current-last8/$theory.tsv"
  merged="$OUT/current/$theory.tsv"
  for start in 0 8; do
    if test "$start" -eq 0; then output=$first; else output=$last; fi
    if test "$start" -eq 0; then
      current_chunked_first8 "$theory" "$count" "$output"
      validate_current_rankings "$theory" "$count"
      continue
    fi
    if test "$start" -eq 8; then
      current_chunked_last8 "$theory" "$count" "$output"
      continue
    fi
    if test -s "$output"; then
      test "$(wc -l <"$output")" -eq "$((count * 8 + 1))"
      test -f "$OUT/mismatch/$theory-$start.jsonl"
      test ! -s "$OUT/mismatch/$theory-$start.jsonl"
      head -1 "$output" | cut -f2- | jq -e \
        --argjson goals "$count" --argjson start "$start" \
        --arg invocation "$(sha "$OUT/invocations/$theory.json")" '
          .goals == $goals and .row_count == $goals * 8 and
          .goal_digest_schema == "hh-goal-struct-v1" and
          .profile_start == $start and .profile_length == 8 and
          .completed_goal_range_start == 0 and
          .completed_goal_range_length == $goals and
          .invocation_provenance_sha256 == $invocation and
          .mismatches == 0 and .binding_mismatches == 0 and
          .prover_spawns == 0' >/dev/null
      if test "$start" -eq 0; then
        validate_current_rankings "$theory" "$count"
      fi
      if test "$start" -eq 8; then
        head -1 "$output" | cut -f2- | jq -e '
          .goal_chunk_schema == "hh-profile-goal-chunks-v1" and
          .goal_chunk_policy_version == "hh-current-goal-bisect-v1" and
          .goal_chunk_count >= 1 and .goal_chunk_max_goals >= 1 and
          (.goal_chunk_range_inventory_sha256 | length) == 64 and
          (.goal_chunk_inventory_sha256 | length) == 64 and
          (.goal_chunk_rows_sha256 | length) == 64' >/dev/null
      fi
      continue
    fi
    status=1
    for ((attempt=1; attempt<=MAX_ATTEMPTS; attempt++)); do
      if current_part_once "$theory" "$count" "$start" "$output" \
        "$OUT/log/current-$theory-$start.log"; then status=0; break; fi
      stamp "current recycle theory=$theory start=$start attempt=$attempt" \
        >>"$OUT/recycles.log"
    done
    test "$status" -eq 0
    if test "$start" -eq 0; then
      validate_current_rankings "$theory" "$count"
    fi
  done
  ranking_inventory=$(sha "$OUT/current-rankings/$theory/SHA256SUMS")
  "$CURRENT_MERGE" "$first" "$last" "$OUT/baseline/$theory.tsv" \
    "$merged" "$ranking_inventory"
}

test_current_model_env_rejection () {
  local theory count names output mismatch log status certificate
  local log_partial
  certificate="$OUT/current-model-env-rejection.json"
  if test -s "$certificate"; then
    jq -e --arg driver "$(sha "$CURRENT_DRIVER")" \
      --arg baseline "$(sha "$OUT/baseline-validation.json")" '
        .schema == "hh-current-model-env-rejection-v1" and
        .status == "rejected" and .driver_sha256 == $driver and
        .baseline_validation_sha256 == $baseline' "$certificate" \
      >/dev/null
    return
  fi
  IFS=$'\t' read -r theory count _ <"$INVENTORY"
  names=$(theorem_names "$theory" | awk '{print $1}')
  output="$STATE/current-model-env-rejection.tsv"
  mismatch="$STATE/current-model-env-rejection.mismatch"
  log="$OUT/current-model-env-rejection.log"
  rm -f "$output" "$output".partial.* "$mismatch" "$mismatch".partial.*
  if HHEVAL_CURRENT_NEGATIVE_MODEL_ENV_TEST=1 \
      current_part_once "$theory" 1 0 "$output" "$log" "$names" \
        current-model-env-rejection "$mismatch"; then
    status=0
  else
    status=$?
  fi
  test "$status" -ne 0
  log_partial="$log.partial.$$"
  test -s "$log_partial"
  grep -F "current first8 rejects a supplied model binding" \
    "$log_partial" >/dev/null
  test ! -e "$output"
  test ! -e "$mismatch"
  mv "$log_partial" "$log"
  find "$STATE/current/current-model-env-rejection" -depth -mindepth 1 \
    -delete 2>/dev/null || true
  jq -n --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg theory "$theory" --arg driver "$(sha "$CURRENT_DRIVER")" \
    --arg baseline "$(sha "$OUT/baseline-validation.json")" \
    --arg log_sha "$(sha "$log")" \
    '{schema:"hh-current-model-env-rejection-v1",status:"rejected",
      completed:$time,theory:$theory,driver_sha256:$driver,
      baseline_validation_sha256:$baseline,log_sha256:$log_sha}' \
    >"$certificate"
  chmod 0444 "$certificate"
}

test_current_ranking_rejections () {
  local theory count names test_root rankings first valid saved premise
  local cross_output cross_mismatch cross_log stale_first stale_output
  local stale_mismatch stale_log status certificate
  certificate="$OUT/current-ranking-rejections.json"
  if test -s "$certificate"; then
    jq -e --arg driver "$(sha "$CURRENT_DRIVER")" \
      --arg baseline "$(sha "$OUT/baseline-validation.json")" '
        .schema == "hh-current-ranking-rejections-v1" and
        .cross_feed_rejected and .stale_model_digest_rejected and
        .driver_sha256 == $driver and
        .baseline_validation_sha256 == $baseline' "$certificate" \
      >/dev/null
    return
  fi
  IFS=$'\t' read -r theory count _ <"$INVENTORY"
  names=$(theorem_names "$theory" | awk '{print $1}')
  test_root="$STATE/current-ranking-rejections"
  rankings="$test_root/rankings"
  mkdir -p "$rankings"
  first="$test_root/first.tsv"
  HHEVAL_CURRENT_RANKINGS_OVERRIDE="$rankings" \
    current_part_once "$theory" 1 0 "$first" \
      "$test_root/first.log" "$names" ranking-rejection-first \
      "$test_root/first.mismatch"
  valid=$(find "$rankings" -maxdepth 1 -type f -name '*.ranking' \
    -print -quit)
  test -n "$valid"
  saved="$test_root/valid.ranking"
  cp "$valid" "$saved"
  premise=$(find "$PREMISES/$theory" -maxdepth 1 -type f \
    -name '*.premises' -print -quit)
  test -n "$premise"
  cp "$premise" "$valid"
  cross_output="$test_root/cross-feed.tsv"
  cross_mismatch="$test_root/cross-feed.mismatch"
  cross_log="$OUT/current-ranking-cross-feed.log"
  if HHEVAL_CURRENT_RANKINGS_OVERRIDE="$rankings" \
      HHEVAL_CURRENT_FIRST8_OVERRIDE="$first" \
      current_part_once "$theory" 1 8 "$cross_output" "$cross_log" \
        "$names" ranking-rejection-cross-feed "$cross_mismatch"; then
    status=0
  else
    status=$?
  fi
  test "$status" -ne 0
  grep -F "cross-fed or malformed current ranking journal" \
    "$cross_log.partial.$$" >/dev/null
  test ! -e "$cross_output"
  mv "$cross_log.partial.$$" "$cross_log"
  cp "$saved" "$valid"
  stale_first="$test_root/stale-first.tsv"
  {
    printf '#hh-anchor-current-v1\t'
    head -1 "$first" | cut -f2- | jq -c \
      '.model_inventory_sha1 = "0000000000000000000000000000000000000000"'
    tail -n +2 "$first"
  } >"$stale_first"
  stale_output="$test_root/stale.tsv"
  stale_mismatch="$test_root/stale.mismatch"
  stale_log="$OUT/current-ranking-stale-model.log"
  if HHEVAL_CURRENT_RANKINGS_OVERRIDE="$rankings" \
      HHEVAL_CURRENT_FIRST8_OVERRIDE="$stale_first" \
      current_part_once "$theory" 1 8 "$stale_output" "$stale_log" \
        "$names" ranking-rejection-stale "$stale_mismatch"; then
    status=0
  else
    status=$?
  fi
  test "$status" -ne 0
  grep -F "current ranking journal provenance is stale" \
    "$stale_log.partial.$$" >/dev/null
  test ! -e "$stale_output"
  mv "$stale_log.partial.$$" "$stale_log"
  jq -n --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg theory "$theory" --arg driver "$(sha "$CURRENT_DRIVER")" \
    --arg baseline "$(sha "$OUT/baseline-validation.json")" \
    --arg valid_ranking "$(sha "$saved")" \
    --arg cross_log "$(sha "$cross_log")" \
    --arg stale_log "$(sha "$stale_log")" \
    '{schema:"hh-current-ranking-rejections-v1",status:"complete",
      completed:$time,theory:$theory,cross_feed_rejected:true,
      stale_model_digest_rejected:true,driver_sha256:$driver,
      baseline_validation_sha256:$baseline,
      valid_ranking_sha256:$valid_ranking,
      cross_feed_log_sha256:$cross_log,stale_log_sha256:$stale_log}' \
    >"$certificate"
  chmod 0444 "$certificate"
  find "$test_root" -depth -mindepth 1 -delete
}

load_worker_function_manifest () {
  local entrypoint function extra previous= current_entrypoints=
  test -s "$WORKER_FUNCTION_MANIFEST"
  test ! -L "$WORKER_FUNCTION_MANIFEST"
  while IFS=$'\t' read -r entrypoint function extra; do
    test -z "${extra:-}"
    case "$entrypoint" in
      baseline_theory_once | current_theory_once) ;;
      *) return 1 ;;
    esac
    [[ "$function" =~ ^[A-Za-z_][A-Za-z0-9_]*$ ]] || return
    declare -F "$function" >/dev/null || return
    if test "$entrypoint" != "$previous"; then
      test -z "$previous" || test "$previous" = baseline_theory_once
      current_entrypoints="$current_entrypoints $entrypoint"
      previous=$entrypoint
    fi
    printf '%s\n' "$function"
  done <"$WORKER_FUNCTION_MANIFEST"
  test "$current_entrypoints" = \
    " baseline_theory_once current_theory_once"
}

mapfile -t WORKER_FUNCTIONS < <(load_worker_function_manifest)
test "${#WORKER_FUNCTIONS[@]}" -gt 0
mapfile -t WORKER_FUNCTIONS < <(printf '%s\n' "${WORKER_FUNCTIONS[@]}" |
  LC_ALL=C sort -u)
export -f "${WORKER_FUNCTIONS[@]}"
HHEVAL_WORKER_FUNCTIONS=$(printf '%s\n' "${WORKER_FUNCTIONS[@]}" |
  paste -sd ' ' -)
export ROOT BASE_F751 OVERLAY_F751 BASE_F258 OVERLAY_F258
export INPUTS EXP EVAL OUT STATE CORPUS INVENTORY PREMISES
export BASELINE_TOOL BASELINE_MERGE CURRENT_WRAPPER CURRENT_DRIVER
export CURRENT_MERGE PROFILE_CHUNK_MERGE WORKER_FUNCTION_MANIFEST
export CHECKPOINT_CHAIN_TOOL CHECKPOINT_POLICY CHECKPOINT_STORAGE_POLICY
export CHECKPOINT_RUNTIME_SHA
export CHECKPOINT_MAX_GOALS CHECKPOINT_ATOM_HEADROOM_KIB
export CHECKPOINT_RESERVATION_POLICY CHECKPOINT_RESERVATION_SLOTS
export CHECKPOINT_RESERVATION_WAIT_SECONDS
export CHECKPOINT_FLOCK_PATH CHECKPOINT_FLOCK_SHA256
export HOST_MEMORY_POLICY HOST_MEMORY_MIN_AVAILABLE_KIB
export HOST_MEMORY_SCOPE_HEADROOM_BYTES HOST_MEMORY_WAIT_SECONDS
export MEMORY_HIGH MEMORY_MAX
export TIMEOUT MAX_ATTEMPTS GOAL_CHUNK_LIMIT GOAL_CHUNK_MIN
export GOAL_CHUNK_POLICY INFRA_ATTEMPTS
export HHEVAL_WORKER_FUNCTIONS

verify_worker_export_boundary () {
  bash --noprofile --norc -Eeuo pipefail -c '
    for function in $HHEVAL_WORKER_FUNCTIONS; do
      declare -F "$function" >/dev/null
    done
    declare -F "$1" >/dev/null
    declare -F validate_current_progress_file >/dev/null
    HHEVAL_HOST_MEMORY_AVAILABLE_OVERRIDE=$HOST_MEMORY_MIN_AVAILABLE_KIB \
      HHEVAL_SCOPE_MEMORY_CURRENT_OVERRIDE=0 \
      HHEVAL_HOST_MEMORY_WAIT_OVERRIDE=0 \
      HHEVAL_MEMORY_ADMISSION_NO_JOURNAL=1 require_host_memory_headroom
  ' worker-export-preflight baseline_theory_once
  bash --noprofile --norc -Eeuo pipefail -c '
    for function in $HHEVAL_WORKER_FUNCTIONS; do
      declare -F "$function" >/dev/null
    done
    declare -F "$1" >/dev/null
    declare -F validate_current_progress_file >/dev/null
    HHEVAL_HOST_MEMORY_AVAILABLE_OVERRIDE=$HOST_MEMORY_MIN_AVAILABLE_KIB \
      HHEVAL_SCOPE_MEMORY_CURRENT_OVERRIDE=0 \
      HHEVAL_HOST_MEMORY_WAIT_OVERRIDE=0 \
      HHEVAL_MEMORY_ADMISSION_NO_JOURNAL=1 require_host_memory_headroom
  ' worker-export-preflight current_theory_once
}

pool () {
  local kind=$1
  awk -F '\t' '{print $1, $2}' "$INVENTORY" |
    xargs -n 2 -P 16 bash -Eeuo pipefail -c \
      '"$1"_theory_once "$2" "$3"' a-worker "$kind"
}

validate_inventories () {
  local kind=$1 theory count manifest expected actual
  local validation_root index=0
  validation_root=$(mktemp -d)
  trap 'find "$validation_root" -depth -mindepth 1 -delete;
    rmdir "$validation_root"' RETURN
  while IFS="$(printf '\t')" read -r theory count _; do
    manifest="$OUT/$kind/$theory.tsv"
    expected="$validation_root/$index.expected"
    actual="$validation_root/$index.actual"
    for theorem in $(theorem_names "$theory"); do
      printf '%s.%s\n' "$theory" "$theorem"
    done | LC_ALL=C sort >"$expected"
    tail -n +2 "$manifest" | awk -F '\t' -v count="$count" '
      NF != 13 || $2 !~ /^[0-9]+$/ || $2 < 1 || $2 > 16 {
        bad = 1; next
      }
      {key=$1 SUBSEP $2; if (seen[key]++) bad=1; goals[$1]=1; rows++}
      END {
        for (goal in goals)
          for (slice=1; slice<=16; slice++)
            if (!seen[goal SUBSEP slice]) bad=1
        if (bad || rows != count * 16) exit 1
        for (goal in goals) print goal
      }' | LC_ALL=C sort >"$actual"
    cmp -s "$expected" "$actual"
    rm -f "$expected" "$actual"
    index=$((index + 1))
  done <"$INVENTORY"
  rmdir "$validation_root"
  trap - RETURN
}

validate_baseline () {
  local counters digest certificate
  test "$(find "$OUT/baseline" -type f -name '*.tsv' | wc -l)" -eq \
    "$EXPECTED_THEORIES"
  counters=$(find "$OUT/baseline" -type f -name '*.tsv' -print0 |
    xargs -0 -n 1 sed -n '1s/^[^\t]*\t//p' | jq -s \
      '{theories:length,goals:map(.goals)|add,rows:map(.row_count)|add,
        checked:map(.task13_rows_checked)|add,
        expected_checked:map(.task13_execution_goals * 8)|add,
        premise:map(.task13_premise_mismatches)|add,
        request:map(.task13_request_key_mismatches)|add,
        internal:map(.task13_internal_key_pair_mismatches)|add,
        prover_spawns:map(.prover_spawns)|add,slices:16,
        chunked:map(.extension_goal_chunks.schema ==
          "hh-profile-goal-chunks-v1")|all,
        chunk_members:map(.extension_goal_chunks.count)|add}')
  jq -e --argjson theories "$EXPECTED_THEORIES" \
    --argjson goals "$EXPECTED_GOALS" --argjson rows "$EXPECTED_ROWS" '
      .theories == $theories and .goals == $goals and .rows == $rows and
      .checked == .expected_checked and .premise == 0 and .request == 0 and
      .internal == 0 and .prover_spawns == 0 and .slices == 16 and
      .chunked == true and .chunk_members >= $theories' \
    <<<"$counters" >/dev/null
  validate_inventories baseline
  digest=$(find "$OUT/baseline" -type f -name '*.tsv' -print0 |
    LC_ALL=C sort -z | xargs -0 sha256sum | sha256sum | awk '{print $1}')
  certificate="$OUT/baseline-validation.json"
  if test -e "$certificate"; then
    test ! -L "$certificate"
    jq -e --argjson counters "$counters" --arg digest "$digest" '
      .status == "complete" and .counters == $counters and
      .manifest_certificate_sha256 == $digest' "$certificate" >/dev/null
  else
    jq -n --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      --argjson counters "$counters" --arg digest "$digest" \
      '{status:"complete",completed:$time,counters:$counters,
        manifest_certificate_sha256:$digest}' >"$certificate"
    chmod 0444 "$certificate"
  fi
}

validate_current () {
  local counters rows goals digest baseline_sha certificate theory count
  local ranking_count ranking_digest ranking_inventory signature_manifest_sha
  verify_no_staged_signatures
  signature_manifest_sha=$(sha "$INPUTS/fallback-current-signatures.tsv")
  test "$(find "$OUT/current" -type f -name '*.tsv' | wc -l)" -eq \
    "$EXPECTED_THEORIES"
  ranking_count=$(find "$OUT/current-rankings" -type f -name '*.ranking' |
    wc -l)
  test "$ranking_count" -eq "$EXPECTED_GOALS"
  while IFS="$(printf '\t')" read -r theory count _; do
    validate_current_rankings "$theory" "$count"
    ranking_inventory=$(sha "$OUT/current-rankings/$theory/SHA256SUMS")
    test "$(head -1 "$OUT/current/$theory.tsv" | cut -f2- | jq -r \
      '.ranking_inventory_sha256')" = "$ranking_inventory"
  done <"$INVENTORY"
  ranking_digest=$(find "$OUT/current-rankings" -type f \
    \( -name '*.ranking' -o -name SHA256SUMS \) -print0 |
    LC_ALL=C sort -z | xargs -0 sha256sum | sha256sum | awk '{print $1}')
  counters=$(find "$OUT/current" -type f -name '*.tsv' -print0 |
    xargs -0 -n 1 sed -n '1s/^[^\t]*\t//p' | jq -s \
      '{theories:length,goals:map(.goals)|add,rows:map(.row_count)|add,
        mismatches:map(.mismatches)|add,
        binding_mismatches:map(.binding_mismatches)|add,
        prover_spawns:map(.prover_spawns)|add,slices:16,
        chunked:map(.extension_goal_chunks.schema ==
          "hh-profile-goal-chunks-v1")|all,
        chunk_members:map(.extension_goal_chunks.count)|add}' |
    jq --argjson ranking_journals "$ranking_count" \
      '. + {ranking_journals:$ranking_journals}')
  jq -e --argjson theories "$EXPECTED_THEORIES" \
    --argjson goals "$EXPECTED_GOALS" --argjson rows "$EXPECTED_ROWS" '
      .theories == $theories and .goals == $goals and .rows == $rows and
      .mismatches == 0 and .binding_mismatches == 0 and
      .prover_spawns == 0 and .slices == 16 and .chunked == true and
      .chunk_members >= $theories and .ranking_journals == $goals' \
    <<<"$counters" >/dev/null
  validate_inventories current
  rows=$(find "$OUT/current" -type f -name '*.tsv' -print0 |
    xargs -0 awk 'FNR > 1 {n++} END {print n+0}')
  goals=$(find "$OUT/current" -type f -name '*.tsv' -print0 |
    xargs -0 awk -F '\t' 'FNR > 1 {seen[$1]=1} END {for (x in seen)n++;
      print n+0}')
  test "$rows" -eq "$EXPECTED_ROWS"
  test "$goals" -eq "$EXPECTED_GOALS"
  test "$(find "$OUT/mismatch" -type f -size +0c | wc -l)" -eq 0
  baseline_sha=$(sha "$OUT/baseline-validation.json")
  digest=$(find "$OUT/current" -type f -name '*.tsv' -print0 |
    LC_ALL=C sort -z | xargs -0 sha256sum | sha256sum | awk '{print $1}')
  certificate="$OUT/result.json"
  if test -e "$certificate"; then
    test ! -L "$certificate"
    jq -e --argjson counters "$counters" --arg baseline "$baseline_sha" \
      --arg digest "$digest" --arg rankings "$ranking_digest" \
      --arg signatures "$signature_manifest_sha" '
        .status == "complete" and .counters == $counters and
        .baseline_validation_sha256 == $baseline and
        .manifest_certificate_sha256 == $digest and
        .ranking_certificate_sha256 == $rankings and
        .fallback_current_signatures_sha256 == $signatures and
        .signature_cleanup_complete == true' "$certificate" >/dev/null
  else
    jq -n --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      --argjson counters "$counters" --arg baseline "$baseline_sha" \
      --arg digest "$digest" --arg rankings "$ranking_digest" \
      --arg signatures "$signature_manifest_sha" \
      '{status:"complete",completed:$time,counters:$counters,
        baseline_validation_sha256:$baseline,
        manifest_certificate_sha256:$digest,
        ranking_certificate_sha256:$rankings,
        fallback_current_signatures_sha256:$signatures,
        signature_cleanup_complete:true}' >"$certificate"
    chmod 0444 "$certificate"
  fi
  jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg event complete --arg result_sha "$(sha "$OUT/result.json")" \
    '{time:$time,event:$event,result_sha256:$result_sha}' \
    >>"$OUT/invocations.jsonl"
}

if test "${HHEVAL_TASK10_RUNNER_LIBRARY_ONLY:-0}" = 1; then
  return 0
fi

verify_existing_tuple_readonly

if test "${1:-}" = VERIFY_INPUTS; then
  test "$#" -eq 1
  verify_inputs
  exit 0
fi

verify_inputs
verify_live_execution_envelope
verify_worker_export_boundary
initialize
trap 'cleanup_staged_signatures' EXIT
trap 'exit 130' HUP INT TERM
if test "$DURABLE_ONLY_RESUME" = 1; then
  validate_baseline
  validate_current
  cleanup_successful_run
  stamp "$EXP durable-only resume complete"
  exit 0
fi
pool baseline
validate_baseline
test_current_model_env_rejection
test_current_ranking_rejections
pool current
validate_current
cleanup_successful_run
stamp "$EXP complete"
