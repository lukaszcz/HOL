# Sourced by run-a.sh.  Every function is listed in
# worker-function-manifest.tsv and exported into the xargs worker shell.

checkpoint_chain_dir () {
  if test -n "${HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE:-}"; then
    printf '%s/%s\n' "$HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE" "$1"
  else
    printf '%s/current-checkpoint-chains/%s\n' "$OUT" "$1"
  fi
}

checkpoint_require_headroom () {
  local available
  test "$CHECKPOINT_ATOM_HEADROOM_KIB" -ge 1
  if test -n "${HHEVAL_CHECKPOINT_TEST_AVAILABLE_KIB:-}"; then
    available=$HHEVAL_CHECKPOINT_TEST_AVAILABLE_KIB
    [[ "$available" =~ ^[0-9]+$ ]]
  else
    available=$(df -Pk "$STATE" | awk 'NR == 2 {print $4}')
  fi
  test "$available" -ge "$CHECKPOINT_ATOM_HEADROOM_KIB" || {
    stamp "current checkpoint headroom-reject" \
      "available_kib=$available" \
      "required_kib=$CHECKPOINT_ATOM_HEADROOM_KIB" \
      "policy=$CHECKPOINT_STORAGE_POLICY" \
      >>"$OUT/recycles.log"
    return 75
  }
}

checkpoint_scope_oom_kills () {
  local relative cgroup
  relative=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
  cgroup="/sys/fs/cgroup$relative"
  awk '$1 == "oom_kill" {print $2}' "$cgroup/memory.events"
}

checkpoint_reservation_identity () {
  CHECKPOINT_RESERVATION_OWNER_PID=${BASHPID:-$$}
  CHECKPOINT_RESERVATION_OWNER_START=$(awk '{print $22}' \
    "/proc/$CHECKPOINT_RESERVATION_OWNER_PID/stat")
  CHECKPOINT_RESERVATION_OWNER_TOKEN=
  CHECKPOINT_RESERVATION_OWNER_TOKEN+="${CHECKPOINT_RESERVATION_OWNER_PID}-"
  CHECKPOINT_RESERVATION_OWNER_TOKEN+="${CHECKPOINT_RESERVATION_OWNER_START}-"
  CHECKPOINT_RESERVATION_OWNER_TOKEN+="$RANDOM"
}

checkpoint_reservation_count_slots () {
  local root=$1 lock fd count=0 index
  mkdir -p "$root"
  for ((index=0; index<CHECKPOINT_RESERVATION_SLOTS; index++)); do
    lock="$root/slot-$(printf '%02d' "$index").lock"
    exec {fd}>"$lock"
    if "$CHECKPOINT_FLOCK_PATH" -n "$fd"; then
      "$CHECKPOINT_FLOCK_PATH" -u "$fd"
    else
      count=$((count + 1))
    fi
    exec {fd}>&-
  done
  printf '%s\n' "$count"
}

checkpoint_reservation_close_child_fd () {
  if test -n "${CHECKPOINT_RESERVATION_FD:-}"; then
    [[ "$CHECKPOINT_RESERVATION_FD" =~ ^[0-9]+$ ]]
    exec {CHECKPOINT_RESERVATION_FD}>&-
    unset CHECKPOINT_RESERVATION_FD
  fi
}

checkpoint_reservation_acquire () {
  local label=$1 root started lock metadata temporary concurrent index fd
  root="$STATE/checkpoint-reservations"
  mkdir -p "$root"
  checkpoint_reservation_identity
  started=$SECONDS
  while true; do
    for ((index=0; index<CHECKPOINT_RESERVATION_SLOTS; index++)); do
      lock="$root/slot-$(printf '%02d' "$index").lock"
      metadata="$root/slot-$(printf '%02d' "$index").owner.tsv"
      exec {fd}>"$lock"
      if ! "$CHECKPOINT_FLOCK_PATH" -n "$fd"; then
        exec {fd}>&-
        continue
      fi
      CHECKPOINT_RESERVATION_FD=$fd
      CHECKPOINT_RESERVATION_SLOT=$index
      CHECKPOINT_RESERVATION_METADATA=$metadata
      temporary="$root/.owner-$CHECKPOINT_RESERVATION_OWNER_TOKEN-$index"
      printf '%s\t%s\t%s\t%s\n' "$CHECKPOINT_RESERVATION_OWNER_PID" \
        "$CHECKPOINT_RESERVATION_OWNER_START" \
        "$CHECKPOINT_RESERVATION_OWNER_TOKEN" "$label" \
        >"$temporary"
      mv -f "$temporary" "$metadata"
      concurrent=$(checkpoint_reservation_count_slots "$root")
      test "$concurrent" -le "$CHECKPOINT_RESERVATION_SLOTS"
      jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
        --arg policy "$CHECKPOINT_RESERVATION_POLICY" \
        --arg event acquire --arg label "$label" \
        --arg token "$CHECKPOINT_RESERVATION_OWNER_TOKEN" \
        --argjson slot "$index" --argjson concurrent "$concurrent" \
        --argjson waited "$((SECONDS - started))" \
        '{time:$time,policy_version:$policy,event:$event,label:$label,
          token:$token,slot:$slot,concurrent_slots:$concurrent,
          waited_seconds:$waited}' >>"$OUT/checkpoint-reservations.jsonl"
      return 0
    done
    if test "$((SECONDS - started))" -ge \
        "$CHECKPOINT_RESERVATION_WAIT_SECONDS"; then
      stamp "current checkpoint reservation-reject" \
        "label=$label" "policy=$CHECKPOINT_RESERVATION_POLICY" \
        >>"$OUT/recycles.log"
      return 75
    fi
    sleep 1
  done
}

checkpoint_reservation_release () {
  local label=$1 status=$2 root concurrent temporary token
  test -n "${CHECKPOINT_RESERVATION_FD:-}" || return 0
  [[ "$CHECKPOINT_RESERVATION_FD" =~ ^[0-9]+$ ]]
  token=$CHECKPOINT_RESERVATION_OWNER_TOKEN
  root="$STATE/checkpoint-reservations"
  temporary="$root/.released-$token-$CHECKPOINT_RESERVATION_SLOT"
  printf '%s\t%s\t%s\t%s\treleased\t%s\n' \
    "$CHECKPOINT_RESERVATION_OWNER_PID" \
    "$CHECKPOINT_RESERVATION_OWNER_START" "$token" "$label" "$status" \
    >"$temporary"
  mv -f "$temporary" "$CHECKPOINT_RESERVATION_METADATA"
  "$CHECKPOINT_FLOCK_PATH" -u "$CHECKPOINT_RESERVATION_FD"
  exec {CHECKPOINT_RESERVATION_FD}>&-
  unset CHECKPOINT_RESERVATION_FD
  concurrent=$(checkpoint_reservation_count_slots "$root")
  jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg policy "$CHECKPOINT_RESERVATION_POLICY" --arg event release \
    --arg label "$label" --arg token "$token" --argjson status "$status" \
    --argjson concurrent "$concurrent" \
    '{time:$time,policy_version:$policy,event:$event,label:$label,
      token:$token,status:$status,concurrent_slots:$concurrent}' \
    >>"$OUT/checkpoint-reservations.jsonl"
  unset CHECKPOINT_RESERVATION_SLOT CHECKPOINT_RESERVATION_OWNER_PID
  unset CHECKPOINT_RESERVATION_OWNER_START CHECKPOINT_RESERVATION_OWNER_TOKEN
  unset CHECKPOINT_RESERVATION_METADATA
}

checkpoint_clear_scratch () {
  local theory=$1 root
  case "$theory" in
    "" | *[!A-Za-z0-9_]*) return 2 ;;
  esac
  root="$STATE/current-checkpoint/$theory"
  case "$root" in
    "$STATE/current-checkpoint/"*) ;;
    *) return 2 ;;
  esac
  if test -d "$root"; then
    find "$root" -depth -mindepth 1 -delete
    rmdir "$root"
  fi
  test ! -e "$root"
}

checkpoint_archive_failure () {
  local theory=$1 label=$2 status=$3 root destination file
  root="$STATE/current-checkpoint/$theory"
  case "$theory:$label" in
    *[!A-Za-z0-9_.:-]*) return 2 ;;
  esac
  mkdir -p "$OUT/checkpoint-failures/$theory"
  destination=$(mktemp -d \
    "$OUT/checkpoint-failures/$theory/$label-status-$status.XXXXXX")
  if test -d "$root"; then
    while IFS= read -r -d '' file; do
      cp "$file" "$destination/${file##*/}"
    done < <(find "$root" -type f \
      \( -name '*.log' -o -name 'progress.json' -o \
         -name 'mismatch.jsonl' -o -name 'metadata.json' -o \
         -name 'db-order.txt' -o -name 'checkpoint-stage' -o \
         -name 'failure-classification.json' \) -print0)
  fi
  printf '%s\n' "$status" >"$destination/status"
  (cd "$destination" && find . -type f ! -name SHA256SUMS -print0 | \
    LC_ALL=C sort -z | xargs -0 sha256sum) >"$destination/SHA256SUMS"
  chmod 0444 "$destination"/*
  CHECKPOINT_FAILURE_ARCHIVE=$destination
}

checkpoint_prune_scratch () {
  local theory=$1 count=$2 completed=${3:-0} root
  root="$STATE/current-checkpoint/$theory"
  case "$root" in
    "$STATE/current-checkpoint/"*) ;;
    *) return 2 ;;
  esac
  checkpoint_validate_chain "$theory" "$count"
  test "$(find "$(checkpoint_chain_dir "$theory")" -type f \
    -name '*.heap' | wc -l)" -eq 1
  checkpoint_clear_scratch "$theory"
  if test "$completed" = 1; then
    test "$CHECKPOINT_CHAIN_END" -eq "$count"
  fi
}

checkpoint_validate_chain_unsafe () {
  local theory=$1 count=$2 chain db canonical expected prior atom manifest
  local start completed next_sha latest_heap rows rankings names_sha ranking
  local model_inventory model_features model_weights model_rows
  chain=$(checkpoint_chain_dir "$theory")
  db="$chain/db-order.txt"
  canonical=$(theorem_names_file "$theory" "$count")
  test -s "$chain/base.json" -a -s "$db"
  test ! -L "$chain/base.json" -a ! -L "$db"
  jq -e --arg theory "$theory" --arg policy "$CHECKPOINT_POLICY" \
    --arg storage "$CHECKPOINT_STORAGE_POLICY" \
    --argjson headroom "$CHECKPOINT_ATOM_HEADROOM_KIB" \
    --arg reservation "$CHECKPOINT_RESERVATION_POLICY" \
    --argjson slots "$CHECKPOINT_RESERVATION_SLOTS" \
    --arg invocation "$(sha "$OUT/invocations/$theory.json")" \
    --arg run "$(sha "$OUT/run.json")" \
    --arg member "$(field "$theory" 7)" \
    --arg sources "$(current_sources_digest "$theory")" \
    --arg objects "$(current_objects_digest "$theory")" \
    --arg runtime "$CHECKPOINT_RUNTIME_SHA" \
    --argjson count "$count" '
      .schema == "hh-current-db-checkpoint-base-receipt-v1" and
      .policy_version == $policy and .theory == $theory and
      .storage_policy_version == $storage and
      .atom_headroom_kib == $headroom and
      .heavy_hol_reservation_policy_version == $reservation and
      .heavy_hol_reservation_maximum_concurrent_atoms == $slots and
      .db_goal_count == $count and
      .invocation_provenance_sha256 == $invocation and
      .run_header_sha256 == $run and
      .canonical_journal_member_sha256 == $member and
      .producer_sources_sha256 == $sources and
      .producer_objects_sha256 == $objects and
      .checkpoint_runtime_sha256 == $runtime and
      (.base_heap_sha256 | test("^[0-9a-f]{64}$")) and
      (.model_inventory_sha1 | test("^[0-9a-f]{40}$")) and
      (.model_features_sha1 | test("^[0-9a-f]{40}$")) and
      (.model_weights_sha1 | test("^[0-9a-f]{40}$")) and
      .model_feature_rows > 0' "$chain/base.json" >/dev/null
  test "$(sha "$db")" = "$(jq -r '.db_order_sha256' "$chain/base.json")"
  test "$(sha "$chain/base-metadata.json")" = \
    "$(jq -r '.base_metadata_sha256' "$chain/base.json")"
  test "$(sha "$chain/base.log")" = \
    "$(jq -r '.base_log_sha256' "$chain/base.json")"
  jq -e --slurpfile bases "$chain/base.json" '
    $bases[0] as $base |
    .schema == "hh-current-db-checkpoint-chain-v1" and
    .theory == $base.theory and .policy_version == $base.policy_version and
    .db_goal_count == $base.db_goal_count and
    .db_order_sha1 == $base.db_order_sha1 and
    .model_inventory_sha1 == $base.model_inventory_sha1 and
    .model_features_sha1 == $base.model_features_sha1 and
    .model_weights_sha1 == $base.model_weights_sha1 and
    .model_feature_rows == $base.model_feature_rows and
    .target_model_features_sha1 == $base.target_model_features_sha1' \
    "$chain/base-metadata.json" >/dev/null
  test "$(wc -l <"$db")" -eq "$count"
  cmp -s <(sort -u "$db") <(sort -u "$canonical")
  test "$(sort -u "$db" | wc -l)" -eq "$count"
  expected=0
  prior=$(jq -r '.base_heap_sha256' "$chain/base.json")
  model_inventory=$(jq -r '.model_inventory_sha1' "$chain/base.json")
  model_features=$(jq -r '.model_features_sha1' "$chain/base.json")
  model_weights=$(jq -r '.model_weights_sha1' "$chain/base.json")
  model_rows=$(jq -r '.model_feature_rows' "$chain/base.json")
  mapfile -t checkpoint_atoms < <(find "$chain/atoms" -mindepth 1 \
    -maxdepth 1 -type d -name '[0-9][0-9][0-9][0-9][0-9][0-9]' | \
    LC_ALL=C sort)
  for atom in "${checkpoint_atoms[@]}"; do
    manifest="$atom/receipt.json"
    test -s "$manifest" -a ! -L "$manifest"
    start=$(jq -er '.start' "$manifest")
    completed=$(jq -er '.completed' "$manifest")
    test "$start" -eq "$expected" -a "$completed" -gt 0
    test "${atom##*/}" = "$(printf '%06d' "$start")"
    jq -e --arg theory "$theory" --arg policy "$CHECKPOINT_POLICY" \
      --arg storage "$CHECKPOINT_STORAGE_POLICY" \
      --argjson headroom "$CHECKPOINT_ATOM_HEADROOM_KIB" \
      --arg reservation "$CHECKPOINT_RESERVATION_POLICY" \
      --argjson slots "$CHECKPOINT_RESERVATION_SLOTS" \
      --arg prior "$prior" --arg invocation "$(sha "$OUT/invocations/$theory.json")" \
      --arg run "$(sha "$OUT/run.json")" --arg member "$(field "$theory" 7)" \
      --arg sources "$(current_sources_digest "$theory")" \
      --arg objects "$(current_objects_digest "$theory")" \
      --arg runtime "$CHECKPOINT_RUNTIME_SHA" \
      --arg model_inventory "$model_inventory" \
      --arg model_features "$model_features" --arg model_weights "$model_weights" \
      --argjson model_rows "$model_rows" \
      --argjson start "$start" --argjson completed "$completed" '
        .schema == "hh-current-db-checkpoint-atom-receipt-v1" and
        .policy_version == $policy and .theory == $theory and
        .storage_policy_version == $storage and
        .atom_headroom_kib == $headroom and
        .heavy_hol_reservation_policy_version == $reservation and
        .heavy_hol_reservation_maximum_concurrent_atoms == $slots and
        .start == $start and .completed == $completed and
        .end == $start + $completed and .prior_heap_sha256 == $prior and
        .invocation_provenance_sha256 == $invocation and
        .run_header_sha256 == $run and
        .canonical_journal_member_sha256 == $member and
        .producer_sources_sha256 == $sources and
        .producer_objects_sha256 == $objects and
        .checkpoint_runtime_sha256 == $runtime and
        .model_inventory_sha1 == $model_inventory and
        .model_features_sha1 == $model_features and
        .model_weights_sha1 == $model_weights and
        .model_feature_rows == $model_rows and
        .profile_start == 0 and .profile_length == 8 and
        .replay_theory == false and .mismatches == 0 and
        .binding_mismatches == 0 and .prover_spawns == 0 and
        .row_count == 8 * $completed and
        .ranking_count == $completed and
        (.next_heap_sha256 | test("^[0-9a-f]{64}$"))' "$manifest" >/dev/null
    test "$(sha "$atom/rows.tsv")" = "$(jq -r '.rows_sha256' "$manifest")"
    test "$(sha "$atom/names.txt")" = "$(jq -r '.names_sha256' "$manifest")"
    test "$(sha "$atom/rankings.sha256")" = \
      "$(jq -r '.rankings_inventory_sha256' "$manifest")"
    test "$(sha "$atom/progress.json")" = \
      "$(jq -r '.progress_sha256' "$manifest")"
    test "$(sha "$atom/mismatch.jsonl")" = \
      "$(jq -r '.mismatch_sha256' "$manifest")"
    test "$(sha "$atom/atom.log")" = \
      "$(jq -r '.atom_log_sha256' "$manifest")"
    test "$(sha "$atom/checkpoint-stage")" = \
      "$(jq -r '.checkpoint_stage_sha256' "$manifest")"
    test "$(cat "$atom/checkpoint-stage")" = saved
    test ! -s "$atom/mismatch.jsonl"
    sed -n "$((start + 1)),$((start + completed))p" "$db" | \
      cmp -s - "$atom/names.txt"
    test "$(wc -l <"$atom/rows.tsv")" -eq "$((completed * 8 + 1))"
    (cd "$atom/rankings" && sha256sum -c ../rankings.sha256 >/dev/null)
    test "$(wc -l <"$atom/rankings.sha256")" -eq "$completed"
    for ranking in "$atom"/rankings/*.ranking; do
      head -1 "$ranking" | cut -f2- | jq -e \
        --arg invocation "$(sha "$OUT/invocations/$theory.json")" \
        --arg run "$(sha "$OUT/run.json")" --arg member "$(field "$theory" 7)" \
        --arg sources "$(current_sources_digest "$theory")" \
        --arg objects "$(current_objects_digest "$theory")" \
        --arg model_inventory "$model_inventory" \
        --arg model_features "$model_features" --arg model_weights "$model_weights" \
        --argjson model_rows "$model_rows" '
          .schema == "hh-anchor-current-ranking-v1" and
          .producer_role == "current" and
          .goal_digest_schema == "hh-goal-struct-v1" and
          .invocation_provenance_sha256 == $invocation and
          .run_header_sha256 == $run and
          .canonical_journal_member_sha256 == $member and
          .producer_sources_sha256 == $sources and
          .producer_objects_sha256 == $objects and
          .model_inventory_sha1 == $model_inventory and
          .model_features_sha1 == $model_features and
          .model_weights_sha1 == $model_weights and
          .model_feature_rows == $model_rows and
          .selected_premise_count >= 0 and .pool_count >= .selected_premise_count' \
        >/dev/null
    done
    prior=$(jq -r '.next_heap_sha256' "$manifest")
    expected=$((expected + completed))
  done
  if test "$expected" -eq 0; then
    latest_heap="$chain/base.heap"
  else
    latest_heap="${checkpoint_atoms[${#checkpoint_atoms[@]}-1]}/next.heap"
  fi
  test -s "$latest_heap" -a ! -L "$latest_heap"
  test "$(sha "$latest_heap")" = "$prior"
  # Every superseded heap is pruned only after its successor receipt commits.
  test "$(find "$chain" -type f -name '*.heap' | wc -l)" -eq 1
  CHECKPOINT_CHAIN_END=$expected
  CHECKPOINT_CHAIN_PRIOR_SHA=$prior
  CHECKPOINT_CHAIN_PRIOR_HEAP=$latest_heap
}

checkpoint_validate_chain () {
  local result override=${HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE:-}
  if result=$(HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE="$override" \
      CHECKPOINT_RUNTIME_SHA="$CHECKPOINT_RUNTIME_SHA" \
      bash -Eeuo pipefail -c '
        checkpoint_validate_chain_unsafe "$1" "$2"
        printf "%s\t%s\t%s\n" "$CHECKPOINT_CHAIN_END" \
          "$CHECKPOINT_CHAIN_PRIOR_SHA" "$CHECKPOINT_CHAIN_PRIOR_HEAP"
      ' checkpoint-chain-validator "$1" "$2"); then
    IFS=$'\t' read -r CHECKPOINT_CHAIN_END CHECKPOINT_CHAIN_PRIOR_SHA \
      CHECKPOINT_CHAIN_PRIOR_HEAP <<<"$result"
  else
    return $?
  fi
  mapfile -t checkpoint_atoms < <(find "$(checkpoint_chain_dir "$1")/atoms" \
    -mindepth 1 -maxdepth 1 -type d \
    -name '[0-9][0-9][0-9][0-9][0-9][0-9]' | LC_ALL=C sort)
}

current_sources_digest () {
  jq -S -c --arg state "$(execution_state "$1")" \
    '.execution_states[$state].current_loaded.sources' \
    "$INPUTS/top-provenance.json" | sha256sum | awk '{print $1}'
}

current_objects_digest () {
  jq -S -c --arg state "$(execution_state "$1")" \
    '.execution_states[$state].current_loaded.objects' \
    "$INPUTS/top-provenance.json" | sha256sum | awk '{print $1}'
}

checkpoint_create_base () {
  local theory=$1 count=$2 chain work launch overlay current_state worker_key
  local invocation metadata base_tmp durable heap_sha db_sha status
  chain=$(checkpoint_chain_dir "$theory")
  if test -s "$chain/base.json"; then
    checkpoint_prune_scratch "$theory" "$count" 0
    return
  fi
  checkpoint_require_headroom
  require_host_memory_headroom
  mkdir -p "$chain/atoms"
  work="$STATE/current-checkpoint/$theory/base"
  find "$work" -depth -mindepth 1 -delete 2>/dev/null || true
  mkdir -p "$work/worker"
  launch=$(launch_directory current "$theory" 0)
  overlay=$(overlay_root "$theory")
  current_state=$(execution_state "$theory")
  invocation="$OUT/invocations/$theory.json"
  worker_key="$theory-checkpoint-base"
  checkpoint_reservation_acquire "base:$theory"
  stage_current_signature "$theory" "$worker_key"
  if (checkpoint_reservation_close_child_fd; cd "$work" && \
    timeout --signal=TERM --kill-after=120s "$TIMEOUT" \
    env -u HHEVAL_ANCHOR_BASELINE -u HHEVAL_CURRENT_BASELINE_SHA256 \
      -u HHEVAL_ANCHOR_PREMISES_DIRECTORY \
      -u HHEVAL_ANCHOR_PREMISES_PROVENANCE_SHA256 \
      -u HHEVAL_CURRENT_RANKINGS_DIRECTORY \
      HOLDIR="$overlay" HHEVAL_CURRENT_OVERLAY="$overlay" \
      HHEVAL_CURRENT_EXECUTION_STATE="$current_state" \
      HHEVAL_TASK10_A_INPUTS="$INPUTS" HHEVAL_THEORY="$theory" \
      HHEVAL_CURRENT_INVOCATION_PROVENANCE_SHA256="$(sha "$invocation")" \
      HHEVAL_CURRENT_INVOCATION_PATH="$invocation" \
      HHEVAL_CURRENT_WORKER_ROOT="$work/worker" \
      HHEVAL_CURRENT_INNER="$INPUTS/current-checkpoint-base.sml" \
      HHEVAL_CURRENT_LAUNCH_DIR="$launch" \
      HHEVAL_CURRENT_CHECKPOINT_LAUNCH=base \
      HHEVAL_CURRENT_CHECKPOINT_HEAP="$work/base.heap" \
      HHEVAL_CURRENT_CHECKPOINT_DB_ORDER="$work/db-order.txt" \
      HHEVAL_CURRENT_CHECKPOINT_BASE_METADATA="$work/metadata.json" \
      "$CURRENT_WRAPPER" >"$work/base.log" 2>&1); then status=0; else status=$?; fi
  unstage_current_signature "$worker_key" || status=1
  checkpoint_reservation_release "base:$theory" "$status" || status=1
  if test "$status" -ne 0; then
    checkpoint_archive_failure "$theory" base "$status"
    checkpoint_clear_scratch "$theory"
    return "$status"
  fi
  if ! grep -q 'HHEVAL_CURRENT_CHECKPOINT_HEAP_LOAD=success' \
      "$work/base.log"; then
    checkpoint_archive_failure "$theory" base-load-marker 1
    checkpoint_clear_scratch "$theory"
    return 1
  fi
  test -s "$work/base.heap" -a -s "$work/db-order.txt" -a -s "$work/metadata.json"
  test "$(wc -l <"$work/db-order.txt")" -eq "$count"
  jq -e --arg theory "$theory" --arg policy "$CHECKPOINT_POLICY" \
    --argjson count "$count" '.schema == "hh-current-db-checkpoint-chain-v1" and
      .policy_version == $policy and .theory == $theory and
      .db_goal_count == $count and .model_feature_rows > 0' \
    "$work/metadata.json" >/dev/null
  heap_sha=$(sha "$work/base.heap"); db_sha=$(sha "$work/db-order.txt")
  durable="$chain/.base.$$"
  mkdir "$durable"
  cp "$work/base.heap" "$durable/base.heap"
  cp "$work/db-order.txt" "$durable/db-order.txt"
  cp "$work/metadata.json" "$durable/metadata.json"
  cp "$work/base.log" "$durable/base.log"
  jq -n --arg theory "$theory" --arg policy "$CHECKPOINT_POLICY" \
    --arg storage "$CHECKPOINT_STORAGE_POLICY" \
    --argjson headroom "$CHECKPOINT_ATOM_HEADROOM_KIB" \
    --arg reservation "$CHECKPOINT_RESERVATION_POLICY" \
    --argjson slots "$CHECKPOINT_RESERVATION_SLOTS" \
    --arg invocation "$(sha "$invocation")" --arg run "$(sha "$OUT/run.json")" \
    --arg member "$(field "$theory" 7)" --arg sources "$(current_sources_digest "$theory")" \
    --arg objects "$(current_objects_digest "$theory")" \
    --arg runtime "$CHECKPOINT_RUNTIME_SHA" --arg heap "$heap_sha" \
    --arg db "$db_sha" --arg metadata "$(sha "$work/metadata.json")" \
    --arg base_log "$(sha "$work/base.log")" \
    --slurpfile metas "$work/metadata.json" '
      $metas[0] as $meta |
      {schema:"hh-current-db-checkpoint-base-receipt-v1",
       policy_version:$policy,theory:$theory,db_goal_count:$meta.db_goal_count,
       storage_policy_version:$storage,atom_headroom_kib:$headroom,
       heavy_hol_reservation_policy_version:$reservation,
       heavy_hol_reservation_maximum_concurrent_atoms:$slots,
       db_order_sha1:$meta.db_order_sha1,db_order_sha256:$db,
       invocation_provenance_sha256:$invocation,run_header_sha256:$run,
       canonical_journal_member_sha256:$member,
       producer_sources_sha256:$sources,producer_objects_sha256:$objects,
       checkpoint_runtime_sha256:$runtime,base_metadata_sha256:$metadata,
       base_log_sha256:$base_log,
       base_heap_sha256:$heap,model_current_theory:$meta.model_current_theory,
       model_ancestry:$meta.model_ancestry,
       model_namespace_count:$meta.model_namespace_count,
       model_inventory_sha1:$meta.model_inventory_sha1,
       model_features_sha1:$meta.model_features_sha1,
       model_weights_sha1:$meta.model_weights_sha1,
       model_feature_rows:$meta.model_feature_rows,
       target_model_features_sha1:$meta.target_model_features_sha1}' \
    >"$durable/base.json"
  chmod 0444 "$durable"/*
  mv "$durable/base.heap" "$chain/base.heap"
  mv "$durable/db-order.txt" "$chain/db-order.txt"
  mv "$durable/metadata.json" "$chain/base-metadata.json"
  mv "$durable/base.log" "$chain/base.log"
  mv "$durable/base.json" "$chain/base.json"
  rmdir "$durable"
  checkpoint_prune_scratch "$theory" "$count" 0
}

checkpoint_atom_once_unsafe () {
  local theory=$1 count=$2 chain start prior prior_sha max names work launch
  local overlay current_state invocation worker_key status completed durable atom
  local header ranking_count ranking_inventory next_sha previous_heap
  local oom_before oom_after kill_marker= retry_status= verified_oom=0
  chain=$(checkpoint_chain_dir "$theory")
  checkpoint_validate_chain "$theory" "$count"
  start=$CHECKPOINT_CHAIN_END
  test "$start" -lt "$count" || return 0
  checkpoint_require_headroom
  require_host_memory_headroom
  prior=$CHECKPOINT_CHAIN_PRIOR_HEAP; prior_sha=$CHECKPOINT_CHAIN_PRIOR_SHA
  max=$((count - start)); test "$max" -le "$CHECKPOINT_MAX_GOALS" || \
    max=$CHECKPOINT_MAX_GOALS
  names=$(sed -n "$((start + 1)),$((start + max))p" "$chain/db-order.txt" | paste -sd ' ' -)
  work="$STATE/current-checkpoint/$theory/atom-$start"
  find "$work" -depth -mindepth 1 -delete 2>/dev/null || true
  mkdir -p "$work/worker" "$work/hammer" "$work/scratch" "$work/rankings"
  launch=$(launch_directory current "$theory" 0); overlay=$(overlay_root "$theory")
  current_state=$(execution_state "$theory"); invocation="$OUT/invocations/$theory.json"
  worker_key="$theory-checkpoint-$(printf '%06d' "$start")"
  if test "${HHEVAL_CHECKPOINT_TEST_SIGKILL_ONCE_THEORY:-}" = "$theory"; then
    mkdir -p "$STATE/checkpoint-test-sigkill-once"
    if mkdir "$STATE/checkpoint-test-sigkill-once/$theory" 2>/dev/null; then
      kill_marker="$STATE/checkpoint-test-sigkill-once/$theory/killed"
    fi
  fi
  checkpoint_reservation_acquire "atom:$theory:$start"
  stage_current_signature "$theory" "$worker_key"
  oom_before=$(checkpoint_scope_oom_kills)
  if test "${HHEVAL_CHECKPOINT_TEST_SIGKILL_CHILD:-0}" = 1; then
    if /bin/bash --noprofile --norc -c 'kill -KILL $$'; then
      status=0
    else
      status=$?
    fi
  elif (checkpoint_reservation_close_child_fd; cd "$work" && \
    timeout --signal=TERM --kill-after=120s "$TIMEOUT" \
    env HOLDIR="$overlay" HOL4_HAMMER_DIR="$work/hammer" \
      HHEVAL_CURRENT_OVERLAY="$overlay" HHEVAL_CURRENT_EXECUTION_STATE="$current_state" \
      HHEVAL_TASK10_A_INPUTS="$INPUTS" HHEVAL_CURRENT_WORKER_ROOT="$work/worker" \
      HHEVAL_CURRENT_INNER="$CURRENT_DRIVER" HHEVAL_CURRENT_LAUNCH_DIR="$launch" \
      HHEVAL_CURRENT_CHECKPOINT_LAUNCH=atom \
      HHEVAL_CURRENT_CHECKPOINT_PRIOR_HEAP="$prior" \
      HHEVAL_CURRENT_CHECKPOINT_PRIOR_SHA256="$prior_sha" \
      HHEVAL_CURRENT_CHECKPOINT_MODE=atom HHEVAL_CURRENT_CHECKPOINT_SOFT_SECONDS=420 \
      HHEVAL_CURRENT_CHECKPOINT_NEXT_HEAP="$work/next.heap" \
      HHEVAL_CURRENT_CHECKPOINT_STAGE_PATH="$work/checkpoint-stage" \
      HHEVAL_CURRENT_CHECKPOINT_COMPLETED_NAMES="$work/names.txt" \
      HHEVAL_THEORY="$theory" HHEVAL_THEORY_DIR="$launch" \
      HHEVAL_ANCHOR_THEOREMS="$names" HHEVAL_ANCHOR_PROFILE_START=0 \
      HHEVAL_ANCHOR_PROFILE_LENGTH=8 HHEVAL_ANCHOR_REPLAY_THEORY=0 \
      HHEVAL_ANCHOR_BASELINE="$OUT/baseline/$theory.tsv" \
      HHEVAL_ANCHOR_OUTPUT="$work/rows.tsv" \
      HHEVAL_ANCHOR_MISMATCHES="$work/mismatch.jsonl" \
      HHEVAL_ANCHOR_SCRATCH="$work/scratch" \
      HHEVAL_CURRENT_INVOCATION_PROVENANCE_SHA256="$(sha "$invocation")" \
      HHEVAL_CURRENT_INVOCATION_PATH="$invocation" \
      HHEVAL_CURRENT_BASELINE_SHA256="$(sha "$OUT/baseline/$theory.tsv")" \
      HHEVAL_CURRENT_RUN_HEADER_SHA256="$(sha "$OUT/run.json")" \
      HHEVAL_CURRENT_CANONICAL_MEMBER_SHA256="$(field "$theory" 7)" \
      HHEVAL_CURRENT_PRODUCER_SOURCES_SHA256="$(current_sources_digest "$theory")" \
      HHEVAL_CURRENT_PRODUCER_OBJECTS_SHA256="$(current_objects_digest "$theory")" \
      HHEVAL_CURRENT_RANKINGS_DIRECTORY="$work/rankings" \
      HHEVAL_CURRENT_PROGRESS_PATH="$work/progress.json" \
      HHEVAL_CURRENT_GOAL_RANGE_START="$start" \
      HHEVAL_CURRENT_GOAL_RANGE_LENGTH="$max" \
      HHEVAL_CURRENT_GOAL_CHUNK_POLICY_VERSION="$CHECKPOINT_POLICY" \
      HHEVAL_CURRENT_TEST_SIGKILL_MARKER="$kill_marker" \
      "$CURRENT_WRAPPER" >"$work/atom.log" 2>&1); then
    status=0
  else
    status=$?
  fi
  oom_after=$(checkpoint_scope_oom_kills)
  unstage_current_signature "$worker_key" || status=1
  checkpoint_reservation_release "atom:$theory:$start" "$status" || status=1
  if test "$status" -ne 0; then
    if test -f "$work/checkpoint-stage" &&
       grep -Eq '^(saving|saved)$' "$work/checkpoint-stage"; then
      retry_status=74
    elif test "$status" -eq 137 ||
         { test -n "$kill_marker" && test -s "$kill_marker"; }; then
      retry_status=76
    elif test "$oom_after" -gt "$oom_before" &&
         test -s "$work/progress.json" &&
         test ! -e "$work/next.heap" &&
         test "$(cat "$work/checkpoint-stage" 2>/dev/null || true)" = deriving; then
      retry_status=76
      verified_oom=1
    else
      retry_status=$status
    fi
    jq -n --arg theory "$theory" --argjson start "$start" \
      --argjson status "$status" --argjson retry_status "$retry_status" \
      --argjson oom_before "$oom_before" --argjson oom_after "$oom_after" \
      --argjson verified_oom "$verified_oom" \
      --arg test_marker "${kill_marker:-}" \
      '{schema:"hh-current-checkpoint-failure-classification-v1",
        theory:$theory,start:$start,worker_status:$status,
        retry_status:$retry_status,oom_kill_before:$oom_before,
        oom_kill_after:$oom_after,verified_scope_oom:$verified_oom,
        test_sigkill_marker:$test_marker,receipt_accepted:false}' \
      >"$work/failure-classification.json"
    checkpoint_archive_failure "$theory" "atom-$start" "$status"
    checkpoint_prune_scratch "$theory" "$count" 0
    return "$retry_status"
  fi
  if ! grep -q 'HHEVAL_CURRENT_CHECKPOINT_HEAP_LOAD=success' \
      "$work/atom.log"; then
    checkpoint_archive_failure "$theory" "atom-$start-load-marker" 1
    checkpoint_prune_scratch "$theory" "$count" 0
    return 1
  fi
  if test "${HHEVAL_CHECKPOINT_TEST_KILL_AFTER_CHILD:-0}" = 1; then
    checkpoint_prune_scratch "$theory" "$count" 0
    return 125
  fi
  for file in next.heap names.txt rows.tsv mismatch.jsonl progress.json atom.log \
      checkpoint-stage; do
    test -e "$work/$file" -a ! -L "$work/$file"
  done
  test ! -s "$work/mismatch.jsonl"
  test "$(cat "$work/checkpoint-stage")" = saved
  completed=$(wc -l <"$work/names.txt"); test "$completed" -gt 0 -a "$completed" -le "$max"
  sed -n "$((start + 1)),$((start + completed))p" "$chain/db-order.txt" | cmp -s - "$work/names.txt"
  header="$work/rows.header.json"
  head -1 "$work/rows.tsv" | cut -f2- >"$header"
  jq -e --arg policy "$CHECKPOINT_POLICY" --argjson start "$start" \
    --argjson max "$max" --argjson completed "$completed" '
      .schema == "hh-anchor-current-v1" and .profile_start == 0 and
      .profile_length == 8 and .replay_theory == false and
      .goal_range_start == $start and .goal_range_length == $max and
      .completed_goal_range_start == $start and
      .completed_goal_range_length == $completed and
      .goal_chunk_policy_version == $policy and .goals == $completed and
      .row_count == 8 * $completed and .mismatches == 0 and
      .binding_mismatches == 0 and .prover_spawns == 0 and
      (.goal_bindings | length) == $completed' "$header" >/dev/null
  ranking_count=$(find "$work/rankings" -maxdepth 1 -type f -name '*.ranking' | wc -l)
  test "$ranking_count" -eq "$completed"
  (cd "$work/rankings" && find . -maxdepth 1 -type f -name '*.ranking' \
    -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) >"$work/rankings.sha256"
  (cd "$work/rankings" && sha256sum -c ../rankings.sha256 >/dev/null)
  next_sha=$(sha "$work/next.heap")
  atom="$chain/atoms/$(printf '%06d' "$start")"; test ! -e "$atom"
  durable="$chain/atoms/.staging-$(printf '%06d' "$start")-$$"; mkdir "$durable"
  cp "$work/next.heap" "$durable/next.heap"; cp "$work/names.txt" "$durable/names.txt"
  cp "$work/rows.tsv" "$durable/rows.tsv"; cp "$work/mismatch.jsonl" "$durable/mismatch.jsonl"
  cp "$work/progress.json" "$durable/progress.json"; cp "$work/atom.log" "$durable/atom.log"
  cp "$work/checkpoint-stage" "$durable/checkpoint-stage"
  cp "$work/rankings.sha256" "$durable/rankings.sha256"; cp -R "$work/rankings" "$durable/rankings"
  ranking_inventory=$(sha "$work/rankings.sha256")
  jq -n --arg theory "$theory" --arg policy "$CHECKPOINT_POLICY" \
    --arg storage "$CHECKPOINT_STORAGE_POLICY" \
    --argjson headroom "$CHECKPOINT_ATOM_HEADROOM_KIB" \
    --arg reservation "$CHECKPOINT_RESERVATION_POLICY" \
    --argjson slots "$CHECKPOINT_RESERVATION_SLOTS" \
    --arg prior "$prior_sha" --arg next "$next_sha" \
    --arg invocation "$(sha "$invocation")" --arg run "$(sha "$OUT/run.json")" \
    --arg member "$(field "$theory" 7)" --arg sources "$(current_sources_digest "$theory")" \
    --arg objects "$(current_objects_digest "$theory")" --arg runtime "$CHECKPOINT_RUNTIME_SHA" \
    --arg rows "$(sha "$work/rows.tsv")" --arg names "$(sha "$work/names.txt")" \
    --arg rankings "$ranking_inventory" --arg progress "$(sha "$work/progress.json")" \
    --arg mismatch "$(sha "$work/mismatch.jsonl")" \
    --arg stage "$(sha "$work/checkpoint-stage")" \
    --arg atom_log "$(sha "$work/atom.log")" --argjson start "$start" \
    --argjson completed "$completed" --slurpfile headers "$header" '
      $headers[0] as $header |
      {schema:"hh-current-db-checkpoint-atom-receipt-v1",policy_version:$policy,
       storage_policy_version:$storage,atom_headroom_kib:$headroom,
       heavy_hol_reservation_policy_version:$reservation,
       heavy_hol_reservation_maximum_concurrent_atoms:$slots,
       theory:$theory,start:$start,completed:$completed,end:($start+$completed),
       profile_start:0,profile_length:8,replay_theory:false,
       prior_heap_sha256:$prior,next_heap_sha256:$next,
       invocation_provenance_sha256:$invocation,run_header_sha256:$run,
       canonical_journal_member_sha256:$member,producer_sources_sha256:$sources,
       producer_objects_sha256:$objects,checkpoint_runtime_sha256:$runtime,
       model_inventory_sha1:$header.model_inventory_sha1,
       model_features_sha1:$header.model_features_sha1,
       model_weights_sha1:$header.model_weights_sha1,
       model_feature_rows:$header.model_feature_rows,
       goal_bindings:$header.goal_bindings,row_count:$header.row_count,
       row_set_sha1:$header.row_set_sha1,mismatches:$header.mismatches,
       binding_mismatches:$header.binding_mismatches,prover_spawns:$header.prover_spawns,
       rows_sha256:$rows,names_sha256:$names,ranking_count:$completed,
       rankings_inventory_sha256:$rankings,progress_sha256:$progress,
       mismatch_sha256:$mismatch,atom_log_sha256:$atom_log,
       checkpoint_stage_sha256:$stage}' \
    >"$durable/receipt.json"
  find "$durable" -type f -exec chmod 0444 {} +
  find "$durable" -type d -exec chmod 0755 {} +
  mv "$durable" "$atom"
  test "$(sha "$atom/next.heap")" = \
    "$(jq -r '.next_heap_sha256' "$atom/receipt.json")"
  test "$(sha "$atom/rows.tsv")" = \
    "$(jq -r '.rows_sha256' "$atom/receipt.json")"
  test "$(sha "$atom/rankings.sha256")" = \
    "$(jq -r '.rankings_inventory_sha256' "$atom/receipt.json")"
  (cd "$atom/rankings" && sha256sum -c ../rankings.sha256 >/dev/null)
  previous_heap=$prior
  if test "$previous_heap" != "$atom/next.heap"; then
    find "$previous_heap" -maxdepth 0 -type f -delete
  fi
  checkpoint_prune_scratch "$theory" "$count" 0
}

checkpoint_atom_once () {
  HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE="${HHEVAL_CHECKPOINT_CHAIN_ROOT_OVERRIDE:-}" \
  bash --noprofile --norc -Eeuo pipefail -c '
    checkpoint_atom_once_unsafe "$1" "$2"
  ' checkpoint-atom-worker "$1" "$2"
}

checkpoint_render_fold_header () {
  local first=$1 bindings=$2 output=$3 chain=$4 inventory=$5 rows=$6
  local goals=$7 atoms=$8
  head -1 "$first" | cut -f2- | jq -c \
    --arg chain "$chain" --arg inventory "$inventory" \
    --arg policy "$CHECKPOINT_POLICY" \
    --arg storage "$CHECKPOINT_STORAGE_POLICY" \
    --argjson headroom "$CHECKPOINT_ATOM_HEADROOM_KIB" \
    --arg reservation "$CHECKPOINT_RESERVATION_POLICY" \
    --argjson slots "$CHECKPOINT_RESERVATION_SLOTS" \
    --arg rows "$rows" --argjson goals "$goals" \
    --argjson atoms "$atoms" --argjson max_goals "$CHECKPOINT_MAX_GOALS" \
    --slurpfile bindings_file "$bindings" '
      $bindings_file[0] as $bindings |
      .goals=$goals | .goal_range_start=0 | .goal_range_length=$goals |
      .completed_goal_range_start=0 |
      .completed_goal_range_length=$goals | .replay_theory=true |
      .goal_bindings=$bindings | .row_count=($goals*8) |
      .goal_chunk_schema="hh-profile-goal-chunks-v1" |
      .goal_chunk_policy_version="hh-current-goal-bisect-v1" |
      .goal_chunk_count=$atoms | .goal_chunk_max_goals=$max_goals |
      .goal_chunk_range_inventory_sha256=$inventory |
      .goal_chunk_inventory_sha256=$inventory |
      .goal_chunk_rows_sha256=$rows |
      .checkpoint_chain_schema="hh-current-db-checkpoint-chain-v1" |
      .checkpoint_chain_policy_version=$policy |
      .checkpoint_storage_policy_version=$storage |
      .checkpoint_atom_headroom_kib=$headroom |
      .checkpoint_heavy_hol_reservation_policy_version=$reservation |
      .checkpoint_heavy_hol_reservation_maximum_concurrent_atoms=$slots |
      .checkpoint_chain_validation_sha256=$chain |
      .checkpoint_chain_inventory_sha256=$inventory |
      .checkpoint_chain_atoms=$atoms' >"$output"
}

checkpoint_fold_chain () {
  local theory=$1 count=$2 output=$3 chain names all_rows ordered bindings
  local certificate chain_digest rankings_dir body_sha atom file
  local baseline_first8 baseline_ordered
  chain=$(checkpoint_chain_dir "$theory"); names=$(theorem_names_file "$theory" "$count")
  mkdir -p "$STATE/current-checkpoint/$theory"
  checkpoint_validate_chain "$theory" "$count"; test "$CHECKPOINT_CHAIN_END" -eq "$count"
  all_rows="$STATE/current-checkpoint/$theory/all-rows.tsv"; : >"$all_rows"
  bindings="$STATE/current-checkpoint/$theory/bindings.jsonl"; : >"$bindings"
  rankings_dir="$OUT/current-rankings/$theory"; mkdir -p "$rankings_dir"
  find "$rankings_dir" -depth -mindepth 1 -delete
  for atom in "${checkpoint_atoms[@]}"; do
    tail -n +2 "$atom/rows.tsv" >>"$all_rows"
    head -1 "$atom/rows.tsv" | cut -f2- | jq -c '.goal_bindings[]' >>"$bindings"
    for file in "$atom"/rankings/*.ranking; do
      test ! -e "$rankings_dir/${file##*/}"; cp "$file" "$rankings_dir/${file##*/}"
    done
  done
  ordered="$STATE/current-checkpoint/$theory/ordered.tsv"
  awk -F '\t' -v theory="$theory" 'NR==FNR {order[theory "." $1]=NR; next}
    {key=order[$1] SUBSEP $2; if (!order[$1] || seen[key]++) bad=1; row[key]=$0}
    END {for(i=1;i<=length(order);i++) for(s=1;s<=8;s++) {
      key=i SUBSEP s; if(!(key in row)) bad=1; else print row[key]}
      if(bad) exit 1}' "$names" "$all_rows" >"$ordered"
  test "$(wc -l <"$ordered")" -eq "$((count * 8))"
  baseline_first8="$STATE/current-checkpoint/$theory/baseline-first8.tsv"
  awk -F '\t' '$2 >= 1 && $2 <= 8' "$OUT/baseline/$theory.tsv" | \
    LC_ALL=C sort -t "$(printf '\t')" -k1,1 -k2,2n >"$baseline_first8"
  baseline_ordered="$STATE/current-checkpoint/$theory/current-first8.sorted.tsv"
  LC_ALL=C sort -t "$(printf '\t')" -k1,1 -k2,2n "$ordered" \
    >"$baseline_ordered"
  cmp -s "$baseline_first8" "$baseline_ordered"
  (cd "$rankings_dir" && find . -maxdepth 1 -type f -name '*.ranking' \
    -print0 | LC_ALL=C sort -z | xargs -0 sha256sum) >"$rankings_dir/SHA256SUMS"
  test "$(wc -l <"$rankings_dir/SHA256SUMS")" -eq "$count"
  chain_digest=$(find "$chain" -type f ! -name '*.heap' \
    ! -name validation.json -print0 | LC_ALL=C sort -z | \
    xargs -0 sha256sum | sha256sum | awk '{print $1}')
  body_sha=$(sha "$ordered")
  certificate="$chain/validation.json"
  jq -n --arg theory "$theory" --arg policy "$CHECKPOINT_POLICY" \
    --arg storage "$CHECKPOINT_STORAGE_POLICY" \
    --argjson headroom "$CHECKPOINT_ATOM_HEADROOM_KIB" \
    --arg reservation "$CHECKPOINT_RESERVATION_POLICY" \
    --argjson slots "$CHECKPOINT_RESERVATION_SLOTS" \
    --arg digest "$chain_digest" --arg heap "$CHECKPOINT_CHAIN_PRIOR_SHA" \
    --arg rows "$body_sha" --argjson goals "$count" \
    --argjson atoms "${#checkpoint_atoms[@]}" \
    '{schema:"hh-current-db-checkpoint-chain-validation-v1",status:"complete",
      theory:$theory,policy_version:$policy,goals:$goals,atoms:$atoms,
      storage_policy_version:$storage,atom_headroom_kib:$headroom,
      heavy_hol_reservation_policy_version:$reservation,
      heavy_hol_reservation_maximum_concurrent_atoms:$slots,
      gap_free:true,nonoverlapping:true,db_order_verified:true,
      canonical_reorder_verified:true,chain_inventory_sha256:$digest,
      final_heap_sha256:$heap,ordered_rows_sha256:$rows}' \
    >"$certificate.partial.$$"
  if test -e "$certificate"; then
    cmp -s "$certificate" "$certificate.partial.$$"
    find "$certificate.partial.$$" -maxdepth 0 -type f -delete
  else
    mv "$certificate.partial.$$" "$certificate"; chmod 0444 "$certificate"
  fi
  jq -s '.' "$bindings" >"$bindings.array"
  checkpoint_render_fold_header "${checkpoint_atoms[0]}/rows.tsv" \
    "$bindings.array" "$output.header.$$" "$(sha "$certificate")" \
    "$chain_digest" "$body_sha" "$count" "${#checkpoint_atoms[@]}"
  { printf '#hh-anchor-current-v1\t'; cat "$output.header.$$"; cat "$ordered"; } \
    >"$output.partial.$$"
  if test -e "$output"; then
    cmp -s "$output" "$output.partial.$$"
    find "$output.partial.$$" -maxdepth 0 -type f -delete
  else
    mv "$output.partial.$$" "$output"
  fi
  rm -f "$output.header.$$"
  : >"$OUT/mismatch/$theory-0.jsonl"
  checkpoint_prune_scratch "$theory" "$count" 1
}

current_checkpoint_chain () {
  local theory=$1 count=$2 output=$3 chain attempt status
  chain=$(checkpoint_chain_dir "$theory"); mkdir -p "$chain/atoms"
  find "$chain/atoms" -mindepth 1 -maxdepth 1 -type d -name '.staging-*' \
    -exec find {} -depth -delete \; 2>/dev/null || true
  checkpoint_create_base "$theory" "$count"
  checkpoint_validate_chain "$theory" "$count"
  while test "$CHECKPOINT_CHAIN_END" -lt "$count"; do
    status=1
    for ((attempt=1; attempt<=MAX_ATTEMPTS; attempt++)); do
      if checkpoint_atom_once "$theory" "$count"; then
        status=0
      else
        status=$?
      fi
      test "$status" -eq 0 && break
      if test "$status" -ne 74 -a "$status" -ne 76; then
        return "$status"
      fi
      stamp "current checkpoint infrastructure-retry" \
        "theory=$theory" "status=$status" "attempt=$attempt" \
        >>"$OUT/recycles.log"
    done
    test "$status" -eq 0
    checkpoint_validate_chain "$theory" "$count"
  done
  checkpoint_fold_chain "$theory" "$count" "$output"
}
