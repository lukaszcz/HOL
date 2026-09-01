#!/usr/bin/env bash
set -Eeuo pipefail

ROOT=${HHEVAL_TASK10_ROOT:-$(git rev-parse --show-toplevel)}
EVIDENCE_ROOT=${HHEVAL_TASK10_EVIDENCE_ROOT:-$ROOT/.task10-evidence}
EVAL="$EVIDENCE_ROOT/runs"
INPUTS=${HHEVAL_TASK10_INPUTS:?immutable preflight inputs are required}
PROVENANCE="$INPUTS/top-provenance.json"
DRIVER="$INPUTS/phase3-task10-driver.sml"
PROBE="$INPUTS/phase3-task10-probe.sml"
SCHEDULE_DRIVER="$INPUTS/phase3-task10-schedule.sml"
FROZEN="$INPUTS/eval/phase2-s30-v3/run.json"
SAMPLE_SOURCE="$INPUTS/eval/phase2-preflight-p-v3-final/journal"
STATE_BASE=${HHEVAL_TASK10_STATE_BASE:-/run/user/$(id -u)/holyhammer-phase3-task10}
TMPFS_CLEANUP_TOOL="$INPUTS/tmpfs-cleanup.sh"
VOLUME_FOLD_TOOL="$INPUTS/phase3-task10-fold-volume.sh"
FOCUSED_GATE_VERIFIER="$INPUTS/verify-focused-gates.sh"
P_F30=$(jq -er '.experiments.f30' "$PROVENANCE")
P_S30=$(jq -er '.experiments.s30v5' "$PROVENANCE")
P_PROBES=$(jq -er '.experiments.probes' "$PROVENANCE")
SAMPLE=500
EXPECTED_GOALS=24721
EXPECTED_THEORIES=253
EXPECTED_NONEMPTY=229
EXPECTED_SAMPLE_GOALS=48
EXPECTED_SAMPLE_THEORIES=33
THEORY_CHUNK=10m
CHUNK_GOALS=1
MAX_RECYCLES=12
CURRENT_COMMIT=$(jq -er '.main.commit' "$PROVENANCE")
CURRENT_DIFF=$(jq -er '.main.tracked_diff_sha256' "$PROVENANCE")
LOADED_SOURCES_SHA=$(jq -er '.main.loaded_sources_sha256' "$PROVENANCE")
LOADED_OBJECTS_SHA=$(jq -er '.main.loaded_objects_sha256' "$PROVENANCE")
GATE_RUN_SHA=$(jq -er '.canonical_gate.run_header_sha256' "$PROVENANCE")
GATE_JOURNAL_SHA=$(jq -er \
  '.canonical_gate.journal_certificate_sha256' "$PROVENANCE")
MEMORY_HIGH=133143986176
MEMORY_MAX=137438953472

# shellcheck source=/dev/null
source "$TMPFS_CLEANUP_TOOL"

E_PATH=$(jq -er '.provers.e.path' "$PROVENANCE")
E_VERSION=$(jq -er '.provers.e.version' "$PROVENANCE")
E_SHA=$(jq -er '.provers.e.sha256' "$PROVENANCE")
V_PATH=$(jq -er '.provers.vampire.path' "$PROVENANCE")
V_VERSION=$(jq -er '.provers.vampire.version' "$PROVENANCE")
V_SHA=$(jq -er '.provers.vampire.sha256' "$PROVENANCE")
Z_PATH=$(jq -er '.provers.zipperposition.path' "$PROVENANCE")
Z_VERSION=$(jq -er '.provers.zipperposition.version' "$PROVENANCE")
Z_SHA=$(jq -er '.provers.zipperposition.sha256' "$PROVENANCE")

stamp() {
  printf '%s %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*"
}

sha256_of() {
  sha256sum "$1" | cut -d' ' -f1
}

journal_digest() {
  local directory=$1
  (cd "$directory" &&
    find . -type f -name '*.jsonl' -print0 | LC_ALL=C sort -z |
      xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
}

source_patch_digest() {
  git -C "$ROOT" diff --binary -- src/holyhammer | sha256sum |
    cut -d' ' -f1
}

verify_scope() {
  local relative cgroup quota period
  relative=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
  cgroup="/sys/fs/cgroup$relative"
  [[ "$(cat "$cgroup/memory.high")" == "$MEMORY_HIGH" ]]
  [[ "$(cat "$cgroup/memory.max")" == "$MEMORY_MAX" ]]
  [[ "$(cat "$cgroup/memory.swap.max")" == 0 ]]
  read -r quota period <"$cgroup/cpu.max"
  [[ "$quota" != max ]]
  ((quota == 32 * period))
  stamp "cgroup=$relative MemoryHigh=$MEMORY_HIGH MemoryMax=$MEMORY_MAX"
}

verify_common() {
  local runtime_path runtime_source runtime_sha
  jq -e '
    .schema == "hh-task10-p-run-v4" and
    (keys == ["canonical_gate","experiments","focused_gates","main",
      "provers","runtime_tools","schema"]) and
    (.canonical_gate | keys == ["journal_certificate_sha256",
      "run_header_sha256"]) and
    (.experiments | keys == ["f30","probes","s30v5","volume"]) and
    (.main | keys == ["commit","loaded_objects_sha256",
      "loaded_sources_sha256","tracked_diff_sha256"]) and
    (.provers | keys == ["e","vampire","zipperposition"]) and
    (.runtime_tools | keys == ["files","origin_inventory_sha256",
      "schema"]) and
    .runtime_tools.schema == "hh-task10-runtime-tools-v2"
  ' \
    "$PROVENANCE" >/dev/null
  [[ "$(git -C "$ROOT" rev-parse HEAD)" == "$CURRENT_COMMIT" ]]
  [[ "$(source_patch_digest)" == "$CURRENT_DIFF" ]]
  [[ "$(sha256_of "$INPUTS/main-loaded-sources.tsv")" == \
     "$LOADED_SOURCES_SHA" ]]
  [[ "$(sha256_of "$INPUTS/main-loaded-objects.tsv")" == \
     "$LOADED_OBJECTS_SHA" ]]
  sh "$INPUTS/check-provenance.sh" "$ROOT" \
    "$INPUTS/main-loaded-sources.tsv"
  sh "$INPUTS/check-provenance.sh" "$ROOT" \
    "$INPUTS/main-loaded-objects.tsv"
  [[ "$(sha256_of "$FROZEN")" == "$GATE_RUN_SHA" ]]
  [[ "$(journal_digest "$INPUTS/eval/phase2-s30-v3/journal")" == \
     "$GATE_JOURNAL_SHA" ]]
  [[ "$(jq '.corpus | length' "$FROZEN")" == "$EXPECTED_THEORIES" ]]
  [[ "$(jq '[.corpus[].theorem_count] | add' "$FROZEN")" == \
     "$EXPECTED_GOALS" ]]
  [[ "$(jq '[.corpus[] | select(.theorem_count > 0)] | length' \
     "$FROZEN")" == "$EXPECTED_NONEMPTY" ]]
  [[ "$(nproc)" == 32 ]]
  [[ "$(findmnt -T "/run/user/$(id -u)" -n -o FSTYPE)" == tmpfs ]]
  [[ "$(sha256_of "$E_PATH")" == "$E_SHA" ]]
  [[ "$(sha256_of "$V_PATH")" == "$V_SHA" ]]
  [[ "$(sha256_of "$Z_PATH")" == "$Z_SHA" ]]
  "$E_PATH" --version | grep -F "$E_VERSION" >/dev/null
  "$V_PATH" --version | grep -F "$V_VERSION" >/dev/null
  "$Z_PATH" --version | grep -F "$Z_VERSION" >/dev/null
  [[ -f "$INPUTS/SHA256SUMS" ]]
  (cd "$INPUTS" && sha256sum -c SHA256SUMS >/dev/null)
  HHEVAL_TASK10_ROOT=$ROOT \
    "$INPUTS/runtime-inventory-selftest.sh" "$INPUTS" >/dev/null
  "$FOCUSED_GATE_VERIFIER" "$INPUTS" "$PROVENANCE"
  [[ "$(sha256_of "$INPUTS/runtime-origin.tsv")" == "$(jq -r \
    '.runtime_tools.origin_inventory_sha256' "$PROVENANCE")" ]]
  while IFS=$'\t' read -r runtime_path runtime_sha; do
    [[ "$(sha256_of "$INPUTS/$runtime_path")" == "$runtime_sha" ]]
  done < <(jq -r '.runtime_tools.files | to_entries[] |
    [.key,.value.sha256] | @tsv' "$PROVENANCE")
  while IFS=$'\t' read -r runtime_path runtime_source runtime_sha; do
    [[ "$(jq -r --arg path "$runtime_path" \
      '.runtime_tools.files[$path].sha256 // empty' "$PROVENANCE")" == \
      "$runtime_sha" ]]
  done <"$INPUTS/runtime-origin.tsv"
  [[ "$(jq '.runtime_tools.files | length' "$PROVENANCE")" == \
    "$(wc -l <"$INPUTS/runtime-origin.tsv")" ]]
  verify_scope
}

verify_existing_outputs_readonly() {
  local exp directory state input_sha accepted_sha
  input_sha=$(sha256_of "$INPUTS/SHA256SUMS")
  for exp in "$P_F30" "$P_S30" "$P_PROBES"; do
    directory="$EVAL/$exp"
    state="$STATE_BASE/$exp"
    if [[ -e "$directory" || -e "$state" ]]; then
      [[ -s "$directory/envelope.json" &&
         ! -L "$directory/envelope.json" ]]
      accepted_sha=$(jq -er '.input_inventory_sha256' \
        "$directory/envelope.json")
      if [[ "$accepted_sha" != "$input_sha" ]]; then
        printf '%s\n' \
          'task10 P tuple mismatch: sealed input does not match accepted envelope' \
          >&2
        return 78
      fi
    fi
  done
}

sample_theories() {
  find "$SAMPLE_SOURCE" -type f -name '*.jsonl' -printf '%f\n' |
    sed 's/\.jsonl$//' | LC_ALL=C sort
}

initialize_p() {
  local exp=$1 variant=$2 slots=$3 state expdir
  local source_patch_sha template input_sha
  state="$STATE_BASE/$exp"
  expdir="$EVAL/$exp"
  source_patch_sha=$(source_patch_digest)
  input_sha=$(sha256_of "$INPUTS/SHA256SUMS")
  if [[ -e "$state/.initialized" ]]; then
    [[ -s "$expdir/envelope.json" && -s "$expdir/run.json" ]]
    jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      --arg event resume --arg input_sha "$input_sha" \
      '{time:$time,event:$event,input_inventory_sha256:$input_sha}' \
      >>"$expdir/invocations.jsonl"
    stamp "$exp resume with durable journals and private cache"
    return
  fi
  [[ ! -e "$state" ]]
  [[ ! -e "$expdir" ]]
  mkdir -p "$state/scratch/out" "$state/scratch/pb" "$expdir/journal"
  mkdir -p "$expdir/scripts"
  ln -s "$state/scratch/out" "$expdir/out"
  ln -s "$state/scratch/pb" "$expdir/pb"
  case "$variant" in
    f30) template="$INPUTS/templates/f30-run.json" ;;
    s30v5) template="$INPUTS/templates/s30v5-run.json" ;;
    *) return 2 ;;
  esac
  jq --arg exp "$exp" --arg commit "$CURRENT_COMMIT" \
    --arg date "$(date -u)" --slurpfile frozen "$FROZEN" '
      .expname = $exp | .hol_commit = $commit | .date = $date |
      .corpus = $frozen[0].corpus |
      .added_from_dat = $frozen[0].added_from_dat
    ' "$template" >"$expdir/run.json"
  chmod 0444 "$expdir/run.json"
  jq -n --arg started "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg commit "$CURRENT_COMMIT" --arg variant "$variant" \
    --arg source_patch_sha "$source_patch_sha" \
    --arg loaded_sources_sha "$LOADED_SOURCES_SHA" \
    --arg loaded_objects_sha "$LOADED_OBJECTS_SHA" \
    --arg state "$state" --argjson slots "$slots" \
    --arg input_sha "$input_sha" \
    --arg run_header_sha "$(sha256_of "$expdir/run.json")" \
    --arg e_path "$E_PATH" --arg e_version "$E_VERSION" \
    --arg e_sha "$E_SHA" --arg v_path "$V_PATH" \
    --arg v_version "$V_VERSION" --arg v_sha "$V_SHA" \
    --arg z_path "$Z_PATH" --arg z_version "$Z_VERSION" \
    --arg z_sha "$Z_SHA" '
      {started:$started,status:"running",hol_commit:$commit,
       tracked_source_patch_sha256:$source_patch_sha,
       loaded_sources_inventory_sha256:$loaded_sources_sha,
       loaded_objects_inventory_sha256:$loaded_objects_sha,
       input_inventory_sha256:$input_sha,
       run_header_sha256:$run_header_sha,
       run:"P",variant:$variant,sample:500,state_root:$state,
       initial_cache_files:0,resumable_journals:true,
       envelope:{cpu_quota_cores:32,memory_high_bytes:133143986176,
         memory_max_bytes:137438953472,memory_swap_max_bytes:0,
         worker_recycle_seconds:600,tmpfs_scratch:true,
         durable_copyback:true,worker_slots:$slots},
       provers:[{name:"e",path:$e_path,version:$e_version,sha256:$e_sha},
         {name:"vampire",path:$v_path,version:$v_version,sha256:$v_sha},
         {name:"zipperposition",path:$z_path,version:$z_version,
          sha256:$z_sha}]}' >"$expdir/envelope.json"
  chmod 0444 "$expdir/envelope.json"
  jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg event start --arg input_sha "$input_sha" \
    '{time:$time,event:$event,input_inventory_sha256:$input_sha}' \
    >"$expdir/invocations.jsonl"
  printf '%s\n' initialized >"$state/.initialized"
}

run_p_theory_once() {
  local exp=$1 variant=$2 slot=$3 theory=$4
  local state="$STATE_BASE/$exp/theory-$theory"
  local log="$EVAL/$exp/worker-slot-$slot.log"
  local status script
  mkdir -p "$state"
  stamp "$exp slot=$slot theory=$theory start" >>"$log"
  if timeout --signal=TERM --kill-after=120s "$THEORY_CHUNK" \
      env HOLDIR="$ROOT" HOL4_HAMMER_DIR="$state" \
        HOL4_HAMMER_EVAL_DIR="$EVAL" \
        HOL4_HAMMER_EVAL_SAMPLE="$SAMPLE" \
        HOL4_EPROVER_EXECUTABLE="$E_PATH" \
        HOL4_VAMPIRE_EXECUTABLE="$V_PATH" \
        HOL4_ZIPPERPOSITION_EXECUTABLE="$Z_PATH" \
        HHEVAL_EXPNAME="$exp" HHEVAL_VARIANT="$variant" \
        HHEVAL_MODE=theory HHEVAL_NCORE=1 HHEVAL_THEORY="$theory" \
        "$ROOT/bin/hol" <"$DRIVER" >>"$log" 2>&1; then
    status=0
  else
    status=$?
  fi
  while IFS= read -r script; do
    mv "$script" "$EVAL/$exp/scripts/$theory.generated"
  done < <(find "$ROOT/src" -type f \
    -name ".hheval_${exp}_${theory}.sml" -print)
  ((status == 0)) || return "$status"
  stamp "$exp slot=$slot theory=$theory done" >>"$log"
}

run_p_theory() {
  local exp=$1 variant=$2 slot=$3 theory=$4 attempt status
  for ((attempt = 1; attempt <= MAX_RECYCLES; attempt++)); do
    if run_p_theory_once "$exp" "$variant" "$slot" "$theory"; then
      return 0
    else
      status=$?
    fi
    if ((status == 124)); then
      stamp "$exp slot=$slot theory=$theory recycle=$attempt" \
        >>"$EVAL/$exp/worker-slot-$slot.log"
    else
      return "$status"
    fi
  done
  stamp "$exp theory=$theory exceeded bounded recycle limit" >&2
  return 1
}

export -f stamp run_p_theory_once run_p_theory
export ROOT EVAL DRIVER STATE_BASE SAMPLE THEORY_CHUNK MAX_RECYCLES
export E_PATH V_PATH Z_PATH

consolidate_header() {
  local exp=$1 variant=$2 temporary
  temporary="$EVAL/$exp/run.json.tmp"
  jq --slurpfile frozen "$FROZEN" '
    .corpus = $frozen[0].corpus |
    .added_from_dat = $frozen[0].added_from_dat
  ' "$EVAL/$exp/run.json" >"$temporary"
  mv "$temporary" "$EVAL/$exp/run.json"
  jq -e --arg commit "$CURRENT_COMMIT" --arg variant "$variant" '
    .hol_commit == $commit and .sample == 500 and
    (.corpus | length) == 253 and
    ([.corpus[].theorem_count] | add) == 24721 and
    (if $variant == "f30" then
       (.conditions | length) == 8 and
       all(.conditions[]; .engine == "prover" and .timeout == 30)
     else
       (.conditions | length) == 1 and
       .conditions[0].engine == "sched" and
       .conditions[0].selector == "perslice" and
       .conditions[0].slices == 24 and
       .conditions[0].cores == 24 and
       .conditions[0].timeout == 30
     end)
  ' "$EVAL/$exp/run.json" >/dev/null
}

run_p_report() {
  local exp=$1 variant=$2 state
  state="$STATE_BASE/$exp/report"
  mkdir -p "$state"
  env HOLDIR="$ROOT" HOL4_HAMMER_DIR="$state" \
    HOL4_HAMMER_EVAL_DIR="$EVAL" \
    HOL4_HAMMER_EVAL_SAMPLE="$SAMPLE" \
    HOL4_EPROVER_EXECUTABLE="$E_PATH" \
    HOL4_VAMPIRE_EXECUTABLE="$V_PATH" \
    HOL4_ZIPPERPOSITION_EXECUTABLE="$Z_PATH" \
    HHEVAL_EXPNAME="$exp" HHEVAL_VARIANT="$variant" \
    HHEVAL_MODE=report "$ROOT/bin/hol" <"$DRIVER" \
    >>"$EVAL/$exp/report.log" 2>&1
}

verify_p_cells() {
  local exp=$1 variant=$2 expected=$3 rows
  rows=$(find "$EVAL/$exp/journal" -type f -name '*.jsonl' -print0 |
    xargs -0 cat | jq -s 'length')
  [[ "$rows" == "$expected" ]]
  find "$EVAL/$exp/journal" -type f -name '*.jsonl' -print0 |
    xargs -0 cat | jq -s -e --arg variant "$variant" '
      all(.[]; (.fresh | type) == "boolean" and .timeout == 30 and
        (.error == null or
          (.szs == "Theorem" and .recon_ok == false)) and
        (if $variant == "f30" then
           .engine == "prover" and
           (.selector | test("^(knn|mepo|mash|mesh)[0-9]+$"))
         else
           .engine == "sched" and .selector == "perslice" and
           (.slices | length) > 0 and (.slices | length) <= 24 and
           all(.slices[];
             .szs != "RunFailure" and .szs != "LoadFailure" and
             .szs != "Error")
         end))
    ' >/dev/null
  [[ "$(jq '.conditions[0].metrics.goals' \
    "$EVAL/$exp/summary.json")" == "$EXPECTED_SAMPLE_GOALS" ]]
}

copyback_p() {
  local exp=$1 variant=$2 state expdir partial certificate
  local start elapsed source_tree durable_tree journal_sha run_sha input_sha
  state="$STATE_BASE/$exp"
  expdir="$EVAL/$exp"
  partial="$expdir/artifacts/tmpfs-state.partial.$$"
  certificate="$expdir/.stages/copyback.json.partial.$$"
  [[ -d "$state" && ! -L "$state" ]]
  [[ ! -e "$expdir/artifacts/tmpfs-state" ]]
  [[ ! -e "$expdir/.stages/copyback.json" ]]
  [[ ! -e "$partial" && ! -e "$certificate" ]]
  start=$(date +%s%N)
  mkdir -p "$expdir/artifacts" "$expdir/.stages"
  cp -a "$state" "$partial"
  source_tree=$(hh_task10_tree_digest "$state")
  durable_tree=$(hh_task10_tree_digest "$partial")
  [[ "$source_tree" == "$durable_tree" ]]
  elapsed=$((($(date +%s%N) - start) / 1000000))
  journal_sha=$(journal_digest "$expdir/journal")
  run_sha=$(sha256_of "$expdir/run.json")
  input_sha=$(sha256_of "$INPUTS/SHA256SUMS")
  jq -n --arg exp "$exp" --arg variant "$variant" \
    --arg input "$input_sha" --arg run "$run_sha" \
    --arg journal "$journal_sha" --arg source "$source_tree" \
    --arg durable "$durable_tree" --argjson elapsed "$elapsed" '
      {schema:"hh-task10-p-copyback-v1",experiment:$exp,variant:$variant,
       input_inventory_sha256:$input,run_header_sha256:$run,
       journal_sha256:$journal,source_tree_sha256:$source,
       durable_tree_sha256:$durable,copyback_milliseconds:$elapsed}
    ' >"$certificate"
  mv "$partial" "$expdir/artifacts/tmpfs-state"
  mv "$certificate" "$expdir/.stages/copyback.json"
}

validate_copyback_p() {
  local exp=$1 variant=$2 state expdir certificate durable_tree
  local journal_sha run_sha input_sha source_tree
  state="$STATE_BASE/$exp"
  expdir="$EVAL/$exp"
  certificate="$expdir/.stages/copyback.json"
  [[ -s "$certificate" ]]
  [[ -d "$expdir/artifacts/tmpfs-state" ]]
  durable_tree=$(hh_task10_tree_digest "$expdir/artifacts/tmpfs-state")
  journal_sha=$(journal_digest "$expdir/journal")
  run_sha=$(sha256_of "$expdir/run.json")
  input_sha=$(sha256_of "$INPUTS/SHA256SUMS")
  jq -e --arg exp "$exp" --arg variant "$variant" \
    --arg input "$input_sha" --arg run "$run_sha" \
    --arg journal "$journal_sha" --arg durable "$durable_tree" '
      .schema == "hh-task10-p-copyback-v1" and
      .experiment == $exp and .variant == $variant and
      .input_inventory_sha256 == $input and .run_header_sha256 == $run and
      .journal_sha256 == $journal and
      .source_tree_sha256 == $durable and
      .durable_tree_sha256 == $durable
    ' "$certificate" >/dev/null
  if [[ -e "$state" ]]; then
    source_tree=$(hh_task10_tree_digest "$state")
    [[ "$source_tree" == "$durable_tree" ]]
  fi
}

fold_volume_p() {
  local exp=$1 variant=$2 expdir temporary stage
  local copyback_sha tool_sha input_sha result_sha inventory_sha volume_sha
  expdir="$EVAL/$exp"
  temporary="$expdir/.export-volume.partial.$$"
  [[ ! -e "$expdir/export-volume" && ! -e "$temporary" ]]
  validate_copyback_p "$exp" "$variant"
  mkdir "$temporary"
  "$VOLUME_FOLD_TOOL" "$variant" \
    "$expdir/artifacts/tmpfs-state" \
    "$temporary/inventory.tsv" "$temporary/volume.tsv" \
    "$temporary/result.json"
  copyback_sha=$(sha256_of "$expdir/.stages/copyback.json")
  tool_sha=$(sha256_of "$VOLUME_FOLD_TOOL")
  input_sha=$(sha256_of "$INPUTS/SHA256SUMS")
  result_sha=$(sha256_of "$temporary/result.json")
  inventory_sha=$(sha256_of "$temporary/inventory.tsv")
  volume_sha=$(sha256_of "$temporary/volume.tsv")
  stage="$temporary/stage.json"
  jq -n --arg exp "$exp" --arg variant "$variant" \
    --arg input "$input_sha" --arg copyback "$copyback_sha" \
    --arg tool "$tool_sha" --arg result "$result_sha" \
    --arg inventory "$inventory_sha" --arg volume "$volume_sha" '
      {schema:"hh-task10-p-volume-stage-v1",experiment:$exp,
       variant:$variant,input_inventory_sha256:$input,
       copyback_certificate_sha256:$copyback,fold_tool_sha256:$tool,
       result_sha256:$result,inventory_sha256:$inventory,
       volume_sha256:$volume}
    ' >"$stage"
  mv "$temporary" "$expdir/export-volume"
}

validate_volume_p() {
  local exp=$1 variant=$2 expdir directory expected
  local input_sha copyback_sha tool_sha result_sha inventory_sha volume_sha
  expdir="$EVAL/$exp"
  directory="$expdir/export-volume"
  validate_copyback_p "$exp" "$variant"
  [[ -d "$directory" && ! -L "$directory" ]]
  [[ "$(find "$directory" -mindepth 1 -maxdepth 1 -type f | wc -l)" == 4 ]]
  for file in stage.json result.json inventory.tsv volume.tsv; do
    [[ -s "$directory/$file" ]]
  done
  input_sha=$(sha256_of "$INPUTS/SHA256SUMS")
  copyback_sha=$(sha256_of "$expdir/.stages/copyback.json")
  tool_sha=$(sha256_of "$VOLUME_FOLD_TOOL")
  result_sha=$(sha256_of "$directory/result.json")
  inventory_sha=$(sha256_of "$directory/inventory.tsv")
  volume_sha=$(sha256_of "$directory/volume.tsv")
  jq -e --arg exp "$exp" --arg variant "$variant" \
    --arg input "$input_sha" --arg copyback "$copyback_sha" \
    --arg tool "$tool_sha" --arg result "$result_sha" \
    --arg inventory "$inventory_sha" --arg volume "$volume_sha" '
      .schema == "hh-task10-p-volume-stage-v1" and
      .experiment == $exp and .variant == $variant and
      .input_inventory_sha256 == $input and
      .copyback_certificate_sha256 == $copyback and
      .fold_tool_sha256 == $tool and .result_sha256 == $result and
      .inventory_sha256 == $inventory and .volume_sha256 == $volume
    ' "$directory/stage.json" >/dev/null
  case "$variant" in f30) expected=384 ;; s30v5) expected=792 ;;
    *) return 2 ;;
  esac
  jq -e --arg variant "$variant" --argjson expected "$expected" '
    .schema == "hh-task10-export-volume-v1" and
    .variant == $variant and .export_files == $expected and
    ([.filters[].count] | add) == $expected
  ' "$directory/result.json" >/dev/null
}

validate_stage_layout() {
  local exp=$1 expdir state artifacts copyback volume result cleanup
  expdir="$EVAL/$exp"
  state="$STATE_BASE/$exp"
  artifacts="$expdir/artifacts/tmpfs-state"
  copyback="$expdir/.stages/copyback.json"
  volume="$expdir/export-volume"
  result="$expdir/result.json"
  cleanup="$expdir/tmpfs-cleanup.json"
  [[ -z "$(find "$expdir" -maxdepth 3 -name '*.partial.*' -print -quit)" ]]
  if [[ -e "$artifacts" ]]; then
    [[ -e "$copyback" ]]
  else
    [[ ! -e "$copyback" ]]
  fi
  [[ ! -e "$volume" || -e "$copyback" ]]
  [[ ! -e "$result" || -e "$volume" ]]
  [[ ! -e "$cleanup" || (-e "$result" && ! -e "$state") ]]
}

emit_p_result() {
  local exp=$1 variant=$2 expected=$3 elapsed=$4 expdir temporary
  local journal_sha copyback_sha volume_sha summary_sha run_sha input_sha
  expdir="$EVAL/$exp"
  temporary="$expdir/result.json.partial.$$"
  [[ ! -e "$expdir/result.json" && ! -e "$temporary" ]]
  verify_p_cells "$exp" "$variant" "$expected"
  validate_copyback_p "$exp" "$variant"
  validate_volume_p "$exp" "$variant"
  journal_sha=$(journal_digest "$expdir/journal")
  copyback_sha=$(sha256_of "$expdir/.stages/copyback.json")
  volume_sha=$(sha256_of "$expdir/export-volume/result.json")
  summary_sha=$(sha256_of "$expdir/summary.json")
  run_sha=$(sha256_of "$expdir/run.json")
  input_sha=$(sha256_of "$INPUTS/SHA256SUMS")
  jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg exp "$exp" --arg variant "$variant" --arg input "$input_sha" \
    --arg journal "$journal_sha" --arg copyback "$copyback_sha" \
    --arg volume "$volume_sha" --arg summary "$summary_sha" \
    --arg run "$run_sha" --argjson elapsed "$elapsed" '
      {schema:"hh-task10-p-result-v2",status:"complete",
       completed:$completed,experiment:$exp,variant:$variant,
       elapsed_seconds:$elapsed,input_inventory_sha256:$input,
       run_header_sha256:$run,journal_sha256:$journal,
       summary_sha256:$summary,copyback_certificate_sha256:$copyback,
       export_volume_result_sha256:$volume}
    ' >"$temporary"
  mv "$temporary" "$expdir/result.json"
}

validate_p_result() {
  local exp=$1 variant=$2 expected=$3 expdir
  local input_sha run_sha journal_sha summary_sha copyback_sha volume_sha
  expdir="$EVAL/$exp"
  verify_p_cells "$exp" "$variant" "$expected"
  validate_copyback_p "$exp" "$variant"
  validate_volume_p "$exp" "$variant"
  input_sha=$(sha256_of "$INPUTS/SHA256SUMS")
  run_sha=$(sha256_of "$expdir/run.json")
  journal_sha=$(journal_digest "$expdir/journal")
  summary_sha=$(sha256_of "$expdir/summary.json")
  copyback_sha=$(sha256_of "$expdir/.stages/copyback.json")
  volume_sha=$(sha256_of "$expdir/export-volume/result.json")
  jq -e --arg exp "$exp" --arg variant "$variant" \
    --arg input "$input_sha" --arg run "$run_sha" \
    --arg journal "$journal_sha" --arg summary "$summary_sha" \
    --arg copyback "$copyback_sha" --arg volume "$volume_sha" '
      .schema == "hh-task10-p-result-v2" and .status == "complete" and
      .experiment == $exp and .variant == $variant and
      .input_inventory_sha256 == $input and .run_header_sha256 == $run and
      .journal_sha256 == $journal and .summary_sha256 == $summary and
      .copyback_certificate_sha256 == $copyback and
      .export_volume_result_sha256 == $volume
    ' "$expdir/result.json" >/dev/null
}

cleanup_p() {
  local exp=$1 variant=$2 expected=$3 state expdir
  local result_sha source_tree durable_tree
  state="$STATE_BASE/$exp"
  expdir="$EVAL/$exp"
  validate_p_result "$exp" "$variant" "$expected"
  result_sha=$(sha256_of "$expdir/result.json")
  source_tree=$(hh_task10_tree_digest "$state")
  durable_tree=$(hh_task10_tree_digest "$expdir/artifacts/tmpfs-state")
  [[ "$source_tree" == "$durable_tree" ]]
  hh_task10_cleanup_tmpfs "$state" "$expdir/tmpfs-cleanup.json" \
    "$result_sha"
  [[ ! -e "$state" ]]
}

run_p_experiment() {
  local exp=$1 variant=$2 slots=$3 expected=$4 started ended rows
  local state expdir result_sha
  state="$STATE_BASE/$exp"
  expdir="$EVAL/$exp"
  if [[ -s "$expdir/result.json" && ! -e "$state" ]]; then
    validate_stage_layout "$exp"
    validate_p_result "$exp" "$variant" "$expected"
    result_sha=$(sha256_of "$expdir/result.json")
    jq -e --arg result "$result_sha" '
      .schema == "hh-task10-tmpfs-cleanup-v1" and
      .status == "removed" and .durable_binding_sha256 == $result and
      .tmpfs_root_absent_after_cleanup == true' \
      "$expdir/tmpfs-cleanup.json" >/dev/null
    jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      --arg event resume --arg result_sha "$result_sha" \
      '{time:$time,event:$event,result_sha256:$result_sha,
        durable_only:true}' >>"$expdir/invocations.jsonl"
    stamp "$exp durable-only resume complete"
    return
  fi
  initialize_p "$exp" "$variant" "$slots"
  validate_stage_layout "$exp"
  started=$(date +%s)
  if [[ ! -e "$expdir/.stages/copyback.json" ]]; then
    [[ ! -e "$expdir/export-volume" && ! -e "$expdir/result.json" ]]
    rows=$(find "$expdir/journal" -type f -name '*.jsonl' -print0 |
      xargs -0 -r cat | jq -s length)
    if [[ "$rows" != "$expected" ]]; then
      [[ ! -e "$expdir/summary.json" ]]
      sample_theories | nl -v 0 -w 1 -s ' ' |
        xargs -n 2 -P "$slots" bash -Eeuo pipefail -c '
          slot=$(($4 % $3)); run_p_theory "$1" "$2" "$slot" "$5"
        ' p-worker "$exp" "$variant" "$slots"
    fi
    if [[ ! -e "$expdir/summary.json" ]]; then
      run_p_report "$exp" "$variant"
    fi
    verify_p_cells "$exp" "$variant" "$expected"
    copyback_p "$exp" "$variant"
  fi
  validate_copyback_p "$exp" "$variant"
  if [[ ! -e "$expdir/export-volume" ]]; then
    fold_volume_p "$exp" "$variant"
  fi
  validate_volume_p "$exp" "$variant"
  ended=$(date +%s)
  if [[ ! -e "$expdir/result.json" ]]; then
    emit_p_result "$exp" "$variant" "$expected" "$((ended - started))"
  fi
  validate_p_result "$exp" "$variant" "$expected"
  cleanup_p "$exp" "$variant" "$expected"
  jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg event complete --arg result_sha \
      "$(sha256_of "$EVAL/$exp/result.json")" \
    '{time:$time,event:$event,result_sha256:$result_sha}' \
    >>"$EVAL/$exp/invocations.jsonl"
  stamp "$exp complete elapsed=$((ended - started))s"
}

stage_selftest_fresh() {
  local variant=$1 exp=$2
  validate_stage_layout "$exp"
  copyback_p "$exp" "$variant"
  validate_copyback_p "$exp" "$variant"
  fold_volume_p "$exp" "$variant"
  validate_volume_p "$exp" "$variant"
}

stage_selftest_validate() {
  local variant=$1 exp=$2
  validate_stage_layout "$exp"
  validate_copyback_p "$exp" "$variant"
  validate_volume_p "$exp" "$variant"
}

run_schedule_probe() {
  local directory="$EVAL/$P_PROBES"
  mkdir -p "$directory"
  env HOLDIR="$ROOT" HOL4_HAMMER_DIR="$STATE_BASE/$P_PROBES/schedule" \
    HHEVAL_SCHEDULE_OUTPUT="$directory/schedule.tsv" \
    "$ROOT/bin/hol" <"$SCHEDULE_DRIVER" >"$directory/schedule.log" 2>&1
  [[ "$(wc -l <"$directory/schedule.tsv")" == 24 ]]
  awk -F '\t' '$1 != NR || $9 != 30.0 {exit 1}' \
    "$directory/schedule.tsv"
}

current_theory_directory() {
  local theory=$1 ui directory
  ui=$(find "$ROOT/src" -type f \
    -path "*/.hol/objs/${theory}Theory.ui" -print -quit)
  if [[ -z "$ui" ]]; then
    ui=$(readlink -f "$ROOT/sigobj/${theory}Theory.ui" 2>/dev/null || true)
  fi
  [[ -n "$ui" ]]
  directory=$(dirname "$(dirname "$(dirname "$ui")")")
  printf '%s\n' "$directory"
}

run_timing_probes() {
  local directory="$EVAL/$P_PROBES" theory theory_dir
  local state="$STATE_BASE/$P_PROBES/timing"
  mkdir -p "$directory/timing" "$directory/log" "$state"
  while IFS= read -r theory; do
    if [[ -s "$directory/timing/$theory.tsv" ]]; then
      continue
    fi
    theory_dir=$(current_theory_directory "$theory")
    timeout --signal=TERM --kill-after=120s 10m \
      env HOLDIR="$ROOT" HOL4_HAMMER_DIR="$state/$theory" \
        HHEVAL_THEORY="$theory" HHEVAL_THEORY_DIR="$theory_dir" \
        HHEVAL_PROBE_OUTPUT="$directory/timing/$theory.tsv.partial" \
        "$ROOT/bin/hol" repl -b "$ROOT/bin/hol.state" <"$PROBE" \
        >"$directory/log/$theory.log" 2>&1
    mv "$directory/timing/$theory.tsv.partial" \
      "$directory/timing/$theory.tsv"
  done < <(sample_theories)
  cat "$directory"/timing/*.tsv >"$directory/timing.tsv"
  [[ "$(awk -F '\t' '$1 == "rank" {n++} END {print n+0}' \
    "$directory/timing.tsv")" == 192 ]]
  [[ "$(awk -F '\t' '$1 == "context" {n++} END {print n+0}' \
    "$directory/timing.tsv")" == "$EXPECTED_SAMPLE_THEORIES" ]]
  [[ "$(awk -F '\t' '$1 == "cleanup" {n++} END {print n+0}' \
    "$directory/timing.tsv")" == "$EXPECTED_SAMPLE_THEORIES" ]]
}

run_p() {
  verify_existing_outputs_readonly
  verify_common
  [[ "$(sample_theories | wc -l)" == "$EXPECTED_SAMPLE_THEORIES" ]]
  [[ "$(find "$SAMPLE_SOURCE" -type f -name '*.jsonl' -print0 |
    xargs -0 cat | jq -s 'length')" == "$EXPECTED_SAMPLE_GOALS" ]]
  run_p_experiment "$P_F30" f30 24 384
  run_p_experiment "$P_S30" s30v5 1 48
  initialize_probes
  run_schedule_probe
  run_timing_probes
  finalize_probes
}

initialize_probes() {
  local directory="$EVAL/$P_PROBES" state="$STATE_BASE/$P_PROBES"
  [[ ! -e "$directory" ]]
  [[ ! -e "$state" ]]
  mkdir -p "$directory" "$state"
  jq -n --arg started "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg commit "$CURRENT_COMMIT" --arg diff "$CURRENT_DIFF" \
    --arg input "$(sha256_of "$INPUTS/SHA256SUMS")" \
    --arg sources "$LOADED_SOURCES_SHA" --arg objects "$LOADED_OBJECTS_SHA" \
    --arg f30 "$(sha256_of "$EVAL/$P_F30/result.json")" \
    --arg s30 "$(sha256_of "$EVAL/$P_S30/result.json")" '
      {schema:"hh-task10-p-probes-v2",status:"scheduled",started:$started,
       hol_commit:$commit,tracked_source_patch_sha256:$diff,
       input_inventory_sha256:$input,
       loaded_sources_inventory_sha256:$sources,
       loaded_objects_inventory_sha256:$objects,
       prerequisite_results:{f30_sha256:$f30,s30v5_sha256:$s30},
       sample:500,initial_cache_files:0,
       envelope:{cpu_quota_cores:32,memory_high_bytes:133143986176,
         memory_max_bytes:137438953472,memory_swap_max_bytes:0,
         atomic_timeout_seconds:600,tmpfs_scratch:true,
         durable_copyback:true},
       expected:{sample_theories:33,sample_goals:48,ranking_rows:192,
         context_rows:33,cleanup_rows:33,schedule_rows:24}}
    ' >"$directory/envelope.json"
  chmod 0444 "$directory/envelope.json"
  jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg envelope "$(sha256_of "$directory/envelope.json")" \
    '{time:$time,event:"start",envelope_sha256:$envelope}' \
    >"$directory/invocations.jsonl"
}

finalize_probes() {
  local directory="$EVAL/$P_PROBES" state="$STATE_BASE/$P_PROBES"
  local peak result_sha source_tree durable_tree
  peak=$(cat /sys/fs/cgroup$(awk -F: '$1 == "0" {print $3}' \
    /proc/self/cgroup)/memory.peak)
  "$INPUTS/phase3-task10-fold-probes.sh" "$directory" "$peak" "$ROOT"
  result_sha=$(sha256_of "$directory/result.json")
  mkdir -p "$directory/artifacts"
  cp -a "$state" "$directory/artifacts/tmpfs-state"
  source_tree=$(hh_task10_tree_digest "$state")
  durable_tree=$(hh_task10_tree_digest "$directory/artifacts/tmpfs-state")
  [[ "$source_tree" == "$durable_tree" ]]
  hh_task10_cleanup_tmpfs "$state" "$directory/tmpfs-cleanup.json" \
    "$result_sha"
  [[ ! -e "$state" ]]
  jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg result "$result_sha" \
    '{time:$time,event:"complete",result_sha256:$result}' \
    >>"$directory/invocations.jsonl"
}

run_probes() {
  verify_existing_outputs_readonly
  verify_common
  if [[ -s "$EVAL/$P_PROBES/result.json" &&
        ! -e "$STATE_BASE/$P_PROBES" ]]; then
    result_sha=$(sha256_of "$EVAL/$P_PROBES/result.json")
    jq -e --arg result "$result_sha" '
      .schema == "hh-task10-tmpfs-cleanup-v1" and
      .status == "removed" and .durable_binding_sha256 == $result and
      .tmpfs_root_absent_after_cleanup == true' \
      "$EVAL/$P_PROBES/tmpfs-cleanup.json" >/dev/null
    jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
      --arg result "$result_sha" \
      '{time:$time,event:"resume",result_sha256:$result,durable_only:true}' \
      >>"$EVAL/$P_PROBES/invocations.jsonl"
    stamp "$P_PROBES durable-only resume complete"
    return
  fi
  initialize_probes
  run_schedule_probe
  run_timing_probes
  finalize_probes
}

case "${1-}" in
  P) run_p ;;
  PROBES) run_probes ;;
  STAGE_FRESH) stage_selftest_fresh "${2:?variant}" "${3:?experiment}" ;;
  STAGE_VALIDATE) stage_selftest_validate \
    "${2:?variant}" "${3:?experiment}" ;;
  *) printf 'usage: %s P|PROBES|STAGE_FRESH|STAGE_VALIDATE\n' "$0" >&2
     exit 2 ;;
esac
