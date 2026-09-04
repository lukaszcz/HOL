#!/usr/bin/env bash
set -Eeuo pipefail

ROOT=${HHEVAL_TASK11_ROOT:-$(git rev-parse --show-toplevel)}
EVIDENCE=${HHEVAL_TASK11_EVIDENCE_ROOT:-$ROOT/.task11-evidence}
INPUTS=${HHEVAL_TASK11_INPUTS:?sealed TASK11 inputs are required}
EXP=${HHEVAL_TASK11_EXPERIMENT:-phase3-task11-f30-v1}
RUN="$EVIDENCE/runs/$EXP"
DEFAULT_STATE_BASE=/run/user/$(id -u)/holyhammer-phase3-task11
STATE_BASE=${HHEVAL_TASK11_STATE_BASE:-$DEFAULT_STATE_BASE}
STATE="$STATE_BASE/$EXP"
PROVENANCE="$INPUTS/top-provenance.json"
DRIVER="$INPUTS/task11-driver.sml"
CHUNK_GOALS=8
SLOTS=32
RECYCLE=600
INPUT_SHA=$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)
E_PATH=$(awk -F '\t' '$1 == "e" {print $2}' "$INPUTS/provers.tsv")
V_PATH=$(awk -F '\t' '$1 == "vampire" {print $2}' "$INPUTS/provers.tsv")

stamp() {
  printf '%s %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*"
}

tree_digest() {
  local directory=$1
  (cd "$directory" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
}

verify_existing_tuple() {
  if [[ -e "$RUN" || -e "$STATE" ]]; then
    if [[ ! -s "$RUN/envelope.json" ]] ||
       [[ "$(jq -r '.input_inventory_sha256' "$RUN/envelope.json")" != \
          "$INPUT_SHA" ]]; then
      echo "TASK11 tuple mismatch: existing output has another input seal" >&2
      exit 78
    fi
  fi
}

verify_atom() {
  local atom=$1 certificate artifact journal tree journal_sha
  local expected theory part parts theory_dir
  certificate="$RUN/atom-certificates/$atom.json"
  artifact="$RUN/artifacts/atoms/$atom"
  journal="$RUN/journal/$atom.jsonl"
  [[ -s "$certificate" && -d "$artifact" && -f "$journal" ]]
  tree=$(tree_digest "$artifact")
  journal_sha=$(sha256sum "$journal" | cut -d' ' -f1)
  expected=$(awk -F '\t' -v atom="$atom" '$1 == atom {print}' \
    "$RUN/atoms.tsv")
  IFS=$'\t' read -r _ theory part parts theory_dir <<<"$expected"
  jq -e --arg atom "$atom" --arg input "$INPUT_SHA" \
    --arg tree "$tree" --arg journal "$journal_sha" \
    --arg theory "$theory" --argjson part "$part" \
    --argjson parts "$parts" --arg theory_dir "$theory_dir" '
      .schema == "hh-task11-f30-atom-v1" and .status == "complete" and
      .atom == $atom and .input_inventory_sha256 == $input and
      .theory == $theory and .part == $part and .parts == $parts and
      .theory_directory == $theory_dir and
      .artifact_tree_sha256 == $tree and .journal_sha256 == $journal and
      .tmpfs_removed == true
    ' "$certificate" >/dev/null
}

verify_pending_atom() {
  local atom=$1 expected certificate artifact tree journal journal_sha
  certificate="$RUN/pending/$atom.json"
  artifact="$RUN/artifacts/atoms/$atom"
  journal="$artifact/experiment/journal/$(awk -F '\t' -v atom="$atom" \
    '$1 == atom {print $2 ".part-" $3 "-of-" $4 ".jsonl"}' \
    "$RUN/atoms.tsv")"
  [[ -s "$certificate" && -d "$artifact" && -f "$journal" ]]
  tree=$(tree_digest "$artifact")
  journal_sha=$(sha256sum "$journal" | cut -d' ' -f1)
  jq -e --arg atom "$atom" --arg input "$INPUT_SHA" \
    --arg tree "$tree" --arg journal "$journal_sha" '
    .schema == "hh-task11-f30-pending-v1" and .atom == $atom and
    .input_inventory_sha256 == $input and
    .artifact_tree_sha256 == $tree and .journal_sha256 == $journal
  ' "$certificate" >/dev/null
}

preflight_resume() {
  local atom relative expected_dir expected theory count parts part
  expected=$(mktemp)
  if ! (jq -r '.corpus[] | select(.theorem_count > 0) |
      [.thy,.theorem_count] | @tsv' "$RUN/run.json" |
      while IFS=$'\t' read -r theory count; do
        relative=$(awk -F '\t' -v theory="$theory" \
          '$1 == theory {print $2}' "$INPUTS/theory-directories.tsv")
        [[ -n "$relative" ]]
        parts=$(((count + CHUNK_GOALS - 1) / CHUNK_GOALS))
        for ((part = 0; part < parts; part++)); do
          printf '%s\t%s\t%s\t%s\t%s\n' \
            "$theory-$part-of-$parts" "$theory" "$part" "$parts" \
            "$ROOT/$relative"
        done
      done >"$expected"); then
    rm -f "$expected"
    return 1
  fi
  if ! cmp "$expected" "$RUN/atoms.tsv"; then
    rm -f "$expected"
    echo "TASK11 atom plan differs from the sealed corpus" >&2
    return 1
  fi
  rm -f "$expected"
  [[ "$(wc -l <"$RUN/atoms.tsv")" == 3212 ]]
  [[ "$(cut -f1 "$RUN/atoms.tsv" | sort -u | wc -l)" == 3212 ]]
  [[ -z "$(find "$RUN" -name '*.partial*' -print -quit)" ]]
  while IFS=$'\t' read -r atom theory part parts theory_dir extra; do
    [[ -z "${extra-}" && "$atom" == "$theory-$part-of-$parts" ]]
    [[ "$part" =~ ^[0-9]+$ && "$parts" =~ ^[1-9][0-9]*$ ]]
    ((part < parts))
    relative=$(awk -F '\t' -v theory="$theory" \
      '$1 == theory {print $2}' "$INPUTS/theory-directories.tsv")
    expected_dir="$ROOT/$relative"
    [[ -n "$relative" && "$theory_dir" == "$expected_dir" ]]
    if [[ -s "$RUN/atom-certificates/$atom.json" ]]; then
      [[ ! -e "$RUN/pending/$atom.json" ]]
      verify_atom "$atom"
    elif [[ -d "$RUN/artifacts/atoms/$atom" ]]; then
      verify_pending_atom "$atom"
    fi
  done <"$RUN/atoms.tsv"
  for path in "$RUN"/atom-certificates/*.json \
      "$RUN"/pending/*.json "$RUN"/artifacts/atoms/*; do
    [[ ! -e "$path" ]] && continue
    atom=$(basename "$path" .json)
    awk -F '\t' -v atom="$atom" '$1 == atom {found=1} END {exit !found}' \
      "$RUN/atoms.tsv"
  done
}

run_atom() {
  local atom=$1 theory=$2 part=$3 parts=$4 theory_dir=$5
  local atom_state work journal_name checkpoint attempts_file log
  local artifact partial tree journal_sha rows attempt status
  if [[ -s "$RUN/atom-certificates/$atom.json" ]]; then
    verify_atom "$atom"
    return
  fi
  atom_state="$STATE/atoms/$atom"
  work="$atom_state/experiment"
  journal_name="$theory.part-$part-of-$parts.jsonl"
  checkpoint="$RUN/checkpoints/$atom.jsonl"
  attempts_file="$RUN/checkpoints/$atom.attempts"
  log="$RUN/log/$atom.log"
  artifact="$RUN/artifacts/atoms/$atom"
  if [[ ! -e "$artifact" ]]; then
    rm -f "$RUN/pending/$atom.json"
    mkdir -p "$work/journal" "$work/out" "$work/pb"
    if [[ -f "$checkpoint" && ! -e "$work/journal/$journal_name" ]]; then
      cp "$checkpoint" "$work/journal/$journal_name"
    fi
    touch "$work/journal/$journal_name"
    attempt=$(cat "$attempts_file" 2>/dev/null || printf '0')
    while true; do
      attempt=$((attempt + 1))
      printf '%s\n' "$attempt" >"$attempts_file.partial"
      mv "$attempts_file.partial" "$attempts_file"
      stamp "$atom attempt=$attempt start" >>"$log"
      if timeout --signal=TERM --kill-after=120s "${RECYCLE}s" \
            env HOLDIR="$ROOT" HOL4_HAMMER_DIR="$atom_state/hammer" \
              HOL4_EPROVER_EXECUTABLE="$E_PATH" \
              HOL4_VAMPIRE_EXECUTABLE="$V_PATH" \
              HHEVAL_EXPDIR="$work" HHEVAL_THEORY="$theory" \
              HHEVAL_THEORY_DIR="$theory_dir" \
              HHEVAL_PART="$part" HHEVAL_PARTS="$parts" \
              HHEVAL_GOAL_INVENTORY="$INPUTS/canonical-goals.tsv" \
              "$ROOT/bin/hol" repl -b "$ROOT/bin/hol.state" \
              <"$DRIVER" >>"$log" 2>&1; then
        status=0
      else
        status=$?
      fi
      cp "$work/journal/$journal_name" "$checkpoint.partial"
      mv "$checkpoint.partial" "$checkpoint"
      stamp "$atom attempt=$attempt status=$status checkpointed" >>"$log"
      if ((status == 0)); then
        break
      elif ((status == 124 || status == 137 || status == 143)); then
        continue
      else
        stamp "$atom failed with non-recycle status $status" >&2
        return "$status"
      fi
    done
    jq -s -e 'all(.[];
        .error == null or (.szs == "Theorem" and .recon_ok == false))' \
      "$work/journal/$journal_name" >/dev/null
    partial="$RUN/artifacts/atoms/$atom.partial.$$"
    [[ ! -e "$partial" ]]
    mkdir -p "$partial/experiment/journal"
    cp "$work/journal/$journal_name" \
      "$partial/experiment/journal/$journal_name"
    tree=$(tree_digest "$partial")
    journal_sha=$(sha256sum \
      "$partial/experiment/journal/$journal_name" | cut -d' ' -f1)
    jq -n --arg atom "$atom" --arg input "$INPUT_SHA" \
      --arg tree "$tree" --arg journal "$journal_sha" '
      {schema:"hh-task11-f30-pending-v1",atom:$atom,
       input_inventory_sha256:$input,artifact_tree_sha256:$tree,
       journal_sha256:$journal}
    ' >"$RUN/pending/$atom.json.partial"
    mv "$RUN/pending/$atom.json.partial" "$RUN/pending/$atom.json"
    mv "$partial" "$artifact"
  else
    verify_pending_atom "$atom"
    tree=$(tree_digest "$artifact")
    attempt=$(cat "$attempts_file" 2>/dev/null || printf '0')
  fi
  cp "$artifact/experiment/journal/$journal_name" \
    "$RUN/journal/$atom.jsonl.partial"
  mv "$RUN/journal/$atom.jsonl.partial" "$RUN/journal/$atom.jsonl"
  journal_sha=$(sha256sum "$RUN/journal/$atom.jsonl" | cut -d' ' -f1)
  rows=$(jq -s length "$RUN/journal/$atom.jsonl")
  chmod -R a-w "$artifact" "$RUN/journal/$atom.jsonl"
  rm -rf "$atom_state"
  rm -f "$checkpoint" "$attempts_file"
  jq -n --arg atom "$atom" --arg theory "$theory" \
    --arg theory_dir "$theory_dir" \
    --arg input "$INPUT_SHA" --arg tree "$tree" \
    --arg journal "$journal_sha" --argjson part "$part" \
    --argjson parts "$parts" --argjson rows "$rows" \
    --argjson attempts "$attempt" '
      {schema:"hh-task11-f30-atom-v1",status:"complete",atom:$atom,
       theory:$theory,part:$part,parts:$parts,
       theory_directory:$theory_dir,
       input_inventory_sha256:$input,attempts:$attempts,cells:$rows,
       artifact_tree_sha256:$tree,journal_sha256:$journal,
       tmpfs_removed:true}
    ' >"$RUN/atom-certificates/$atom.json.partial"
  mv "$RUN/atom-certificates/$atom.json.partial" \
    "$RUN/atom-certificates/$atom.json"
  rm -f "$RUN/pending/$atom.json"
  stamp "$atom complete cells=$rows attempts=$attempt" >>"$log"
}

export -f stamp tree_digest verify_atom verify_pending_atom run_atom
export ROOT RUN STATE INPUT_SHA DRIVER RECYCLE E_PATH V_PATH

initialize() {
  local commit diff initial_cache theory_dir
  [[ ! -e "$STATE" ]]
  if [[ -e "$STATE_BASE" ]]; then
    initial_cache=$(find "$STATE_BASE" -type f | wc -l)
  else
    initial_cache=0
  fi
  [[ "$initial_cache" == 0 ]]
  mkdir -p "$RUN/journal" "$RUN/checkpoints" "$RUN/log"
  mkdir -p "$RUN/atom-certificates" "$RUN/artifacts/atoms" "$RUN/pending"
  mkdir -p "$STATE/atoms"
  commit=$(jq -r '.main.commit' "$PROVENANCE")
  diff=$(jq -r '.main.tracked_diff_sha256' "$PROVENANCE")
  jq --arg exp "$EXP" --arg commit "$commit" --arg date "$(date -u)" '
      .expname = $exp | .hol_commit = $commit | .date = $date |
      .sample = 1 |
      .conditions |= map(.cond_id |= sub("^p-"; ""))
    ' "$INPUTS/corpus-run.json" >"$RUN/run.json"
  chmod 0444 "$RUN/run.json"
  jq -n --arg started "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg input "$INPUT_SHA" --arg commit "$commit" --arg diff "$diff" \
    --arg state "$STATE" \
    --arg run "$(sha256sum "$RUN/run.json" | cut -d' ' -f1)" '
      {schema:"hh-task11-f30-envelope-v1",status:"running",
       started:$started,input_inventory_sha256:$input,
       hol_commit:$commit,tracked_source_patch_sha256:$diff,
       run_header_sha256:$run,state_root:$state,initial_cache_files:0,
       isolated_caches:true,resumable_journals:true,
       envelope:{cpu_quota_cores:32,memory_high_bytes:133143986176,
         memory_max_bytes:137438953472,memory_swap_max_bytes:0,
         worker_recycle_seconds:600,worker_slots:32,
         chunk_target_goals:8,tmpfs_scratch:true,durable_copyback:true}}
    ' >"$RUN/envelope.json"
  chmod 0444 "$RUN/envelope.json"
  jq -r '.corpus[] | select(.theorem_count > 0) |
    [.thy,.theorem_count] | @tsv' "$RUN/run.json" |
    while IFS=$'\t' read -r theory count; do
      theory_dir=$(awk -F '\t' -v theory="$theory" \
        '$1 == theory {print $2}' "$INPUTS/theory-directories.tsv")
      [[ -n "$theory_dir" && -d "$ROOT/$theory_dir" ]]
      parts=$(((count + CHUNK_GOALS - 1) / CHUNK_GOALS))
      for ((part = 0; part < parts; part++)); do
        printf '%s\t%s\t%s\t%s\t%s\n' \
          "$theory-$part-of-$parts" "$theory" "$part" "$parts" \
          "$ROOT/$theory_dir"
      done
    done >"$RUN/atoms.tsv"
  chmod 0444 "$RUN/atoms.tsv"
  jq -nc --arg time "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg input "$INPUT_SHA" \
    '{event:"start",time:$time,input_inventory_sha256:$input}' \
    >"$RUN/invocations.jsonl"
}

finalize() {
  local cgroup relative peak oom
  "$INPUTS/verify-inputs.sh" "$INPUTS" "$ROOT"
  relative=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
  cgroup="/sys/fs/cgroup$relative"
  peak=$(cat "$cgroup/memory.peak")
  [[ "$(cat "$cgroup/memory.swap.peak" 2>/dev/null || printf '0')" == 0 ]]
  oom=$(awk '$1 == "oom_kill" {print $2}' "$cgroup/memory.events")
  rm -rf "$STATE"
  [[ ! -e "$STATE" ]]
  HHEVAL_TASK11_MEMORY_PEAK_HUMAN="$peak bytes" \
  HHEVAL_TASK11_OOM_KILL_EVENTS="$oom" \
    "$INPUTS/certify-result.sh" "$INPUTS" "$RUN" \
      "$INPUTS/canonical-goals.tsv" "$INPUTS/canonical-goals.json"
  stamp "$EXP measurement complete; terminal certification required"
}

run_all() {
  verify_existing_tuple
  if [[ -s "$RUN/final-certificate.json" ]]; then
    if [[ ! -s "$RUN/evidence-compaction.json" ||
          -s "$RUN/evidence-compaction.pending.json" ]]; then
      "$INPUTS/compact-evidence.sh" "$INPUTS" "$RUN"
    else
      "$RUN/verifier/verify-result.sh" "$INPUTS" "$RUN"
    fi
    stamp "$EXP durable-only verification complete"
    return
  fi
  if [[ -s "$RUN/result.json" ]]; then
    stamp "$EXP measurement complete; run CERTIFY_TERMINAL after service exit"
    return
  fi
  "$INPUTS/verify-inputs.sh" "$INPUTS" "$ROOT"
  if [[ ! -e "$RUN" ]]; then
    initialize
  fi
  preflight_resume
  [[ -d "$STATE" ]] || mkdir -p "$STATE/atoms"
  xargs -d '\n' -n 1 -P "$SLOTS" bash -Eeuo pipefail -c '
    IFS=$'"'"'\t'"'"' read -r atom theory part parts theory_dir <<<"$1"
    trap '"'"'exit 255'"'"' ERR
    run_atom "$atom" "$theory" "$part" "$parts" "$theory_dir"
  ' task11-atom <"$RUN/atoms.tsv"
  [[ "$(find "$RUN/atom-certificates" -type f | wc -l)" == \
     "$(wc -l <"$RUN/atoms.tsv")" ]]
  finalize
}

if [[ ${BASH_SOURCE[0]} == "$0" ]]; then
  case "${1-}" in
    RUN) run_all ;;
    VERIFY_INPUTS) "$INPUTS/verify-inputs.sh" "$INPUTS" ;;
    VERIFY_RESULT) "$INPUTS/verify-result.sh" "$INPUTS" "$RUN" ;;
    CERTIFY_TERMINAL)
      "$INPUTS/certify-terminal-run.sh" "$INPUTS" "$RUN" "${2:?service}" ;;
    *)
      echo "usage: $0 RUN|VERIFY_INPUTS|VERIFY_RESULT|CERTIFY_TERMINAL SERVICE" \
        >&2
      exit 2
      ;;
  esac
fi
