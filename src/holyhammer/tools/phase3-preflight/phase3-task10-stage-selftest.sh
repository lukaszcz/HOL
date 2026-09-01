#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 2 || {
  echo "usage: $0 RUNNER SEALED_INPUTS" >&2
  exit 2
}
runner=$1
inputs=$2
test -x "$runner" && test -s "$inputs/SHA256SUMS"
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM
evidence=$work/evidence
states=$work/states
mkdir -p "$evidence/runs" "$states"

tree_digest() {
  local directory=$1
  (cd "$directory" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum | sha256sum | awk '{print $1}')
}

make_file() {
  local file=$1 contents=$2
  mkdir -p "$(dirname "$file")"
  printf '%s' "$contents" > "$file"
}

run_stage() {
  env HHEVAL_TASK10_ROOT="$PWD" HHEVAL_TASK10_EVIDENCE_ROOT="$evidence" \
    HHEVAL_TASK10_INPUTS="$inputs" HHEVAL_TASK10_STATE_BASE="$states" \
    "$runner" "$@"
}

make_fixture() {
  local variant=$1 exp=$2 state="$states/$exp" expdir="$evidence/runs/$exp"
  local filter binding per_theory theory i
  mkdir -p "$state" "$expdir/journal"
  printf '{}\n' > "$expdir/run.json"
  printf '{}\n' > "$expdir/journal/fixture.jsonl"
  case "$variant" in
    f30)
      for filter in knn mepo mash mesh
      do
        for ((i = 0; i < 96; i++))
        do
          make_file \
            "$state/scratch/pb/t$i/g$i-p-f30-e-$filter/atp_in" \
            "$filter-$i"
        done
      done
      ;;
    s30v5)
      for binding in knn:16 mepo:2 mash:2 mesh:4
      do
        filter=${binding%%:*}
        per_theory=${binding#*:}
        for ((theory = 0; theory < 33; theory++))
        do
          for ((i = 0; i < per_theory; i++))
          do
            make_file \
              "$state/theory-t$theory/problems/e.$filter.fof.x.$i/atp_in" \
              "$filter-$theory-$i"
          done
        done
      done
      ;;
    *) return 2 ;;
  esac
}

negative_validate() {
  local variant=$1 exp=$2 label=$3
  if run_stage STAGE_VALIDATE "$variant" "$exp" \
       >"$work/$exp-$label.log" 2>&1
  then
    echo "$label stage corruption unexpectedly passed" >&2
    exit 1
  fi
}

for variant in f30 s30v5
do
  exp=stage-$variant
  expdir=$evidence/runs/$exp
  make_fixture "$variant" "$exp"
  run_stage STAGE_FRESH "$variant" "$exp"
  before=$(tree_digest "$expdir")
  run_stage STAGE_VALIDATE "$variant" "$exp"
  run_stage STAGE_VALIDATE "$variant" "$exp"
  after=$(tree_digest "$expdir")
  test "$before" = "$after"

  cp "$expdir/.stages/copyback.json" "$work/copyback.json"
  printf 'corrupt\n' >> "$expdir/.stages/copyback.json"
  negative_validate "$variant" "$exp" corrupt-copyback
  cp "$work/copyback.json" "$expdir/.stages/copyback.json"
  run_stage STAGE_VALIDATE "$variant" "$exp"

  cp "$expdir/export-volume/inventory.tsv" "$work/inventory.tsv"
  printf 'corrupt\n' >> "$expdir/export-volume/inventory.tsv"
  negative_validate "$variant" "$exp" corrupt-volume
  cp "$work/inventory.tsv" "$expdir/export-volume/inventory.tsv"
  run_stage STAGE_VALIDATE "$variant" "$exp"

  printf 'partial\n' > "$expdir/result.json.partial.dead"
  negative_validate "$variant" "$exp" partial-marker
  rm "$expdir/result.json.partial.dead"
  run_stage STAGE_VALIDATE "$variant" "$exp"
done

echo "preflight staged copyback/fold resume and corruption: OK"
