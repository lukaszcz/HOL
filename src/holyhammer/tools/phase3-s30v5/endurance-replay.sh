#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 1)); then
  echo "usage: $0 FINAL_EVIDENCE" >&2
  exit 2
fi

final=$(realpath "$1")
sample="$final/sample"
"$final/verifier/verify-result.sh" "$final"
printf 'Validated replay inputs: %s atoms, %s cells, schedule %s\n' \
  "$(wc -l <"$sample/endurance/atom-inventory.tsv")" \
  "$(wc -l <"$sample/endurance/journal.jsonl")" \
  "$(sha256sum "$sample/schedule.tsv" | cut -d' ' -f1)"
printf '%s\n' \
  'The retained bundle replays validation and statistical folding.' \
  'It does not claim byte identity with the compacted untracked runner.'
