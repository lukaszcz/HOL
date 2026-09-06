#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 4)); then
  exit 2
fi
atom=$1
attempt=$2
goals=$3
output=$4
if [[ "$atom" == fixture-0-of-2 && "$attempt" == 1 ]]; then
  exit 1
fi
LC_ALL=C sort -r "$goals" |
while IFS=$'\t' read -r theory goal extra; do
  [[ -z "${extra-}" ]]
  jq -cn --arg thy "$theory" --arg goal "$goal" \
    '{thy:$thy,goal_id:$goal}'
done >"$output"
