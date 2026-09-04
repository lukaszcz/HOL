#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 4)); then
  echo "usage: $0 RUN GOALS EXCLUDED_GOALS CRITERION_B_REPORT" >&2
  exit 2
fi

RUN=$(realpath "$1")
GOALS=$(realpath "$2")
EXCLUDED=$3
CRITERION=$4
OBSERVED=$(mktemp)
trap 'rm -f "$OBSERVED"' EXIT HUP INT TERM

find "$RUN/journal" -type f -name '*.jsonl' -print0 |
  xargs -0 jq -r '.goal_id' | LC_ALL=C sort -u >"$OBSERVED"
awk -F '\t' 'NR == FNR {goals[$2] = 1; next} !goals[$1] {print $1}' \
  "$GOALS" "$OBSERVED" >"$EXCLUDED"

jq -r '
  if .shape.criterion_b_pass then
    "Criterion (b) holds for both provers; no violation."
  else
    "# F30 criterion (b) investigation\n\n" +
    ([.shape.vampire,.shape.e] |
      map(select(.criterion_b.pass == false) | .prover) | join(", ")) as
      $failed |
    "Criterion (b) is violated for: " + $failed + ".\n\n" +
    "The exact paired counts are retained in result.json and " +
    "shape-investigation.json. No slice identity, fact count, timeout, " +
    "or ranking constant was changed."
  end
' "$RUN/result.json" >"$CRITERION"

[[ "$(wc -l <"$EXCLUDED")" == \
   "$(jq -r '.excluded_extra_goals' "$RUN/result.json")" ]]
[[ "$(sha256sum "$EXCLUDED" | cut -d' ' -f1)" == \
   "$(jq -r '.excluded_extra_goal_ids_sha256' "$RUN/result.json")" ]]
