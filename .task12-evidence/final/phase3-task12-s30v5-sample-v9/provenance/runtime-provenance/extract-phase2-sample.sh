#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 4)); then
  echo "usage: $0 PHASE2_JOURNAL_DIR TRUSTED_SUMS SELECTION OUTPUT" >&2
  exit 2
fi

baseline=$(realpath "$1")
sums=$(realpath "$2")
selection=$(realpath "$3")
output=$4
expected_manifest=d2b145c9a16710611dcb61acdfc8e0635fd8acc46259e9ac2bddda7ca50c3318
expected_sample=4c0da14d6a7e5054fe6976ba26cdce76244b0e4b28ff990768f55344a3b322a2

[[ ! -e "$output" ]]
[[ "$(sha256sum "$sums" | cut -d' ' -f1)" == "$expected_manifest" ]]
(cd "$baseline" && sha256sum -c "$sums" >/dev/null)
temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT HUP INT TERM
cut -f3 "$selection" >"$temp/ids"
jq -Rn --rawfile ids "$temp/ids" '
  $ids|split("\n")|map(select(length>0))|INDEX(.)
' >"$temp/set"
find "$baseline" -maxdepth 1 -type f -name '*.jsonl' -print0 |
  LC_ALL=C sort -z | xargs -0 jq -c --slurpfile selected \
    "$temp/set" 'select($selected[0][.goal_id] != null)' |
  LC_ALL=C sort -S 64M >"$output"
[[ "$(wc -l <"$output")" == 3000 ]]
[[ "$(sha256sum "$output" | cut -d' ' -f1)" == "$expected_sample" ]]
