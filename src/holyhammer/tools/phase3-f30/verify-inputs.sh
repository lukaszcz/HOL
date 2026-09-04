#!/usr/bin/env bash
set -Eeuo pipefail

if (($# < 1 || $# > 2)); then
  echo "usage: $0 SEALED_INPUTS [LIVE_ROOT]" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
ROOT=${2-}
LIVE_PATH=$PATH
PATH="$INPUTS/verify-bin"
export PATH

[[ -d "$INPUTS" && ! -L "$INPUTS" && -s "$INPUTS/SHA256SUMS" ]]
(cd "$INPUTS" && sha256sum -c SHA256SUMS >/dev/null)

expected=$(wc -l <"$INPUTS/SHA256SUMS")
actual=$(find "$INPUTS" -type f ! -name SHA256SUMS -print | wc -l)
[[ "$expected" == "$actual" ]]
jq -e '
  .schema == "hh-task11-f30-input-v1" and
  .envelope.cpu_quota_cores == 32 and
  .envelope.memory_high_bytes == 133143986176 and
  .envelope.memory_max_bytes == 137438953472 and
  .envelope.memory_swap_max_bytes == 0 and
  .envelope.worker_recycle_seconds == 600 and
  .envelope.worker_slots == 32 and
  (.provers | length) == 2
' "$INPUTS/top-provenance.json" >/dev/null
[[ "$(sha256sum "$INPUTS/main-loaded-sources.tsv" | cut -d' ' -f1)" == \
   "$(jq -r '.main.loaded_sources_sha256' \
     "$INPUTS/top-provenance.json")" ]]
[[ "$(sha256sum "$INPUTS/main-loaded-objects.tsv" | cut -d' ' -f1)" == \
   "$(jq -r '.main.loaded_objects_sha256' \
     "$INPUTS/top-provenance.json")" ]]
[[ "$(sha256sum "$INPUTS/task10-inventory.tsv" | cut -d' ' -f1)" == \
   "$(jq -r '.task10_inventory_sha256' \
     "$INPUTS/top-provenance.json")" ]]
(cd "$INPUTS" && sha256sum -c task10-inventory.tsv >/dev/null)
if jq -e 'has("canonical_goal_inventory_sha256") and
    has("canonical_goal_certificate_sha256")' \
    "$INPUTS/top-provenance.json" >/dev/null; then
  [[ "$(sha256sum "$INPUTS/canonical-goals.tsv" | cut -d' ' -f1)" == \
     "$(jq -r '.canonical_goal_inventory_sha256' \
       "$INPUTS/top-provenance.json")" ]]
  [[ "$(sha256sum "$INPUTS/canonical-goals.json" | cut -d' ' -f1)" == \
     "$(jq -r '.canonical_goal_certificate_sha256' \
       "$INPUTS/top-provenance.json")" ]]
  jq -e --arg goals "$(sha256sum "$INPUTS/canonical-goals.tsv" |
      cut -d' ' -f1)" '
    .schema == "hh-task11-canonical-goals-v1" and
    .status == "complete" and .goals == 24721 and .theories == 229 and
    .canonical_goal_inventory_sha256 == $goals and
    .baseline_current_rows_byte_identical == true
  ' "$INPUTS/canonical-goals.json" >/dev/null
  awk -F '\t' '
    NF != 2 || $1 == "" || $2 == "" || $2 !~ ("^" $1 "\\.") ||
    seen[$2]++ {exit 1}
    END {if (NR != 24721) exit 1}
  ' "$INPUTS/canonical-goals.tsv"
else
  [[ "$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)" == \
     acd7541e9efa02b114cb0829093ddc6b2caa4e82e61852f9d0c3fa5e9ddd0ea8 ]]
  [[ ! -e "$INPUTS/canonical-goals.tsv" &&
     ! -e "$INPUTS/canonical-goals.json" ]]
fi
[[ "$(wc -l <"$INPUTS/theory-directories.tsv")" == 229 ]]
awk -F '\t' '
  NF != 4 || $1 == "" || $2 == "" ||
  $3 !~ /^[0-9a-f]{64}$/ || $4 !~ /^[0-9a-f]{64}$/ {exit 1}
' "$INPUTS/theory-directories.tsv"
[[ "$(cut -f1 "$INPUTS/theory-directories.tsv" | sort -u | wc -l)" == \
   229 ]]

if [[ -z "$ROOT" ]]; then
  exit 0
fi

PATH=$LIVE_PATH
export PATH

[[ "$(git -C "$ROOT" rev-parse HEAD)" == \
   "$(jq -r '.main.commit' "$INPUTS/top-provenance.json")" ]]
live_diff=$(git -C "$ROOT" diff --binary -- src/holyhammer | sha256sum |
  cut -d' ' -f1)
[[ "$live_diff" == \
   "$(jq -r '.main.tracked_diff_sha256' \
     "$INPUTS/top-provenance.json")" ]]
"$INPUTS/check-provenance.sh" "$ROOT" \
  "$INPUTS/main-loaded-sources.tsv"
"$INPUTS/check-provenance.sh" "$ROOT" \
  "$INPUTS/main-loaded-objects.tsv"
[[ -z "$(git -C "$ROOT" diff --name-only -- \
  src/AI/machine_learning)" ]]

while IFS=$'\t' read -r theory relative ui_sha uo_sha extra; do
  [[ -n "$theory" && -n "$relative" && -z "${extra-}" ]]
  [[ "$relative" != /* && "$relative" != ../* ]]
  ui="$ROOT/$relative/.hol/objs/${theory}Theory.ui"
  uo="$ROOT/$relative/.hol/objs/${theory}Theory.uo"
  [[ -f "$ui" && ! -L "$ui" && -f "$uo" && ! -L "$uo" ]]
  [[ "$(sha256sum "$ui" | cut -d' ' -f1)" == "$ui_sha" ]]
  [[ "$(sha256sum "$uo" | cut -d' ' -f1)" == "$uo_sha" ]]
done <"$INPUTS/theory-directories.tsv"

while IFS=$'\t' read -r name path version digest extra; do
  [[ -n "$name" && -x "$path" && -z "${extra-}" ]]
  [[ "$(sha256sum "$path" | cut -d' ' -f1)" == "$digest" ]]
  "$path" --version 2>&1 | head -1 | grep -F "$version" >/dev/null
done <"$INPUTS/provers.tsv"

relative=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
cgroup="/sys/fs/cgroup$relative"
[[ "$(cat "$cgroup/memory.high")" == 133143986176 ]]
[[ "$(cat "$cgroup/memory.max")" == 137438953472 ]]
[[ "$(cat "$cgroup/memory.swap.max")" == 0 ]]
read -r quota period <"$cgroup/cpu.max"
[[ "$quota" != max && "$quota" == "$((32 * period))" ]]
[[ "$(nproc)" == 32 ]]
[[ "$(findmnt -T "/run/user/$(id -u)" -n -o FSTYPE)" == tmpfs ]]
