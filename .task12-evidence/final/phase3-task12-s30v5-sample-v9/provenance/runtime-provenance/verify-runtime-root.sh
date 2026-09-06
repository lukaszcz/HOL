#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 2)); then
  echo "usage: $0 HOL_ROOT RUNTIME_BUNDLE" >&2
  exit 2
fi

root=$(realpath "$1")
bundle=$(realpath "$2")
certificate="$bundle/runtime-root-certificate.json"
temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT HUP INT TERM
commit=$(jq -er '.accepted_commit' "$certificate")
[[ "$(git -C "$root" rev-parse HEAD)" == "$commit" ]]
git -C "$root" diff --quiet HEAD -- .
git -C "$root" diff --cached --quiet HEAD -- .
[[ ! -s "$bundle/allowed-source-diff.tsv" ]]

check_manifest() {
  local manifest=$1 base=$2 expected_count=$3 actual_count=0
  while read -r expected path extra; do
    [[ -z "${extra-}" && -n "$expected" && -n "$path" &&
      "$path" != *../* ]]
    if [[ "$path" == /* ]]; then
      [[ "$base" == / ]]
      target=$path
    else
      target="$base/$path"
    fi
    [[ -f "$target" && ! -L "$target" &&
      "$(sha256sum "$target" | cut -d' ' -f1)" == "$expected" ]]
    ((actual_count += 1))
  done <"$manifest"
  [[ "$actual_count" == "$expected_count" ]]
}

object_count=$(jq -er '.hol_runtime_objects.count' "$certificate")
target_count=$(jq -er '.target_theory_objects.count' "$certificate")
host_count=$(jq -er '.host_runtime.count' "$certificate")
check_manifest "$bundle/hol-runtime-objects.tsv" "$root" "$object_count"
check_manifest "$bundle/target-theory-objects.tsv" "$root" "$target_count"
check_manifest "$bundle/host-runtime.tsv" / "$host_count"
for command in awk bash cat cmp cp cut date dirname env find git grep head \
    id journalctl jq mkdir mktemp mv realpath rm rmdir sed sha256sum sort \
    stat tail timeout tr wc xargs; do
  command_path=$(realpath "$(command -v "$command")")
  awk -v path="$command_path" '$2 == path {found++}
    END {if (found != 1) exit 1}' "$bundle/host-runtime.tsv"
done
(cd "$root" &&
  find src -path '*/.hol/objs/*' -type f \
    \( -name '*.uo' -o -name '*.ui' -o -name '*.dat' -o \
       -name '*.sml' -o -name '*.sig' -o -name '*.cachekey' \) -print |
    LC_ALL=C sort) >"$temp/actual-runtime-paths"
awk '{print $2}' "$bundle/hol-runtime-objects.tsv" | LC_ALL=C sort \
  >"$temp/sealed-runtime-paths"
cmp "$temp/sealed-runtime-paths" "$temp/actual-runtime-paths"
jq -e --arg allowed "$(sha256sum "$bundle/allowed-source-diff.tsv" |
    cut -d' ' -f1)" \
  --arg objects "$(sha256sum "$bundle/hol-runtime-objects.tsv" |
    cut -d' ' -f1)" \
  --arg targets "$(sha256sum "$bundle/target-theory-objects.tsv" |
    cut -d' ' -f1)" \
  --arg host "$(sha256sum "$bundle/host-runtime.tsv" | cut -d' ' -f1)" '
  .schema == "hh-task12-runtime-root-v1" and .status == "complete" and
  .allowed_tracked_diff_count == 0 and
  .allowed_source_diff_sha256 == $allowed and
  .hol_runtime_objects.sha256 == $objects and
  .target_theory_objects.theories == 229 and
  .target_theory_objects.sha256 == $targets and
  .host_runtime.sha256 == $host
' "$certificate" >/dev/null
