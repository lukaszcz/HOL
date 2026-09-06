#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 2)); then
  echo "usage: $0 ROOTS_BEFORE_TSV ROOTS_REMOVED_TSV" >&2
  exit 2
fi

manifest=$(realpath "$1")
removed=$2
uid=$(id -u)
[[ ! -e "$removed" ]]
temp=$(mktemp)
trap 'rm -f "$temp"' EXIT HUP INT TERM
: >"$temp"

while IFS=$'\t' read -r target owner kind bytes files dirs extra; do
  [[ -n "$target" && -z "${extra-}" && "$owner" == "$uid" &&
     "$kind" == directory ]]
  [[ "$target" == /tmp/* && "${target#/tmp/}" != */* ]]
  base=${target#/tmp/}
  [[ "$base" =~ [Pp][Hh][Aa][Ss][Ee]3|[Tt][Aa][Ss][Kk](10|11|12) ]]
  [[ -d "$target" && ! -L "$target" ]]
  [[ "$(realpath -e -- "$target")" == "$target" ]]
  [[ "$(stat -c %u -- "$target")" == "$uid" ]]
  [[ "$(du -sb -- "$target" | cut -f1)" == "$bytes" ]]
  [[ "$(find "$target" -xdev -type f -printf . | wc -c)" == "$files" ]]
  [[ "$(find "$target" -xdev -type d -printf . | wc -c)" == "$dirs" ]]
  chmod -R u+w -- "$target"
  rm -rf -- "$target"
  [[ ! -e "$target" && ! -L "$target" ]]
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$target" "$owner" "$kind" "$bytes" "$files" "$dirs" >>"$temp"
done <"$manifest"

cmp "$manifest" "$temp"
mv "$temp" "$removed"
trap - EXIT HUP INT TERM
