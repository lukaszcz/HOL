#!/bin/sh
set -eu

test "$#" -eq 2 || {
  echo "usage: $0 anchor|preflight EMPTY_DESTINATION" >&2
  exit 2
}

kind=$1
destination=$2
tool_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
case "$kind" in
  anchor) manifest=$tool_root/phase3-anchor/runtime-files.tsv ;;
  preflight) manifest=$tool_root/phase3-preflight/runtime-files.tsv ;;
  *) echo "unknown runtime kind: $kind" >&2; exit 2 ;;
esac
test -s "$manifest"
test ! -e "$destination" || {
  echo "runtime destination must be initially absent" >&2
  exit 2
}
mkdir -p "$destination"
origin=$destination/runtime-origin.tsv
: > "$origin"
while IFS="$(printf '\t')" read -r source target extra
do
  test -n "$source" && test -n "$target" && test -z "${extra-}"
  case "$source:$target" in
    /*:* | *:/*/../* | *:../* | *:*/.. | *:..)
      echo "unsafe runtime path: $source -> $target" >&2
      exit 2
      ;;
  esac
  source_path=$tool_root/$source
  target_path=$destination/$target
  test -f "$source_path" && test ! -L "$source_path"
  mkdir -p "$(dirname -- "$target_path")"
  cp "$source_path" "$target_path"
  test "$(sha256sum "$source_path" | awk '{print $1}')" = \
       "$(sha256sum "$target_path" | awk '{print $1}')"
  printf '%s\t%s\t%s\n' "$target" "$source" \
    "$(sha256sum "$target_path" | awk '{print $1}')" >> "$origin"
done < "$manifest"
chmod 0444 "$origin"
