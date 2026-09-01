#!/bin/bash
set -Eeuo pipefail

input=${1:?input inventory is required}
output=${2:?output inventory is required}
partial=$output.partial.$$
trap 'rm -f "$partial"' EXIT HUP INT TERM
: >"$partial"

while IFS=$'\t' read -r theory goals directory dat ui member member_sha state
do
  case "$state" in
    f751)
      base=/tmp/holyhammer-anchor-f751
      overlay=/tmp/holyhammer-current-overlay-f751
      ;;
    f258)
      base=/tmp/holyhammer-anchor-f258
      overlay=/tmp/holyhammer-current-overlay-f258
      ;;
    *) exit 2 ;;
  esac
  case "$directory" in
    "$base"/*) relative_directory=${directory#"$base"/} ;;
    *) exit 2 ;;
  esac
  raw=
  if test -f "$directory/Holmakefile"; then
    raw=$(awk '$1 == "HOLHEAP" && $2 == "=" {print $3; exit}' \
      "$directory/Holmakefile")
  fi
  if test -z "$raw"; then
    heap_relative=bin/hol.state
  else
    case "$raw" in
      '$(HOLDIR)/'*) heap_relative=${raw#'$(HOLDIR)/'} ;;
      *)
        heap=$(realpath -m "$directory/$raw")
        case "$heap" in
          "$base"/*) heap_relative=${heap#"$base"/} ;;
          *) exit 2 ;;
        esac
        ;;
    esac
  fi
  base_heap=$base/$heap_relative
  overlay_heap=$overlay/$heap_relative
  test -f "$base_heap" && test ! -L "$base_heap"
  test -f "$overlay_heap" && test ! -L "$overlay_heap"
  object_inventory=$(cd "$directory/.hol/objs" &&
    find . -maxdepth 1 -type f -print0 | LC_ALL=C sort -z |
      xargs -0 sha256sum | sha256sum | awk '{print $1}')
  if test -f "$directory/Holmakefile"; then
    holmakefile_sha=$(sha256sum "$directory/Holmakefile" | awk '{print $1}')
  else
    holmakefile_sha=-
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$theory" "$goals" "$directory" "$dat" "$ui" "$member" \
    "$member_sha" "$state" "$heap_relative" \
    "$(sha256sum "$base_heap" | awk '{print $1}')" \
    "$(sha256sum "$overlay_heap" | awk '{print $1}')" \
    "$object_inventory" "$holmakefile_sha" >>"$partial"
done <"$input"

mv "$partial" "$output"
trap - EXIT HUP INT TERM
