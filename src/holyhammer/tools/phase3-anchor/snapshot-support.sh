#!/bin/bash
set -Eeuo pipefail

test "$#" -ge 2 || {
  echo "usage: $0 SOURCE_DIRECTORY EMPTY_DESTINATION [RELATIVE_FILE ...]" >&2
  exit 2
}
source_directory=$1
destination=$2
shift 2
test -d "$source_directory" && test ! -L "$source_directory"
test ! -e "$destination" || {
  echo "support snapshot destination must be initially absent" >&2
  exit 2
}
mkdir -p "$destination"
if test "$#" -eq 0; then
  test -z "$(find "$source_directory" -type l -print -quit)" || {
    echo "support snapshot source contains a symlink" >&2
    exit 2
  }
  cp -a "$source_directory/." "$destination/"
else
  for relative in "$@"; do
    case "$relative" in
      "" | /* | .. | ../* | */../* | */..)
        echo "unsafe support snapshot member: $relative" >&2
        exit 2
        ;;
    esac
    source_file=$source_directory/$relative
    destination_file=$destination/$relative
    test -f "$source_file" && test ! -L "$source_file"
    mkdir -p "$(dirname -- "$destination_file")"
    cp -p "$source_file" "$destination_file"
  done
fi
test -z "$(find "$destination" -type l -print -quit)"
# A sealed source may intentionally have non-writable directories.  The
# destination remains under construction until the enclosing tuple is sealed,
# so restore owner write permission on copied directories only.
find "$destination" -type d -exec chmod u+w {} +
inventory=$destination/SNAPSHOT-SHA256SUMS
(cd "$destination" && find . -type f \
  ! -name SNAPSHOT-SHA256SUMS -print0 | LC_ALL=C sort -z |
  xargs -0 sha256sum) >"$inventory"
test -s "$inventory"
(cd "$destination" && sha256sum -c SNAPSHOT-SHA256SUMS >/dev/null)
