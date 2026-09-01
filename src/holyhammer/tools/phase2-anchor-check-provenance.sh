#!/bin/sh
set -eu

test "$#" -eq 2 || {
  echo "usage: $0 ROOT SHA256_INVENTORY" >&2
  exit 2
}

root=$1
inventory=$2
test -d "$root" && test -f "$inventory" || {
  echo "provenance root or inventory is missing" >&2
  exit 2
}

rows=0
while read -r expected relative extra
do
  test -n "$expected" && test -n "$relative" && test -z "${extra-}" || {
    echo "malformed provenance inventory row" >&2
    exit 2
  }
  case "$relative" in
    /* | ../* | */../* | */..)
      echo "unsafe provenance inventory path: $relative" >&2
      exit 2
      ;;
  esac
  path=$root/$relative
  test -f "$path" && test ! -L "$path" || {
    echo "missing or non-regular provenance input: $path" >&2
    exit 2
  }
  actual=$(sha256sum "$path" | awk '{print $1}')
  test "$actual" = "$expected" || {
    echo "unexpected SHA-256 for $path: $actual" >&2
    exit 2
  }
  rows=$((rows + 1))
done < "$inventory"

test "$rows" -gt 0 || {
  echo "provenance inventory is empty" >&2
  exit 2
}
