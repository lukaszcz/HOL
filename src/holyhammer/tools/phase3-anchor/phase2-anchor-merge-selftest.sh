#!/bin/sh
set -eu

test "$#" -eq 1 || {
  echo "usage: $0 PHASE2_ANCHOR_MERGER" >&2
  exit 2
}
merger=$1
test -x "$merger"
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM

reject_scheduler () {
  label=$1
  scheduler=$2
  diagnostic=$3
  if "$merger" "$work/missing-first" "$work/missing-last" \
      "$work/$label.tsv" \
      0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef \
      "$scheduler" > "$work/$label.log" 2>&1
  then
    echo "$label scheduler digest unexpectedly passed" >&2
    exit 1
  fi
  grep -F "$diagnostic" "$work/$label.log" >/dev/null
  test ! -e "$work/$label.tsv"
}

reject_scheduler empty "" "invalid extension scheduler SHA-256"
reject_scheduler malformed xyz "invalid extension scheduler SHA-256"
reject_scheduler short deadbeef \
  "invalid extension scheduler SHA-256 length"
echo "extension scheduler digest negatives: rejected"
