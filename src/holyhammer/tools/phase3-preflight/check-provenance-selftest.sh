#!/bin/sh
set -eu

test "$#" -eq 1 || {
  echo "usage: $0 CHECK_PROVENANCE_TOOL" >&2
  exit 2
}
checker=$1
test -x "$checker"
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM
: >"$work/empty.sha256"
if "$checker" "$work" "$work/empty.sha256" >"$work/empty.log" 2>&1
then
  echo "empty provenance inventory unexpectedly passed" >&2
  exit 1
fi
grep -F "provenance inventory is empty" "$work/empty.log" >/dev/null
printf '%s\n' bound >"$work/input"
sha256sum "$work/input" | sed "s|$work/||" >"$work/one.sha256"
"$checker" "$work" "$work/one.sha256"
echo "empty provenance inventory: rejected"
