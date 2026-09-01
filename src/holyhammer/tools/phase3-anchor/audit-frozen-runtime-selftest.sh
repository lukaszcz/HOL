#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 1 || {
  echo "usage: $0 AUDIT_TOOL" >&2
  exit 2
}
audit_tool=$1
test -x "$audit_tool"
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM
mkdir -p "$work/tools/phase3-anchor" "$work/historical/tools"
mkdir -p "$work/historical/eval"
cp "$audit_tool" "$work/tools/phase3-anchor/audit-frozen-runtime.sh"
printf '%s\n' '#!/bin/sh' 'exit 0' \
  >"$work/tools/phase3-anchor/example.sh"
cp "$work/tools/phase3-anchor/example.sh" "$work/historical/example.sh"
printf '%s\t%s\n' phase3-anchor/example.sh example.sh \
  >"$work/tools/phase3-anchor/runtime-files.tsv"
"$work/tools/phase3-anchor/audit-frozen-runtime.sh" \
  "$work/historical" "$work/accepted.tsv"
test "$(awk -F '\t' '{print $5}' "$work/accepted.tsv")" = byte-identical
printf '%s\n' '# changed' >>"$work/tools/phase3-anchor/example.sh"
if "$work/tools/phase3-anchor/audit-frozen-runtime.sh" \
    "$work/historical" "$work/rejected.tsv" 2>/dev/null; then
  echo "runtime audit accepted an unreviewed difference" >&2
  exit 1
fi
test ! -e "$work/rejected.tsv"
echo "frozen runtime mismatch rejection: passed"
