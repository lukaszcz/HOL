#!/bin/bash
set -Eeuo pipefail

snapshot=${1:?snapshot-support tool required}
verify_tool=${2:?verify-support tool required}
work=$(mktemp -d)
trap 'chmod -R u+w "$work" 2>/dev/null || true; \
  find "$work" -depth -delete 2>/dev/null || true' EXIT HUP INT TERM
external=$work/external
internal=$work/internal
mkdir -p "$external/nested"
printf '%s\n' alpha >"$external/record.json"
printf '%s\n' beta >"$external/nested/record.json"
chmod a-w "$external" "$external/nested"
"$snapshot" "$external" "$internal"
chmod u+w "$external" "$external/nested"

verify () {
  "$verify_tool" "$internal" "$internal/SNAPSHOT-SHA256SUMS"
}
verify
printf '%s\n' changed >"$external/record.json"
printf '%s\n' added >"$external/added.json"
verify

chmod u+w "$internal/record.json"
printf '%s\n' tampered >"$internal/record.json"
if verify 2>/dev/null; then
  echo "internal support tamper was accepted" >&2
  exit 1
fi
cp "$external/nested/record.json" "$internal/record.json"
if verify 2>/dev/null; then
  echo "fabricated internal replacement was accepted" >&2
  exit 1
fi
chmod u+w "$internal/SNAPSHOT-SHA256SUMS"
sha256sum "$internal/record.json" | sed 's#  .*#  ./record.json#' \
  >"$internal/SNAPSHOT-SHA256SUMS"
if verify 2>/dev/null; then
  echo "fabricated incomplete inventory was accepted" >&2
  exit 1
fi
printf '%s\n' "self-contained support snapshot selftest: passed"
