#!/bin/bash
set -Eeuo pipefail

root=${HHEVAL_TASK10_ROOT:-$(git rev-parse --show-toplevel)}
tool_root=$root/src/holyhammer/tools/phase3-anchor
work=$(mktemp -d)
trap 'chmod -R u+w "$work" 2>/dev/null || true; rm -rf "$work"' \
  EXIT HUP INT TERM
inputs=$work/inputs

"$tool_root/freeze-runtime.sh" preflight "$inputs"
mkdir -p "$inputs/nested/evidence"
printf '%s\n' payload >"$inputs/nested/evidence/payload"
(cd "$inputs/nested/evidence" && sha256sum payload) \
  >"$inputs/nested/evidence/SHA256SUMS"
printf '%s\n' \
  '{"schema":"hh-task10-p-run-v4","main":{}}' \
  >"$inputs/top-provenance.json"

HHEVAL_TASK10_ROOT=$root "$inputs/seal-inputs.sh" "$inputs" >/dev/null
grep -F '  ./nested/evidence/SHA256SUMS' "$inputs/SHA256SUMS" \
  >/dev/null
(cd "$inputs" && sha256sum -c SHA256SUMS >/dev/null)
jq -e '
  .schema == "hh-task10-p-run-v4" and
  (.main.commit | test("^[0-9a-f]{40}$")) and
  (.main.tracked_diff_sha256 | test("^[0-9a-f]{64}$")) and
  .runtime_tools.schema == "hh-task10-runtime-tools-v2" and
  (has("external_tools") | not) and
  (has("current_checkpoint_chain") | not)
' "$inputs/top-provenance.json" >/dev/null
test ! -e "$inputs/external-tools.tsv"
test ! -e "$inputs/verify-bin"

chmod u+w "$inputs/nested/evidence/SHA256SUMS"
printf '%s\n' corrupt >>"$inputs/nested/evidence/SHA256SUMS"
if (cd "$inputs" && sha256sum -c SHA256SUMS >/dev/null 2>&1); then
  echo "nested evidence inventory corruption was not detected" >&2
  exit 1
fi

printf '%s\n' \
  "seal-inputs selftest: nested inventories and P schema are exact"
