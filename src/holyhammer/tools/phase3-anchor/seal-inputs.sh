#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 1 || {
  echo "usage: $0 MUTABLE_STAGED_INPUT_DIRECTORY" >&2
  exit 2
}
inputs=$1
root=${HHEVAL_TASK10_ROOT:-$(git rev-parse --show-toplevel)}
test -d "$inputs" && test ! -L "$inputs"
test -s "$inputs/top-provenance.json"
test ! -e "$inputs/SHA256SUMS" || {
  echo "input directory is already sealed" >&2
  exit 2
}
test -z "$(find "$inputs" -type l -print -quit)"
HHEVAL_TASK10_ROOT=$root \
  "$inputs/runtime-inventory-selftest.sh" "$inputs" >/dev/null

runtime=$(mktemp)
external=$(mktemp)
top=$(mktemp)
trap 'rm -f "$runtime" "$external" "$top"' EXIT HUP INT TERM
"$inputs/runtime-provenance.sh" "$inputs" "$runtime"
commit=$(git -C "$root" rev-parse HEAD)
diff=$(git -C "$root" diff --binary -- src/holyhammer | sha256sum |
  awk '{print $1}')
schema=$(jq -er '.schema' "$inputs/top-provenance.json")
case "$schema" in
  hh-task10-a-run-v13)
    "$inputs/runtime-provenance.sh" --external "$inputs" "$external"
    jq --slurpfile runtime "$runtime" --slurpfile external "$external" \
      --arg commit "$commit" --arg diff "$diff" \
      '.main.commit=$commit | .main.tracked_diff_sha256=$diff |
       .runtime_tools=$runtime[0] | .external_tools=$external[0] |
       (.external_tools.tools[] | select(.name == "flock")) as $flock |
       .current_checkpoint_chain.heavy_hol_reservation.flock_path =
         $flock.command_path |
       .current_checkpoint_chain.heavy_hol_reservation.flock_sha256 =
         $flock.sha256' \
      "$inputs/top-provenance.json" >"$top"
    ;;
  hh-task10-p-run-v4)
    jq --slurpfile runtime "$runtime" --arg commit "$commit" \
      --arg diff "$diff" \
      '.main.commit=$commit | .main.tracked_diff_sha256=$diff |
       .runtime_tools=$runtime[0]' \
      "$inputs/top-provenance.json" >"$top"
    ;;
  *)
    echo "unsupported input provenance schema: $schema" >&2
    exit 2
    ;;
esac
mv "$top" "$inputs/top-provenance.json"

(cd "$inputs" && find . -type f ! -path ./SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$inputs/SHA256SUMS"
test -s "$inputs/SHA256SUMS"
(cd "$inputs" && sha256sum -c SHA256SUMS >/dev/null)
HHEVAL_TASK10_ROOT=$root \
  "$inputs/runtime-inventory-selftest.sh" "$inputs" >/dev/null
chmod -R a-w "$inputs"
printf 'sealed input files=%s inventory_sha256=%s\n' \
  "$(wc -l <"$inputs/SHA256SUMS")" \
  "$(sha256sum "$inputs/SHA256SUMS" | awk '{print $1}')"
trap - EXIT HUP INT TERM
rm -f "$runtime"
rm -f "$external"
