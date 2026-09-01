#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 2 || {
  echo "usage: $0 HISTORICAL_FROZEN_INPUTS AUDIT_OUTPUT" >&2
  exit 2
}
historical=$1
output=$2
tool_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
manifest=$tool_root/phase3-anchor/runtime-files.tsv
temporary=$output.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM
declare -A source_for
while IFS=$'\t' read -r source target; do source_for[$target]=$source; done \
  < "$manifest"
mapfile -t historical_tools < <(
  find "$historical" -maxdepth 1 -type f \
    \( -name '*.sh' -o -name '*.sml' -o -name 'Holmakefile*' \
       -o -name worker-function-manifest.tsv \) -printf '%f\n'
  find "$historical/tools" -maxdepth 1 -type f \
    \( -name '*.sh' -o -name '*.sml' -o -name '*.sha256' \) \
    -printf 'tools/%f\n'
  find "$historical/eval" -maxdepth 1 -type f -name '*.sml' \
    -printf 'eval/%f\n'
)
: > "$temporary"
for target in "${historical_tools[@]}"; do
  source=${source_for[$target]:-}
  test -n "$source" || {
    echo "historical runtime has no maintained source: $target" >&2
    exit 2
  }
  old_sha=$(sha256sum "$historical/$target" | awk '{print $1}')
  new_sha=$(sha256sum "$tool_root/$source" | awk '{print $1}')
  test "$old_sha" = "$new_sha" || {
    echo "frozen runtime differs without a reviewed allowlist: $target" >&2
    exit 1
  }
  status=byte-identical
  printf '%s\t%s\t%s\t%s\t%s\n' "$target" "$source" \
    "$old_sha" "$new_sha" "$status" >> "$temporary"
done
test "$(wc -l < "$temporary")" -eq "${#historical_tools[@]}"
mv "$temporary" "$output"
trap - EXIT HUP INT TERM
