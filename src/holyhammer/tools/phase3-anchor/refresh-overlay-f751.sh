#!/bin/bash
set -Eeuo pipefail

inputs=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=${HHEVAL_TASK10_ROOT:-$(git rev-parse --show-toplevel)}
overlay=${HHEVAL_TASK10_OVERLAY_F751:-/tmp/holyhammer-current-overlay-f751}
top=$inputs/top-provenance.json
allowlist=$inputs/phase3-overlay-allowlist.tsv
temporary=$top.partial.$$
expected=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$temporary" "$expected" "$actual"' EXIT HUP INT TERM

test "$(git -C "$overlay" rev-parse HEAD)" = \
  f7511d0d5ee7c2918236f7eda4c16ee8c01e00fa
git -C "$root" diff --name-only \
  788f0b8817901c57206e56495367f27b0351dd68 -- src/holyhammer |
  awk '$0 == "src/holyhammer/Holmakefile" ||
    ($0 ~ /^src\/holyhammer\/[^/]+\.(sig|sml)$/ &&
     $0 !~ /\/(selftest|smoke)\.sml$/)' | LC_ALL=C sort >"$expected"
awk -F '\t' 'NR > 1 &&
  ($2 == "current-runtime" || $2 == "build-only") {print $1}' \
  "$allowlist" | LC_ALL=C sort >"$actual"
cmp -s "$expected" "$actual"

while IFS=$'\t' read -r file_path _; do
  test "$file_path" != path || continue
  mkdir -p "$overlay/${file_path%/*}"
  cp "$root/$file_path" "$overlay/$file_path"
done <"$allowlist"
(cd "$overlay/src/holyhammer" && "$overlay/bin/Holmake")

git -C "$overlay" diff --binary -- src/AI src/holyhammer \
  >"$inputs/overlay-f751.patch"
diff_sha=$(sha256sum "$inputs/overlay-f751.patch" | awk '{print $1}')
jq --arg digest "$diff_sha" \
  '.execution_states.f751.current_diff_sha256=$digest' \
  "$top" >"$temporary"
mv "$temporary" "$top"

: >"$inputs/overlay-f751-loaded-sources.tsv"
for file_path in $(jq -r \
  '.execution_states.f751.current_loaded.sources | keys[]' "$top")
do
  digest=$(sha256sum "$overlay/$file_path" | awk '{print $1}')
  printf '%s\t%s\n' "$file_path" "$digest" \
    >>"$inputs/overlay-f751-loaded-sources.tsv"
  jq --arg file "$file_path" --arg digest "$digest" \
    '.execution_states.f751.current_loaded.sources[$file]=$digest' \
    "$top" >"$temporary"
  mv "$temporary" "$top"
done

: >"$inputs/overlay-f751-loaded-objects.tsv"
for file_path in $(jq -r \
  '.execution_states.f751.current_loaded.objects | keys[]' "$top")
do
  digest=$(sha256sum "$overlay/$file_path" | awk '{print $1}')
  printf '%s\t%s\n' "$file_path" "$digest" \
    >>"$inputs/overlay-f751-loaded-objects.tsv"
  jq --arg file "$file_path" --arg digest "$digest" \
    '.execution_states.f751.current_loaded.objects[$file]=$digest' \
    "$top" >"$temporary"
  mv "$temporary" "$top"
done

trap - EXIT HUP INT TERM
rm -f "$expected" "$actual"
