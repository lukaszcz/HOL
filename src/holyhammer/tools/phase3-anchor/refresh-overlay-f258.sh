#!/bin/bash
set -Eeuo pipefail

inputs=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=${HHEVAL_TASK10_ROOT:-$(git rev-parse --show-toplevel)}
overlay=${HHEVAL_TASK10_OVERLAY_F258:-/tmp/holyhammer-current-overlay-f258}
top=$inputs/top-provenance.json
allowlist=$inputs/phase3-overlay-allowlist.tsv
support=$inputs/phase3-overlay-support-f258.tsv
closure=$inputs/phase3-overlay-runtime-closure-uos.tsv
temporary=$top.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM

# The runtime overlay is the committed Phase 3 production delta from 788, plus
# the exact signatures that are unchanged at 788 but incompatible with f258.
# This is a closed, mechanically checked set rather than a trial-based mix.
expected_delta=$(mktemp)
actual_delta=$(mktemp)
expected_compat=$(mktemp)
actual_compat=$(mktemp)
trap 'rm -f "$temporary" "$expected_delta" "$actual_delta" \
  "$expected_compat" "$actual_compat"' EXIT HUP INT TERM
git -C "$root" diff --name-only \
  788f0b8817901c57206e56495367f27b0351dd68 -- src/holyhammer |
  awk '$0 == "src/holyhammer/Holmakefile" ||
    ($0 ~ /^src\/holyhammer\/[^/]+\.(sig|sml)$/ &&
     $0 !~ /\/(selftest|smoke)\.sml$/)' | LC_ALL=C sort >"$expected_delta"
awk -F '\t' 'NR > 1 && ($2 == "current-runtime" || $2 == "build-only") {
  print $1
}' "$allowlist" | LC_ALL=C sort >"$actual_delta"
cmp -s "$expected_delta" "$actual_delta"
printf '%s\n' \
  src/holyhammer/hhMonomorph.sig \
  src/holyhammer/hhProblemGen.sig \
  src/holyhammer/hhProver.sig | LC_ALL=C sort >"$expected_compat"
awk -F '\t' 'NR > 1 && $2 == "compatibility-interface" {print $1}' \
  "$allowlist" | LC_ALL=C sort >"$actual_compat"
cmp -s "$expected_compat" "$actual_compat"
while IFS= read -r file_path; do
  test "$(git -C "$root" show \
    788f0b8817901c57206e56495367f27b0351dd68:"$file_path" | sha256sum |
    awk '{print $1}')" = "$(sha256sum "$root/$file_path" | awk '{print $1}')"
done <"$expected_compat"

# The support set is the f258-to-788 difference intersected with the complete
# transitive dependency closure of hhEval.  Support files come from 788, while
# Phase 3 files above come from the current worktree.
while IFS=$'\t' read -r file_path _; do
  test "$file_path" != path || continue
  git -C "$root" diff --quiet \
    f25871c404016d4368a0927ba0a868860fc82c70 \
    788f0b8817901c57206e56495367f27b0351dd68 -- "$file_path" && exit 2
  git -C "$root" show \
    788f0b8817901c57206e56495367f27b0351dd68:"$file_path" \
    >"$overlay/$file_path"
done <"$support"

while IFS=$'\t' read -r file_path _; do
  test "$file_path" != path || continue
  mkdir -p "$overlay/${file_path%/*}"
  cp "$root/$file_path" "$overlay/$file_path"
done <"$allowlist"

# Source copies deliberately precede the build.  This makes every recorded
# object a product of the exact copied sources and prevents a later worker
# Holmake from silently rebuilding a provenance-pinned object.
(cd "$overlay/src/holyhammer" && "$overlay/bin/Holmake")

git -C "$overlay" diff --binary -- src/AI src/holyhammer \
  >"$inputs/overlay-f258.patch"
diff_sha=$(sha256sum "$inputs/overlay-f258.patch" | awk '{print $1}')
allowlist_sha=$(sha256sum "$allowlist" | awk '{print $1}')
support_sha=$(sha256sum "$support" | awk '{print $1}')
: >"$inputs/overlay-f258-allowlisted-files.tsv"
while IFS=$'\t' read -r file_path _; do
  test "$file_path" != path || continue
  digest=$(sha256sum "$overlay/$file_path" | awk '{print $1}')
  test "$digest" = "$(sha256sum "$root/$file_path" | awk '{print $1}')"
  printf '%s\t%s\n' "$file_path" "$digest" \
    >>"$inputs/overlay-f258-allowlisted-files.tsv"
done <"$allowlist"
while IFS=$'\t' read -r file_path _; do
  test "$file_path" != path || continue
  digest=$(sha256sum "$overlay/$file_path" | awk '{print $1}')
  test "$digest" = "$(git -C "$root" show \
    788f0b8817901c57206e56495367f27b0351dd68:"$file_path" | sha256sum |
    awk '{print $1}')"
  printf '%s\t%s\n' "$file_path" "$digest" \
    >>"$inputs/overlay-f258-allowlisted-files.tsv"
done <"$support"
allowlisted_files_sha=$(sha256sum \
  "$inputs/overlay-f258-allowlisted-files.tsv" | awk '{print $1}')
closure_sha=$(sha256sum "$closure" | awk '{print $1}')
: >"$inputs/overlay-f258-runtime-objects.tsv"
: >"$inputs/overlay-f258-runtime-sources.tsv"
while IFS= read -r object_path; do
  test -f "$overlay/$object_path"
  printf '%s\t%s\n' "$object_path" \
    "$(sha256sum "$overlay/$object_path" | awk '{print $1}')" \
    >>"$inputs/overlay-f258-runtime-objects.tsv"
  directory=${object_path%/.hol/objs/*}
  module=${object_path##*/}
  module=${module%.uo}
  source_path=$directory/$module.sml
  test -f "$overlay/$source_path"
  printf '%s\t%s\n' "$source_path" \
    "$(sha256sum "$overlay/$source_path" | awk '{print $1}')" \
    >>"$inputs/overlay-f258-runtime-sources.tsv"
done <"$closure"
closure_objects_sha=$(sha256sum \
  "$inputs/overlay-f258-runtime-objects.tsv" | awk '{print $1}')
closure_sources_sha=$(sha256sum \
  "$inputs/overlay-f258-runtime-sources.tsv" | awk '{print $1}')
jq --arg digest "$diff_sha" --arg allowlist "$allowlist_sha" \
  --arg support "$support_sha" \
  --arg closure "$closure_sha" --arg objects "$closure_objects_sha" \
  --arg sources "$closure_sources_sha" \
  --arg files "$allowlisted_files_sha" \
  '.execution_states.f258.current_diff_sha256=$digest |
   .execution_state_mapping.overlay_allowlist_sha256=$allowlist |
   .execution_state_mapping.f258_support_closure_sha256=$support |
   .execution_state_mapping.f258_runtime_closure_sha256=$closure |
   .execution_state_mapping.f258_runtime_objects_sha256=$objects |
   .execution_state_mapping.f258_runtime_sources_sha256=$sources |
   .execution_state_mapping.f258_allowlisted_files_sha256=$files' \
  "$top" >"$temporary"
mv "$temporary" "$top"

: >"$inputs/overlay-f258-loaded-sources.tsv"
for file_path in $(jq -r \
  '.execution_states.f258.current_loaded.sources | keys[]' "$top")
do
  digest=$(sha256sum "$overlay/$file_path" | awk '{print $1}')
  printf '%s\t%s\n' "$file_path" "$digest" \
    >>"$inputs/overlay-f258-loaded-sources.tsv"
  jq --arg file "$file_path" --arg digest "$digest" \
    '.execution_states.f258.current_loaded.sources[$file]=$digest' \
    "$top" >"$temporary"
  mv "$temporary" "$top"
done

: >"$inputs/overlay-f258-loaded-objects.tsv"
for file_path in $(jq -r \
  '.execution_states.f258.current_loaded.objects | keys[]' "$top")
do
  digest=$(sha256sum "$overlay/$file_path" | awk '{print $1}')
  printf '%s\t%s\n' "$file_path" "$digest" \
    >>"$inputs/overlay-f258-loaded-objects.tsv"
  jq --arg file "$file_path" --arg digest "$digest" \
    '.execution_states.f258.current_loaded.objects[$file]=$digest' \
    "$top" >"$temporary"
  mv "$temporary" "$top"
done

trap - EXIT HUP INT TERM
rm -f "$expected_delta" "$actual_delta" "$expected_compat" "$actual_compat"
