#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 5)); then
  echo "usage: $0 BASE_PROVENANCE RUNTIME CHECKED_AT TMP_CLEANUP OUTPUT" >&2
  exit 2
fi

base=$(realpath "$1")
runtime=$(realpath "$2")
checked_at=$3
tmp_cleanup=$(realpath "$4")
output=$5
state_base=/run/user/$(id -u)/holyhammer-phase3-task12
[[ ! -e "$output" && ! -e "$state_base/k-revised-v3" ]]
if [[ -d "$state_base" ]]; then
  [[ -z "$(find "$state_base" -mindepth 1 -maxdepth 1 -print -quit)" ]]
fi
mkdir "$output"
for path in phase2-s30-v3-journal.sha256 task10-a-final.json \
  task11-final.json task12-input-SHA256SUMS task12-input-provenance.json; do
  cp "$base/$path" "$output/$path"
done
cp -a "$runtime" "$output/runtime-provenance"
cp -a "$tmp_cleanup" "$output/tmp-cleanup"
jq --arg checked "$checked_at" \
  --arg state "$state_base/k-revised-v3" \
  --arg root "$(sha256sum "$runtime/runtime-root-certificate.json" |
    cut -d' ' -f1)" \
  --arg dependencies "$(sha256sum \
    "$runtime/runtime-dependency-certificate.json" | cut -d' ' -f1)" \
  --arg tmp "$(sha256sum "$tmp_cleanup/certificate.json" |
    cut -d' ' -f1)" \
  --arg roots "$(sha256sum "$tmp_cleanup/roots-before.tsv" |
    cut -d' ' -f1)" \
  --arg files "$(sha256sum "$tmp_cleanup/direct-files-before.tsv" |
    cut -d' ' -f1)" '
  .schema="hh-task12-cleanup-v6" | .checked_at=$checked |
  if (.removed_roots | index($state)) == null then
    .removed_roots += [$state]
  else . end |
  .runtime_root_certificate_sha256=$root |
  .runtime_dependency_certificate_sha256=$dependencies |
  .tmp_cleanup_certificate_sha256=$tmp |
  .tmp_cleanup_roots_manifest_sha256=$roots |
  .tmp_cleanup_roots=224 |
  .tmp_cleanup_files_manifest_sha256=$files |
  .tmp_cleanup_files=551
' "$base/cleanup-certificate.json" >"$output/cleanup-certificate.json"
(cd "$output" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$output/SHA256SUMS"
chmod -R a-w "$output"
