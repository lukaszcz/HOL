#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 4)); then
  echo "usage: $0 BASE_PROVENANCE RUNTIME CHECKED_AT OUTPUT" >&2
  exit 2
fi

base=$(realpath "$1")
runtime=$(realpath "$2")
checked_at=$3
output=$4
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
jq --arg checked "$checked_at" \
  --arg state "$state_base/k-revised-v3" \
  --arg root "$(sha256sum "$runtime/runtime-root-certificate.json" |
    cut -d' ' -f1)" \
  --arg dependencies "$(sha256sum \
    "$runtime/runtime-dependency-certificate.json" | cut -d' ' -f1)" '
  .schema="hh-task12-cleanup-v4" | .checked_at=$checked |
  if (.removed_roots | index($state)) == null then
    .removed_roots += [$state]
  else . end |
  .runtime_root_certificate_sha256=$root |
  .runtime_dependency_certificate_sha256=$dependencies
' "$base/cleanup-certificate.json" >"$output/cleanup-certificate.json"
(cd "$output" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$output/SHA256SUMS"
chmod -R a-w "$output"
