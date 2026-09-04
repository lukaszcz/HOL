#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 4)); then
  echo "usage: $0 TASK10_RUN TASK10_CERTS OUTPUT_TSV OUTPUT_JSON" >&2
  exit 2
fi

TASK10_RUN=$(realpath "$1")
TASK10_CERTS=$(realpath "$2")
OUTPUT=$3
CERTIFICATE=$4
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT HUP INT TERM

(cd "$TASK10_CERTS" && sha256sum -c SHA256SUMS >/dev/null)
FINAL="$TASK10_CERTS/final-certificate.json"
ACCEPTANCE="$TASK10_CERTS/final-acceptance.json"
FOLD="$TASK10_CERTS/independent-fold.json"
jq -e '
  .schema == "hh-task10-final-acceptance-v2" and
  .status == "complete" and .final_certificate_cross_binding_verified
' "$ACCEPTANCE" >/dev/null
jq -e '
  .schema == "hh-task10-a-final-certificate-v3" and
  .status == "complete" and .canonical_rows_byte_identical and
  .canonical_inventory.members == 229 and
  .canonical_inventory.goals == 24721 and
  .canonical_inventory.slices == 16 and
  .canonical_inventory.rows == 395536
' "$FINAL" >/dev/null
[[ "$(jq -r '.run_final_certificate_sha256' "$ACCEPTANCE")" == \
   "$(sha256sum "$FINAL" | cut -d' ' -f1)" ]]
[[ "$(jq -r '.independent_fold_sha256' "$FINAL")" == \
   "$(sha256sum "$FOLD" | cut -d' ' -f1)" ]]

find "$TASK10_RUN/current" -maxdepth 1 -type f -name '*.tsv' -print0 |
  LC_ALL=C sort -z | xargs -0 -n1 tail -n +2 |
  LC_ALL=C sort >"$WORK/current.sorted.tsv"
find "$TASK10_RUN/baseline" -maxdepth 1 -type f -name '*.tsv' -print0 |
  LC_ALL=C sort -z | xargs -0 -n1 tail -n +2 |
  LC_ALL=C sort >"$WORK/baseline.sorted.tsv"
cmp "$WORK/baseline.sorted.tsv" "$WORK/current.sorted.tsv"
body_sha=$(sha256sum "$WORK/current.sorted.tsv" | cut -d' ' -f1)
[[ "$body_sha" == \
   "$(jq -r '.canonical_sorted_body_sha256' "$FINAL")" ]]

awk -F '\t' '
  NF != 13 || $1 == "" || $2 !~ /^[0-9]+$/ ||
  $2 < 1 || $2 > 16 {bad=1; next}
  {seen[$1]++; theory=$1; sub(/\..*$/, "", theory); thys[$1]=theory}
  END {
    for (goal in seen) {
      if (seen[goal] != 16) bad=1
      print thys[goal] "\t" goal
    }
    if (bad) exit 1
  }
' "$WORK/current.sorted.tsv" | LC_ALL=C sort >"$WORK/goals.tsv"
[[ "$(wc -l <"$WORK/goals.tsv")" == 24721 ]]
[[ "$(cut -f1 "$WORK/goals.tsv" | sort -u | wc -l)" == 229 ]]
mv "$WORK/goals.tsv" "$OUTPUT"

jq -n --arg created "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg inventory "$(sha256sum "$OUTPUT" | cut -d' ' -f1)" \
  --arg body "$body_sha" \
  --arg task10_final "$(sha256sum "$FINAL" | cut -d' ' -f1)" \
  --arg task10_acceptance "$(sha256sum "$ACCEPTANCE" | cut -d' ' -f1)" \
  --arg task10_fold "$(sha256sum "$FOLD" | cut -d' ' -f1)" '
  {schema:"hh-task11-canonical-goals-v1",status:"complete",
   created:$created,goals:24721,theories:229,slices:16,rows:395536,
   canonical_goal_inventory_sha256:$inventory,
   canonical_sorted_anchor_body_sha256:$body,
   task10_final_certificate_sha256:$task10_final,
   task10_final_acceptance_sha256:$task10_acceptance,
   task10_independent_fold_sha256:$task10_fold,
   baseline_current_rows_byte_identical:true}
' >"$CERTIFICATE"

