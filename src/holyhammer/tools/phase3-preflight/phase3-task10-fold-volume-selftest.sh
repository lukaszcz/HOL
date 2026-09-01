#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 1 || {
  echo "usage: $0 FOLD_TOOL" >&2
  exit 2
}
tool=$1
test -x "$tool"
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM

make_file() {
  local file=$1 contents=$2
  mkdir -p "$(dirname "$file")"
  printf '%s' "$contents" > "$file"
}

for filter in knn mepo mash mesh
do
  for ((i = 0; i < 96; i++))
  do
    make_file "$work/f30/scratch/pb/thy$i/g$i-p-f30-e-$filter/atp_in" \
      "$filter-$i"
  done
done
"$tool" f30 "$work/f30" "$work/f30-inventory.tsv" \
  "$work/f30-volume.tsv" "$work/f30-result.json"
jq -e '.export_files == 384 and
  ([.filters[].count] | add) == 384' "$work/f30-result.json" >/dev/null

for binding in knn:16 mepo:2 mash:2 mesh:4
do
  filter=${binding%%:*}
  per_theory=${binding#*:}
  for ((theory = 0; theory < 33; theory++))
  do
    for ((i = 0; i < per_theory; i++))
    do
      make_file \
        "$work/s30/theory-t$theory/problems/e.$filter.fof.x.$i/atp_in" \
        "$filter-$theory-$i"
    done
  done
done
"$tool" s30v5 "$work/s30" "$work/s30-inventory.tsv" \
  "$work/s30-volume.tsv" "$work/s30-result.json"
jq -e '.export_files == 792 and
  ([.filters[].count] | add) == 792' "$work/s30-result.json" >/dev/null

cp -a "$work/f30" "$work/f30-missing"
find "$work/f30-missing" -type f -name atp_in -print -quit | xargs rm
if "$tool" f30 "$work/f30-missing" "$work/missing-inventory.tsv" \
     "$work/missing-volume.tsv" "$work/missing-result.json" \
     >"$work/missing.log" 2>&1
then
  echo "missing export unexpectedly passed" >&2
  exit 1
fi
grep -F "missing or extra f30 export files" "$work/missing.log" >/dev/null

cp -a "$work/s30" "$work/s30-unknown"
unknown=$(find "$work/s30-unknown" -type f -name atp_in -print -quit)
parent=$(dirname "$unknown")
mv "$parent" "${parent%/*}/e.unknown.fof.x.0"
if "$tool" s30v5 "$work/s30-unknown" "$work/unknown-inventory.tsv" \
     "$work/unknown-volume.tsv" "$work/unknown-result.json" \
     >"$work/unknown.log" 2>&1
then
  echo "unknown filter unexpectedly passed" >&2
  exit 1
fi
grep -F "unknown filter in export metadata" "$work/unknown.log" >/dev/null

echo "preflight export volume layouts: OK"
