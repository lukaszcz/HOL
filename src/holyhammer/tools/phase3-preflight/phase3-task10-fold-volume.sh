#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 5 || {
  echo "usage: $0 f30|s30v5 EXPORT_TREE INVENTORY VOLUME RESULT" >&2
  exit 2
}

variant=$1
tree=$2
inventory=$3
volume=$4
result=$5
test -d "$tree" && test ! -L "$tree"
for output in "$inventory" "$volume" "$result"
do
  test ! -e "$output" || {
    echo "volume-fold output already exists: $output" >&2
    exit 2
  }
done

case "$variant" in
  f30)
    expected_total=384
    expected_knn=96
    expected_mepo=96
    expected_mash=96
    expected_mesh=96
    ;;
  s30v5)
    expected_total=792
    expected_knn=528
    expected_mepo=66
    expected_mash=66
    expected_mesh=132
    ;;
  *) echo "unknown preflight variant: $variant" >&2; exit 2 ;;
esac

work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM
raw=$work/raw.tsv
sorted=$work/inventory.tsv
: > "$raw"

test -z "$(find "$tree" -type l -name atp_in -print -quit)" || {
  echo "symlinked atp_in is forbidden" >&2
  exit 2
}

find "$tree" -type f -name atp_in -print0 | while IFS= read -r -d '' file
do
  relative=${file#"$tree"/}
  test "$relative" != "$file"
  parent=$(basename "$(dirname "$file")")
  filter=
  prover=
  case "$variant" in
    f30)
      case "$relative" in
        scratch/pb/*/*/atp_in) ;;
        *) echo "unexpected F30 export path: $relative" >&2; exit 2 ;;
      esac
      filter=${parent##*-}
      prefix=${parent%-"$filter"}
      prover=${prefix##*-}
      prefix=${prefix%-"$prover"}
      case "$prefix" in *-p-f30) ;; *)
        echo "malformed F30 export metadata: $relative" >&2
        exit 2
      esac
      ;;
    s30v5)
      case "$relative" in
        theory-*/problems/*/atp_in) ;;
        *) echo "unexpected S30 export path: $relative" >&2; exit 2 ;;
      esac
      prover=${parent%%.*}
      rest=${parent#*.}
      test "$rest" != "$parent"
      filter=${rest%%.*}
      test "$filter" != "$rest"
      ;;
  esac
  case "$prover" in e|vampire|zipperposition) ;; *)
    echo "unknown prover in export metadata: $relative" >&2
    exit 2
  esac
  case "$filter" in knn|mepo|mash|mesh) ;; *)
    echo "unknown filter in export metadata: $relative" >&2
    exit 2
  esac
  sha=$(sha256sum "$file" | awk '{print $1}')
  bytes=$(wc -c < "$file")
  printf '%s\t%s\t%s\t%s\t%s\n' \
    "$variant" "$filter" "$sha" "$bytes" "$relative" >> "$raw"
done

LC_ALL=C sort -t "$(printf '\t')" -k5,5 "$raw" > "$sorted"
test "$(wc -l < "$raw")" -eq "$expected_total" || {
  echo "missing or extra $variant export files" >&2
  exit 2
}
test "$(cut -f5 "$sorted" | LC_ALL=C sort -u | wc -l)" -eq \
  "$expected_total" || {
  echo "duplicate $variant export inventory key" >&2
  exit 2
}

awk -F '\t' '{count[$2]++; bytes[$2]+=$4}
  END {for (filter in count)
    print filter "\t" count[filter] "\t" bytes[filter]}' \
  "$sorted" | LC_ALL=C sort > "$work/volume.tsv"
for binding in knn:$expected_knn mepo:$expected_mepo \
               mash:$expected_mash mesh:$expected_mesh
do
  filter=${binding%%:*}
  expected=${binding#*:}
  actual=$(awk -F '\t' -v filter="$filter" \
    '$1 == filter {print $2}' "$work/volume.tsv")
  test "$actual" = "$expected" || {
    echo "unexpected $variant $filter export count: ${actual:-missing}" >&2
    exit 2
  }
done

cp "$sorted" "$inventory"
cp "$work/volume.tsv" "$volume"
inventory_sha=$(sha256sum "$inventory" | awk '{print $1}')
volume_sha=$(sha256sum "$volume" | awk '{print $1}')
filters=$(jq -Rn '
  [inputs | split("\t") |
    {filter:.[0],count:(.[1]|tonumber),bytes:(.[2]|tonumber)}]' \
  < "$volume")
jq -n --arg variant "$variant" --arg inventory "$inventory_sha" \
  --arg volume "$volume_sha" --argjson total "$expected_total" \
  --argjson filters "$filters" '
    {schema:"hh-task10-export-volume-v1",variant:$variant,
     export_files:$total,inventory_sha256:$inventory,
     volume_sha256:$volume,filters:$filters}' > "$result"

trap - EXIT HUP INT TERM
find "$work" -depth -mindepth 1 -delete
rmdir "$work"
