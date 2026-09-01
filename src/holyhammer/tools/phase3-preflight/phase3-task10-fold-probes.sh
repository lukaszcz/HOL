#!/bin/sh
set -eu

test "$#" -eq 3 || {
  echo "usage: $0 PROBE_DIRECTORY SCOPE_PEAK_BYTES SOURCE_ROOT" >&2
  exit 2
}
directory=$1
peak=$2
source_root=$3
timing=$directory/timing.tsv

metric () {
  kind=$1
  name=$2
  column=$3
  values=$directory/.metric-$kind-$name
  awk -F '\t' -v kind="$kind" -v name="$name" -v column="$column" '
    $1 == kind && (kind != "rank" || $3 == name) {
      value = $column
      gsub(/E~/, "e-", value)
      printf "%.9f\n", value
    }
  ' "$timing" | LC_ALL=C sort -g >"$values"
  count=$(wc -l <"$values")
  test "$count" -gt 0
  p50=$(((count + 1) / 2))
  p90=$((count * 90 / 100))
  test "$p50" -gt 0 || p50=1
  test "$p90" -gt 0 || p90=1
  total=$(awk '{n += $1} END {printf "%.9f", n}' "$values")
  mean=$(awk -v count="$count" '{n += $1}
    END {printf "%.9f", n / count}' "$values")
  median=$(sed -n "${p50}p" "$values")
  ninety=$(sed -n "${p90}p" "$values")
  maximum=$(tail -n 1 "$values")
  rm -f "$values"
  jq -nc --argjson mean "$mean" --argjson p50 "$median" \
    --argjson p90 "$ninety" --argjson max "$maximum" \
    --argjson total "$total" \
    '{mean:$mean,p50:$p50,p90:$p90,max:$max,total:$total}'
}

test "$(wc -l <"$directory/schedule.tsv")" -eq 24
test "$(find "$directory/timing" -type f -name '*.tsv' | wc -l)" -eq 33
test "$(awk -F '\t' '$1 == "rank" {n++} END {print n+0}' \
  "$timing")" -eq 192
test "$(awk -F '\t' '$1 == "context" {n++} END {print n+0}' \
  "$timing")" -eq 33
test "$(awk -F '\t' '$1 == "cleanup" {n++} END {print n+0}' \
  "$timing")" -eq 33

knn=$(metric rank knn 5)
mepo=$(metric rank mepo 5)
mash=$(metric rank mash 5)
mesh=$(metric rank mesh 5)
load=$(metric context load 3)
thmdata=$(metric context thmdata 4)
nb_mepo=$(metric context nb_mepo 5)
cleanup=$(metric cleanup cleanup 3)
generated=$(find "$source_root/src" -type f \
  -name '.hheval_phase3-task10-p-*-probes_*.sml' | wc -l)

jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg envelope "$(sha256sum "$directory/envelope.json" | cut -d' ' -f1)" \
  --arg schedule "$(sha256sum "$directory/schedule.tsv" | cut -d' ' -f1)" \
  --arg timing "$(sha256sum "$timing" | cut -d' ' -f1)" \
  --argjson knn "$knn" --argjson mepo "$mepo" \
  --argjson mash "$mash" --argjson mesh "$mesh" \
  --argjson load "$load" --argjson thmdata "$thmdata" \
  --argjson nb_mepo "$nb_mepo" --argjson cleanup "$cleanup" \
  --argjson generated "$generated" --argjson peak "$peak" '
    {status:"complete",completed:$completed,envelope_sha256:$envelope,
     schedule_sha256:$schedule,timing_sha256:$timing,
     counts:{schedule_rows:24,timing_theories:33,ranking_rows:192,
       context_rows:33,cleanup_rows:33,
       generated_scripts_after_cleanup:$generated},
     ranking_seconds:{knn:$knn,mepo:$mepo,mash:$mash,mesh:$mesh},
     context_seconds:{load:$load,thmdata:$thmdata,nb_mepo:$nb_mepo,
       cleanup:$cleanup},observed_scope_peak_memory_bytes:$peak}
  ' >"$directory/result.json"
