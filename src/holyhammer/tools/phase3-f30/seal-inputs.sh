#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 3)); then
  echo "usage: $0 ROOT ACCEPTED_TASK10_P_INPUTS EMPTY_DESTINATION" >&2
  exit 2
fi

ROOT=$1
P_INPUTS=$2
DEST=$3
TOOLS="$ROOT/src/holyhammer/tools"
MANIFEST="$TOOLS/phase3-f30/runtime-files.tsv"
TASK10="$ROOT/.task10-evidence"

[[ -d "$ROOT" && -d "$P_INPUTS" && -s "$MANIFEST" ]]
[[ ! -e "$DEST" ]]
mkdir -p "$DEST"

while IFS=$'\t' read -r source target extra; do
  [[ -n "$source" && -n "$target" && -z "${extra-}" ]]
  [[ "$source" != /* && "$target" != /* ]]
  [[ "$source" != *../* && "$target" != *../* ]]
  mkdir -p "$DEST/$(dirname "$target")"
  cp "$TOOLS/$source" "$DEST/$target"
done <"$MANIFEST"

cp "$P_INPUTS/templates/f30-run.json" "$DEST/corpus-run.json"
cp "$P_INPUTS/main-loaded-sources.tsv" \
  "$DEST/source-path-template.tsv"
cp "$P_INPUTS/main-loaded-objects.tsv" \
  "$DEST/object-path-template.tsv"

"$TOOLS/phase3-f30/make-goal-inventory.sh" \
  "$TASK10/runs/phase3-task10-a-final-source-v12" \
  "$TASK10/certificates/a-final-source-v12" \
  "$DEST/canonical-goals.tsv" "$DEST/canonical-goals.json"

mkdir -p "$DEST/task10"
for source in \
    "$TASK10/certificates/p-final-source-v12/final-certificate.json" \
    "$TASK10/certificates/a-final-source-v12/final-acceptance.json" \
    "$TASK10/runs/phase3-task10-a-final-source-v12/result.json" \
    "$TASK10/runs/phase3-task10-a-final-source-v12/run.json"; do
  [[ -s "$source" && ! -L "$source" ]]
  cp "$source" "$DEST/task10/$(basename "$source")"
done

rehash_paths() {
  local template=$1 output=$2 relative
  : >"$output"
  while read -r _ relative extra; do
    [[ -n "$relative" && -z "${extra-}" ]]
    [[ -f "$ROOT/$relative" && ! -L "$ROOT/$relative" ]]
    printf '%s\t%s\n' "$(sha256sum "$ROOT/$relative" | cut -d' ' -f1)" \
      "$relative" >>"$output"
  done <"$template"
}

rehash_paths "$DEST/source-path-template.tsv" \
  "$DEST/main-loaded-sources.tsv"
rehash_paths "$DEST/object-path-template.tsv" \
  "$DEST/main-loaded-objects.tsv"
rm "$DEST/source-path-template.tsv" "$DEST/object-path-template.tsv"

ui_list=$(mktemp)
trap 'rm -f "$ui_list"' EXIT HUP INT TERM
find "$ROOT/src" -type f -path '*/.hol/objs/*Theory.ui' -print \
  >"$ui_list"
theory_directories="$DEST/theory-directories.tsv"
: >"$theory_directories"
while IFS= read -r theory; do
  mapfile -t matches < <(awk -v suffix="/.hol/objs/${theory}Theory.ui" '
    substr($0, length($0) - length(suffix) + 1) == suffix {print}
  ' "$ui_list")
  [[ "${#matches[@]}" == 1 ]]
  ui=${matches[0]}
  uo=${ui%.ui}.uo
  [[ -f "$uo" && ! -L "$ui" && ! -L "$uo" ]]
  directory=$(dirname "$(dirname "$(dirname "$ui")")")
  relative=$(realpath --relative-to "$ROOT" "$directory")
  [[ "$relative" != /* && "$relative" != ../* ]]
  printf '%s\t%s\t%s\t%s\n' "$theory" "$relative" \
    "$(sha256sum "$ui" | cut -d' ' -f1)" \
    "$(sha256sum "$uo" | cut -d' ' -f1)" >>"$theory_directories"
done < <(jq -r '.corpus[] | select(.theorem_count > 0) | .thy' \
  "$DEST/corpus-run.json")
[[ "$(wc -l <"$theory_directories")" == 229 ]]
rm -f "$ui_list"
trap - EXIT HUP INT TERM

runtime_origin="$DEST/runtime-origin.tsv"
: >"$runtime_origin"
while IFS=$'\t' read -r source target extra; do
  [[ -n "$source" && -n "$target" && -z "${extra-}" ]]
  printf '%s\t%s\t%s\n' "$target" "$source" \
    "$(sha256sum "$DEST/$target" | cut -d' ' -f1)" >>"$runtime_origin"
done <"$MANIFEST"

task10_inventory="$DEST/task10-inventory.tsv"
(cd "$DEST" && find task10 -type f -print0 | LC_ALL=C sort -z |
  xargs -0 sha256sum) >"$task10_inventory"

commit=$(git -C "$ROOT" rev-parse HEAD)
diff=$(git -C "$ROOT" diff --binary -- src/holyhammer | sha256sum |
  cut -d' ' -f1)
source_sha=$(sha256sum "$DEST/main-loaded-sources.tsv" | cut -d' ' -f1)
object_sha=$(sha256sum "$DEST/main-loaded-objects.tsv" | cut -d' ' -f1)
task10_sha=$(sha256sum "$task10_inventory" | cut -d' ' -f1)
goals_sha=$(sha256sum "$DEST/canonical-goals.tsv" | cut -d' ' -f1)
goals_cert_sha=$(sha256sum "$DEST/canonical-goals.json" | cut -d' ' -f1)

provers="$DEST/provers.tsv"
: >"$provers"
for row in \
    "e:/home/lukasz/.local/bin/eprover:3.2.5-ho" \
    "vampire:/home/lukasz/.local/bin/vampire:5.0.1"; do
  IFS=: read -r name path version <<<"$row"
  [[ -x "$path" ]]
  "$path" --version 2>&1 | head -1 | grep -F "$version" >/dev/null
  printf '%s\t%s\t%s\t%s\n' "$name" "$path" "$version" \
    "$(sha256sum "$path" | cut -d' ' -f1)" >>"$provers"
done

jq -Rn --arg schema "hh-task11-f30-input-v1" \
  --arg commit "$commit" --arg diff "$diff" \
  --arg sources "$source_sha" --arg objects "$object_sha" \
  --arg task10 "$task10_sha" --arg goals "$goals_sha" \
  --arg goals_cert "$goals_cert_sha" '
    [inputs | split("\t") |
      {name:.[0],path:.[1],version:.[2],sha256:.[3]}] as $provers |
    {schema:$schema,
     main:{commit:$commit,tracked_diff_sha256:$diff,
       loaded_sources_sha256:$sources,loaded_objects_sha256:$objects},
     task10_inventory_sha256:$task10,
     canonical_goal_inventory_sha256:$goals,
     canonical_goal_certificate_sha256:$goals_cert,
     accepted_task10:{p_input_inventory_sha256:
       "e8bf287fce2fbd110e04fcb84f3a99608a9ac91cb881bc704858d7fc96701427",
       a_input_inventory_sha256:
       "336147f15b76e7f920c287ec0b2721d529498df8a57c78e16e2007966891fe96"},
     envelope:{cpu_quota_cores:32,memory_high_bytes:133143986176,
       memory_max_bytes:137438953472,memory_swap_max_bytes:0,
       worker_recycle_seconds:600,worker_slots:32,
       chunk_target_goals:8,tmpfs_scratch:true,durable_copyback:true},
     provers:$provers}' <"$provers" >"$DEST/top-provenance.json"

"$DEST/runtime-provenance.sh" --external "$DEST" \
  "$DEST/external-tools.json"

(cd "$DEST" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$DEST/SHA256SUMS"
chmod -R a-w "$DEST"
printf '%s\n' "$(sha256sum "$DEST/SHA256SUMS" | cut -d' ' -f1)"
