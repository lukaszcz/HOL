#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 3)); then
  echo "usage: $0 HOL_ROOT ATOMS OUTPUT" >&2
  exit 2
fi

root=$(realpath "$1")
atoms=$(realpath "$2")
output=$3
expected_commit=c5db8bb9cb4399c871fb011cf4b1c523cbec8d27
[[ ! -e "$output" && "$(git -C "$root" rev-parse HEAD)" == \
  "$expected_commit" ]]
mkdir "$output"

# The accepted runtime had no tracked changes.  Keep an explicit (empty)
# allowed-diff manifest rather than treating a self-reported aggregate as an
# authority.
git -C "$root" diff --quiet HEAD -- .
git -C "$root" diff --cached --quiet HEAD -- .
: >"$output/allowed-source-diff.tsv"

(cd "$root" &&
  find src -path '*/.hol/objs/*' -type f \
    \( -name '*.uo' -o -name '*.ui' -o -name '*.dat' -o \
       -name '*.sml' -o -name '*.sig' -o -name '*.cachekey' \) -print0 |
    LC_ALL=C sort -z | xargs -0 sha256sum) \
  >"$output/hol-runtime-objects.tsv"

temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT HUP INT TERM
awk -F '\t' '!seen[$2]++ {print $2 "\t" $5}' "$atoms" |
  LC_ALL=C sort >"$temp/targets.tsv"
: >"$output/target-theory-objects.tsv"
while IFS=$'\t' read -r theory directory extra; do
  [[ -z "${extra-}" ]]
  case "$directory" in
    "$root"/*) relative=${directory#"$root"/} ;;
    *) echo "target theory is outside HOL root: $directory" >&2; exit 1 ;;
  esac
  for extension in cachekey dat sig sml ui uo; do
    path="$relative/.hol/objs/${theory}Theory.$extension"
    [[ -f "$root/$path" && ! -L "$root/$path" ]]
    printf '%s  %s\n' "$(sha256sum "$root/$path" | cut -d' ' -f1)" \
      "$path" >>"$output/target-theory-objects.tsv"
  done
done <"$temp/targets.tsv"

{
  for command in awk bash cat cmp cp cut date dirname env find git grep head \
    id journalctl jq mkdir mktemp mv realpath rm rmdir sed sha256sum sort \
    stat tail timeout tr wc xargs; do
    command -v "$command"
  done
  for executable in "$root/bin/hol" \
    "$(command -v bash)" "$(command -v git)" "$(command -v jq)"; do
    ldd "$executable" | awk '
      $2 == "=>" && $3 ~ /^\// {print $3}
      $1 ~ /^\// {print $1}
    '
  done
} | while IFS= read -r path; do realpath "$path"; done |
  LC_ALL=C sort -u >"$temp/host-paths"
: >"$output/host-runtime.tsv"
while IFS= read -r path; do
  [[ -f "$path" && ! -L "$path" ]]
  printf '%s  %s\n' "$(sha256sum "$path" | cut -d' ' -f1)" "$path" \
    >>"$output/host-runtime.tsv"
done <"$temp/host-paths"

jq -n --arg commit "$expected_commit" \
  --arg allowed "$(sha256sum "$output/allowed-source-diff.tsv" |
    cut -d' ' -f1)" \
  --arg objects "$(sha256sum "$output/hol-runtime-objects.tsv" |
    cut -d' ' -f1)" \
  --arg targets "$(sha256sum "$output/target-theory-objects.tsv" |
    cut -d' ' -f1)" \
  --arg host "$(sha256sum "$output/host-runtime.tsv" | cut -d' ' -f1)" \
  --argjson theories "$(wc -l <"$temp/targets.tsv")" \
  --argjson object_count "$(wc -l <"$output/hol-runtime-objects.tsv")" \
  --argjson target_count "$(wc -l <"$output/target-theory-objects.tsv")" \
  --argjson host_count "$(wc -l <"$output/host-runtime.tsv")" '
  {schema:"hh-task12-runtime-root-v1",status:"complete",
   accepted_commit:$commit,allowed_tracked_diff_count:0,
   allowed_source_diff_sha256:$allowed,
   hol_runtime_objects:{count:$object_count,sha256:$objects},
   target_theory_objects:{theories:$theories,count:$target_count,
     sha256:$targets},
   host_runtime:{count:$host_count,sha256:$host}}
' >"$output/runtime-root-certificate.json"
chmod -R a-w "$output"
