#!/bin/sh
set -eu

test "$#" -eq 1 || {
  echo "usage: $0 FROZEN_RUNTIME_DIRECTORY" >&2
  exit 2
}
frozen=$1
origin=$frozen/runtime-origin.tsv
repo=${HHEVAL_TASK10_ROOT:-$(git rev-parse --show-toplevel)}
tool_root=$repo/src/holyhammer/tools
test -d "$tool_root/phase3-anchor"
test -s "$origin" && test ! -L "$origin"
rows=0
targets=$(mktemp)
trap 'rm -f "$targets"' EXIT HUP INT TERM
: > "$targets"
while IFS="$(printf '\t')" read -r target source expected extra
do
  test -n "$target" && test -n "$source" && test -n "$expected"
  test -z "${extra-}"
  case "$target:$source" in
    /*:* | *:/* | *:../* | *:*/../* | *:*/..)
      echo "unsafe runtime origin row" >&2
      exit 2
      ;;
  esac
  case "$expected" in
    *[!0-9a-f]* | "") exit 2 ;;
  esac
  test "${#expected}" -eq 64
  test -f "$frozen/$target" && test ! -L "$frozen/$target"
  test -f "$tool_root/$source" && test ! -L "$tool_root/$source"
  repo_path=${tool_root#"$repo"/}/$source
  if ! git -C "$repo" ls-files --error-unmatch "$repo_path" >/dev/null 2>&1
  then
    test -z "$(git -C "$repo" check-ignore "$repo_path" || true)" || {
      echo "runtime source is ignored and cannot be landed: $repo_path" >&2
      exit 2
    }
  fi
  test "$(sha256sum "$frozen/$target" | awk '{print $1}')" = "$expected"
  test "$(sha256sum "$tool_root/$source" | awk '{print $1}')" = \
    "$expected"
  printf '%s\n' "$target" >> "$targets"
  rows=$((rows + 1))
done < "$origin"
test "$rows" -gt 0
test "$(LC_ALL=C sort "$targets" | uniq -d | wc -l)" -eq 0

if test -s "$frozen/top-provenance.json" &&
   jq -e '.runtime_tools.files | type == "object"' \
     "$frozen/top-provenance.json" >/dev/null 2>&1; then
  jq -r '.runtime_tools.files | keys[]' "$frozen/top-provenance.json" |
  while IFS= read -r declared
  do
    case "$declared" in
      *.json | *.sha256) continue ;;
    esac
    grep -Fx "$declared" "$targets" >/dev/null || {
      echo "declared runtime tool has no tracked origin: $declared" >&2
      exit 2
    }
  done
fi

echo "tracked runtime inventory: $rows byte-identical files"
