#!/bin/bash
set -Eeuo pipefail

if test "${1:-}" = --external; then
  test "$#" -eq 3 || {
    echo "usage: $0 --external FROZEN_RUNTIME_DIRECTORY OUTPUT_JSON" >&2
    exit 2
  }
  frozen=$2
  output=$3
  inventory=$frozen/external-tools.tsv
  verify_bin=$frozen/verify-bin
  temporary=$output.partial.$$
  test -s "$frozen/top-provenance.json"
  test ! -e "$inventory" && test ! -e "$verify_bin"
  mkdir "$verify_bin"
  for tool in jq sha256sum awk sed sort cmp find wc cut paste dirname \
      basename id realpath tail
  do
    command_path=$(command -v "$tool")
    path=$(realpath "$command_path")
    test -x "$path" && test ! -L "$path"
    cp "$path" "$verify_bin/$tool"
  done
  : >"$inventory"
  for tool in bash sh jq sha256sum timeout flock git findmnt nproc xargs \
      awk sed sort cmp find wc cut paste realpath poly dirname \
      basename id head tail grep tr date mkdir cp mv rm chmod touch sleep \
      rmdir env readlink stat rg
  do
    command_path=$(command -v "$tool")
    path=$(realpath "$command_path")
    test -x "$path" && test ! -L "$path"
    version=$($path --version </dev/null 2>&1 | head -1 || true)
    test -n "$version"
    digest=$(sha256sum "$path" | awk '{print $1}')
    version_digest=$(printf '%s' "$version" | sha256sum | awk '{print $1}')
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$tool" "$command_path" \
      "$path" "$digest" "$version" "$version_digest" >>"$inventory"
  done
  jq -r '.pinned_provers[]? | [.name,.path,.sha256,.version] | @tsv' \
    "$frozen/top-provenance.json" |
    while IFS="$(printf '\t')" read -r tool command_path digest version
    do
      path=$(realpath "$command_path")
      test -x "$path" && test ! -L "$path"
      test "$(sha256sum "$path" | awk '{print $1}')" = "$digest"
      probe=$($path --version </dev/null 2>&1 | head -1)
      test -n "$probe"
      case "$probe" in *"$version"*) ;; *) exit 1 ;; esac
      version_digest=$(printf '%s' "$probe" | sha256sum |
        awk '{print $1}')
      printf 'prover:%s\t%s\t%s\t%s\t%s\t%s\n' "$tool" \
        "$command_path" "$path" "$digest" "$probe" "$version_digest" \
        >>"$inventory"
    done
  test "$(cut -f1 "$inventory" | LC_ALL=C sort -u | wc -l)" = \
    "$(wc -l <"$inventory")"
  jq -Rn --arg inventory "$(sha256sum "$inventory" | awk '{print $1}')" '
    [inputs | split("\t") |
     {name:.[0],command_path:.[1],path:.[2],sha256:.[3],version:.[4],
      version_sha256:.[5]}] as $tools |
    {schema:"hh-task10-external-tools-v1",
     inventory_path:"external-tools.tsv",
     inventory_sha256:$inventory,tools:$tools}
  ' <"$inventory" >"$temporary"
  mv "$temporary" "$output"
  chmod 0444 "$output" "$inventory"
  chmod -R a-w "$verify_bin"
  exit 0
fi

test "$#" -eq 2 || {
  echo "usage: $0 FROZEN_RUNTIME_DIRECTORY OUTPUT_JSON" >&2
  exit 2
}
frozen=$1
output=$2
origin=$frozen/runtime-origin.tsv
temporary=$output.partial.$$
trap 'rm -f "$temporary"' EXIT HUP INT TERM
test -s "$origin" && test ! -L "$origin"
jq -Rn --arg origin "$(sha256sum "$origin" | awk '{print $1}')" '
  [inputs | split("\t") |
    {key:.[0],value:{tracked_source:.[1],sha256:.[2]}}] |
  {schema:"hh-task10-runtime-tools-v2",
   origin_inventory_sha256:$origin,files:from_entries}' \
  < "$origin" > "$temporary"
jq -e '.files | length > 0 and all(.[];
  (.sha256 | test("^[0-9a-f]{64}$")) and
  (.tracked_source | type) == "string")' "$temporary" >/dev/null
mv "$temporary" "$output"
chmod 0444 "$output"
trap - EXIT HUP INT TERM
