#!/bin/bash
set -Eeuo pipefail

root=${1:-$(git rev-parse --show-toplevel)}
tab=$(printf '\t')
while IFS= read -r script; do
  if LC_ALL=C grep -n "$tab" "$script" >/dev/null; then
    echo "literal TAB byte in tracked source script: $script" >&2
    exit 1
  fi
done < <(find "$root/src/holyhammer/tools" -type f -name '*.sh' |
  LC_ALL=C sort)
printf '%s\n' "tracked source scripts contain no literal TAB bytes"

