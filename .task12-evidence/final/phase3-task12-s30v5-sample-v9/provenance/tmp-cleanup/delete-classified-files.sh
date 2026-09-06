#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 CLASSIFICATION.tsv" >&2
  exit 64
fi

manifest=$1
expected_uid=$(id -u)

while IFS=$'\t' read -r path uid kind size digest decision reason; do
  [[ $path != path ]] || continue
  [[ $decision == delete ]] || continue
  [[ $path == /tmp/* ]] || {
    echo "refusing non-/tmp path: $path" >&2
    exit 65
  }
  leaf=${path#/tmp/}
  [[ -n $leaf && $leaf != */* ]] || {
    echo "refusing non-direct /tmp child: $path" >&2
    exit 65
  }
  [[ ${leaf,,} =~ (phase3|task10|task11|task12) ]] || {
    echo "refusing non-task basename: $path" >&2
    exit 65
  }
  [[ $uid == "$expected_uid" &&
     ( $kind == "regular file" || $kind == "regular empty file" ) ]] || {
    echo "refusing unexpected ownership/type: $path" >&2
    exit 65
  }
  [[ ! -L $path && -f $path ]] || {
    echo "refusing missing/non-regular/symlink path: $path" >&2
    exit 66
  }
  canonical=$(realpath -e -- "$path")
  [[ $canonical == "$path" ]] || {
    echo "refusing canonical-path mismatch: $path" >&2
    exit 66
  }
  [[ $(stat -c %u -- "$path") == "$uid" ]] || exit 67
  [[ $(stat -c %s -- "$path") == "$size" ]] || exit 67
  [[ $(sha256sum -- "$path" | cut -d ' ' -f 1) == "$digest" ]] || exit 67
  rm -f -- "$path"
  [[ ! -e $path && ! -L $path ]] || exit 68
done < "$manifest"
