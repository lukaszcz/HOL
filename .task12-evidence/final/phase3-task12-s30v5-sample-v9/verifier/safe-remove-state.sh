#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 1)); then
  echo "usage: $0 TASK12_STATE_CHILD" >&2
  exit 2
fi

target=$1
[[ -n "$target" ]]
uid=$(id -u)
base="/run/user/$uid/holyhammer-phase3-task12"
case "$target" in
  "$base"/*) ;;
  *) echo "target is outside the TASK12 namespace" >&2; exit 2 ;;
esac
[[ ! -L "$target" ]]
resolved_base=$(realpath -m "$base")
resolved=$(realpath -m "$target")
[[ "$resolved_base" == "$base" && "$resolved" == "$base/"* ]]
[[ "$(dirname "$resolved")" == "$base" ]]
case $(basename "$resolved") in
  phase3-task12-*|k-revised-*) ;;
  *) echo "not an exact TASK12-owned state child: $target" >&2; exit 2 ;;
esac

if [[ -e "$target" ]]; then
  chmod -R u+w "$target"
  rm -rf -- "$target"
fi
[[ ! -e "$target" && ! -L "$target" ]]
