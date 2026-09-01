#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 1 || {
  echo "usage: $0 TMPFS_CLEANUP_LIBRARY" >&2
  exit 2
}
library=$1
test -s "$library"
# shellcheck source=/dev/null
source "$library"
experiment=phase3-task10-cleanup-selftest-$$
state=/run/user/$(id -u)/holyhammer-phase3-task10/$experiment
work=$(mktemp -d)
trap 'find "$state" -depth -mindepth 1 -delete 2>/dev/null || true;
  rmdir "$state" 2>/dev/null || true;
  find "$work" -depth -mindepth 1 -delete; rmdir "$work"' EXIT HUP INT TERM
mkdir -p "$state/cache" "$state/scratch"
printf '%s\n' cache > "$state/cache/entry"
ln -s ../cache/entry "$state/scratch/cache-link"
dd if=/dev/zero of="$state/scratch/payload" bs=1024 count=64 status=none
printf '%s\n' durable > "$work/result.json"
binding=$(sha256sum "$work/result.json" | awk '{print $1}')
hh_task10_cleanup_tmpfs "$state" "$work/cleanup.json" "$binding"
test ! -e "$state"
jq -e --arg binding "$binding" '
  .schema == "hh-task10-tmpfs-cleanup-v1" and .status == "removed" and
  .state_files == 2 and .state_symlinks == 1 and .state_bytes > 65536 and
  .durable_binding_sha256 == $binding and
  .tmpfs_root_absent_after_cleanup == true and
  (.state_tree_sha256 | test("^[0-9a-f]{64}$"))' \
  "$work/cleanup.json" >/dev/null
echo "successful tmpfs teardown: removed after durable binding"
