#!/bin/sh

hh_task10_tree_digest () {
  directory=$1
  test -d "$directory" && test ! -L "$directory"
  (cd "$directory" && {
    find . -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum
    find . -type l -printf 'symlink\t%p\t%l\n' | LC_ALL=C sort
  }) | sha256sum | awk '{print $1}'
}

hh_task10_cleanup_tmpfs () {
  state=$1
  certificate=$2
  durable_binding=$3
  prefix=/run/user/$(id -u)/holyhammer-phase3-task10/
  case "$state" in
    "$prefix"?*) ;;
    *) echo "unsafe Task10 tmpfs cleanup root: $state" >&2; return 2 ;;
  esac
  case "$durable_binding" in
    *[!0-9a-f]* | "") return 2 ;;
  esac
  test "${#durable_binding}" -eq 64
  test -d "$state" && test ! -L "$state"
  test ! -e "$certificate"
  temporary=$certificate.partial.$$
  state_digest=$(hh_task10_tree_digest "$state")
  files=$(find "$state" -type f | wc -l)
  symlinks=$(find "$state" -type l | wc -l)
  bytes=$(find "$state" -type f -printf '%s\n' |
    awk '{total += $1} END {print total+0}')
  jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg state "$state" --arg state_digest "$state_digest" \
    --arg durable "$durable_binding" --argjson files "$files" \
    --argjson symlinks "$symlinks" --argjson bytes "$bytes" '
      {schema:"hh-task10-tmpfs-cleanup-v1",status:"removed",
       completed:$completed,state_root:$state,state_tree_sha256:$state_digest,
       state_files:$files,state_symlinks:$symlinks,state_bytes:$bytes,
       durable_binding_sha256:$durable,tmpfs_root_absent_after_cleanup:true}' \
    > "$temporary"
  find "$state" -depth -mindepth 1 -delete
  rmdir "$state"
  test ! -e "$state"
  mv "$temporary" "$certificate"
  chmod 0444 "$certificate"
}
