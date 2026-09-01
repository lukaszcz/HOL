#!/bin/bash
set -Eeuo pipefail

directory=${1:?snapshot directory required}
inventory=${2:?snapshot inventory required}
test -d "$directory" && test ! -L "$directory"
test -s "$inventory" && test ! -L "$inventory"
case "$inventory" in "$directory"/*) ;; *) exit 2 ;; esac
(cd "$directory" && sha256sum -c "${inventory#"$directory"/}" \
  >/dev/null)
cmp -s \
  <(sed -n 's/^[0-9a-f]\{64\}  //p' "$inventory" | LC_ALL=C sort) \
  <(cd "$directory" && find . -type f \
    ! -path "./${inventory#"$directory"/}" -print | LC_ALL=C sort)

