#!/bin/sh
set -eu
ALIAS=/home/lukasz/dev/HOL/worktrees/simplifier
AUTO_BIND="--bind /tmp/task25-isolated/src/auto $ALIAS/src/auto"
if [ "${TASK25_NO_AUTO:-0}" = 1 ]; then AUTO_BIND=""; fi
exec bwrap --bind / / --dev /dev --tmpfs /home --dir /home/lukasz \
 --dir /home/lukasz/dev/HOL/worktrees \
 --ro-bind /home/lukasz/work /home/lukasz/work \
 --bind /tmp/task25-core "$ALIAS" \
 $AUTO_BIND \
 -- sh -c 'cd /home/lukasz/dev/HOL/worktrees/simplifier; export HOLDIR="$PWD" PATH="$PWD/bin:$PATH"; exec "$@"' sh "$@"
