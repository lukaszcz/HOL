#!/bin/sh
exec bwrap --bind / / --dev /dev --tmpfs /home --dir /home/lukasz \
 --dir /home/lukasz/dev/HOL/worktrees \
 --bind /home/lukasz/work /home/lukasz/work \
 --bind /home/lukasz/work/HOL/worktrees/simplifier \
 /home/lukasz/dev/HOL/worktrees/simplifier -- sh -c '
  cd /home/lukasz/dev/HOL/worktrees/simplifier || exit
  export HOLDIR="$PWD" PATH="$PWD/bin:$PATH"
  exec "$@"
' sh "$@"
