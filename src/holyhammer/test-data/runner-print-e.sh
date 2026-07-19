#!/bin/sh

if [ "$1" = "--version" ]; then
  printf '%s\n' test
  exit 0
fi

exec /bin/cat "${0%/*}/e-theorem-chatter.out"
