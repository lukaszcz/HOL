#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 2)); then
  echo "usage: $0 INPUTS RUN" >&2
  exit 2
fi

RUN=$(realpath "$2")
TOOLS=$(dirname "$(realpath "$0")")
FROZEN="$RUN/verifier"
if [[ "$TOOLS" != "$FROZEN" && -x "$FROZEN/verify-result.sh" ]]; then
  exec "$FROZEN/verify-result.sh" "$@"
fi
exec "$TOOLS/verify-certified-result.sh" "$@"
