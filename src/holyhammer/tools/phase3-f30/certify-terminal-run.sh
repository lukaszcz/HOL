#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 3)); then
  echo "usage: $0 INPUTS RUN TERMINAL_SERVICE" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
RUN=$(realpath "$2")
SERVICE=$3
TOOLS=$(dirname "$(realpath "$0")")

[[ -s "$RUN/result.json" && ! -e "$RUN/final-certificate.json" ]]
"$TOOLS/seal-terminal-envelope.sh" "$INPUTS" "$RUN" "$SERVICE"
"$TOOLS/freeze-verifier.sh" "$RUN"
"$TOOLS/make-final-certificate.sh" "$RUN" \
  "$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)" \
  "$RUN/final-certificate.json"
"$RUN/verifier/verify-result.sh" "$INPUTS" "$RUN"
"$TOOLS/compact-evidence.sh" "$INPUTS" "$RUN"
