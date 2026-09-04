#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 1)); then
  echo "usage: $0 RUN" >&2
  exit 2
fi

RUN=$(realpath "$1")
TOOLS=$(dirname "$(realpath "$0")")
DEST="$RUN/verifier"
[[ ! -e "$DEST" ]]
mkdir "$DEST"

for item in verify-result.sh verify-certified-result.sh verify-inputs.sh \
    fold-result.sh investigate-shape.sh make-final-certificate.sh \
    make-auxiliary-evidence.sh; do
  [[ -s "$TOOLS/$item" && ! -L "$TOOLS/$item" ]]
  cp "$TOOLS/$item" "$DEST/$item"
done
(cd "$DEST" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$DEST/SHA256SUMS"
chmod -R a-w "$DEST"
