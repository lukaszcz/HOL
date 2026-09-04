#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 1)); then
  echo "usage: $0 COMPACTED_RUN" >&2
  exit 2
fi

RUN=$(realpath "$1")
TOOLS=$(dirname "$(realpath "$0")")
DEST="$RUN/lineage/v3"
[[ ! -e "$DEST" ]]
mkdir -p "$DEST"

for item in envelope.json final-certificate.json evidence-compaction.json \
    full-artifact-verifier.sh; do
  [[ -s "$RUN/$item" && ! -L "$RUN/$item" ]]
  cp "$RUN/$item" "$DEST/$item"
done
for item in fold-result.sh investigate-shape.sh \
    make-final-certificate.sh; do
  cp "$TOOLS/$item" "$DEST/$item"
done

FINAL="$DEST/final-certificate.json"
jq -e \
  --arg fold "$(sha256sum "$DEST/fold-result.sh" | cut -d' ' -f1)" \
  --arg shape "$(sha256sum "$DEST/investigate-shape.sh" | cut -d' ' -f1)" \
  --arg maker "$(sha256sum "$DEST/make-final-certificate.sh" |
    cut -d' ' -f1)" '
  .schema == "hh-task11-f30-final-v3" and .status == "complete" and
  .fold_tool_sha256 == $fold and .shape_tool_sha256 == $shape and
  .certificate_tool_sha256 == $maker
' "$FINAL" >/dev/null
jq -e \
  --arg final "$(sha256sum "$FINAL" | cut -d' ' -f1)" \
  --arg verifier "$(sha256sum "$DEST/full-artifact-verifier.sh" |
    cut -d' ' -f1)" '
  .schema == "hh-task11-evidence-compaction-v1" and
  .status == "removed" and .full_verification_before_cleanup == true and
  .final_certificate_sha256 == $final and
  .full_verifier_sha256 == $verifier
' "$DEST/evidence-compaction.json" >/dev/null

(cd "$DEST" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$DEST/SHA256SUMS"
chmod -R a-w "$DEST"
