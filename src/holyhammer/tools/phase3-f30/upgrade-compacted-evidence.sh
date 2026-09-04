#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 3)); then
  echo "usage: $0 INPUTS COMPACTED_RUN TERMINAL_SERVICE" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
RUN=$(realpath "$2")
SERVICE=$3
TOOLS=$(dirname "$(realpath "$0")")
LINEAGE="$RUN/lineage/v3"
[[ -s "$LINEAGE/SHA256SUMS" ]]
(cd "$LINEAGE" && sha256sum -c SHA256SUMS >/dev/null)
[[ ! -e "$RUN/artifacts" && ! -e "$RUN/log" ]]

if [[ ! -e "$RUN/envelope-start.json" ]]; then
  "$TOOLS/seal-terminal-envelope.sh" "$INPUTS" "$RUN" "$SERVICE"
else
  [[ -s "$RUN/terminal-service.json" && -s "$RUN/terminal-service.log" ]]
fi
"$TOOLS/make-auxiliary-evidence.sh" "$RUN" \
  "$RUN/canonical-goals.tsv" "$RUN/excluded-extra-goals.tsv.new" \
  "$RUN/criterion-b-investigation.md.new"
chmod u+w "$RUN/excluded-extra-goals.tsv" \
  "$RUN/criterion-b-investigation.md"
mv "$RUN/excluded-extra-goals.tsv.new" "$RUN/excluded-extra-goals.tsv"
mv "$RUN/criterion-b-investigation.md.new" \
  "$RUN/criterion-b-investigation.md"
chmod 0444 "$RUN/excluded-extra-goals.tsv" \
  "$RUN/criterion-b-investigation.md"

if [[ -d "$RUN/verifier" ]]; then
  chmod -R u+w "$RUN/verifier"
  find "$RUN/verifier" -depth -mindepth 1 -delete
  rmdir "$RUN/verifier"
fi
"$TOOLS/freeze-verifier.sh" "$RUN"
for item in final-certificate.json evidence-compaction.json; do
  if [[ -e "$RUN/$item" ]]; then
    chmod u+w "$RUN/$item"
    rm "$RUN/$item"
  fi
done
"$TOOLS/make-final-certificate.sh" "$RUN" \
  "$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)" \
  "$RUN/final-certificate.json"

OLD_COMPACTION="$LINEAGE/evidence-compaction.json"
jq --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg final "$(sha256sum "$RUN/final-certificate.json" | cut -d' ' -f1)" \
  --arg verifier "$(sha256sum "$RUN/verifier/SHA256SUMS" |
    cut -d' ' -f1)" \
  --arg lineage "$(sha256sum "$LINEAGE/SHA256SUMS" | cut -d' ' -f1)" \
  --arg predecessor_final "$(sha256sum "$LINEAGE/final-certificate.json" |
    cut -d' ' -f1)" \
  --arg predecessor_compaction "$(sha256sum "$OLD_COMPACTION" |
    cut -d' ' -f1)" '
  .schema = "hh-task11-evidence-compaction-v2" |
  .completed = $completed | .final_certificate_sha256 = $final |
  .verifier_inventory_sha256 = $verifier |
  .predecessor_lineage_inventory_sha256 = $lineage |
  .predecessor_final_certificate_sha256 = $predecessor_final |
  .predecessor_compaction_certificate_sha256 = $predecessor_compaction |
  .retained_evidence_reverified_after_compaction = true |
  del(.full_verifier_sha256)
' "$OLD_COMPACTION" >"$RUN/evidence-compaction.json"
chmod 0444 "$RUN/evidence-compaction.json"

if [[ -e "$RUN/full-artifact-verifier.sh" ]]; then
  chmod u+w "$RUN/full-artifact-verifier.sh"
  rm "$RUN/full-artifact-verifier.sh"
fi
"$RUN/verifier/verify-result.sh" "$INPUTS" "$RUN"
