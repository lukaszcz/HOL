#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 7)); then
  echo "usage: $0 SAMPLE K PROVENANCE VERIFIER REPORT METADATA FINAL" >&2
  exit 2
fi

sample=$(realpath "$1")
k=$(realpath "$2")
provenance=$(realpath "$3")
verifier=$(realpath "$4")
report=$(realpath "$5")
metadata=$(realpath "$6")
final=$7
[[ ! -e "$final" ]]
for component in "$sample" "$k" "$provenance" "$verifier"; do
  (cd "$component" && sha256sum -c SHA256SUMS >/dev/null)
done
jq -e '.schema=="hh-task12-final-v5" and .status=="complete"' \
  "$metadata" >/dev/null
mkdir "$final"
cp -a "$sample" "$final/sample"
cp -a "$k" "$final/k"
cp -a "$provenance" "$final/provenance"
cp -a "$verifier" "$final/verifier"
cp "$report" "$final/report.md"
jq --arg sample "$(sha256sum "$final/sample/SHA256SUMS" | cut -d' ' -f1)" \
  --arg k "$(sha256sum "$final/k/SHA256SUMS" | cut -d' ' -f1)" \
  --arg provenance "$(sha256sum "$final/provenance/SHA256SUMS" |
    cut -d' ' -f1)" \
  --arg verifier "$(sha256sum "$final/verifier/SHA256SUMS" |
    cut -d' ' -f1)" \
  --arg report "$(sha256sum "$final/report.md" | cut -d' ' -f1)" \
  --arg endurance "$(sha256sum \
    "$final/sample/endurance/terminal-certificate.json" | cut -d' ' -f1)" \
  --arg kterm "$(sha256sum "$final/k/terminal-service.json" |
    cut -d' ' -f1)" \
  --arg cleanup "$(sha256sum \
    "$final/provenance/cleanup-certificate.json" | cut -d' ' -f1)" \
  --arg runtime "$(sha256sum \
    "$final/provenance/runtime-provenance/certificate.json" | cut -d' ' -f1)" '
  .sample_inventory_sha256=$sample | .k_inventory_sha256=$k |
  .provenance_inventory_sha256=$provenance |
  .verifier_inventory_sha256=$verifier | .report_sha256=$report |
  .endurance_terminal_certificate_sha256=$endurance |
  .k_terminal_certificate_sha256=$kterm |
  .cleanup_certificate_sha256=$cleanup |
  .runtime_provenance_certificate_sha256=$runtime
' "$metadata" >"$final/final-certificate.json"
chmod -R a-w "$final"
"$final/verifier/verify-result.sh" "$final"
