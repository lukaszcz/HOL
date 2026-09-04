#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 2)); then
  echo "usage: $0 INPUTS RUN" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
RUN=$(realpath "$2")
ARTIFACTS="$RUN/artifacts/atoms"
LOGS="$RUN/log"
OUTPUT="$RUN/evidence-compaction.json"
PENDING="$RUN/evidence-compaction.pending.json"

if [[ -s "$OUTPUT" ]]; then
  "$RUN/verifier/verify-result.sh" "$INPUTS" "$RUN"
  rm -f "$PENDING"
  exit 0
fi

verifier_sha=$(sha256sum "$RUN/verifier/SHA256SUMS" |
  cut -d' ' -f1)
if [[ -s "$PENDING" ]]; then
  jq -e \
    --arg final "$(sha256sum "$RUN/final-certificate.json" | cut -d' ' -f1)" \
    --arg atoms "$(sha256sum "$RUN/atom-inventory.tsv" | cut -d' ' -f1)" \
    --arg verifier "$verifier_sha" '
    .schema == "hh-task11-evidence-compaction-v2" and
    .status == "removing" and .artifact_directories_removed == 3212 and
    .final_certificate_sha256 == $final and
    .atom_inventory_sha256 == $atoms and
    .verifier_inventory_sha256 == $verifier and
    .full_verification_before_cleanup == true
  ' "$PENDING" >/dev/null
  (cd "$RUN/verifier" && sha256sum -c SHA256SUMS >/dev/null)
else
  [[ "$(find "$ARTIFACTS" -mindepth 1 -maxdepth 1 -type d | wc -l)" == \
     3212 ]]
  "$RUN/verifier/verify-result.sh" "$INPUTS" "$RUN"
  artifact_files=$(find "$ARTIFACTS" -type f | wc -l)
  artifact_bytes=$(find "$ARTIFACTS" -type f -printf '%s\n' |
    awk '{sum += $1} END {print sum+0}')
  artifact_blocks=$(du -sb "$ARTIFACTS" | cut -f1)
  log_files=$(find "$LOGS" -type f | wc -l)
  log_bytes=$(find "$LOGS" -type f -printf '%s\n' |
    awk '{sum += $1} END {print sum+0}')
  tree_inventory=$(jq -r '[.atom,.artifact_tree_sha256] | @tsv' \
    "$RUN"/atom-certificates/*.json | LC_ALL=C sort | sha256sum |
    cut -d' ' -f1)
  final_sha=$(sha256sum "$RUN/final-certificate.json" | cut -d' ' -f1)
  atom_sha=$(sha256sum "$RUN/atom-inventory.tsv" | cut -d' ' -f1)
  jq -n --arg started "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg final "$final_sha" --arg atoms "$atom_sha" \
    --arg trees "$tree_inventory" --arg verifier "$verifier_sha" \
    --argjson directories 3212 --argjson files "$artifact_files" \
    --argjson bytes "$artifact_bytes" --argjson blocks "$artifact_blocks" \
    --argjson log_files "$log_files" --argjson log_bytes "$log_bytes" '
    {schema:"hh-task11-evidence-compaction-v2",status:"removing",
     started:$started,artifact_directories_removed:$directories,
     artifact_files_removed:$files,artifact_bytes_removed:$bytes,
     artifact_allocated_bytes_removed:$blocks,log_files_removed:$log_files,
     log_bytes_removed:$log_bytes,artifact_tree_inventory_sha256:$trees,
     final_certificate_sha256:$final,atom_inventory_sha256:$atoms,
     verifier_inventory_sha256:$verifier,
     predecessor_lineage_inventory_sha256:null,
     predecessor_final_certificate_sha256:null,
     predecessor_compaction_certificate_sha256:null,
     full_verification_before_cleanup:true,
     retained_evidence_reverified_after_compaction:false,
     retained_journals_and_atom_certificates:true}
  ' >"$PENDING.partial"
  mv "$PENDING.partial" "$PENDING"
  chmod 0444 "$PENDING"
fi

if [[ -d "$ARTIFACTS" ]]; then
  chmod -R u+w "$ARTIFACTS"
  find "$ARTIFACTS" -depth -mindepth 1 -delete
  rmdir "$ARTIFACTS"
fi
[[ ! -d "$RUN/artifacts" ]] || rmdir "$RUN/artifacts"
if [[ -d "$LOGS" ]]; then
  chmod -R u+w "$LOGS"
  find "$LOGS" -depth -mindepth 1 -delete
  rmdir "$LOGS"
fi
[[ ! -e "$RUN/artifacts" && ! -e "$RUN/log" ]]

jq --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" '
  .status = "removed" | .completed = $completed |
  .artifacts_absent_after_cleanup = true |
  .logs_absent_after_cleanup = true |
  .retained_evidence_reverified_after_compaction = true
' "$PENDING" >"$OUTPUT.partial"
mv "$OUTPUT.partial" "$OUTPUT"
chmod 0444 "$OUTPUT"
rm -f "$PENDING"
"$RUN/verifier/verify-result.sh" "$INPUTS" "$RUN"
