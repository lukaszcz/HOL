#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 3)); then
  echo "usage: $0 INPUTS RUN OUTPUT" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
RUN=$(realpath "$2")
OUTPUT=$3
TEMP="$OUTPUT.partial.$$"
trap 'rm -f "$TEMP"' EXIT HUP INT TERM

tree_digest() {
  local directory=$1
  (cd "$directory" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
}

state=$(jq -r '.state_root' "$RUN/envelope.json")
[[ ! -e "$state" ]]
before=$(tree_digest "$RUN")
before_files=$(find "$RUN" -type f | wc -l)
before_bytes=$(find "$RUN" -type f -printf '%s\n' |
  awk '{sum += $1} END {print sum+0}')
"$RUN/verifier/verify-result.sh" "$INPUTS" "$RUN"
after=$(tree_digest "$RUN")
after_files=$(find "$RUN" -type f | wc -l)
after_bytes=$(find "$RUN" -type f -printf '%s\n' |
  awk '{sum += $1} END {print sum+0}')
[[ "$before" == "$after" && "$before_files" == "$after_files" &&
   "$before_bytes" == "$after_bytes" && ! -e "$state" ]]

jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg tree "$before" --argjson files "$before_files" \
  --argjson bytes "$before_bytes" \
  --arg input "$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)" \
  --arg final "$(sha256sum "$RUN/final-certificate.json" | cut -d' ' -f1)" \
  --arg compact "$(sha256sum "$RUN/evidence-compaction.json" |
    cut -d' ' -f1)" \
  --arg verifier "$(sha256sum "$RUN/verifier/SHA256SUMS" |
    cut -d' ' -f1)" '
  {schema:"hh-task11-durable-resume-v2",status:"complete",
   completed:$completed,input_inventory_sha256:$input,
   final_certificate_sha256:$final,evidence_compaction_sha256:$compact,
   verifier_inventory_sha256:$verifier,directory_tree_sha256:$tree,
   files:$files,bytes:$bytes,durable_only:true,
   tmpfs_absent_before_and_after:true,
   immutable_results_byte_identical:true}
' >"$TEMP"
mv "$TEMP" "$OUTPUT"
chmod 0444 "$OUTPUT"
trap - EXIT HUP INT TERM
