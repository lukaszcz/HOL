#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 2)); then
  echo "usage: $0 SEALED_INPUTS COMPACTED_RUN" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
RUN=$(realpath "$2")
TEMP=$(mktemp -d)
cleanup() {
  chmod -R u+w "$TEMP" 2>/dev/null || true
  rm -rf "$TEMP"
}
trap cleanup EXIT HUP INT TERM

tree_digest() {
  local directory=$1
  (cd "$directory" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
}

before=$(tree_digest "$RUN")
mkdir "$TEMP/mutated-working-tree"
cp "$RUN/verifier/fold-result.sh" \
  "$TEMP/mutated-working-tree/fold-result.sh"
chmod u+w "$TEMP/mutated-working-tree/fold-result.sh"
printf '%s\n' '# deliberately unrelated working-tree mutation' \
  >>"$TEMP/mutated-working-tree/fold-result.sh"
(cd "$TEMP/mutated-working-tree" &&
  "$RUN/verifier/verify-result.sh" "$INPUTS" "$RUN")
after=$(tree_digest "$RUN")
[[ "$before" == "$after" ]]

for damage in missing tampered; do
  SHADOW="$TEMP/$damage/run"
  mkdir -p "$SHADOW"
  cp -a "$RUN/verifier" "$SHADOW/verifier"
  chmod -R u+w "$SHADOW/verifier"
  if [[ "$damage" == missing ]]; then
    rm "$SHADOW/verifier/fold-result.sh"
  else
    printf '%s\n' '# tampered' >>"$SHADOW/verifier/fold-result.sh"
  fi
  if "$SHADOW/verifier/verify-result.sh" "$INPUTS" "$SHADOW" \
      >/dev/null 2>&1; then
    echo "$damage frozen verifier dependency unexpectedly passed" >&2
    exit 1
  fi
done

[[ "$before" == "$(tree_digest "$RUN")" ]]
