#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 5 || {
  echo "usage: $0 RUNNER ACCEPTED_INPUTS CHALLENGER EVIDENCE_ROOT CERT" >&2
  exit 2
}
runner=$1
accepted_inputs=$2
challenger=$3
evidence=$4
certificate=$5
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM

sha () { sha256sum "$1" | awk '{print $1}'; }
tree () {
  if test ! -e "$1"; then printf '%s\n' absent; return; fi
  (cd "$1" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum) | sha256sum | awk '{print $1}'
}

for tuple in "$accepted_inputs" "$challenger"; do
  test -s "$tuple/SHA256SUMS" && test ! -L "$tuple/SHA256SUMS"
  (cd "$tuple" && sha256sum -c SHA256SUMS >/dev/null)
done
test "$(sha "$accepted_inputs/SHA256SUMS")" != \
  "$(sha "$challenger/SHA256SUMS")"
guard_line=$(grep -n '^  verify_existing_outputs_readonly$' "$runner" |
  head -1 | cut -d: -f1)
common_line=$(grep -n '^  verify_common$' "$runner" |
  head -1 | cut -d: -f1)
test "$guard_line" -lt "$common_line"

# The same tuple reaches the complete fail-closed verifier and durable resume.
env HHEVAL_TASK10_INPUTS="$accepted_inputs" \
  HHEVAL_TASK10_EVIDENCE_ROOT="$evidence" "$runner" PROBES >/dev/null

before=$(tree "$evidence")
if env HHEVAL_TASK10_INPUTS="$challenger" \
    HHEVAL_TASK10_EVIDENCE_ROOT="$evidence" "$runner" P \
    >"$work/distinct.stdout" 2>"$work/distinct.stderr"; then
  status=0
else
  status=$?
fi
test "$status" -eq 78
diagnostic='task10 P tuple mismatch: sealed input does not match accepted envelope'
test "$(grep -Fxc "$diagnostic" "$work/distinct.stderr")" -eq 1
test "$before" = "$(tree "$evidence")"

for kind in missing corrupt; do
  candidate=$work/$kind
  cp -a --reflink=auto "$accepted_inputs" "$candidate"
  chmod -R u+w "$candidate"
  if test "$kind" = missing; then
    rm "$candidate/phase3-task10-driver.sml"
  else
    printf '%s\n' corrupt >>"$candidate/phase3-task10-driver.sml"
  fi
  if env HHEVAL_TASK10_INPUTS="$candidate" \
      HHEVAL_TASK10_EVIDENCE_ROOT="$evidence" "$runner" P \
      >"$work/$kind.stdout" 2>"$work/$kind.stderr"; then
    echo "invalid $kind P candidate passed" >&2
    exit 1
  fi
  test "$before" = "$(tree "$evidence")"
done

jq -n --arg completed "$(date -u +%FT%TZ)" \
  --arg accepted "$(sha "$accepted_inputs/SHA256SUMS")" \
  --arg challenger "$(sha "$challenger/SHA256SUMS")" \
  --arg tree "$before" --arg runner "$(sha "$runner")" \
  --arg diagnostic "$diagnostic" '
  {schema:"hh-task10-p-existing-tuple-guard-selftest-v1",
   status:"complete",completed:$completed,
   accepted_input_inventory_sha256:$accepted,
   challenger_input_inventory_sha256:$challenger,
   runner_sha256:$runner,distinct_exit_status:78,
   distinct_diagnostic:$diagnostic,evidence_tree_sha256:$tree,
   same_tuple_full_verification:true,
   missing_and_corrupt_same_identity_rejected:true,
   guard_precedes_verification:true,
   distinct_before_after_identical:true}
  ' >"$certificate"
chmod 0444 "$certificate"
echo "P existing-tuple guard selftest: passed"
