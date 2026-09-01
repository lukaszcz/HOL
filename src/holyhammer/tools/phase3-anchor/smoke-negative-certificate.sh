#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 6 || {
  echo "usage: $0 ROOT ACCEPTED ACCEPTED_INPUTS RUNNER KIND CERTIFICATE" >&2
  exit 2
}
root=$1
accepted=$2
accepted_inputs=$3
runner=$4
kind=$5
certificate=$6
experiment=${accepted##*/}
state=/run/user/$(id -u)/holyhammer-phase3-task10/$experiment
work=$(mktemp -d)
temporary=$certificate.partial.$$
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"; \
  rm -f "$temporary"' EXIT HUP INT TERM
sha () { sha256sum "$1" | awk '{print $1}'; }
tree () {
  if test ! -e "$1"; then printf '%s\n' absent; return; fi
  (cd "$1" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum) | sha256sum | awk '{print $1}'
}

test ! -e "$state"
for required in run.json result.json invocations.jsonl
do
  test -s "$accepted/$required" && test ! -L "$accepted/$required"
done
(cd "$accepted_inputs" && sha256sum -c SHA256SUMS >/dev/null)
challenger=$work/challenger
cp -a "$accepted_inputs" "$challenger"
chmod -R u+w "$challenger"
case "$kind" in
  stale-runtime)
    printf '%s\n' '# stale-runtime-negative' >>"$challenger/run-a.sh"
    digest=$(sha "$challenger/run-a.sh")
    awk -F '\t' -v OFS='\t' -v digest="$digest" '
      $1 == "run-a.sh" {$3=digest} {print}
    ' "$challenger/runtime-origin.tsv" >"$work/runtime-origin.tsv"
    mv "$work/runtime-origin.tsv" "$challenger/runtime-origin.tsv"
    origin=$(sha "$challenger/runtime-origin.tsv")
    jq --arg digest "$digest" --arg origin "$origin" '
      .runtime_tools.files["run-a.sh"].sha256=$digest |
      .runtime_tools.origin_inventory_sha256=$origin
    ' "$challenger/top-provenance.json" >"$work/top.json"
    mv "$work/top.json" "$challenger/top-provenance.json"
    ;;
  corrupt-checkpoint)
    jq '.current_checkpoint_chain.equivalence_certificate_sha256 =
      "0000000000000000000000000000000000000000000000000000000000000000"' \
      "$challenger/top-provenance.json" >"$work/top.json"
    mv "$work/top.json" "$challenger/top-provenance.json"
    ;;
  *) echo "unknown negative kind: $kind" >&2; exit 2 ;;
esac
(cd "$challenger" && find . -type f ! -path ./SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum >SHA256SUMS)
(cd "$challenger" && sha256sum -c SHA256SUMS >/dev/null)

before=$(tree "$accepted")
invocations=$(sha "$accepted/invocations.jsonl")
diagnostic=$work/diagnostic.log
if env HHEVAL_TASK10_A_INPUTS="$challenger" \
    HHEVAL_TASK10_A_EXP="$experiment" \
    HHEVAL_TASK10_EVIDENCE_ROOT="$root/.task10-evidence" \
    "$runner" \
    >"$diagnostic" 2>&1; then
  status=0
else
  status=$?
fi
test "$status" -eq 78
test "$(cat "$diagnostic")" = \
  "task10 tuple mismatch: sealed input does not match accepted run header"
test "$before" = "$(tree "$accepted")"
test "$invocations" = "$(sha "$accepted/invocations.jsonl")"
test ! -e "$state"

jq -n --arg completed "$(date -u +%FT%TZ)" --arg kind "$kind" \
  --arg experiment "$experiment" \
  --arg input "$(sha "$accepted_inputs/SHA256SUMS")" \
  --arg challenger "$(sha "$challenger/SHA256SUMS")" \
  --arg run "$(sha "$accepted/run.json")" \
  --arg result "$(sha "$accepted/result.json")" \
  --arg tree "$before" --arg invocations "$invocations" \
  --arg runner "$(sha "$runner")" --arg verifier "$(sha "$0")" \
  --arg diagnostic "$(sha "$diagnostic")" \
  --argjson exit_status "$status" '
  {schema:"hh-task10-smoke-negative-v3",status:"rejected",
   completed:$completed,kind:$kind,experiment:$experiment,
   exit_status:$exit_status,
   accepted:{input_inventory_sha256:$input,run_header_sha256:$run,
     result_sha256:$result,directory_tree_sha256:$tree,
     invocation_log_sha256:$invocations},
   challenger:{input_inventory_sha256:$challenger},
   runner_sha256:$runner,verifier_sha256:$verifier,
   diagnostic_sha256:$diagnostic,before_after_identical:true,
   accepted_invocations_unchanged:true,tmpfs_absent:true,
   rejected_before_output:true}
' >"$temporary"
mv "$temporary" "$certificate"
chmod 0444 "$certificate"
trap - EXIT HUP INT TERM
find "$work" -depth -mindepth 1 -delete
rmdir "$work"
