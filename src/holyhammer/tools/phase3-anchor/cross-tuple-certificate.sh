#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 5 || {
  echo "usage: $0 ACCEPTED_OUTPUT ACCEPTED_INPUTS CHALLENGER RUNNER CERTIFICATE" \
    >&2
  exit 2
}
accepted=$1
accepted_inputs=$2
challenger=$3
runner=$4
certificate=$5
experiment=${accepted##*/}
state=/run/user/$(id -u)/holyhammer-phase3-task10/$experiment
stdout_log=${certificate%.json}.stdout.log
stderr_log=${certificate%.json}.stderr.log
temporary=$certificate.partial.$$
seal_actual=
seal_listed=
readonly expected_status=78
expected_diagnostic='task10 tuple mismatch: sealed input does not match '
expected_diagnostic+='accepted run header'
readonly expected_diagnostic
cleanup () {
  rm -f "$temporary"
  test -z "$seal_actual" || rm -f "$seal_actual"
  test -z "$seal_listed" || rm -f "$seal_listed"
}
trap cleanup EXIT HUP INT TERM

sha () { sha256sum "$1" | awk '{print $1}'; }

tree_digest () {
  local directory=$1
  if test ! -e "$directory"; then
    printf '%s\n' absent
    return
  fi
  test -d "$directory" && test ! -L "$directory"
  (cd "$directory" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum) | sha256sum | awk '{print $1}'
}

tree_files () {
  test ! -d "$1" && { printf '0\n'; return; }
  find "$1" -type f | wc -l
}

tree_bytes () {
  test ! -d "$1" && { printf '0\n'; return; }
  find "$1" -type f -printf '%s\n' |
    awk '{bytes += $1} END {print bytes+0}'
}

verify_sealed_tuple () {
  local tuple=$1 actual listed target source digest extra
  test -d "$tuple" && test ! -L "$tuple"
  for required in SHA256SUMS top-provenance.json runtime-origin.tsv run-a.sh
  do
    test -s "$tuple/$required" && test ! -L "$tuple/$required"
  done
  test -z "$(find "$tuple" -type l -print -quit)"
  actual=$(mktemp)
  listed=$(mktemp)
  seal_actual=$actual
  seal_listed=$listed
  (cd "$tuple" && find . -type f ! -path ./SHA256SUMS -printf '%P\n' |
    LC_ALL=C sort) >"$actual"
  awk '
    NF != 2 || $1 !~ /^[0-9a-f]{64}$/ || $2 == "" ||
    $2 ~ /^\// || $2 ~ /(^|\/)\.\.($|\/)/ || seen[$2]++ {exit 1}
    {path=$2; sub(/^\.\//,"",path); print path}
    END {if (NR == 0) exit 1}
  ' "$tuple/SHA256SUMS" | LC_ALL=C sort >"$listed"
  cmp -s "$actual" "$listed"
  (cd "$tuple" && sha256sum -c SHA256SUMS >/dev/null)
  while IFS=$'\t' read -r target source digest extra; do
    test -n "$target" && test -n "$source" && test -n "$digest"
    test -z "${extra:-}"
    test "$(sha "$tuple/$target")" = "$digest"
    test "$(jq -r --arg target "$target" \
      '.runtime_tools.files[$target].tracked_source' \
      "$tuple/top-provenance.json")" = "$source"
    test "$(jq -r --arg target "$target" \
      '.runtime_tools.files[$target].sha256' \
      "$tuple/top-provenance.json")" = "$digest"
  done <"$tuple/runtime-origin.tsv"
  test "$(wc -l <"$tuple/runtime-origin.tsv")" -eq \
    "$(jq '.runtime_tools.files | length' \
      "$tuple/top-provenance.json")"
  env HHEVAL_TASK10_A_INPUTS="$tuple" \
    HHEVAL_TASK10_A_EXP="cross-tuple-input-verification" \
    "$runner" VERIFY_INPUTS >/dev/null
  rm -f "$actual" "$listed"
  seal_actual=
  seal_listed=
}

for required in run.json result.json final-certificate.json invocations.jsonl
do
  test -s "$accepted/$required" && test ! -L "$accepted/$required"
done
test -x "$runner" && test ! -L "$runner"
verify_sealed_tuple "$accepted_inputs"
verify_sealed_tuple "$challenger"
cmp -s "$accepted/run.json" "$accepted_inputs/top-provenance.json"
jq -e '.status == "complete"' "$accepted/result.json" >/dev/null
jq -e '
  .schema == "hh-task10-a-final-certificate-v3" and
  .status == "complete"
' "$accepted/final-certificate.json" >/dev/null

accepted_input_sha=$(sha "$accepted_inputs/SHA256SUMS")
challenger_input_sha=$(sha "$challenger/SHA256SUMS")
accepted_tuple_sha=$(sha "$accepted_inputs/top-provenance.json")
challenger_tuple_sha=$(sha "$challenger/top-provenance.json")
test "$accepted_input_sha" != "$challenger_input_sha"
test "$accepted_tuple_sha" != "$challenger_tuple_sha"
test "$(sha "$runner")" = "$(sha "$accepted_inputs/run-a.sh")"
test "$(sha "$runner")" = "$(sha "$challenger/run-a.sh")"
test "$(jq -r '.input_inventory_sha256' \
  "$accepted/final-certificate.json")" = "$accepted_input_sha"
test "$(jq -r '.run_header_sha256' \
  "$accepted/final-certificate.json")" = "$(sha "$accepted/run.json")"
test "$(jq -r '.result_sha256' \
  "$accepted/final-certificate.json")" = "$(sha "$accepted/result.json")"

before=$(tree_digest "$accepted")
before_files=$(tree_files "$accepted")
before_bytes=$(tree_bytes "$accepted")
state_before=$(tree_digest "$state")
invocations_before=$(sha "$accepted/invocations.jsonl")
command=(env "HHEVAL_TASK10_A_INPUTS=$challenger"
  "HHEVAL_TASK10_A_EXP=$experiment" "$runner")
if "${command[@]}" >"$stdout_log" 2>"$stderr_log"; then
  status=0
else
  status=$?
fi
test "$status" -eq "$expected_status"
test "$(grep -Fxc "$expected_diagnostic" "$stderr_log")" -eq 1
test "$(wc -l <"$stderr_log")" -eq 1

after=$(tree_digest "$accepted")
after_files=$(tree_files "$accepted")
after_bytes=$(tree_bytes "$accepted")
state_after=$(tree_digest "$state")
invocations_after=$(sha "$accepted/invocations.jsonl")
test "$before" = "$after"
test "$before_files" -eq "$after_files"
test "$before_bytes" -eq "$after_bytes"
test "$state_before" = "$state_after"
test "$invocations_before" = "$invocations_after"

command_json=$(printf '%s\0' "${command[@]}" | jq -Rs \
  'split("\u0000")[:-1]')
command_sha=$(printf '%s\0' "${command[@]}" | sha256sum | awk '{print $1}')
jq -n --arg completed "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg experiment "$experiment" --arg accepted_tree "$before" \
  --arg state_tree "$state_before" --arg invocation "$invocations_before" \
  --arg accepted_input "$accepted_input_sha" \
  --arg accepted_tuple "$accepted_tuple_sha" \
  --arg challenger_input "$challenger_input_sha" \
  --arg challenger_tuple "$challenger_tuple_sha" \
  --arg accepted_header "$(sha "$accepted/run.json")" \
  --arg accepted_result "$(sha "$accepted/result.json")" \
  --arg accepted_final "$(sha "$accepted/final-certificate.json")" \
  --arg runner "$(sha "$runner")" --arg verifier "$(sha "$0")" \
  --arg stdout "$(sha "$stdout_log")" --arg stderr "$(sha "$stderr_log")" \
  --arg diagnostic "$expected_diagnostic" --arg command_sha "$command_sha" \
  --argjson command "$command_json" --argjson exit_status "$status" \
  --argjson files "$before_files" --argjson bytes "$before_bytes" '
    {schema:"hh-task10-cross-tuple-certificate-v2",status:"rejected",
     completed:$completed,experiment:$experiment,
     accepted:{input_inventory_sha256:$accepted_input,
       tuple_header_sha256:$accepted_tuple,
       run_header_sha256:$accepted_header,result_sha256:$accepted_result,
       final_certificate_sha256:$accepted_final,
       directory_tree_sha256:$accepted_tree,files:$files,bytes:$bytes,
       invocation_log_sha256:$invocation,state_tree_sha256:$state_tree},
     challenger:{input_inventory_sha256:$challenger_input,
       tuple_header_sha256:$challenger_tuple},
     command:$command,command_sha256:$command_sha,exit_status:$exit_status,
     expected_diagnostic:$diagnostic,stdout_sha256:$stdout,
     stderr_sha256:$stderr,runner_sha256:$runner,verifier_sha256:$verifier,
     accepted_seal_verified:true,challenger_seal_verified:true,
     tuples_distinct:true,before_after_identical:true,
     invocation_and_state_unchanged:true}' >"$temporary"
mv "$temporary" "$certificate"
chmod 0444 "$certificate" "$stdout_log" "$stderr_log"
trap - EXIT HUP INT TERM
