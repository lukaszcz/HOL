#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 5 || {
  echo "usage: $0 RUNNER ACCEPTED_INPUTS CHALLENGER OUTPUT CERTIFICATE" >&2
  exit 2
}
runner=$1
accepted_inputs=$2
challenger=$3
output=$4
certificate=$5
experiment=${output##*/}
evidence_root=${output%/runs/$experiment}
state=/run/user/$(id -u)/holyhammer-phase3-task10/$experiment
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM

sha () { sha256sum "$1" | awk '{print $1}'; }
tree () {
  if test ! -e "$1"; then printf '%s\n' absent; return; fi
  (cd "$1" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum) | sha256sum | awk '{print $1}'
}

test -x "$runner" && test ! -L "$runner"
for tuple in "$accepted_inputs" "$challenger"; do
  test -s "$tuple/SHA256SUMS" && test ! -L "$tuple/SHA256SUMS"
  (cd "$tuple" && sha256sum -c SHA256SUMS >/dev/null)
done
test -s "$output/run.json" && test ! -L "$output/run.json"
cmp -s "$output/run.json" "$accepted_inputs/top-provenance.json"
test "$(sha "$accepted_inputs/SHA256SUMS")" != \
  "$(sha "$challenger/SHA256SUMS")"

guard_line=$(grep -n '^verify_existing_tuple_readonly$' "$runner" |
  tail -1 | cut -d: -f1)
boundary_line=$(grep -n '^verify_worker_export_boundary$' "$runner" |
  tail -1 | cut -d: -f1)
inputs_line=$(grep -n '^verify_inputs$' "$runner" | tail -1 | cut -d: -f1)
initialize_line=$(grep -n '^initialize$' "$runner" | tail -1 | cut -d: -f1)
live_line=$(grep -n '^verify_live_execution_envelope$' "$runner" |
  tail -1 | cut -d: -f1)
test "$guard_line" -lt "$boundary_line"
test "$guard_line" -lt "$inputs_line"
test "$guard_line" -lt "$initialize_line"
test "$inputs_line" -lt "$live_line"
test "$live_line" -lt "$boundary_line"
test "$boundary_line" -lt "$initialize_line"

before_tree=$(tree "$output")
before_invocations=$(sha "$output/invocations.jsonl")
before_admission=$(sha "$output/memory-admission.jsonl")
before_state=$(tree "$state")

# Fail closed if any filesystem mutator or live-envelope command is reachable
# from the offline verifier.  The deliberately impossible live overrides also
# prove that VERIFY_INPUTS does not sample or admit the caller's cgroup.
block=$work/block
mkdir "$block"
cut -f1,2 "$accepted_inputs/external-tools.tsv" |
  while IFS="$(printf '\t')" read -r name path; do
    command=${name#prover:}
    printf '%s\n' '#!/bin/sh' 'exit 97' >"$block/$command"
    chmod +x "$block/$command"
  done
for command in mkdir touch cp mv rm sleep findmnt nproc jq sha256sum \
    timeout flock git poly Holmake eprover vampire zipperposition; do
  printf '%s\n' '#!/bin/sh' 'exit 97' >"$block/$command"
  chmod +x "$block/$command"
done
PATH="$block:$PATH" \
  HHEVAL_HOST_MEMORY_AVAILABLE_OVERRIDE=0 \
  HHEVAL_SCOPE_MEMORY_CURRENT_OVERRIDE=999999999999 \
  HHEVAL_HOST_MEMORY_WAIT_OVERRIDE=0 \
  HHEVAL_TASK10_A_INPUTS="$accepted_inputs" \
  HHEVAL_TASK10_A_EXP="$experiment" \
  HHEVAL_TASK10_EVIDENCE_ROOT="$evidence_root" \
  "$runner" VERIFY_INPUTS
test "$before_tree" = "$(tree "$output")"
test "$before_invocations" = "$(sha "$output/invocations.jsonl")"
test "$before_admission" = "$(sha "$output/memory-admission.jsonl")"
test "$before_state" = "$(tree "$state")"

# The normal execution path must leave the sealed verifier toolchain, discover
# the poisoned caller tool boundary, and reject it before admission or resume
# mutation.
if PATH="$block:$PATH" \
    HHEVAL_TASK10_A_INPUTS="$accepted_inputs" \
    HHEVAL_TASK10_A_EXP="$experiment" \
    HHEVAL_TASK10_EVIDENCE_ROOT="$evidence_root" \
    "$runner" >"$work/live-poison.stdout" \
    2>"$work/live-poison.stderr"; then
  echo "poisoned live execution boundary passed" >&2
  exit 1
fi
test "$before_tree" = "$(tree "$output")"
test "$before_invocations" = "$(sha "$output/invocations.jsonl")"
test "$before_admission" = "$(sha "$output/memory-admission.jsonl")"
test "$before_state" = "$(tree "$state")"

# The command dispatcher and the verifier body contain no path to execution
# admission or initialization.  This complements the dynamic blocked-command
# test above and catches accidental call-graph regressions before a run.
verify_branch=$(sed -n '/^if test "${1:-}" = VERIFY_INPUTS;/,/^fi$/p' \
  "$runner")
test -n "$verify_branch"
branch_forbidden='verify_live_execution_envelope|verify_scope|'
branch_forbidden+='require_host_memory|verify_worker_export_boundary|'
branch_forbidden+='initialize|pool |cleanup_'
if grep -Eq "$branch_forbidden" <<<"$verify_branch"; then
  echo "VERIFY_INPUTS dispatcher reaches a mutator" >&2
  exit 1
fi
verify_body=$(sed -n '/^verify_inputs () {/,/^}$/p' "$runner")
test -n "$verify_body"
body_forbidden='verify_live_execution_envelope|verify_scope|'
body_forbidden+='require_host_memory|mktemp|mkdir|touch|sleep|findmnt|'
body_forbidden+='nproc|invocations|memory-admission|git -C|\$ROOT|\$BASE_|'
body_forbidden+='\$OVERLAY_|overlay_root|verify_live_source_state|'
body_forbidden+='verify_live_external_tools'
if grep -Eq "$body_forbidden" <<<"$verify_body"; then
  echo "read-only verifier body reaches a mutator or live sampler" >&2
  exit 1
fi

if env HHEVAL_TASK10_A_INPUTS="$challenger" \
    HHEVAL_TASK10_A_EXP="$experiment" \
    HHEVAL_TASK10_EVIDENCE_ROOT="$evidence_root" "$runner" \
    >"$work/distinct.stdout" 2>"$work/distinct.stderr"; then
  status=0
else
  status=$?
fi
test "$status" -eq 78
diagnostic='task10 tuple mismatch: sealed input does not match accepted run header'
test "$(grep -Fxc "$diagnostic" "$work/distinct.stderr")" -eq 1
test "$(wc -l <"$work/distinct.stderr")" -eq 1
test "$before_tree" = "$(tree "$output")"
test "$before_invocations" = "$(sha "$output/invocations.jsonl")"
test "$before_admission" = "$(sha "$output/memory-admission.jsonl")"
test "$before_state" = "$(tree "$state")"

for kind in missing corrupt; do
  candidate=$work/$kind
  cp -a --reflink=auto "$accepted_inputs" "$candidate"
  chmod -R u+w "$candidate"
  if test "$kind" = missing; then
    rm "$candidate/current-driver.sml"
  else
    printf '%s\n' corrupt >>"$candidate/current-driver.sml"
  fi
  if env HHEVAL_TASK10_A_INPUTS="$candidate" \
      HHEVAL_TASK10_A_EXP="$experiment" \
      HHEVAL_TASK10_EVIDENCE_ROOT="$evidence_root" \
      "$runner" VERIFY_INPUTS \
      >"$work/$kind.stdout" 2>"$work/$kind.stderr"; then
    echo "invalid $kind candidate passed tuple guard" >&2
    exit 1
  fi
  test "$before_tree" = "$(tree "$output")"
  test "$before_invocations" = "$(sha "$output/invocations.jsonl")"
  test "$before_admission" = "$(sha "$output/memory-admission.jsonl")"
  test "$before_state" = "$(tree "$state")"
done

jq -n --arg completed "$(date -u +%FT%TZ)" \
  --arg accepted "$(sha "$accepted_inputs/SHA256SUMS")" \
  --arg challenger "$(sha "$challenger/SHA256SUMS")" \
  --arg tree "$before_tree" --arg invocations "$before_invocations" \
  --arg admission "$before_admission" --arg state "$before_state" \
  --arg runner "$(sha "$runner")" --arg diagnostic "$diagnostic" '
  {schema:"hh-task10-a-existing-tuple-guard-selftest-v1",
   status:"complete",completed:$completed,
   accepted_input_inventory_sha256:$accepted,
   challenger_input_inventory_sha256:$challenger,
   runner_sha256:$runner,distinct_exit_status:78,
   distinct_diagnostic:$diagnostic,accepted_tree_sha256:$tree,
   invocation_log_sha256:$invocations,memory_admission_sha256:$admission,
   state_tree_sha256:$state,same_tuple_full_verification:true,
   same_tuple_offline_scope_independent:true,
   same_tuple_tree_and_logs_unchanged:true,
   missing_and_corrupt_same_identity_rejected:true,
   sealed_verifier_ignores_poisoned_caller_tools:true,
   poisoned_live_execution_rejected_before_mutation:true,
   guard_precedes_all_mutators:true,readonly_call_graph_certified:true,
   distinct_before_after_identical:true}
  ' >"$certificate"
chmod 0444 "$certificate"
echo "A existing-tuple guard selftest: passed"
