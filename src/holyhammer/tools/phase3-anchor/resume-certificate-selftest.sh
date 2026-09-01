#!/bin/sh
set -eu

test "$#" -eq 1 || {
  echo "usage: $0 RESUME_CERTIFICATE_TOOL" >&2
  exit 2
}
tool=$1
test -x "$tool"
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM
output=$work/resume-certificate-selftest-$$
inputs=$work/inputs
runner=$work/runner.sh
diagnostic=$work/diagnostic.log
certificate=$work/resume-certificate.json
mkdir -p "$output" "$inputs"
for name in baseline current current-rankings current-checkpoint-chains; do
  mkdir -p "$output/$name"
  printf '%s\n' "$name" >"$output/$name/member.json"
done
printf '%s\n' sealed-inputs >"$inputs/SHA256SUMS"
printf '%s\n' '{"schema":"test-run"}' >"$output/run.json"
printf '%s\n' '{"status":"complete"}' \
  >"$output/baseline-validation.json"
printf '%s\n' '{"status":"complete"}' >"$output/result.json"
printf '%s\n' \
  '{"schema":"hh-task10-tmpfs-cleanup-v1","status":"removed"}' \
  >"$output/tmpfs-cleanup.json"
jq -nc --arg run "$(printf 'a%.0s' $(seq 1 64))" \
  --arg input "$(printf 'b%.0s' $(seq 1 64))" \
  '{event:"start",run_header_sha256:$run,
    input_inventory_sha256:$input}' >"$output/invocations.jsonl"
jq -nc --arg result "$(printf 'c%.0s' $(seq 1 64))" \
  '{event:"complete",result_sha256:$result}' \
  >>"$output/invocations.jsonl"
cat >"$runner" <<'EOF'
#!/bin/sh
set -eu
test -n "${HHEVAL_TASK10_A_INPUTS:-}"
test -n "${HHEVAL_TASK10_A_EXP:-}"
test "$HHEVAL_TASK10_A_INPUTS" = "$FAKE_RESUME_INPUTS"
test "$HHEVAL_TASK10_A_EXP" = "${FAKE_RESUME_OUTPUT##*/}"
run=$(sha256sum "$FAKE_RESUME_OUTPUT/run.json" | awk '{print $1}')
input=$(sha256sum "$FAKE_RESUME_INPUTS/SHA256SUMS" | awk '{print $1}')
result=$(sha256sum "$FAKE_RESUME_OUTPUT/result.json" | awk '{print $1}')
printf '{"event":"resume","run_header_sha256":"%s","input_inventory_sha256":"%s"}\n' \
  "$run" "$input" >>"$FAKE_RESUME_OUTPUT/invocations.jsonl"
printf '{"event":"complete","result_sha256":"%s"}\n' "$result" \
  >>"$FAKE_RESUME_OUTPUT/invocations.jsonl"
EOF
chmod +x "$runner"
FAKE_RESUME_INPUTS=$inputs FAKE_RESUME_OUTPUT=$output \
  "$tool" "$output" "$inputs" "$runner" "$diagnostic" "$certificate"
jq -e '
  .schema == "hh-task10-exact-resume-v1" and .status == "complete" and
  .durable_only == true and .tmpfs_absent_before_and_after == true and
  .immutable_results_byte_identical == true and
  (.invocation_log_before_sha256 | length) == 64 and
  (.invocation_log_after_sha256 | length) == 64 and
  .invocation_log_before_sha256 != .invocation_log_after_sha256' \
  "$certificate" >/dev/null
jq -s -e 'length == 4 and .[-2].event == "resume" and
  .[-2].durable_only == null and .[-1].event == "complete"' \
  "$output/invocations.jsonl" >/dev/null
echo "exact durable-resume certificate selftest: passed"
