#!/bin/bash
set -Eeuo pipefail

test "$#" -eq 1 || {
  echo "usage: $0 VERIFY_TOOL" >&2
  exit 2
}
verify_tool=$1
test -x "$verify_tool"
work=$(mktemp -d)
trap 'find "$work" -depth -mindepth 1 -delete; rmdir "$work"' \
  EXIT HUP INT TERM
mkdir -p "$work/input" "$work/gate"
printf '%s\n' member >"$work/input/member"
(cd "$work/input" && sha256sum member >SHA256SUMS)
for name in run result baseline resume model ranking stale corrupt first8 oom reserve
do
  printf '%s\n' "$name" >"$work/gate/$name.json"
done
sha () { sha256sum "$1" | awk '{print $1}'; }
input_sha=$(sha "$work/input/SHA256SUMS")
run_sha=$(sha "$work/gate/run.json")
result_sha=$(sha "$work/gate/result.json")
baseline_sha=$(sha "$work/gate/baseline.json")
resume_sha=$(sha "$work/gate/resume.json")
jq -n --arg input "$input_sha" --arg run "$run_sha" \
  --arg result "$result_sha" --arg baseline "$baseline_sha" \
  --arg resume "$resume_sha" --arg model "$(sha "$work/gate/model.json")" \
  --arg ranking "$(sha "$work/gate/ranking.json")" \
  --arg stale "$(sha "$work/gate/stale.json")" \
  --arg corrupt "$(sha "$work/gate/corrupt.json")" \
  --arg first8 "$(sha "$work/gate/first8.json")" \
  --arg oom "$(sha "$work/gate/oom.json")" \
  --arg reserve "$(sha "$work/gate/reserve.json")" '
    {schema:"hh-task10-a-integration-gate-v4",status:"complete",
     input_inventory_sha256:$input,run_header_sha256:$run,
     result_sha256:$result,baseline_validation_sha256:$baseline,
     exact_resume_sha256:$resume,model_env_rejection_sha256:$model,
     ranking_rejections_sha256:$ranking,stale_rejection_sha256:$stale,
     corrupt_rejection_sha256:$corrupt,first8_equivalence_sha256:$first8,
     xargs_oom_selftest_sha256:$oom,
     reservation_selftest_sha256:$reserve,
     counters:{members:5,goals:426,rows:6816,historical_divergences:0,
       current_mismatches:0,binding_mismatches:0,prover_spawns:0}}
  ' >"$work/gate/integration.json"

jq -n --arg input "$input_sha" --arg run "$run_sha" \
  --arg result "$result_sha" --arg baseline "$baseline_sha" \
  --arg integration "$(sha "$work/gate/integration.json")" \
  --arg resume "$resume_sha" --arg model "$(sha "$work/gate/model.json")" \
  --arg ranking "$(sha "$work/gate/ranking.json")" \
  --arg stale "$(sha "$work/gate/stale.json")" \
  --arg corrupt "$(sha "$work/gate/corrupt.json")" \
  --arg first8 "$(sha "$work/gate/first8.json")" \
  --arg oom "$(sha "$work/gate/oom.json")" \
  --arg reserve "$(sha "$work/gate/reserve.json")" '
    {schema:"hh-task10-a-run-v13",
     integration_gate:{schema:"hh-task10-a-integration-support-v1",
       input_inventory_path:"input/SHA256SUMS",
       input_inventory_sha256:$input,
       run_header_path:"gate/run.json",run_header_sha256:$run,
       result_path:"gate/result.json",result_sha256:$result,
       baseline_validation_path:"gate/baseline.json",
       baseline_validation_sha256:$baseline,
       integration_certificate_path:"gate/integration.json",
       integration_certificate_sha256:$integration,
       resume_certificate_path:"gate/resume.json",
       resume_certificate_sha256:$resume,
       model_env_rejection_path:"gate/model.json",
       model_env_rejection_sha256:$model,
       ranking_rejections_path:"gate/ranking.json",
       ranking_rejections_sha256:$ranking,
       stale_rejection_path:"gate/stale.json",stale_rejection_sha256:$stale,
       corrupt_rejection_path:"gate/corrupt.json",
       corrupt_rejection_sha256:$corrupt,
       first8_equivalence_path:"gate/first8.json",
       first8_equivalence_sha256:$first8,
       xargs_oom_selftest_path:"gate/oom.json",
       xargs_oom_selftest_sha256:$oom,
       reservation_selftest_path:"gate/reserve.json",
       reservation_selftest_sha256:$reserve}}
  ' >"$work/top.json"
"$verify_tool" "$work" "$work/top.json"

reject () {
  local name=$1 filter=$2
  jq "$filter" "$work/top.json" >"$work/$name.json"
  if "$verify_tool" "$work" "$work/$name.json" >/dev/null 2>&1; then
    echo "integration verifier accepted invalid case: $name" >&2
    exit 1
  fi
}
reject missing 'del(.integration_gate.integration_certificate_path)'
reject stale '.integration_gate.result_sha256 =
  "0000000000000000000000000000000000000000000000000000000000000000"'
reject extra '.integration_gate.ignored_support = true'
echo "A integration-gate verification: passed"
