#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 3)); then
  echo "usage: $0 INPUTS SAMPLE K_OUTPUT" >&2
  exit 2
fi

tools=$(dirname "$(realpath "$0")")
inputs=$(realpath "$1")
sample=$(realpath "$2")
output=$3
default_state_base=/run/user/$(id -u)/holyhammer-phase3-task12
state_base=${HHEVAL_TASK12_STATE_BASE:-$default_state_base}
state="$state_base/k-revised-v3"
"$tools/run-k.sh" "$inputs" "$sample" "$output"
cp "$tools/run-k-current.sh" "$output/run-k-current.sh"
"$tools/finish-k.sh" "$inputs" "$sample" "$output" "$state"
