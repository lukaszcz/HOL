#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 4)); then
  echo "usage: $0 ATOM ATTEMPT GOALS OUTPUT_JOURNAL" >&2
  exit 2
fi

atom=$1
attempt=$2
goals=$(realpath "$3")
output=$4
input=${HHEVAL_REFERENCE_INPUT:?HHEVAL_REFERENCE_INPUT is not set}
root=${HHEVAL_REFERENCE_HOL_ROOT:?HHEVAL_REFERENCE_HOL_ROOT is not set}
hammer=${HHEVAL_REFERENCE_HAMMER_DIR:?HHEVAL_REFERENCE_HAMMER_DIR is not set}
dependency="$input/runtime-dependency-certificate.json"
validation=${HHEVAL_REFERENCE_RUNTIME_VALIDATION:?
HHEVAL_REFERENCE_RUNTIME_VALIDATION is not set}
[[ "$attempt" =~ ^[1-9][0-9]*$ && -f "$dependency" &&
  -f "$validation" ]]
expected_validation=$(sha256sum "$input/runtime-root-certificate.json")
[[ "$(cat "$validation")" == "$expected_validation" ]]

IFS=$'\t' read -r found theory part parts relative extra < <(
  awk -F '\t' -v atom="$atom" '$1==atom {print; found++}
    END {if (found != 1) exit 1}' "$input/atoms.tsv")
[[ -z "${extra-}" && "$found" == "$atom" ]]
case "$relative" in
  */src/*) relative="src/${relative#*/src/}" ;;
esac
[[ "$relative" != /* && "$relative" != ../* && "$relative" != *../* ]]
directory="$root/$relative"
[[ -d "$directory" && -x "$root/bin/hol" && -f "$root/bin/hol.state" ]]

check_hash() {
  local path=$1 expression=$2 expected
  expected=$(jq -er "$expression" "$dependency")
  [[ "$(sha256sum "$path" | cut -d' ' -f1)" == "$expected" ]]
}
check_hash "$root/bin/hol" '.equivalent_environment.bin_hol_sha256'
check_hash "$root/bin/hol.state" '.equivalent_environment.hol_state_sha256'
check_hash "${HOL4_EPROVER_EXECUTABLE:?}" '.prover_binaries.e'
check_hash "${HOL4_VAMPIRE_EXECUTABLE:?}" '.prover_binaries.vampire'
check_hash "${HOL4_ZIPPERPOSITION_EXECUTABLE:?}" \
  '.prover_binaries.zipperposition'
while IFS=$'\t' read -r expected relative_object extra; do
  [[ -z "${extra-}" && "$relative_object" != /* &&
    "$relative_object" != ../* && "$relative_object" != *../* ]]
  [[ "$(sha256sum "$root/$relative_object" | cut -d' ' -f1)" == \
    "$expected" ]]
done <"$input/accepted-loaded-objects.tsv"

work=$(dirname "$output")/hol-worker
mkdir -p "$work/journal" "$work/out" "$work/pb"
env HOLDIR="$root" HOL4_HAMMER_DIR="$hammer" \
  HOL4_EPROVER_EXECUTABLE="$HOL4_EPROVER_EXECUTABLE" \
  HOL4_VAMPIRE_EXECUTABLE="$HOL4_VAMPIRE_EXECUTABLE" \
  HOL4_ZIPPERPOSITION_EXECUTABLE="$HOL4_ZIPPERPOSITION_EXECUTABLE" \
  HHEVAL_EXPDIR="$work" HHEVAL_THEORY="$theory" \
  HHEVAL_THEORY_DIR="$directory" HHEVAL_PART="$part" \
  HHEVAL_PARTS="$parts" HHEVAL_TASK12_MODE=measure \
  HHEVAL_GOAL_INVENTORY="$goals" \
  "$root/bin/hol" repl -b "$root/bin/hol.state" \
  <"$input/task12-driver.sml" >"$work/worker.log" 2>&1
cp "$work/journal/$theory.part-$part-of-$parts.jsonl" "$output"
