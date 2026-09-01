#!/bin/sh
set -eu

overlay=${HHEVAL_CURRENT_OVERLAY:?current overlay is required}
state=${HHEVAL_CURRENT_EXECUTION_STATE:?execution state is required}
inputs=${HHEVAL_TASK10_A_INPUTS:?immutable input directory is required}

check_sha () {
  expected=$1
  path=$2
  actual=$(sha256sum "$path" | awk '{print $1}')
  test "$actual" = "$expected" || {
    echo "provenance mismatch: $path: $actual" >&2
    exit 2
  }
}

commit=$(jq -r --arg state "$state" \
  '.execution_states[$state].base_commit' "$inputs/top-provenance.json")
test "$(git -C "$overlay" rev-parse HEAD)" = "$commit"
check_sha "$HHEVAL_CURRENT_INVOCATION_PROVENANCE_SHA256" \
  "$HHEVAL_CURRENT_INVOCATION_PATH"
check_sha "$(jq -r --arg state "$state" \
  '.execution_states[$state].current_diff_sha256' \
  "$inputs/top-provenance.json")" "$inputs/overlay-$state.patch"

jq -r --arg state "$state" \
  '.execution_states[$state].current_loaded.sources |
   to_entries[] | [.value,.key] | @tsv' \
  "$inputs/top-provenance.json" | while IFS="$(printf '\t')" read -r digest path
do
  check_sha "$digest" "$overlay/$path"
done
jq -r --arg state "$state" \
  '.execution_states[$state].current_loaded.objects |
   to_entries[] | [.value,.key] | @tsv' \
  "$inputs/top-provenance.json" | while IFS="$(printf '\t')" read -r digest path
do
  check_sha "$digest" "$overlay/$path"
done

case ${HHEVAL_CURRENT_CHECKPOINT_LAUNCH:-ordinary} in
  ordinary | base)
    exec "$overlay/bin/hol" < "$inputs/current-controller.sml"
    ;;
  atom)
    prior=${HHEVAL_CURRENT_CHECKPOINT_PRIOR_HEAP:?prior heap is required}
    check_sha "$HHEVAL_CURRENT_CHECKPOINT_PRIOR_SHA256" "$prior"
    exec "$overlay/bin/hol" < "$inputs/current-controller.sml"
    ;;
  *)
    echo "invalid current checkpoint launch mode" >&2
    exit 2
    ;;
esac
