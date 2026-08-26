#!/bin/sh
set -eu

behavior_commit=788f0b8817901c57206e56495367f27b0351dd68
run_sha=d50c414547280480105ea6286e395cc4b4e428885748d866008887c746466b87
journal_sha=d2b145c9a16710611dcb61acdfc8e0635fd8acc46259e9ac2bddda7ca50c3318
paired_sha=fa3cf7cb3efdd8da8c27145ab8112e3a702b11d6ed82f2af0dbc562e89b93000
command_sha=6973a9241be97aee6c3aa6cc39b0ed17232d2ecd16efe1c56e8947ad343bea24
run_path=src/holyhammer/eval/phase2-s30-v3/run.json
journal_path=src/holyhammer/eval/phase2-s30-v3/journal/\*.jsonl
member_path=src/holyhammer/eval/phase2-s30-v3/journal/list.jsonl
member_sha=\
20a2fdfe70831c52aee997b6d870d3422a64c3ccca7ef8b21a3dba7a0ceca766

test "${1-}" != "" || {
  echo "usage: $0 PHASE2_COMPLETE_WORKTREE" >&2
  exit 2
}
worktree=$1
test "$(git -C "$worktree" rev-parse HEAD)" = "$behavior_commit" || {
  echo "selftest worktree is not at $behavior_commit" >&2
  exit 2
}

tool_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
fixture_dir=$(dirname -- "$tool_dir")/test-data/hheval-anchor-phase2
eval_dir=$(dirname -- "$tool_dir")/eval
worker_root=$(mktemp -d /tmp/hheval-anchor-index-selftest.XXXXXX)
trap 'rm -rf "$worker_root"' EXIT HUP INT TERM

run_rejected () {
  name=$1
  legacy=$2
  command=$3
  expected=$4
  log=$worker_root/$name.log
  set +e
  env HOLDIR="$worktree" \
    HOL4_HAMMER_DIR="$worker_root/$name-hammer" \
    HHEVAL_ANCHOR_WORKER_ROOT="$worker_root/$name-worker" \
    HHEVAL_ANCHOR_DRIVER="$tool_dir/phase2-anchor-manifest.sml" \
    HHEVAL_ANCHOR_SOURCE_COMMIT="$behavior_commit" \
    HHEVAL_ANCHOR_THEORY=list HHEVAL_ANCHOR_OUTPUT="$worker_root/out.tsv" \
    HHEVAL_ANCHOR_JOURNAL="$eval_dir/phase2-s30-v3/journal/list.jsonl" \
    HHEVAL_ANCHOR_LEGACY_ROWS="$legacy" \
    HHEVAL_ANCHOR_COMMAND_ROWS="$command" \
    HHEVAL_ANCHOR_ACCEPTED_RUN_HEADER="$run_path" \
    HHEVAL_ANCHOR_ACCEPTED_RUN_HEADER_SHA256="$run_sha" \
    HHEVAL_ANCHOR_ACCEPTED_JOURNAL="$journal_path" \
    HHEVAL_ANCHOR_ACCEPTED_JOURNAL_SHA256="$journal_sha" \
    HHEVAL_ANCHOR_INPUT_RUN_HEADER_SHA256="$run_sha" \
    HHEVAL_ANCHOR_INPUT_JOURNAL="$member_path" \
    HHEVAL_ANCHOR_INPUT_JOURNAL_SHA256="$member_sha" \
    HHEVAL_ANCHOR_PAIRED_ROWS_SHA256="$paired_sha" \
    HHEVAL_ANCHOR_COMMAND_ROWS_SHA256="$command_sha" \
    "$worktree/bin/hol" < "$tool_dir/phase2-anchor-manifest-controller.sml" \
    > "$log" 2>&1
  status=$?
  set -e
  test "$status" -ne 0 || {
    echo "$name unexpectedly succeeded" >&2
    exit 1
  }
  grep -F "$expected" "$log" >/dev/null || {
    echo "$name did not report its expected rejection" >&2
    exit 1
  }
  echo "$name: rejected"
}

run_rejected duplicate-legacy \
  "$fixture_dir/index-duplicate-legacy.tsv" \
  "$fixture_dir/index-malformed-command.tsv" \
  "duplicate historical premise key"
run_rejected malformed-nontarget-command \
  "$fixture_dir/task13-paired-first8.tsv" \
  "$fixture_dir/index-malformed-command.tsv" \
  "anchor manifest generation failed"

caller_log=$worker_root/caller-journal.log
if env HHEVAL_ANCHOR_WORKTREE="$worktree" HHEVAL_ANCHOR_THEORY=list \
    HHEVAL_ANCHOR_OUTPUT="$worker_root/caller.tsv" \
    HHEVAL_ANCHOR_JOURNAL="$fixture_dir/journal-list-two-goals.jsonl" \
    "$tool_dir/phase2-anchor-manifest.sh" > "$caller_log" 2>&1
then
  echo "caller-supplied journal unexpectedly succeeded" >&2
  exit 1
fi
grep -F "provenance-controlled and must not be supplied" \
  "$caller_log" >/dev/null || {
  echo "caller-supplied journal rejection was not diagnostic" >&2
  exit 1
}
echo "caller-supplied-journal: rejected"
