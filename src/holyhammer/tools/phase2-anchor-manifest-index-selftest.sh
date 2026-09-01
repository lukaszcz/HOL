#!/bin/sh
set -eu

behavior_commit=f7511d0d5ee7c2918236f7eda4c16ee8c01e00fa
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
anchor_objects=$worktree/src/holyhammer/.hol/objs
theory_dir=$worktree/src/list/src

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
  mkdir -p "$worker_root/$name-worker" "$worker_root/$name-hammer"
  set +e
  env HOLDIR="$worktree" \
    HOL4_HAMMER_DIR="$worker_root/$name-hammer" \
    HHEVAL_ANCHOR_WORKER_ROOT="$worker_root/$name-worker" \
    HHEVAL_ANCHOR_SUCCESS_MARKER="$worker_root/$name-success" \
    HHEVAL_ANCHOR_DRIVER="$tool_dir/phase2-anchor-manifest.sml" \
    HHEVAL_ANCHOR_OBJECTS="$anchor_objects" \
    HHEVAL_ANCHOR_SOURCE_COMMIT="$behavior_commit" \
    HHEVAL_ANCHOR_BEHAVIOR_COMMIT="$behavior_commit" \
    HHEVAL_ANCHOR_WORKTREE="$worktree" \
    HHEVAL_ANCHOR_THEORY_DIR="$theory_dir" \
    HHEVAL_ANCHOR_BASELINE_PROVENANCE_SHA256=\
"baseline-provenance-fixture" \
    HHEVAL_ANCHOR_INVOCATION_PROVENANCE_SHA256=\
"invocation-provenance-fixture" \
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
    cat "$log" >&2
    echo "$name unexpectedly succeeded" >&2
    exit 1
  }
  grep -F "$expected" "$log" >/dev/null || {
    cat "$log" >&2
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
    HHEVAL_ANCHOR_EXECUTION_STATE=f751 \
    HHEVAL_ANCHOR_RUNTIME_WORKTREE="$worktree" \
    HHEVAL_ANCHOR_RUNTIME_COMMIT="$behavior_commit" \
    HHEVAL_ANCHOR_THEORY_DIR="$theory_dir" \
    HHEVAL_ANCHOR_OUTPUT="$worker_root/caller.tsv" \
    HHEVAL_ANCHOR_INVOCATION_PROVENANCE_SHA256=\
0000000000000000000000000000000000000000000000000000000000000000 \
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

caller_objects_log=$worker_root/caller-objects.log
if env HHEVAL_ANCHOR_WORKTREE="$worktree" HHEVAL_ANCHOR_THEORY=list \
    HHEVAL_ANCHOR_EXECUTION_STATE=f751 \
    HHEVAL_ANCHOR_RUNTIME_WORKTREE="$worktree" \
    HHEVAL_ANCHOR_RUNTIME_COMMIT="$behavior_commit" \
    HHEVAL_ANCHOR_THEORY_DIR="$theory_dir" \
    HHEVAL_ANCHOR_OUTPUT="$worker_root/caller-objects.tsv" \
    HHEVAL_ANCHOR_INVOCATION_PROVENANCE_SHA256=\
0000000000000000000000000000000000000000000000000000000000000000 \
    HHEVAL_ANCHOR_OBJECTS="$worker_root/caller-objects" \
    "$tool_dir/phase2-anchor-manifest.sh" \
    > "$caller_objects_log" 2>&1
then
  echo "caller-supplied objects unexpectedly succeeded" >&2
  exit 1
fi
grep -F "provenance-controlled and must not be supplied" \
  "$caller_objects_log" >/dev/null || {
  echo "caller-supplied objects rejection was not diagnostic" >&2
  exit 1
}
echo "caller-supplied-objects: rejected"

provenance_root=$worker_root/provenance-root
provenance_inventory=$worker_root/provenance.sha256
mkdir -p "$provenance_root/src" "$provenance_root/.hol/objs"
printf '%s\n' 'source-v1' > "$provenance_root/src/module.sml"
printf '%s\n' 'object-v1' > "$provenance_root/.hol/objs/module.uo"
{
  sha256sum "$provenance_root/src/module.sml" |
    sed "s|  $provenance_root/|  |"
  sha256sum "$provenance_root/.hol/objs/module.uo" |
    sed "s|  $provenance_root/|  |"
} > "$provenance_inventory"
sh "$tool_dir/phase2-anchor-check-provenance.sh" \
  "$provenance_root" "$provenance_inventory"

: > "$worker_root/empty-provenance.sha256"
if sh "$tool_dir/phase2-anchor-check-provenance.sh" \
    "$provenance_root" "$worker_root/empty-provenance.sha256" \
    > "$worker_root/empty-provenance.log" 2>&1
then
  echo "empty provenance inventory unexpectedly passed" >&2
  exit 1
fi
grep -F 'provenance inventory is empty' \
  "$worker_root/empty-provenance.log" >/dev/null
echo "empty-provenance-inventory: rejected"

printf '%s\n' 'source-v2-stale' > "$provenance_root/src/module.sml"
if sh "$tool_dir/phase2-anchor-check-provenance.sh" \
    "$provenance_root" "$provenance_inventory" \
    > "$worker_root/stale-source.log" 2>&1
then
  echo "stale source unexpectedly passed provenance validation" >&2
  exit 1
fi
grep -F 'unexpected SHA-256' "$worker_root/stale-source.log" >/dev/null
printf '%s\n' 'source-v1' > "$provenance_root/src/module.sml"

printf '%s\n' 'object-v2-corrupt' > \
  "$provenance_root/.hol/objs/module.uo"
if sh "$tool_dir/phase2-anchor-check-provenance.sh" \
    "$provenance_root" "$provenance_inventory" \
    > "$worker_root/corrupt-object.log" 2>&1
then
  echo "corrupt object unexpectedly passed provenance validation" >&2
  exit 1
fi
grep -F 'unexpected SHA-256' "$worker_root/corrupt-object.log" >/dev/null
echo "stale-source-and-corrupt-object: rejected"
