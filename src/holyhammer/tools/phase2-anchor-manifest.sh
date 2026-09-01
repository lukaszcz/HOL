#!/bin/sh
set -eu

gate_commit=f25871c404016d4368a0927ba0a868860fc82c70
run_sha=d50c414547280480105ea6286e395cc4b4e428885748d866008887c746466b87
paired_sha=fa3cf7cb3efdd8da8c27145ab8112e3a702b11d6ed82f2af0dbc562e89b93000
command_sha=6973a9241be97aee6c3aa6cc39b0ed17232d2ecd16efe1c56e8947ad343bea24
paired_driver_sha=\
2fd0a344574906d38a59774f5e293fc673cb1fca28bcab07664dcb52779bf430
paired_controller_sha=\
fb98abd78825ca7e4e15c64bfe6d7ffcc3cee34dca8c6e59fe78828552968141
accepted_journal_sha=\
d2b145c9a16710611dcb61acdfc8e0635fd8acc46259e9ac2bddda7ca50c3318
optimized_monomorph_sha=\
8a13d4029b9f937214c3d9dfbd214373e94551195f91b850e6cdd9d80682d1c0
optimized_monomorph_patch_sha=\
5ce27d177945e6e6ce713e287a635151edae03c19c5b637f72fc3f4b74fa4bd1

required () {
  eval "value=\${$1-}"
  test -n "$value" || {
    echo "$1 is not set" >&2
    exit 2
  }
}

for name in HHEVAL_ANCHOR_WORKTREE HHEVAL_ANCHOR_THEORY \
  HHEVAL_ANCHOR_EXECUTION_STATE \
  HHEVAL_ANCHOR_RUNTIME_WORKTREE HHEVAL_ANCHOR_RUNTIME_COMMIT \
  HHEVAL_ANCHOR_THEORY_DIR \
  HHEVAL_ANCHOR_OUTPUT HHEVAL_ANCHOR_INVOCATION_PROVENANCE_SHA256
do
  required "$name"
done

case "$HHEVAL_ANCHOR_EXECUTION_STATE" in
  f751) behavior_commit=f7511d0d5ee7c2918236f7eda4c16ee8c01e00fa ;;
  f258) behavior_commit=f25871c404016d4368a0927ba0a868860fc82c70 ;;
  *)
    echo "invalid anchor execution state: $HHEVAL_ANCHOR_EXECUTION_STATE" >&2
    exit 2
    ;;
esac

for name in HHEVAL_ANCHOR_JOURNAL HHEVAL_ANCHOR_INPUT_JOURNAL_SHA256 \
  HHEVAL_ANCHOR_INPUT_JOURNAL HHEVAL_ANCHOR_RUN_HEADER \
  HHEVAL_ANCHOR_LEGACY_ROWS HHEVAL_ANCHOR_COMMAND_ROWS \
  HHEVAL_ANCHOR_OBJECTS
do
  eval "caller_value=\${$name-}"
  test -z "$caller_value" || {
    echo "$name is provenance-controlled and must not be supplied" >&2
    exit 2
  }
done

case "$HHEVAL_ANCHOR_THEORY" in
  *[!A-Za-z0-9_]*)
    echo "invalid anchor theory name: $HHEVAL_ANCHOR_THEORY" >&2
    exit 2
    ;;
esac
test -d "$HHEVAL_ANCHOR_THEORY_DIR" &&
test ! -L "$HHEVAL_ANCHOR_THEORY_DIR" || {
  echo "anchor theory directory is not a regular directory" >&2
  exit 2
}
test -f "$HHEVAL_ANCHOR_THEORY_DIR/.hol/objs/"\
"${HHEVAL_ANCHOR_THEORY}Theory.dat" &&
test -f "$HHEVAL_ANCHOR_THEORY_DIR/.hol/objs/"\
"${HHEVAL_ANCHOR_THEORY}Theory.ui" || {
  echo "anchor theory directory has no certified theory objects" >&2
  exit 2
}
case "$HHEVAL_ANCHOR_INVOCATION_PROVENANCE_SHA256" in
  *[!0-9a-f]* | "")
    echo "invalid invocation provenance SHA-256" >&2
    exit 2
    ;;
esac
test "${#HHEVAL_ANCHOR_INVOCATION_PROVENANCE_SHA256}" -eq 64 || {
  echo "invalid invocation provenance SHA-256 length" >&2
  exit 2
}

test "$(git -C "$HHEVAL_ANCHOR_WORKTREE" rev-parse HEAD)" = \
  "$behavior_commit" || {
  echo "anchor worktree is not at $behavior_commit" >&2
  exit 2
}
test "$(git -C "$HHEVAL_ANCHOR_RUNTIME_WORKTREE" rev-parse HEAD)" = \
  "$HHEVAL_ANCHOR_RUNTIME_COMMIT" || {
  echo "anchor runtime worktree is not at $HHEVAL_ANCHOR_RUNTIME_COMMIT" >&2
  exit 2
}

check_sha () {
  expected=$1
  path=$2
  actual=$(sha256sum "$path" | awk '{print $1}')
  test "$actual" = "$expected" || {
    echo "unexpected SHA-256 for $path: $actual" >&2
    exit 2
  }
}

check_sha "$optimized_monomorph_sha" \
  "$HHEVAL_ANCHOR_WORKTREE/src/holyhammer/hhMonomorph.sml"
test "$(git -C "$HHEVAL_ANCHOR_WORKTREE" diff --binary -- \
  src/holyhammer/hhMonomorph.sml | sha256sum | awk '{print $1}')" = \
  "$optimized_monomorph_patch_sha" || {
  echo "unexpected historical baseline patch" >&2
  exit 2
}
HHEVAL_ANCHOR_OBJECTS=\
$HHEVAL_ANCHOR_WORKTREE/src/holyhammer/.hol/objs
test -f "$HHEVAL_ANCHOR_OBJECTS/hhMonomorph.uo" &&
test -f "$HHEVAL_ANCHOR_OBJECTS/hhProblemGen.uo" &&
test -f "$HHEVAL_ANCHOR_OBJECTS/hhSchedule.uo" || {
  echo "anchor optimized objects are not built" >&2
  exit 2
}
export HHEVAL_ANCHOR_OBJECTS

tool_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
provenance=$tool_dir/../loaded-$HHEVAL_ANCHOR_EXECUTION_STATE.sha256
sh "$tool_dir/phase2-anchor-check-provenance.sh" \
  "$HHEVAL_ANCHOR_WORKTREE" "$provenance"
HHEVAL_ANCHOR_BASELINE_PROVENANCE_SHA256=$(sha256sum "$provenance" |
  awk '{print $1}')
export HHEVAL_ANCHOR_BASELINE_PROVENANCE_SHA256
eval_dir=$(dirname -- "$tool_dir")/eval
run_header=$eval_dir/phase2-s30-v3/run.json
journal_dir=$eval_dir/phase2-s30-v3/journal
certificate=$tool_dir/../test-data/hheval-anchor-phase2/\
phase2-s30-v3-journal.sha256
legacy_rows=$eval_dir/phase2-task13-derived-anchor-rows.tsv
command_rows=$eval_dir/phase2-task13-s30v3-anchor-audit-v3.tsv

actual_journal_sha=$(
  cd "$journal_dir"
  find . -type f -name '*.jsonl' -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum | sha256sum | awk '{print $1}'
)
test "$actual_journal_sha" = "$accepted_journal_sha" || {
  echo "canonical accepted journal aggregate mismatch: "\
"$actual_journal_sha" >&2
  exit 2
}

check_sha "$accepted_journal_sha" "$certificate"
LC_ALL=C awk '
  BEGIN { previous = ""; bad = 0 }
  {
    digest = substr($0, 1, 64)
    separator = substr($0, 65, 2)
    path = substr($0, 67)
    theory = substr(path, 3, length(path) - 8)
    if (length(digest) != 64 || digest ~ /[^0-9a-f]/ ||
        separator != "  " || path !~ /^\.\/[A-Za-z0-9_]+\.jsonl$/ ||
        theory == "" || seen_path[path]++ || seen_theory[theory]++ ||
        (previous != "" && path <= previous))
      bad = 1
    previous = path
  }
  END { if (bad || NR != 229) exit 1 }
' "$certificate" || {
  echo "invalid canonical anchor journal certificate" >&2
  exit 2
}
certificate_member_sha=$(LC_ALL=C awk -v expected="./$HHEVAL_ANCHOR_THEORY.jsonl" '
  substr($0, 67) == expected { print substr($0, 1, 64) }
' "$certificate")
certificate_member_path=$(LC_ALL=C awk \
  -v expected="./$HHEVAL_ANCHOR_THEORY.jsonl" '
  substr($0, 67) == expected { print substr($0, 67) }
' "$certificate")
test -n "$certificate_member_sha" || {
  echo "anchor journal certificate has no member for theory "\
"$HHEVAL_ANCHOR_THEORY" >&2
  exit 2
}
test "$certificate_member_path" = "./$HHEVAL_ANCHOR_THEORY.jsonl" || {
  echo "anchor journal certificate returned a non-canonical member" >&2
  exit 2
}
certificate_member_file=${certificate_member_path#./}
journal_member=$journal_dir/$certificate_member_file
test -f "$journal_member" && test ! -L "$journal_member" || {
  echo "canonical accepted journal has no regular member for theory "\
"$HHEVAL_ANCHOR_THEORY" >&2
  exit 2
}
check_sha "$certificate_member_sha" "$journal_member"

check_sha "$run_sha" "$run_header"
check_sha "$paired_sha" "$legacy_rows"
check_sha "$command_sha" "$command_rows"
check_sha "$paired_driver_sha" \
  "$eval_dir/phase2-task13-anchor-key-driver.sml"
check_sha "$paired_controller_sha" \
  "$eval_dir/phase2-task13-anchor-key-controller.sml"
worker_root=$(mktemp -d /tmp/hheval-anchor-worker.XXXXXX)
trap 'rm -rf "$worker_root"' EXIT HUP INT TERM
HHEVAL_ANCHOR_SUCCESS_MARKER=$worker_root/worker-success
export HHEVAL_ANCHOR_SUCCESS_MARKER
requested_output=$HHEVAL_ANCHOR_OUTPUT
HHEVAL_ANCHOR_OUTPUT=$worker_root/manifest.tsv
export HHEVAL_ANCHOR_OUTPUT

export HOLDIR="$HHEVAL_ANCHOR_RUNTIME_WORKTREE"
export HOL4_HAMMER_DIR="$worker_root/hammer"
export HHEVAL_ANCHOR_WORKER_ROOT="$worker_root"
export HHEVAL_ANCHOR_DRIVER="$tool_dir/phase2-anchor-manifest.sml"
export HHEVAL_ANCHOR_SOURCE_COMMIT="$behavior_commit"
export HHEVAL_ANCHOR_BEHAVIOR_COMMIT="$behavior_commit"
export HHEVAL_ANCHOR_JOURNAL="$journal_member"
export HHEVAL_ANCHOR_LEGACY_ROWS="$legacy_rows"
export HHEVAL_ANCHOR_COMMAND_ROWS="$command_rows"
accepted_run=src/holyhammer/eval/phase2-s30-v3/run.json
export HHEVAL_ANCHOR_ACCEPTED_RUN_HEADER="$accepted_run"
export HHEVAL_ANCHOR_ACCEPTED_RUN_HEADER_SHA256="$run_sha"
accepted_journal=src/holyhammer/eval/phase2-s30-v3/journal/\*.jsonl
export HHEVAL_ANCHOR_ACCEPTED_JOURNAL="$accepted_journal"
export HHEVAL_ANCHOR_ACCEPTED_JOURNAL_SHA256="$accepted_journal_sha"
export HHEVAL_ANCHOR_INPUT_RUN_HEADER_SHA256="$run_sha"
input_journal=src/holyhammer/eval/phase2-s30-v3/journal/\
$certificate_member_file
export HHEVAL_ANCHOR_INPUT_JOURNAL="$input_journal"
HHEVAL_ANCHOR_INPUT_JOURNAL_SHA256=$certificate_member_sha
export HHEVAL_ANCHOR_INPUT_JOURNAL_SHA256
export HHEVAL_ANCHOR_PAIRED_ROWS_SHA256="$paired_sha"
export HHEVAL_ANCHOR_COMMAND_ROWS_SHA256="$command_sha"

controller_log=$worker_root/controller.log
if "$HHEVAL_ANCHOR_RUNTIME_WORKTREE/bin/hol" < \
    "$tool_dir/phase2-anchor-manifest-controller.sml" \
    > "$controller_log" 2>&1
then
  status=0
else
  status=$?
fi
cat "$controller_log"
test "$status" -eq 0 &&
  grep -F "HHEVAL_ANCHOR_CONTROLLER=success" \
    "$controller_log" >/dev/null &&
  test -f "$HHEVAL_ANCHOR_OUTPUT" || {
  echo "anchor manifest controller did not complete" >&2
  exit 1
}
mv "$HHEVAL_ANCHOR_OUTPUT" "$requested_output"
case "${HHEVAL_ANCHOR_CAPTURE_DIR-}" in
  "") ;;
  *)
    test ! -e "$HHEVAL_ANCHOR_CAPTURE_DIR"
    mkdir -p "$HHEVAL_ANCHOR_CAPTURE_DIR"
    cp -a "$worker_root/hammer/problems" "$HHEVAL_ANCHOR_CAPTURE_DIR/"
    ;;
esac
