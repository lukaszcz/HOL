#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 1)); then
  echo "usage: $0 SEALED_INPUTS" >&2
  exit 2
fi

INPUTS=$(realpath "$1")
TOOLS=$(dirname "$(realpath "$0")")
INPUT_SHA=$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)
TEMP=$(mktemp -d)
cleanup() {
  chmod -R u+w "$TEMP" 2>/dev/null || true
  rm -rf "$TEMP"
}
trap cleanup EXIT HUP INT TERM

tree_digest() {
  local directory=$1
  (cd "$directory" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
}

FIXTURE="$TEMP/fixture"
mkdir -p "$FIXTURE/journal"
printf 'fixture\tfixture.fresh\nfixture\tfixture.seen\n' \
  >"$TEMP/canonical-goals.tsv"

"$INPUTS/verify-inputs.sh" "$INPUTS"
before=$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)
"$INPUTS/verify-inputs.sh" "$INPUTS"
after=$(sha256sum "$INPUTS/SHA256SUMS" | cut -d' ' -f1)
[[ "$before" == "$after" ]]

cp -a "$INPUTS" "$TEMP/tampered"
chmod -R u+w "$TEMP/tampered"
printf '\n' >>"$TEMP/tampered/task11-driver.sml"
if "$TEMP/tampered/verify-inputs.sh" "$TEMP/tampered" >/dev/null 2>&1; then
  echo "tampered input unexpectedly verified" >&2
  exit 1
fi

jq -n '
  def c($id;$prover;$selector):
    {cond_id:$id,regime:"chainy",selector:$selector,engine:"prover",
     prover:$prover,timeout:30,reconstruct:true};
  {schema:4,expname:"fixture",date:"fixture",host:"fixture",
   hol_commit:"fixture",provers:[],
   corpus:[{thy:"fixture",theorem_count:2,dep_stamp:"fixture"}],
   added_from_dat:[],sample:1,
   conditions:[c("f30-vampire-knn";"vampire";"knn96"),
     c("f30-vampire-mepo";"vampire";"mepo96"),
     c("f30-vampire-mash";"vampire";"mash96"),
     c("f30-vampire-mesh";"vampire";"mesh96"),
     c("f30-e-knn";"e";"knn128"),
     c("f30-e-mepo";"e";"mepo128"),
     c("f30-e-mash";"e";"mash128"),
     c("f30-e-mesh";"e";"mesh128")]}
' >"$FIXTURE/run.json"

jq -nc '
  def row($goal;$fresh;$cond;$prover;$selector;$proved):
    {run:"experiment",thy:"fixture",thm:$goal,
     goal_id:("fixture."+$goal),cond:$cond,regime:"chainy",
     selector:$selector,engine:"prover",ho:false,fresh:$fresh,
     prover:$prover,
     prover_version:(if $prover == "e" then "3.2.5-ho" else "5.0.1" end),
     nfacts:($selector | capture("(?<count>[0-9]+)$").count | tonumber),
     timeout:30,t_prover:0,stac:(if $proved then "fixture" else null end),
     szs:(if $proved then "Theorem" else "Timeout" end),
     axioms_used:(if $proved then [] else null end),
     recon_ok:(if $proved then true else null end),
     recon_method:(if $proved then "metis" else null end),
     t_recon:(if $proved then 0 else null end),error:null};
  [["vampire","knn96"],["vampire","mepo96"],
   ["vampire","mash96"],["vampire","mesh96"],
   ["e","knn128"],["e","mepo128"],["e","mash128"],
   ["e","mesh128"]][] as $spec |
  ($spec[1] | sub("[0-9]+$"; "")) as $filter |
  [row("seen";false;("f30-"+$spec[0]+"-"+$filter);
      $spec[0];$spec[1];($filter == "mash" or $filter == "mesh")),
   row("fresh";true;("f30-"+$spec[0]+"-"+$filter);
      $spec[0];$spec[1];($filter != "knn"))][]
' >"$FIXTURE/journal/fixture.part-0-of-1.jsonl"

HHEVAL_TASK11_SELFTEST=1 HHEVAL_TASK11_EXPECTED_GOALS=2 \
  HHEVAL_TASK11_EXPECTED_THEORIES=1 HHEVAL_TASK11_EXPECTED_NONEMPTY=1 \
  "$TOOLS/fold-result.sh" "$FIXTURE" fixture "$TEMP/result.json" \
  "$TEMP/inventory.tsv" "$TEMP/canonical-goals.tsv"
jq -e '.gate.pass and .shape.criterion_a_pass and
  .shape.criterion_b_pass' "$TEMP/result.json" >/dev/null

EXTRA="$TEMP/extra"
cp -a "$FIXTURE" "$EXTRA"
jq -nc '
  def row($cond;$prover;$selector):
    {run:"experiment",thy:"fixture",thm:"post_corpus",
     goal_id:"fixture.post_corpus",cond:$cond,regime:"chainy",
     selector:$selector,engine:"prover",ho:false,fresh:true,
     prover:$prover,
     prover_version:(if $prover == "e" then "3.2.5-ho" else "5.0.1" end),
     nfacts:($selector | capture("(?<count>[0-9]+)$").count | tonumber),
     timeout:30,t_prover:0,szs:"Timeout",axioms_used:null,
     recon_ok:null,recon_method:null,t_recon:null,stac:null,error:null};
  [["vampire","knn96"],["vampire","mepo96"],
   ["vampire","mash96"],["vampire","mesh96"],
   ["e","knn128"],["e","mepo128"],
   ["e","mash128"],["e","mesh128"]][] as $spec |
  ($spec[1] | sub("[0-9]+$"; "")) as $filter |
  row(("f30-"+$spec[0]+"-"+$filter);$spec[0];$spec[1])
' >>"$EXTRA/journal/fixture.part-0-of-1.jsonl"
HHEVAL_TASK11_ALLOW_SUPERSET=1 HHEVAL_TASK11_SELFTEST=1 \
  HHEVAL_TASK11_EXPECTED_GOALS=2 HHEVAL_TASK11_EXPECTED_THEORIES=1 \
  HHEVAL_TASK11_EXPECTED_NONEMPTY=1 \
  "$TOOLS/fold-result.sh" "$EXTRA" fixture "$TEMP/extra.json" \
    "$TEMP/extra.tsv" "$TEMP/canonical-goals.tsv"
jq -e '.excluded_extra_goals == 1 and .observed_cells == 24' \
  "$TEMP/extra.json" >/dev/null
cp "$TEMP/extra.json" "$EXTRA/result.json"
"$TOOLS/make-auxiliary-evidence.sh" "$EXTRA" \
  "$TEMP/canonical-goals.tsv" "$TEMP/excluded.tsv" \
  "$TEMP/criterion-b.md"
cmp <(printf '%s\n' fixture.post_corpus) "$TEMP/excluded.tsv"
[[ -s "$TEMP/criterion-b.md" ]]

for mutation in timeout prover selector nfacts regime engine fresh ho \
    timing error; do
  BAD_EXTRA="$TEMP/bad-extra-$mutation"
  cp -a "$EXTRA" "$BAD_EXTRA"
  case "$mutation" in
    timeout) change='.timeout = 31' ;;
    prover) change='.prover = "e"' ;;
    selector) change='.selector = "mepo96"' ;;
    nfacts) change='.nfacts = 97' ;;
    regime) change='.regime = "plain"' ;;
    engine) change='.engine = "replay"' ;;
    fresh) change='.fresh = false' ;;
    ho) change='.ho = true' ;;
    timing) change='.t_prover = -1' ;;
    error) change='.error = {bad:true}' ;;
  esac
  jq -c "if .goal_id == \"fixture.post_corpus\" and
      .cond == \"f30-vampire-knn\" then $change else . end" \
    "$BAD_EXTRA/journal/fixture.part-0-of-1.jsonl" \
    >"$BAD_EXTRA/journal/fixture.part-0-of-1.jsonl.new"
  mv "$BAD_EXTRA/journal/fixture.part-0-of-1.jsonl.new" \
    "$BAD_EXTRA/journal/fixture.part-0-of-1.jsonl"
  if HHEVAL_TASK11_ALLOW_SUPERSET=1 HHEVAL_TASK11_SELFTEST=1 \
      HHEVAL_TASK11_EXPECTED_GOALS=2 HHEVAL_TASK11_EXPECTED_THEORIES=1 \
      HHEVAL_TASK11_EXPECTED_NONEMPTY=1 \
      "$TOOLS/fold-result.sh" "$BAD_EXTRA" fixture \
        "$TEMP/bad-extra.json" "$TEMP/bad-extra.tsv" \
        "$TEMP/canonical-goals.tsv" >/dev/null 2>&1; then
    echo "invalid excluded $mutation row unexpectedly folded" >&2
    exit 1
  fi
done

printf '%s\n' "$(head -1 "$FIXTURE/journal/fixture.part-0-of-1.jsonl")" \
  >>"$FIXTURE/journal/fixture.part-0-of-1.jsonl"
if HHEVAL_TASK11_SELFTEST=1 HHEVAL_TASK11_EXPECTED_GOALS=2 \
    HHEVAL_TASK11_EXPECTED_THEORIES=1 HHEVAL_TASK11_EXPECTED_NONEMPTY=1 \
    "$TOOLS/fold-result.sh" "$FIXTURE" fixture "$TEMP/bad.json" \
      "$TEMP/bad.tsv" "$TEMP/canonical-goals.tsv" >/dev/null 2>&1; then
  echo "duplicate journal cell unexpectedly folded" >&2
  exit 1
fi

# Exercise the production durable-resume path without running a prover.  This
# represents a worker killed after its atomic artifact rename but before its
# certificate was committed.  Recovery must consume that artifact, remove all
# mutable checkpoint/tmpfs state, and then become a mutation-free no-op.
RESUME="$TEMP/resume"
export HHEVAL_TASK11_ROOT="$TEMP/root"
export HHEVAL_TASK11_EVIDENCE_ROOT="$RESUME/evidence"
export HHEVAL_TASK11_INPUTS="$INPUTS"
export HHEVAL_TASK11_EXPERIMENT=fixture-resume
export HHEVAL_TASK11_STATE_BASE="$RESUME/state"
RUN="$HHEVAL_TASK11_EVIDENCE_ROOT/runs/$HHEVAL_TASK11_EXPERIMENT"
STATE="$HHEVAL_TASK11_STATE_BASE/$HHEVAL_TASK11_EXPERIMENT"
JOURNAL_FILE="$RUN/artifacts/atoms/fixture-0-of-1/experiment/"\
"journal/fixture.part-0-of-1.jsonl"
mkdir -p "$RUN/artifacts/atoms/fixture-0-of-1/experiment/journal"
mkdir -p "$RUN/atom-certificates" "$RUN/journal" "$RUN/checkpoints"
mkdir -p "$RUN/pending"
mkdir -p "$RUN/log" "$STATE/atoms/fixture-0-of-1" "$TEMP/theory"
printf 'fixture-0-of-1\tfixture\t0\t1\t%s\n' "$TEMP/theory" \
  >"$RUN/atoms.tsv"
touch "$JOURNAL_FILE"
pending_tree=$(tree_digest "$RUN/artifacts/atoms/fixture-0-of-1")
pending_journal=$(sha256sum "$JOURNAL_FILE" | cut -d' ' -f1)
jq -n --arg tree "$pending_tree" --arg journal "$pending_journal" \
  --arg input "$INPUT_SHA" '
  {schema:"hh-task11-f30-pending-v1",atom:"fixture-0-of-1",
   input_inventory_sha256:$input,artifact_tree_sha256:$tree,
   journal_sha256:$journal}
' >"$RUN/pending/fixture-0-of-1.json"
printf 'stale checkpoint\n' >"$RUN/checkpoints/fixture-0-of-1.jsonl"
printf '2\n' >"$RUN/checkpoints/fixture-0-of-1.attempts"
source "$TOOLS/run.sh"
bash -Eeuo pipefail -c 'declare -F verify_pending_atom >/dev/null'
run_atom fixture-0-of-1 fixture 0 1 "$TEMP/theory"
verify_atom fixture-0-of-1
[[ ! -e "$STATE/atoms/fixture-0-of-1" ]]
[[ ! -e "$RUN/checkpoints/fixture-0-of-1.jsonl" ]]
[[ ! -e "$RUN/checkpoints/fixture-0-of-1.attempts" ]]
resume_before=$(tree_digest "$RUN")
run_atom fixture-0-of-1 fixture 0 1 "$TEMP/theory"
resume_after=$(tree_digest "$RUN")
[[ "$resume_before" == "$resume_after" ]]

chmod u+w "$RUN/atom-certificates/fixture-0-of-1.json"
jq '.journal_sha256 = "corrupt"' \
  "$RUN/atom-certificates/fixture-0-of-1.json" \
  >"$RUN/atom-certificates/corrupt.json"
mv "$RUN/atom-certificates/corrupt.json" \
  "$RUN/atom-certificates/fixture-0-of-1.json"
corrupt_before=$(tree_digest "$RUN")
if verify_atom fixture-0-of-1 >/dev/null 2>&1; then
  echo "corrupt atom certificate unexpectedly resumed" >&2
  exit 1
fi
corrupt_after=$(tree_digest "$RUN")
[[ "$corrupt_before" == "$corrupt_after" ]]
