#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 3)); then
  echo "usage: $0 SEALED_ENDURANCE_SAMPLE PHASE2_SAMPLE OUTPUT" >&2
  exit 2
fi

source_sample=$(realpath "$1")
baseline=$(realpath "$2")
output=$3
tools=$(dirname "$(realpath "$0")")
expected_baseline=4c0da14d6a7e5054fe6976ba26cdce76244b0e4b28ff990768f55344a3b322a2
[[ ! -e "$output" ]]
[[ "$(sha256sum "$baseline" | cut -d' ' -f1)" == "$expected_baseline" ]]
temp=$(mktemp -d)
trap 'rm -rf "$temp"' EXIT HUP INT TERM

mkdir "$output"
cp -a "$source_sample/endurance" "$output/endurance"
cp "$source_sample/canonical-goals.tsv" "$source_sample/schedule.tsv" \
  "$output/"
jq -r '[.goal_id,.thy]|@tsv' "$output/endurance/journal.jsonl" |
  while IFS=$'\t' read -r goal theory; do
    printf '%s\t%s\t%s\n' \
      "$(printf '%s' "$goal" | sha256sum | cut -d' ' -f1)" \
      "$theory" "$goal"
  done | LC_ALL=C sort -t $'\t' -k1,1 -k3,3 | head -n 3000 \
  >"$output/sample-selection.tsv"
cut -f3 "$output/sample-selection.tsv" >"$temp/ids"
jq -Rn --rawfile ids "$temp/ids" '
  $ids|split("\n")|map(select(length>0))|INDEX(.)
' >"$temp/set"
jq -c --slurpfile selected "$temp/set" \
  'select($selected[0][.goal_id] != null)' \
  "$output/endurance/journal.jsonl" | LC_ALL=C sort -S 64M \
  >"$output/s30v5-sample.jsonl"
cp "$baseline" "$output/s30v3-sample.jsonl"
jq -n --slurpfile old "$output/s30v3-sample.jsonl" \
  --slurpfile new "$output/s30v5-sample.jsonl" \
  --rawfile schedule "$output/schedule.tsv" -f "$tools/paired-result.jq" |
  jq -S . >"$output/result.json"
jq -n --slurpfile old "$output/s30v3-sample.jsonl" \
  --slurpfile new "$output/s30v5-sample.jsonl" \
  -f "$tools/loss-investigations.jq" | jq -c '.[]' \
  >"$output/loss-investigations.jsonl"
head -n 128 "$output/sample-selection.tsv" | cut -f2,3 \
  >"$output/k-subset.tsv"

created=$(jq -r '.created' "$source_sample/sample-certificate.json")
jq -n --arg created "$created" \
  --arg input "$(jq -r '.input_inventory_sha256' \
    "$source_sample/sample-certificate.json")" \
  --arg schedule "$(sha256sum "$output/schedule.tsv" | cut -d' ' -f1)" \
  --arg frame "$(sha256sum "$output/endurance/journal.jsonl" |
    cut -d' ' -f1)" \
  --arg inventory "$(sha256sum "$output/endurance/atom-inventory.tsv" |
    cut -d' ' -f1)" \
  --arg terminal "$(sha256sum \
    "$output/endurance/terminal-certificate.json" | cut -d' ' -f1)" \
  --arg selection "$(sha256sum "$output/sample-selection.tsv" |
    cut -d' ' -f1)" \
  --arg old "$(sha256sum "$output/s30v3-sample.jsonl" | cut -d' ' -f1)" \
  --arg new "$(sha256sum "$output/s30v5-sample.jsonl" | cut -d' ' -f1)" \
  --arg result "$(sha256sum "$output/result.json" | cut -d' ' -f1)" \
  --arg losses "$(sha256sum "$output/loss-investigations.jsonl" |
    cut -d' ' -f1)" \
  --arg k "$(sha256sum "$output/k-subset.tsv" | cut -d' ' -f1)" '
  {schema:"hh-task12-revised-input-v4",status:"sample-sealed",
   created:$created,input_inventory_sha256:$input,schedule_sha256:$schedule,
   completed_atomic_frame:{atoms:408,goals:3119,journal_sha256:$frame,
     atom_inventory_sha256:$inventory,terminal_certificate_sha256:$terminal,
     state_root:"/run/user/1003/holyhammer-phase3-task12/phase3-task12-s30v5-v5",
     state_root_removed:true,selection_independent_of_cell_outcome:true,
     no_within_atom_partial_completion:true,
     membership_recomputed_with_hheval_partition:true},
   sample:{algorithm:"lowest SHA-256(goal_id), bytewise",goals:3000,
     selection_sha256:$selection,s30v3_sha256:$old,s30v5_sha256:$new,
     result_sha256:$result,loss_investigations_sha256:$losses},
   phase2_anchor:{sample_sha256:$old,
     full_journal_manifest_sha256:
       "d2b145c9a16710611dcb61acdfc8e0635fd8acc46259e9ac2bddda7ca50c3318",
     task10_final_sha256:
       "4a9f965a6571843a1b36abda51aa973e531ae20ecc42e68eaa9b0e10cf653660"},
   k_subset:{algorithm:"first 128 rows of sealed sample selection",
     goals:128,sha256:$k},tuning_performed:false,
   full_corpus_s30v5_measured:false,no_full_corpus_claim:true}
' >"$output/sample-certificate.json"
(cd "$output" && find . -type f ! -name SHA256SUMS -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$output/SHA256SUMS"
chmod -R a-w "$output"
