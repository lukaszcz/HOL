#!/usr/bin/env bash
set -Eeuo pipefail
trap 'status=$?; echo "TASK12 selftest failed at line $LINENO" >&2;
  exit "$status"' ERR

if (($# != 1)); then
  echo "usage: $0 FINAL_EVIDENCE" >&2
  exit 2
fi

FINAL=$(realpath "$1")
TOOLS=$(dirname "$(realpath "$0")")
if [[ -d "$FINAL/verifier/verify-bin" ]]; then
  PATH="$FINAL/verifier/verify-bin"
  export PATH
fi
TEMP=$(mktemp -d)
cleanup() {
  chmod -R u+w "$TEMP" 2>/dev/null || true
  rm -rf "$TEMP"
}
trap cleanup EXIT HUP INT TERM

tree_digest() {
  (cd "$1" && find . -type f -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
}

reseal_component() {
  local root=$1 component=$2 field=$3
  chmod u+w "$root" "$root/$component"
  (cd "$root/$component" &&
    find . -type f ! -name SHA256SUMS -print0 | LC_ALL=C sort -z |
    xargs -0 sha256sum) >"$root/$component/SHA256SUMS"
  local digest
  digest=$(sha256sum "$root/$component/SHA256SUMS" | cut -d' ' -f1)
  chmod u+w "$root/final-certificate.json"
  jq --arg digest "$digest" --arg field "$field" \
    '.[$field]=$digest' "$root/final-certificate.json" \
    >"$root/final-certificate.json.new"
  mv "$root/final-certificate.json.new" "$root/final-certificate.json"
}

relink_k() {
  local root=$1 k_dir="$1/k" result terminal_digest
  result=$(sha256sum "$k_dir/certificate.json" | cut -d' ' -f1)
  chmod u+w "$k_dir/terminal-service.json"
  jq --arg result "$result" '.k_certificate_sha256=$result' \
    "$k_dir/terminal-service.json" >"$k_dir/terminal-service.json.new"
  mv "$k_dir/terminal-service.json.new" "$k_dir/terminal-service.json"
  terminal_digest=$(sha256sum "$k_dir/terminal-service.json" | cut -d' ' -f1)
  reseal_component "$root" k k_inventory_sha256
  chmod u+w "$root/final-certificate.json"
  jq --arg terminal "$terminal_digest" \
    '.k_terminal_certificate_sha256=$terminal' \
    "$root/final-certificate.json" >"$root/final-certificate.json.new"
  mv "$root/final-certificate.json.new" "$root/final-certificate.json"
}

before=$(tree_digest "$FINAL")
"$TOOLS/verify-result.sh" "$FINAL"
[[ "$before" == "$(tree_digest "$FINAL")" ]]

cp -a "$FINAL" "$TEMP/tampered-result"
chmod u+w "$TEMP/tampered-result/sample/result.json"
printf '\n' >>"$TEMP/tampered-result/sample/result.json"
if "$TEMP/tampered-result/verifier/verify-result.sh" \
    "$TEMP/tampered-result" >/dev/null 2>&1; then
  echo "tampered paired result unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/coherent-result"
chmod u+w "$TEMP/coherent-result/sample" \
  "$TEMP/coherent-result/sample/result.json" \
  "$TEMP/coherent-result/sample/SHA256SUMS"
jq '.proved.delta += 1' "$TEMP/coherent-result/sample/result.json" \
  >"$TEMP/result.json"
mv "$TEMP/result.json" "$TEMP/coherent-result/sample/result.json"
reseal_component "$TEMP/coherent-result" sample sample_inventory_sha256
if "$TEMP/coherent-result/verifier/verify-result.sh" \
    "$TEMP/coherent-result" >/dev/null 2>&1; then
  echo "coherently resealed false semantic result unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/compensated-baseline"
baseline="$TEMP/compensated-baseline/sample/s30v3-sample.jsonl"
sample_dir="$TEMP/compensated-baseline/sample"
chmod u+w "$sample_dir" "$baseline" "$sample_dir/result.json" \
  "$sample_dir/loss-investigations.jsonl" \
  "$sample_dir/sample-certificate.json" "$sample_dir/SHA256SUMS"
jq -sc '
  ([to_entries[]|select(.value.szs=="Theorem")][0].key) as $proved |
  ([to_entries[]|select(.value.szs!="Theorem")][0].key) as $failed |
  .[$proved].szs as $ps | .[$proved].recon_ok as $pr |
  .[$failed].szs as $fs | .[$failed].recon_ok as $fr |
  .[$proved].szs=$fs | .[$proved].recon_ok=$fr |
  .[$failed].szs=$ps | .[$failed].recon_ok=$pr | .[]
' "$baseline" | jq -c . >"$TEMP/swapped-baseline.jsonl"
mv "$TEMP/swapped-baseline.jsonl" "$baseline"
jq -n --slurpfile old "$baseline" \
  --slurpfile new "$sample_dir/s30v5-sample.jsonl" \
  --rawfile schedule "$sample_dir/schedule.tsv" \
  -f "$FINAL/verifier/paired-result.jq" | jq -S . \
  >"$sample_dir/result.json"
jq -n --slurpfile old "$baseline" \
  --slurpfile new "$sample_dir/s30v5-sample.jsonl" \
  -f "$FINAL/verifier/loss-investigations.jq" | jq -c '.[]' \
  >"$sample_dir/loss-investigations.jsonl"
jq --arg old "$(sha256sum "$baseline" | cut -d' ' -f1)" \
  --arg result "$(sha256sum "$sample_dir/result.json" | cut -d' ' -f1)" \
  --arg losses "$(sha256sum "$sample_dir/loss-investigations.jsonl" |
    cut -d' ' -f1)" '
  .sample.s30v3_sha256=$old | .sample.result_sha256=$result |
  .sample.loss_investigations_sha256=$losses
' "$sample_dir/sample-certificate.json" >"$TEMP/sample-certificate.json"
mv "$TEMP/sample-certificate.json" "$sample_dir/sample-certificate.json"
reseal_component "$TEMP/compensated-baseline" sample \
  sample_inventory_sha256
if "$TEMP/compensated-baseline/verifier/verify-result.sh" \
    "$TEMP/compensated-baseline" >/dev/null 2>&1; then
  echo "compensated Phase 2 outcome swap unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/coherent-atom"
inventory="$TEMP/coherent-atom/sample/endurance/atom-inventory.tsv"
atom=$(awk -F '\t' 'NR == 1 {print $1}' "$inventory")
certificate="$TEMP/coherent-atom/sample/endurance/atom-certificates/$atom.json"
chmod u+w "$TEMP/coherent-atom/sample/endurance" \
  "$TEMP/coherent-atom/sample/endurance/atom-certificates" \
  "$inventory" "$certificate" \
  "$TEMP/coherent-atom/sample/SHA256SUMS"
false_hash=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
jq --arg hash "$false_hash" '.journal_sha256=$hash' "$certificate" \
  >"$TEMP/atom.json"
mv "$TEMP/atom.json" "$certificate"
certificate_hash=$(sha256sum "$certificate" | cut -d' ' -f1)
awk -F '\t' -v OFS='\t' -v atom="$atom" -v journal="$false_hash" \
  -v certificate="$certificate_hash" \
  '$1==atom {$4=journal;$5=certificate} {print}' "$inventory" \
  >"$TEMP/inventory.tsv"
mv "$TEMP/inventory.tsv" "$inventory"
reseal_component "$TEMP/coherent-atom" sample sample_inventory_sha256
if "$TEMP/coherent-atom/verifier/verify-result.sh" \
    "$TEMP/coherent-atom" >/dev/null 2>&1; then
  echo "coherently resealed false atom segment unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/boundary-9-8"
sample_dir="$TEMP/boundary-9-8/sample"
inventory="$sample_dir/endurance/atom-inventory.tsv"
cert_dir="$sample_dir/endurance/atom-certificates"
terminal="$sample_dir/endurance/terminal-certificate.json"
chmod u+w "$sample_dir" "$sample_dir/endurance" "$cert_dir" \
  "$inventory" "$terminal" "$sample_dir/sample-certificate.json" \
  "$sample_dir/SHA256SUMS"
first_atom=$(awk -F '\t' 'NR==34 {print $1}' "$inventory")
second_atom=$(awk -F '\t' 'NR==35 {print $1}' "$inventory")
first_line=$(awk -F '\t' 'NR<34 {sum+=$2} END {print sum+1}' "$inventory")
awk -v first="$first_line" 'NR>=first && NR<first+8' \
  "$sample_dir/endurance/journal.jsonl" >"$TEMP/first-segment"
awk -v first="$((first_line + 8))" 'NR>=first && NR<first+9' \
  "$sample_dir/endurance/journal.jsonl" >"$TEMP/second-segment"
first_hash=$(sha256sum "$TEMP/first-segment" | cut -d' ' -f1)
second_hash=$(sha256sum "$TEMP/second-segment" | cut -d' ' -f1)
for spec in "$first_atom:8:$first_hash" "$second_atom:9:$second_hash"; do
  IFS=: read -r atom cells journal_hash <<<"$spec"
  certificate="$cert_dir/$atom.json"
  chmod u+w "$certificate"
  jq --argjson cells "$cells" --arg hash "$journal_hash" \
    '.cells=$cells | .journal_sha256=$hash' "$certificate" \
    >"$TEMP/certificate.json"
  mv "$TEMP/certificate.json" "$certificate"
done
first_cert=$(sha256sum "$cert_dir/$first_atom.json" | cut -d' ' -f1)
second_cert=$(sha256sum "$cert_dir/$second_atom.json" | cut -d' ' -f1)
awk -F '\t' -v OFS='\t' -v a="$first_atom" -v ah="$first_hash" \
  -v ac="$first_cert" -v b="$second_atom" -v bh="$second_hash" \
  -v bc="$second_cert" '
  $1==a {$2=8;$4=ah;$5=ac} $1==b {$2=9;$4=bh;$5=bc} {print}
' "$inventory" >"$TEMP/inventory.tsv"
mv "$TEMP/inventory.tsv" "$inventory"
inventory_hash=$(sha256sum "$inventory" | cut -d' ' -f1)
jq --arg hash "$inventory_hash" '.atom_inventory_sha256=$hash' \
  "$terminal" >"$TEMP/terminal.json"
mv "$TEMP/terminal.json" "$terminal"
terminal_hash=$(sha256sum "$terminal" | cut -d' ' -f1)
jq --arg inventory "$inventory_hash" --arg terminal "$terminal_hash" '
  .completed_atomic_frame.atom_inventory_sha256=$inventory |
  .completed_atomic_frame.terminal_certificate_sha256=$terminal
' "$sample_dir/sample-certificate.json" >"$TEMP/sample-certificate.json"
mv "$TEMP/sample-certificate.json" "$sample_dir/sample-certificate.json"
reseal_component "$TEMP/boundary-9-8" sample sample_inventory_sha256
if "$TEMP/boundary-9-8/verifier/verify-result.sh" \
    "$TEMP/boundary-9-8" >/dev/null 2>&1; then
  echo "coherent 9/8 atom-boundary shift unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/coherent-schedule"
chmod u+w "$TEMP/coherent-schedule/sample" \
  "$TEMP/coherent-schedule/sample/schedule.tsv" \
  "$TEMP/coherent-schedule/sample/SHA256SUMS"
sed '1s/\t96\t/\t97\t/' "$TEMP/coherent-schedule/sample/schedule.tsv" \
  >"$TEMP/schedule.tsv"
mv "$TEMP/schedule.tsv" "$TEMP/coherent-schedule/sample/schedule.tsv"
reseal_component "$TEMP/coherent-schedule" sample sample_inventory_sha256
if "$TEMP/coherent-schedule/verifier/verify-result.sh" \
    "$TEMP/coherent-schedule" >/dev/null 2>&1; then
  echo "coherently resealed divergent schedule unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/coherent-duplicate"
journal="$TEMP/coherent-duplicate/sample/s30v5-sample.jsonl"
chmod u+w "$TEMP/coherent-duplicate/sample" "$journal" \
  "$TEMP/coherent-duplicate/sample/SHA256SUMS"
head -n 2999 "$journal" >"$TEMP/duplicate.jsonl"
head -n 1 "$journal" >>"$TEMP/duplicate.jsonl"
mv "$TEMP/duplicate.jsonl" "$journal"
reseal_component "$TEMP/coherent-duplicate" sample sample_inventory_sha256
if "$TEMP/coherent-duplicate/verifier/verify-result.sh" \
    "$TEMP/coherent-duplicate" >/dev/null 2>&1; then
  echo "coherently resealed duplicate sample row unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/coherent-k"
k_journal="$TEMP/coherent-k/k/replay-journal.jsonl"
chmod u+w "$TEMP/coherent-k/k" "$k_journal" \
  "$TEMP/coherent-k/k/SHA256SUMS"
head -n 1 "$k_journal" | jq -c '.slices[0].cached=false' \
  >"$TEMP/k-first.jsonl"
tail -n +2 "$k_journal" >>"$TEMP/k-first.jsonl"
mv "$TEMP/k-first.jsonl" "$k_journal"
prime_hash=$(sha256sum "$k_journal" | cut -d' ' -f1)
jq --arg journal "$prime_hash" '.replay_journal_sha256=$journal' \
  "$TEMP/coherent-k/k/certificate.json" >"$TEMP/k-certificate.json"
mv "$TEMP/k-certificate.json" "$TEMP/coherent-k/k/certificate.json"
relink_k "$TEMP/coherent-k"
if "$TEMP/coherent-k/verifier/verify-result.sh" \
    "$TEMP/coherent-k" >/dev/null 2>&1; then
  echo "coherently resealed non-cached K cell unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/coherent-k-prime"
k_journal="$TEMP/coherent-k-prime/k/prime-journal.jsonl"
chmod u+w "$TEMP/coherent-k-prime/k" "$k_journal" \
  "$TEMP/coherent-k-prime/k/SHA256SUMS"
head -n 1 "$k_journal" | jq -c '.slices[0].cached=false' \
  >"$TEMP/k-prime-first.jsonl"
tail -n +2 "$k_journal" >>"$TEMP/k-prime-first.jsonl"
mv "$TEMP/k-prime-first.jsonl" "$k_journal"
prime_hash=$(sha256sum "$k_journal" | cut -d' ' -f1)
jq --arg journal "$prime_hash" '.prime_journal_sha256=$journal' \
  "$TEMP/coherent-k-prime/k/certificate.json" >"$TEMP/k-certificate.json"
mv "$TEMP/k-certificate.json" \
  "$TEMP/coherent-k-prime/k/certificate.json"
relink_k "$TEMP/coherent-k-prime"
if "$TEMP/coherent-k-prime/verifier/verify-result.sh" \
    "$TEMP/coherent-k-prime" >/dev/null 2>&1; then
  echo "coherently resealed non-cached K prime cell unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/coherent-k-versions"
k_dir="$TEMP/coherent-k-versions/k"
chmod u+w "$k_dir" "$k_dir/version-spawns.tsv" \
  "$k_dir/certificate.json" "$k_dir/SHA256SUMS"
awk -F '\t' 'BEGIN {OFS="\t"} NR==1 {$2=2} {print}' \
  "$k_dir/version-spawns.tsv" >"$TEMP/version-spawns.tsv"
mv "$TEMP/version-spawns.tsv" "$k_dir/version-spawns.tsv"
jq '.version_resolution_spawns=80 |
  .explicit_version_resolution.observed_spawns=80' \
  "$k_dir/certificate.json" >"$TEMP/k-certificate.json"
mv "$TEMP/k-certificate.json" "$k_dir/certificate.json"
relink_k "$TEMP/coherent-k-versions"
if "$TEMP/coherent-k-versions/verifier/verify-result.sh" \
    "$TEMP/coherent-k-versions" >/dev/null 2>&1; then
  echo "coherently resealed missing K version probe unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/coherent-k-fresh-root"
k_dir="$TEMP/coherent-k-fresh-root/k"
chmod u+w "$k_dir" "$k_dir/fresh-root-proof.json" \
  "$k_dir/certificate.json" "$k_dir/SHA256SUMS"
jq '.resume_allowed=true' "$k_dir/fresh-root-proof.json" \
  >"$TEMP/fresh-root-proof.json"
mv "$TEMP/fresh-root-proof.json" "$k_dir/fresh-root-proof.json"
fresh_hash=$(sha256sum "$k_dir/fresh-root-proof.json" | cut -d' ' -f1)
jq --arg fresh "$fresh_hash" '.fresh_root_proof_sha256=$fresh' \
  "$k_dir/certificate.json" >"$TEMP/k-certificate.json"
mv "$TEMP/k-certificate.json" "$k_dir/certificate.json"
relink_k "$TEMP/coherent-k-fresh-root"
if "$TEMP/coherent-k-fresh-root/verifier/verify-result.sh" \
    "$TEMP/coherent-k-fresh-root" >/dev/null 2>&1; then
  echo "coherently resealed resumable K roots unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/tampered-resume"
certificate=$(find \
  "$TEMP/tampered-resume/sample/endurance/atom-certificates" \
  -type f -print -quit)
chmod u+w "$certificate"
printf '\n' >>"$certificate"
if "$TEMP/tampered-resume/verifier/verify-result.sh" \
    "$TEMP/tampered-resume" >/dev/null 2>&1; then
  echo "tampered resume certificate unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/missing-dependency"
chmod -R u+w "$TEMP/missing-dependency/verifier/verify-bin"
rm "$TEMP/missing-dependency/verifier/verify-bin/jq"
if "$TEMP/missing-dependency/verifier/verify-result.sh" \
    "$TEMP/missing-dependency" >/dev/null 2>&1; then
  echo "missing frozen verifier dependency unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/tampered-runtime-object"
runtime_manifest="$TEMP/tampered-runtime-object/provenance/"\
"runtime-provenance/target-theory-objects.tsv"
chmod u+w "$(dirname "$runtime_manifest")" "$runtime_manifest"
sed '1s/^[0-9a-f]/0/' "$runtime_manifest" >"$TEMP/runtime-manifest"
mv "$TEMP/runtime-manifest" "$runtime_manifest"
if "$TEMP/tampered-runtime-object/verifier/verify-result.sh" \
    "$TEMP/tampered-runtime-object" >/dev/null 2>&1; then
  echo "altered target-theory runtime manifest unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/nonexecutable-runtime"
runner="$TEMP/nonexecutable-runtime/provenance/runtime-provenance/"\
"endurance-runner-reference.sh"
chmod a-x "$runner"
if "$TEMP/nonexecutable-runtime/verifier/verify-result.sh" \
    "$TEMP/nonexecutable-runtime" >/dev/null 2>&1; then
  echo "non-executable runtime controller unexpectedly verified" >&2
  exit 1
fi

cp -a "$FINAL" "$TEMP/tampered-cache-snapshot"
cache_manifest="$TEMP/tampered-cache-snapshot/k/cache-after.tsv"
chmod u+w "$(dirname "$cache_manifest")" "$cache_manifest"
sed '1s/^[0-9a-f]/0/' "$cache_manifest" >"$TEMP/cache-manifest"
mv "$TEMP/cache-manifest" "$cache_manifest"
if "$TEMP/tampered-cache-snapshot/verifier/verify-result.sh" \
    "$TEMP/tampered-cache-snapshot" >/dev/null 2>&1; then
  echo "altered real-cache snapshot unexpectedly verified" >&2
  exit 1
fi

[[ -z "$(find "$FINAL" -name '*.partial' -o -name '*.partial.*')" ]]
jq -s -e 'all(.[].durable_copyback;. == "atomic")' \
  "$FINAL/sample/endurance/atom-certificates"/*.json >/dev/null
state=$(jq -r '.state_root' "$FINAL/k/certificate.json")
[[ ! -e "$state" ]]
endurance_state=$(jq -r '.state_root' \
  "$FINAL/sample/endurance/terminal-certificate.json")
[[ ! -e "$endurance_state" ]]

safe="$FINAL/verifier/safe-remove-state.sh"
for unsafe in "" / "$HOME" "$FINAL" \
    "/run/user/$(id -u)/holyhammer-phase3-task12" \
    "/run/user/$(id -u)/holyhammer-phase3-task10/not-ours"; do
  if "$safe" "$unsafe" >/dev/null 2>&1; then
    echo "unsafe cleanup target unexpectedly accepted: $unsafe" >&2
    exit 1
  fi
done
state_base="/run/user/$(id -u)/holyhammer-phase3-task12"
escape="$state_base/phase3-task12-selftest-escape"
if ! mkdir -p "$state_base"; then
  echo "TASK12 selftest requires writable state namespace: $state_base" >&2
  exit 1
fi
positive="$state_base/phase3-task12-selftest-positive"
if ! mkdir "$positive"; then
  echo "TASK12 selftest requires writable state namespace: $state_base" >&2
  exit 1
fi
  : >"$positive/sentinel"
  "$safe" "$positive"
  [[ ! -e "$positive" ]]
  ln -s "$TEMP" "$escape"
  if "$safe" "$escape" >/dev/null 2>&1; then
    echo "symlink cleanup escape unexpectedly accepted" >&2
    exit 1
  fi
  rm -- "$escape"
  fixture="$TEMP/reference-input"
  fixture_output="$TEMP/reference-output"
  fixture_state="$state_base/phase3-task12-reference-selftest"
  mkdir "$fixture"
  printf '%s\n' \
    $'fixture\tfixture.one' $'fixture\tfixture.two' \
    $'fixture\tfixture.three' $'fixture\tfixture.four' \
    >"$fixture/canonical-goals.tsv"
  printf '%s\n' \
    $'fixture-0-of-2\tfixture\t0\t2\t/fixture' \
    $'fixture-1-of-2\tfixture\t1\t2\t/fixture' >"$fixture/atoms.tsv"
  {
    printf 'file\t%s\tcanonical-goals.tsv\n' \
      "$(sha256sum "$fixture/canonical-goals.tsv" | cut -d' ' -f1)"
    printf 'file\t%s\tatoms.tsv\n' \
      "$(sha256sum "$fixture/atoms.tsv" | cut -d' ' -f1)"
  } >"$fixture/runtime-dependencies.tsv"
  "$FINAL/provenance/runtime-provenance/endurance-runner-reference.sh" \
    "$fixture" "$fixture_state" "$fixture_output" \
    "$FINAL/provenance/runtime-provenance/reference-fixture-worker.sh" 2
  [[ ! -e "$fixture_state" &&
    "$(find "$fixture_output/atom-certificates" -type f | wc -l)" == 2 &&
    "$(wc -l <"$fixture_output/resume-events.tsv")" == 1 &&
    -z "$(find "$fixture_output" -name '*.partial*' -print)" ]]
  awk -F '\t' 'NF != 3 || $3 != "cause-and-status-unretained" {
    exit 1}' "$fixture_output/resume-events.tsv"
  jq -s -e 'all(.[];
    .schema == "hh-task12-reference-atom-v2" and
    .durable_copyback == "atomic" and
    .certificate_publish == "output-local-partial-then-rename" and
    .actual_worker_row_order_sha256 == .journal_sha256)' \
    "$fixture_output/atom-certificates"/*.json >/dev/null
  jq -r '.goal_id' \
    "$fixture_output/journal/fixture-0-of-2.jsonl" \
    >"$TEMP/fixture-actual-order"
  cut -f2 "$fixture/canonical-goals.tsv" >"$TEMP/fixture-canonical-order"
  if cmp "$TEMP/fixture-actual-order" \
      "$TEMP/fixture-canonical-order" >/dev/null; then
    echo "shuffled worker order was not exercised" >&2
    exit 1
  fi
  LC_ALL=C sort "$TEMP/fixture-actual-order" >"$TEMP/fixture-actual-set"
  LC_ALL=C sort "$TEMP/fixture-canonical-order" \
    >"$TEMP/fixture-canonical-set"
  cmp "$TEMP/fixture-actual-set" "$TEMP/fixture-canonical-set"
  jq -e '
    .schema == "hh-task12-reference-terminal-v1" and
    .status == "complete" and .completed_atoms == 2 and
    .restart_resume_events == 1 and .fixed_atom_order == true and
    .atomic_copyback == true and .state_root_removed == true
  ' "$fixture_output/terminal-certificate.json" >/dev/null
rmdir "$state_base" 2>/dev/null || true

reproduced_sample="$TEMP/reproduced-sample"
"$FINAL/provenance/runtime-provenance/sample-and-fold.sh" \
  "$FINAL/sample" "$FINAL/sample/s30v3-sample.jsonl" \
  "$reproduced_sample"
[[ "$(tree_digest "$FINAL/sample")" == \
  "$(tree_digest "$reproduced_sample")" ]]
reproduced_final="$TEMP/reproduced-final"
"$FINAL/provenance/runtime-provenance/certify-final.sh" \
  "$reproduced_sample" "$FINAL/k" "$FINAL/provenance" \
  "$FINAL/verifier" "$FINAL/report.md" "$FINAL/final-certificate.json" \
  "$reproduced_final"
[[ "$(tree_digest "$FINAL")" == "$(tree_digest "$reproduced_final")" ]]
printf 'TASK12 revised evidence selftest passed\n'
