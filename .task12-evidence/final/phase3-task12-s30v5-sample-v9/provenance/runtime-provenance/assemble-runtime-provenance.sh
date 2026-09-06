#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 4)); then
  echo "usage: $0 BASE_RUNTIME HARNESS CLOSURE OUTPUT" >&2
  exit 2
fi

base=$(realpath "$1")
harness=$(realpath "$2")
closure=$(realpath "$3")
output=$4
[[ ! -e "$output" ]]
mkdir "$output"
cp -a "$base/." "$output/"
chmod -R u+w "$output"
cp "$closure"/* "$output/"

while IFS=$'\t' read -r source destination extra; do
  [[ -z "${extra-}" && "$source" == phase3-s30v5/* ]]
  cp "$harness/${source#phase3-s30v5/}" "$output/$destination"
done <"$harness/runtime-files.tsv"
rm -f "$output/run-k-seed-v8.sh" "$output/finish-k-v9.sh"

: >"$output/runtime-dependencies.tsv"
for path in accepted-loaded-objects.tsv allowed-source-diff.tsv atoms.tsv \
  canonical-goals.tsv endurance-hol-worker-reference.sh \
  endurance-runner-reference.sh hol-runtime-objects.tsv host-runtime.tsv \
  provers-task12.tsv runtime-root-certificate.json schedule.tsv \
  source-envelope.json source-input-SHA256SUMS source-provenance.json \
  source-run.json target-theory-objects.tsv task12-driver.sml \
  verify-runtime-root.sh; do
  printf 'file\t%s\t%s\n' \
    "$(sha256sum "$output/$path" | cut -d' ' -f1)" "$path" \
    >>"$output/runtime-dependencies.tsv"
done

jq -n \
  --arg dependencies "$(sha256sum "$output/runtime-dependencies.tsv" |
    cut -d' ' -f1)" \
  --arg runner "$(sha256sum "$output/endurance-runner-reference.sh" |
    cut -d' ' -f1)" \
  --arg worker "$(sha256sum "$output/endurance-hol-worker-reference.sh" |
    cut -d' ' -f1)" \
  --arg root "$(sha256sum "$output/runtime-root-certificate.json" |
    cut -d' ' -f1)" \
  --arg objects "$(sha256sum "$output/hol-runtime-objects.tsv" |
    cut -d' ' -f1)" \
  --arg targets "$(sha256sum "$output/target-theory-objects.tsv" |
    cut -d' ' -f1)" \
  --arg allowed "$(sha256sum "$output/allowed-source-diff.tsv" |
    cut -d' ' -f1)" \
  --arg host "$(sha256sum "$output/host-runtime.tsv" | cut -d' ' -f1)" '
  {schema:"hh-task12-equivalent-runtime-dependencies-v3",
   status:"complete",runtime_dependency_manifest_sha256:$dependencies,
   accepted_source:{
     hol_commit:"c5db8bb9cb4399c871fb011cf4b1c523cbec8d27",
     allowed_tracked_diff_count:0,allowed_source_diff_sha256:$allowed,
     original_driver_sha256:
       "361a0296784e473354e5493c74d9284a82e96ba040865f47416465a87530affa",
     original_wrapper_sha256:
       "9c78ce8a92d34f977fc4b3db2df895acaef0c0710f3f0e0279322a63f2c00d67",
     original_wrapper_bytes_retained:false},
   equivalent_environment:{
     bin_hol_sha256:
       "a5aede5eddd31e525a9efc89b7e5682226222a57481c084a8b7cfc8a38489db6",
     hol_state_sha256:
       "289fe0a08b348ae0d9c205fa36ca114f7f710932cb6cd7c7e97a7d6df69535b5",
     reference_runner_sha256:$runner,hol_worker_sha256:$worker,
     runtime_root_certificate_sha256:$root,
     hol_runtime_objects_sha256:$objects,
     target_theory_objects_sha256:$targets,host_runtime_sha256:$host,
     hol_runtime_object_count:3023,target_theories:229,
     target_theory_object_count:1374},
   prover_binaries:{
     e:"3a471eff44535f9ac18f3f80e48fbce7589922d79e493c1baa8545ae449b3ebc",
     vampire:
       "765c5aa84bf7333e3ed6e7936a5f44eec832777c00ac0ab5ee3b0aadf65c44de",
     zipperposition:
       "a5962fd8f986ec73cdf2ff80ab5aab7758dd4059464a0d55d57fa2200bd7d7f8"},
   original_byte_identity_claim:false,equivalent_reference_executable:true,
   exhaustive_theory_dependency_closure:true,bounded_fixture_required:true}
' >"$output/runtime-dependency-certificate.json"

(cd "$output" && find . -type f ! -name SHA256SUMS \
  ! -name certificate.json -print0 | LC_ALL=C sort -z |
  xargs -0 sha256sum) >"$output/SHA256SUMS"
jq -n \
  --arg driver "$(sha256sum "$output/task12-driver.sml" | cut -d' ' -f1)" \
  --arg schedule "$(sha256sum "$output/schedule.tsv" | cut -d' ' -f1)" \
  --arg runner "$(sha256sum "$output/endurance-runner-reference.sh" |
    cut -d' ' -f1)" \
  --arg worker "$(sha256sum "$output/endurance-hol-worker-reference.sh" |
    cut -d' ' -f1)" \
  --arg root "$(sha256sum "$output/runtime-root-certificate.json" |
    cut -d' ' -f1)" \
  --arg dependencies "$(sha256sum \
    "$output/runtime-dependency-certificate.json" | cut -d' ' -f1)" \
  --arg manifest "$(sha256sum "$output/SHA256SUMS" | cut -d' ' -f1)" '
  {schema:"hh-task12-runtime-provenance-v3",
   status:"equivalent-replayable-bundle",
   exact_original_runner_bytes_recoverable:false,
   exact_bit_identity_claim:false,
   derivation:{ancestor:"TASK10 preflight runner",
     measurement_semantics:"retained TASK12 driver measure path",
     post_run_change_scope:
       "evidence hardening and cache-witness plumbing; schedule unchanged",
     original_wrapper_bytes:"lost during post-certification compaction"},
   files:{driver_sha256:$driver,schedule_sha256:$schedule,
     reference_runner_sha256:$runner,hol_worker_sha256:$worker,
     runtime_root_certificate_sha256:$root,
     runtime_dependency_certificate_sha256:$dependencies,
     bundle_manifest_sha256:$manifest}}
' >"$output/certificate.json"
chmod -R a-w "$output"
