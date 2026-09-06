#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 1)); then
  echo "usage: $0 FINAL_EVIDENCE" >&2
  exit 2
fi

FINAL=$(realpath "$1")
if [[ -x "$FINAL/verifier/verify-result.sh" &&
      "$(realpath "$0")" != \
      "$(realpath "$FINAL/verifier/verify-result.sh")" ]]; then
  exec "$FINAL/verifier/verify-result.sh" "$FINAL"
fi
if [[ -d "$FINAL/verifier/verify-bin" ]]; then
  PATH="$FINAL/verifier/verify-bin"
  export PATH
fi

SAMPLE="$FINAL/sample"
K="$FINAL/k"
TEMP=$(mktemp -d)
trap 'rm -rf "$TEMP"' EXIT HUP INT TERM

for directory in "$SAMPLE" "$K" "$FINAL/provenance" \
    "$FINAL/verifier"; do
  [[ -d "$directory" && ! -L "$directory" ]]
  (cd "$directory" && sha256sum -c SHA256SUMS >/dev/null)
done
[[ "$(sha256sum "$SAMPLE/schedule.tsv" | cut -d' ' -f1)" == \
  c6a797f0a951f09050f11bbef18f5a74e8b787c41fe0b5a238fd2eb66a20e299 ]]

[[ "$(sha256sum "$FINAL/provenance/phase2-s30-v3-journal.sha256" |
  cut -d' ' -f1)" == \
  d2b145c9a16710611dcb61acdfc8e0635fd8acc46259e9ac2bddda7ca50c3318 ]]
[[ "$(sha256sum "$SAMPLE/s30v3-sample.jsonl" | cut -d' ' -f1)" == \
  4c0da14d6a7e5054fe6976ba26cdce76244b0e4b28ff990768f55344a3b322a2 ]]
[[ "$(sha256sum "$FINAL/provenance/task10-a-final.json" |
  cut -d' ' -f1)" == \
  4a9f965a6571843a1b36abda51aa973e531ae20ecc42e68eaa9b0e10cf653660 ]]
jq -e '
  .schema == "hh-task10-a-final-certificate-v3" and .status == "complete" and
  .baseline_validation_sha256 ==
    "249d94daedbb1148c2a5fae793ea9645bf28a426b298c6aefebbafd307d25ba1" and
  .canonical_inventory.goals == 24721 and
  .historical_first8.premise_mismatches == 0 and
  .historical_first8.request_key_mismatches == 0 and
  .historical_first8.prover_spawns == 0
' "$FINAL/provenance/task10-a-final.json" >/dev/null
[[ "$(sha256sum "$FINAL/provenance/task12-input-SHA256SUMS" |
  cut -d' ' -f1)" == \
  cc793e532c19105a722979a77c328e6391db27645df731b105586edf2cd530d2 ]]
[[ "$(sha256sum "$FINAL/provenance/task11-final.json" |
  cut -d' ' -f1)" == \
  e8bc88e1a2dd6697d33807b34ccf00ead8d747083776c11aa240822051c6f531 ]]
RUNTIME="$FINAL/provenance/runtime-provenance"
jq -e --arg driver "$(sha256sum \
    "$RUNTIME/task12-driver.sml" | cut -d' ' -f1)" \
  --arg schedule "$(sha256sum \
    "$RUNTIME/schedule.tsv" | cut -d' ' -f1)" \
  --arg runner "$(sha256sum \
    "$RUNTIME/endurance-runner-reference.sh" | cut -d' ' -f1)" \
  --arg worker "$(sha256sum \
    "$RUNTIME/endurance-hol-worker-reference.sh" | cut -d' ' -f1)" \
  --arg root "$(sha256sum \
    "$RUNTIME/runtime-root-certificate.json" | cut -d' ' -f1)" \
  --arg dependencies "$(sha256sum \
    "$RUNTIME/runtime-dependency-certificate.json" | cut -d' ' -f1)" \
  --arg manifest "$(sha256sum \
    "$RUNTIME/SHA256SUMS" | cut -d' ' -f1)" '
  .schema == "hh-task12-runtime-provenance-v3" and
  .status == "equivalent-replayable-bundle" and
  .exact_original_runner_bytes_recoverable == false and
  .exact_bit_identity_claim == false and
  .files.driver_sha256 == $driver and .files.schedule_sha256 == $schedule and
  .files.reference_runner_sha256 == $runner and
  .files.hol_worker_sha256 == $worker and
  .files.runtime_root_certificate_sha256 == $root and
  .files.runtime_dependency_certificate_sha256 == $dependencies and
  .files.bundle_manifest_sha256 == $manifest
' "$RUNTIME/certificate.json" >/dev/null
(cd "$RUNTIME" &&
  sha256sum -c SHA256SUMS >/dev/null)
[[ "$(sha256sum "$RUNTIME/runtime-dependencies.tsv" | cut -d' ' -f1)" == \
  685bca03c4bb6f56a7400591b73aab814f2896b2fde47642b8c42e4236e1f34e ]]
jq -e --arg manifest "$(sha256sum "$RUNTIME/runtime-dependencies.tsv" |
    cut -d' ' -f1)" \
  --arg runner "$(sha256sum "$RUNTIME/endurance-runner-reference.sh" |
    cut -d' ' -f1)" \
  --arg worker "$(sha256sum "$RUNTIME/endurance-hol-worker-reference.sh" |
    cut -d' ' -f1)" \
  --arg root "$(sha256sum "$RUNTIME/runtime-root-certificate.json" |
    cut -d' ' -f1)" \
  --arg objects "$(sha256sum "$RUNTIME/hol-runtime-objects.tsv" |
    cut -d' ' -f1)" \
  --arg targets "$(sha256sum "$RUNTIME/target-theory-objects.tsv" |
    cut -d' ' -f1)" \
  --arg host "$(sha256sum "$RUNTIME/host-runtime.tsv" | cut -d' ' -f1)" \
  --arg allowed "$(sha256sum "$RUNTIME/allowed-source-diff.tsv" |
    cut -d' ' -f1)" '
  .schema == "hh-task12-equivalent-runtime-dependencies-v3" and
  .status == "complete" and
  .runtime_dependency_manifest_sha256 == $manifest and
  .accepted_source == {
    hol_commit:"c5db8bb9cb4399c871fb011cf4b1c523cbec8d27",
    allowed_tracked_diff_count:0,allowed_source_diff_sha256:$allowed,
    original_driver_sha256:
      "361a0296784e473354e5493c74d9284a82e96ba040865f47416465a87530affa",
    original_wrapper_sha256:
      "9c78ce8a92d34f977fc4b3db2df895acaef0c0710f3f0e0279322a63f2c00d67",
    original_wrapper_bytes_retained:false} and
  .equivalent_environment.bin_hol_sha256 ==
    "a5aede5eddd31e525a9efc89b7e5682226222a57481c084a8b7cfc8a38489db6" and
  .equivalent_environment.hol_state_sha256 ==
    "289fe0a08b348ae0d9c205fa36ca114f7f710932cb6cd7c7e97a7d6df69535b5" and
  .equivalent_environment.reference_runner_sha256 == $runner and
  .equivalent_environment.hol_worker_sha256 == $worker and
  .equivalent_environment.runtime_root_certificate_sha256 == $root and
  .equivalent_environment.hol_runtime_objects_sha256 == $objects and
  .equivalent_environment.target_theory_objects_sha256 == $targets and
  .equivalent_environment.host_runtime_sha256 == $host and
  .equivalent_environment.hol_runtime_object_count == 3023 and
  .equivalent_environment.target_theories == 229 and
  .equivalent_environment.target_theory_object_count == 1374 and
  .prover_binaries == {
    e:"3a471eff44535f9ac18f3f80e48fbce7589922d79e493c1baa8545ae449b3ebc",
    vampire:
      "765c5aa84bf7333e3ed6e7936a5f44eec832777c00ac0ab5ee3b0aadf65c44de",
    zipperposition:
      "a5962fd8f986ec73cdf2ff80ab5aab7758dd4059464a0d55d57fa2200bd7d7f8"} and
  .original_byte_identity_claim == false and
  .equivalent_reference_executable == true and
  .exhaustive_theory_dependency_closure == true and
  .bounded_fixture_required == true
' "$RUNTIME/runtime-dependency-certificate.json" >/dev/null
[[ "$(wc -l <"$RUNTIME/runtime-dependencies.tsv")" == 18 ]]
while IFS=$'\t' read -r mode expected path extra; do
  [[ -z "${extra-}" && "$mode" == file && "$path" != /* &&
    "$path" != *../* && -f "$RUNTIME/$path" && ! -L "$RUNTIME/$path" ]]
  [[ "$(sha256sum "$RUNTIME/$path" | cut -d' ' -f1)" == "$expected" ]]
done <"$RUNTIME/runtime-dependencies.tsv"
for path in endurance-runner-reference.sh endurance-hol-worker-reference.sh \
    verify-runtime-root.sh safe-remove-state.sh sample-and-fold.sh \
    certify-final.sh run-k.sh finish-k.sh run-k-current.sh; do
  [[ -x "$RUNTIME/$path" ]]
done
[[ "$(sha256sum "$RUNTIME/hol-runtime-objects.tsv" | cut -d' ' -f1)" == \
  533bd035103ef41d480f0b7ad42ad248d1a2ff2a6503af98659c1c8e5da0008b ]]
[[ "$(sha256sum "$RUNTIME/target-theory-objects.tsv" | cut -d' ' -f1)" == \
  4aac9c7355b9ecce6bdae058eaa9d4e57b1b346d93b69ca14006542f466ea493 ]]
[[ "$(sha256sum "$RUNTIME/host-runtime.tsv" | cut -d' ' -f1)" == \
  552b578a47d72e8d948d75b47b5d12e3787b78fd697d57597a9e50026eed3464 ]]
jq -e '
  .schema == "hh-task12-runtime-root-v1" and .status == "complete" and
  .accepted_commit == "c5db8bb9cb4399c871fb011cf4b1c523cbec8d27" and
  .allowed_tracked_diff_count == 0 and
  .allowed_source_diff_sha256 ==
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" and
  .hol_runtime_objects == {count:3023,
    sha256:"533bd035103ef41d480f0b7ad42ad248d1a2ff2a6503af98659c1c8e5da0008b"} and
  .target_theory_objects == {theories:229,count:1374,
    sha256:"4aac9c7355b9ecce6bdae058eaa9d4e57b1b346d93b69ca14006542f466ea493"} and
  .host_runtime == {count:42,
    sha256:"552b578a47d72e8d948d75b47b5d12e3787b78fd697d57597a9e50026eed3464"}
' "$RUNTIME/runtime-root-certificate.json" >/dev/null
jq -e '
  .schema == "hh-task12-cleanup-v4" and .status == "complete" and
  .removed_roots == [
    "/run/user/1003/holyhammer-phase3-task10",
    "/run/user/1003/holyhammer-phase3-task10-write-test",
    "/run/user/1003/holyhammer-phase3-task11-smoke",
    "/run/user/1003/phase3-task10-anchorcheck",
    "/run/user/1003/phase3-task10-anchorcheck2",
    "/run/user/1003/phase3-task10-anchorcheck3",
    "/run/user/1003/phase3-task10-currentcheck",
    "/run/user/1003/holyhammer-phase3-task12/phase3-task12-s30v5-v5",
    "/run/user/1003/holyhammer-phase3-task12/k-revised-v1",
    "/run/user/1003/holyhammer-phase3-task12/k-revised-v2",
    "/run/user/1003/holyhammer-phase3-task12/k-revised-v3"] and
  .task12_namespace_children == 0 and
  .task12_transient_units_remaining == 0 and
  .runtime_root_certificate_sha256 ==
    "87a5d9c638c154a6ffcf21ed824d4e8dbb355c2ced97c26c820fc50883762abf" and
  .runtime_dependency_certificate_sha256 ==
    "b57f8e0bfb1c1f95d976a95aebd072af3e4388493f7c8ea6aff56d6e60a3a200" and
  .removed_workspace_bulk == [
    ".task10-evidence/staging/a-final-source-v12",
    ".task10-evidence/staging/p-final-source-v12",
    ".task10-evidence/runs/phase3-task10-a-final-source-v12"] and
  .preserved_compact_dependencies == {
    task10_a_final_sha256:
      "4a9f965a6571843a1b36abda51aa973e531ae20ecc42e68eaa9b0e10cf653660",
    phase2_full_manifest_sha256:
      "d2b145c9a16710611dcb61acdfc8e0635fd8acc46259e9ac2bddda7ca50c3318",
    task11_sealed_task10_result_sha256:
      "934b69a7004d91ea639e4ccd25ca5ea7e3b52fb397a963c31676f032cf9086eb",
    task11_sealed_task10_run_sha256:
      "c51fae74ad1ad831b1c6012c6135cba0044307d6f123174518119a77a485f016"}
' "$FINAL/provenance/cleanup-certificate.json" >/dev/null

jq -e '.schema == "hh-task12-revised-input-v4" and
  .status == "sample-sealed" and
  .input_inventory_sha256 ==
    "cc793e532c19105a722979a77c328e6391db27645df731b105586edf2cd530d2" and
  .completed_atomic_frame.atoms == 408 and
  .completed_atomic_frame.goals == 3119 and
  .completed_atomic_frame.selection_independent_of_cell_outcome == true and
  .completed_atomic_frame.no_within_atom_partial_completion == true and
  .completed_atomic_frame.membership_recomputed_with_hheval_partition == true and
  .sample.goals == 3000 and
  .sample.algorithm == "lowest SHA-256(goal_id), bytewise" and
  .k_subset.goals == 128 and .tuning_performed == false and
  .full_corpus_s30v5_measured == false and .no_full_corpus_claim == true' \
  "$SAMPLE/sample-certificate.json" >/dev/null
cmp "$RUNTIME/canonical-goals.tsv" "$SAMPLE/canonical-goals.tsv"
cmp "$RUNTIME/atoms.tsv" "$SAMPLE/endurance/atoms.tsv"
cmp "$RUNTIME/source-run.json" "$SAMPLE/endurance/run.json"
cmp "$RUNTIME/source-envelope.json" "$SAMPLE/endurance/envelope.json"
cmp "$RUNTIME/schedule.tsv" "$SAMPLE/schedule.tsv"
jq -e '
  .phase2_anchor.sample_sha256 ==
    "4c0da14d6a7e5054fe6976ba26cdce76244b0e4b28ff990768f55344a3b322a2" and
  .phase2_anchor.full_journal_manifest_sha256 ==
    "d2b145c9a16710611dcb61acdfc8e0635fd8acc46259e9ac2bddda7ca50c3318" and
  .phase2_anchor.task10_final_sha256 ==
    "4a9f965a6571843a1b36abda51aa973e531ae20ecc42e68eaa9b0e10cf653660"
' "$SAMPLE/sample-certificate.json" >/dev/null
jq -e \
  --arg frame "$(sha256sum "$SAMPLE/endurance/journal.jsonl" | cut -d' ' -f1)" \
  --arg inventory "$(sha256sum \
    "$SAMPLE/endurance/atom-inventory.tsv" | cut -d' ' -f1)" \
  --arg terminal "$(sha256sum \
    "$SAMPLE/endurance/terminal-certificate.json" | cut -d' ' -f1)" \
  --arg selection "$(sha256sum "$SAMPLE/sample-selection.tsv" | \
    cut -d' ' -f1)" \
  --arg old "$(sha256sum "$SAMPLE/s30v3-sample.jsonl" | cut -d' ' -f1)" \
  --arg new "$(sha256sum "$SAMPLE/s30v5-sample.jsonl" | cut -d' ' -f1)" \
  --arg result "$(sha256sum "$SAMPLE/result.json" | cut -d' ' -f1)" \
  --arg losses "$(sha256sum \
    "$SAMPLE/loss-investigations.jsonl" | cut -d' ' -f1)" \
  --arg k "$(sha256sum "$SAMPLE/k-subset.tsv" | cut -d' ' -f1)" '
  .completed_atomic_frame.journal_sha256 == $frame and
  .completed_atomic_frame.atom_inventory_sha256 == $inventory and
  .completed_atomic_frame.terminal_certificate_sha256 == $terminal and
  .sample.selection_sha256 == $selection and .sample.s30v3_sha256 == $old and
  .sample.s30v5_sha256 == $new and .sample.result_sha256 == $result and
  .sample.loss_investigations_sha256 == $losses and
  .k_subset.sha256 == $k
' "$SAMPLE/sample-certificate.json" >/dev/null
jq -e '
  .schema == "hh-task12-s30v5-envelope-v1" and .status == "running" and
  .input_inventory_sha256 ==
    "cc793e532c19105a722979a77c328e6391db27645df731b105586edf2cd530d2" and
  .state_root ==
    "/run/user/1003/holyhammer-phase3-task12/phase3-task12-s30v5-v5" and
  .initial_cache_files == 0 and .isolated_caches == true and
  .resumable_journals == true and .canonical_goal_allowlist == true and
  .envelope == {cpu_quota_cores:32,memory_high_bytes:133143986176,
    memory_max_bytes:137438953472,memory_swap_max_bytes:0,
    worker_recycle_seconds:600,worker_slots:1,schedule_cores:24,
    chunk_target_goals:8,tmpfs_scratch:true,durable_copyback:true}
' "$SAMPLE/endurance/envelope.json" >/dev/null
jq -e '
  .schema == 4 and .expname == "phase3-task12-s30v5-v5" and
  .hol_commit == "c5db8bb9cb4399c871fb011cf4b1c523cbec8d27" and
  .conditions == [{cond_id:"s30-v5",regime:"chainy",selector:"perslice",
    engine:"sched",provers:["e","vampire","zipperposition"],slices:24,
    cores:24,max_proofs:4,timeout:30,reconstruct:true}] and .sample == 1
' "$SAMPLE/endurance/run.json" >/dev/null

[[ "$(wc -l <"$SAMPLE/endurance/atom-inventory.tsv")" == 408 ]]
[[ "$(wc -l <"$SAMPLE/endurance/journal.jsonl")" == 3119 ]]
[[ "$(wc -l <"$SAMPLE/endurance/resume-events.tsv")" == 2 ]]
[[ "$(sha256sum "$SAMPLE/endurance/journal.jsonl" | cut -d' ' -f1)" == \
  d7715a892b0ccb06e2123855ad57371e3432b0b9d7d13dee05388e66e54ef921 ]]
[[ "$(sha256sum "$SAMPLE/endurance/terminal-systemd.jsonl" |
  cut -d' ' -f1)" == \
  5e35c5ebd09c7bd9f484822ba0d172d8dac0434c173933deb987dbf2a4b5d7d5 ]]
[[ "$(find "$SAMPLE/endurance/atom-certificates" -type f | wc -l)" == \
  408 ]]
cut -f1 "$SAMPLE/endurance/atom-inventory.tsv" >"$TEMP/inventory-atoms"
head -n 408 "$SAMPLE/endurance/atoms.tsv" | cut -f1 >"$TEMP/plan-atoms"
cmp "$TEMP/plan-atoms" "$TEMP/inventory-atoms"
if LC_ALL=C grep -q $'[^\t -~]' "$SAMPLE/canonical-goals.tsv"; then
  echo "canonical goal inventory is not bytewise ASCII" >&2
  exit 1
fi
jq -Rr '
  def sample_hash:
    reduce (explode[]) as $byte
      (0; ((. * 65599 + $byte) % 2147483647));
  split("\t") as $row |
  if ($row|length) != 2 or $row[1] == "" then error("bad goal row")
  else [$row[0],$row[1],($row[1]|sample_hash)]|@tsv end
' "$SAMPLE/canonical-goals.tsv" >"$TEMP/canonical-hashes.tsv"
[[ "$(wc -l <"$TEMP/canonical-hashes.tsv")" == 24721 ]]
offset=1
: >"$TEMP/expected-resume.tsv"
total_attempts=0
empty_atoms=0
restart_events=0
while IFS=$'\t' read -r atom cells attempts journal certificate extra; do
  [[ -z "${extra-}" ]]
  path="$SAMPLE/endurance/atom-certificates/$atom.json"
  [[ "$(sha256sum "$path" | cut -d' ' -f1)" == "$certificate" ]]
  IFS=$'\t' read -r plan_atom plan_theory plan_part plan_parts \
    plan_directory plan_extra < <(awk -F '\t' -v atom="$atom" \
      '$1 == atom {print; found++} END {if (found != 1) exit 1}' \
      "$SAMPLE/endurance/atoms.tsv")
  [[ -z "${plan_extra-}" && "$plan_atom" == "$atom" ]]
  jq -e --arg atom "$atom" --arg journal "$journal" \
    --arg theory "$plan_theory" --arg directory "$plan_directory" \
    --argjson part "$plan_part" --argjson parts "$plan_parts" \
    --argjson cells "$cells" --argjson attempts "$attempts" '
    .schema == "hh-task12-s30v5-atom-v1" and .status == "complete" and
    .input_inventory_sha256 ==
      "cc793e532c19105a722979a77c328e6391db27645df731b105586edf2cd530d2" and
    (.witness_cache_retained|type) == "boolean" and .atom == $atom and
    .journal_sha256 == $journal and .cells == $cells and
    .attempts == $attempts and .theory == $theory and
    .part == $part and .parts == $parts and
    .theory_directory == $directory and .durable_copyback == "atomic"
  ' "$path" >/dev/null
  awk -v first="$offset" -v cells="$cells" \
    'NR >= first && NR < first + cells' \
    "$SAMPLE/endurance/journal.jsonl" >"$TEMP/atom-segment"
  [[ "$(wc -l <"$TEMP/atom-segment")" == "$cells" ]]
  [[ "$(sha256sum "$TEMP/atom-segment" | cut -d' ' -f1)" == "$journal" ]]
  theory=$(jq -r '.theory' "$path")
  jq -s -e --arg theory "$theory" --argjson cells "$cells" '
    length == $cells and all(.[];
      type == "object" and .thy == $theory and
      .goal_id == (.thy + "." + .thm))
  ' "$TEMP/atom-segment" >/dev/null
  awk -F '\t' -v theory="$plan_theory" -v part="$plan_part" \
    -v parts="$plan_parts" '
    $1 == theory && $3 % parts == part {print $2}
  ' "$TEMP/canonical-hashes.tsv" | LC_ALL=C sort \
    >"$TEMP/expected-atom-goals"
  jq -r '.goal_id' "$TEMP/atom-segment" | LC_ALL=C sort \
    >"$TEMP/actual-atom-goals"
  [[ "$(wc -l <"$TEMP/expected-atom-goals")" == "$cells" ]]
  cmp "$TEMP/expected-atom-goals" "$TEMP/actual-atom-goals"
  offset=$((offset + cells))
  total_attempts=$((total_attempts + attempts))
  if ((cells == 0)); then
    empty_atoms=$((empty_atoms + 1))
  fi
  if ((attempts > 1)); then
    restart_events=$((restart_events + attempts - 1))
    printf '%s\t%s\t%s\tcause-and-status-unknown\n' "$atom" "$attempts" \
      "$((attempts - 1))" >>"$TEMP/expected-resume.tsv"
  fi
done <"$SAMPLE/endurance/atom-inventory.tsv"
[[ "$offset" == 3120 ]]
[[ "$total_attempts" == 410 && "$empty_atoms" == 2 &&
  "$restart_events" == 2 ]]
cmp "$TEMP/expected-resume.tsv" "$SAMPLE/endurance/resume-events.tsv"

jq -s -e '
  length == 4 and (map(.invocation_id)|unique) ==
    ["492dbc2b61504a1398ce8b33cbced19d"] and
  all(.[];.unit == "phase3-task12-s30v5-v5-run.service") and
  .[0].job_type == "start" and .[0].job_result == "done" and
  .[1].job_type == "stop" and .[2].job_type == "stop" and
  .[2].job_result == "done" and
  .[0].realtime_usec == 1788539503796484 and
  .[2].realtime_usec == 1788636310148897 and
  .[3].cpu_usage_nsec == 1279298591726000 and
  .[3].memory_peak_bytes == 85072396288 and
  .[3].memory_swap_peak_bytes == 0 and
  ([.[]|select(.message|test("Failed|Main process exited"))]|length) == 0
' "$SAMPLE/endurance/terminal-systemd.jsonl" >/dev/null
jq -e --arg journal "$(sha256sum \
    "$SAMPLE/endurance/terminal-systemd.jsonl" | cut -d' ' -f1)" \
  --arg plan "$(sha256sum "$SAMPLE/endurance/atoms.tsv" | cut -d' ' -f1)" \
  --arg inventory "$(sha256sum \
    "$SAMPLE/endurance/atom-inventory.tsv" | cut -d' ' -f1)" '
  .schema == "hh-task12-endurance-terminal-v4" and
  .status == "stopped-at-atomic-checkpoint" and
  .unit == "phase3-task12-s30v5-v5-run.service" and
  .invocation_id == "492dbc2b61504a1398ce8b33cbced19d" and
  .structured_journal_sha256 == $journal and .atom_plan_sha256 == $plan and
  .atom_inventory_sha256 == $inventory and .completed_atoms == 408 and
  .completed_cells == 3119 and .empty_atoms == 2 and .attempts == 410 and
  .restart_resume_events == 2 and .atomic_continuity == true and
  .restart_causes_retained == false and
  .restart_statuses_retained == false and
  .restart_cause_and_status == "unknown" and
  .last_atom == "combin-5-of-7" and
  .duration_usec == (.stop_realtime_usec - .start_realtime_usec) and
  .stop_realtime_usec == 1788636310148897 and
  .state_root ==
    "/run/user/1003/holyhammer-phase3-task12/phase3-task12-s30v5-v5" and
  .state_root_removed == true and .fixed_atom_order == true and
  .atomic_copyback == true and .resume_events == 2
' "$SAMPLE/endurance/terminal-certificate.json" >/dev/null

jq -r '[.goal_id,.thy] | @tsv' "$SAMPLE/endurance/journal.jsonl" |
  while IFS=$'\t' read -r goal theory; do
    printf '%s\t%s\t%s\n' \
      "$(printf '%s' "$goal" | sha256sum | cut -d' ' -f1)" \
      "$theory" "$goal"
  done | LC_ALL=C sort -t $'\t' -k1,1 -k3,3 | head -n 3000 \
  >"$TEMP/selection.tsv"
cmp "$TEMP/selection.tsv" "$SAMPLE/sample-selection.tsv"
cut -f3 "$SAMPLE/sample-selection.tsv" >"$TEMP/sample-goal-ids"
jq -Rn --rawfile ids "$TEMP/sample-goal-ids" '
  $ids|split("\n")|map(select(length>0))|INDEX(.)
' >"$TEMP/sample-set.json"
jq -scS --slurpfile selected "$TEMP/sample-set.json" \
  '[.[]|select($selected[0][.goal_id] != null)]|sort_by(.goal_id)' \
  "$SAMPLE/endurance/journal.jsonl" >"$TEMP/source-v5.json"
jq -scS 'sort_by(.goal_id)' "$SAMPLE/s30v5-sample.jsonl" \
  >"$TEMP/sample-v5.json"
cmp "$TEMP/source-v5.json" "$TEMP/sample-v5.json"
head -n 128 "$SAMPLE/sample-selection.tsv" | cut -f2,3 \
  >"$TEMP/k-subset.tsv"
cmp "$TEMP/k-subset.tsv" "$K/subset.tsv"
[[ "$(sha256sum "$K/source-sample-certificate.json" | cut -d' ' -f1)" == \
  9a67b7ed60e84746c29af64909d39dd1a3027d8ecdbf51064105d707c94b88aa ]]
cmp "$K/run-k-seed.sh" "$RUNTIME/run-k.sh"
cmp "$K/finish-k.sh" "$RUNTIME/finish-k.sh"
cmp "$K/run-k-current.sh" "$RUNTIME/run-k-current.sh"

jq -s -e 'length == 3000 and (map(.goal_id)|unique|length) == 3000' \
  "$SAMPLE/s30v3-sample.jsonl" >/dev/null
jq -s -e --rawfile schedule "$SAMPLE/schedule.tsv" '
  def skey:
    [.prover,.filter,.format,.type_enc,.lam_trans,
     (.nfacts|tostring),(.slice_size|tostring),(.extra_opts|tojson)] |
    join("\t");
  ($schedule|split("\n")|map(select(length>0)|split("\t")|
    {prover:.[1],filter:.[2],format:.[3],type_enc:.[4],lam_trans:.[5],
     nfacts:(.[6]|tonumber),slice_size:(.[7]|tonumber),extra_opts:[]}|skey)|
    sort) as $expected |
  length == 3000 and (map(.goal_id)|unique|length) == 3000 and
  all(.[];.cond == "s30-v5" and .engine_params ==
    {provers:["e","vampire","zipperposition"],slices:24,cores:24,
     max_proofs:4} and .timeout == 30 and (.slices|length) == 24 and
     ((.slices|map(.slice|skey)|sort) == $expected))' \
  "$SAMPLE/s30v5-sample.jsonl" >/dev/null
jq -n --slurpfile old "$SAMPLE/s30v3-sample.jsonl" \
  --slurpfile new "$SAMPLE/s30v5-sample.jsonl" '
  def p: .szs == "Theorem";
  def r: p and .recon_ok == true;
  ($old|sort_by(.goal_id)) as $o | ($new|sort_by(.goal_id)) as $n |
  ($o|map(.goal_id)) == ($n|map(.goal_id)) and
  ([$o[]|select(p)]|length) == 1731 and
  ([$n[]|select(p)]|length) == 1856 and
  ([$o[]|select(r)]|length) == 1221 and
  ([$n[]|select(r)]|length) == 1714 and
  ([range(0;3000)|select(($n[.]|p) and (($o[.]|p)|not))]|length) == 129 and
  ([range(0;3000)|select(($o[.]|p) and (($n[.]|p)|not))]|length) == 4 and
  ([range(0;3000)|select(($n[.]|r) and (($o[.]|r)|not))]|length) == 497 and
  ([range(0;3000)|select(($o[.]|r) and (($n[.]|r)|not))]|length) == 4
' >/dev/null
jq -n --slurpfile old "$SAMPLE/s30v3-sample.jsonl" \
  --slurpfile new "$SAMPLE/s30v5-sample.jsonl" \
  --rawfile schedule "$SAMPLE/schedule.tsv" \
  -f "$FINAL/verifier/paired-result.jq" | jq -S . \
  >"$TEMP/recomputed-result.json"
cmp "$TEMP/recomputed-result.json" "$SAMPLE/result.json"
jq -n --slurpfile old "$SAMPLE/s30v3-sample.jsonl" \
  --slurpfile new "$SAMPLE/s30v5-sample.jsonl" \
  -f "$FINAL/verifier/loss-investigations.jq" \
  >"$TEMP/expected-loss-array.json"
jq -sS 'sort_by(.goal_id)' "$SAMPLE/loss-investigations.jsonl" \
  >"$TEMP/actual-loss-array.json"
jq -S 'sort_by(.goal_id)' "$TEMP/expected-loss-array.json" \
  >"$TEMP/sorted-expected-loss-array.json"
cmp "$TEMP/sorted-expected-loss-array.json" "$TEMP/actual-loss-array.json"

cache_files=$(wc -l <"$K/cache-before.tsv")
cache_bytes=$(awk -F '\t' '{n += $2} END {print n+0}' \
  "$K/cache-before.tsv")
seed_spawns=$(awk -F '\t' '{n += $2} END {print n+0}' \
  "$K/seed-spawns.tsv")
version_spawns=$(awk -F '\t' '{n += $2} END {print n+0}' \
  "$K/version-spawns.tsv")
prime_spawns=$(awk -F '\t' '{n += $2} END {print n+0}' \
  "$K/prime-spawns.tsv")
replay_spawns=$(awk -F '\t' '{n += $2} END {print n+0}' \
  "$K/replay-spawns.tsv")
jq -e --arg sample "$(sha256sum "$K/source-sample-certificate.json" |
  cut -d' ' -f1)" \
  --arg subset "$(sha256sum "$K/subset.tsv" | cut -d' ' -f1)" \
  --arg seed "$(sha256sum "$K/seed-journal.jsonl" | cut -d' ' -f1)" \
  --arg prime "$(sha256sum "$K/prime-journal.jsonl" | cut -d' ' -f1)" \
  --arg replay "$(sha256sum "$K/replay-journal.jsonl" | cut -d' ' -f1)" \
  --arg cache "$(sha256sum "$K/cache-before.tsv" | cut -d' ' -f1)" \
  --arg fresh "$(sha256sum "$K/fresh-root-proof.json" | cut -d' ' -f1)" \
  --arg seed_script "$(sha256sum "$K/run-k-seed.sh" |
    cut -d' ' -f1)" \
  --arg run_script "$(sha256sum "$K/run-k.sh" | cut -d' ' -f1)" \
  --arg finish_script "$(sha256sum "$K/finish-k.sh" | cut -d' ' -f1)" \
  --arg current_script "$(sha256sum "$K/run-k-current.sh" |
    cut -d' ' -f1)" \
  --arg input_manifest "$(sha256sum "$K/input-SHA256SUMS" |
    cut -d' ' -f1)" \
  --arg provers "$(sha256sum "$K/provers.tsv" | cut -d' ' -f1)" \
  --arg theories "$(sha256sum "$K/theory-directories.tsv" |
    cut -d' ' -f1)" --argjson seed_spawns "$seed_spawns" \
  --argjson version_spawns "$version_spawns" \
  --argjson prime_spawns "$prime_spawns" \
  --argjson replay_spawns "$replay_spawns" \
  --argjson files "$cache_files" --argjson bytes "$cache_bytes" '
  .schema == "hh-task12-k-cache-witness-v6" and
  .status == "complete" and .subset_goals == 128 and
  .sample_certificate_sha256 == $sample and .subset_sha256 == $subset and
  .seed_journal_sha256 == $seed and .prime_journal_sha256 == $prime and
  .replay_journal_sha256 == $replay and
  .seed_prover_spawns == $seed_spawns and
  .version_resolution_spawns == $version_spawns and
  .prime_cache_check_spawns == $prime_spawns and
  .replay_prover_spawns == $replay_spawns and
  $version_spawns == 81 and $prime_spawns == 0 and $replay_spawns == 0 and
  .slices_per_goal == 24 and
  .cached_slices_per_goal == 24 and
  .filter_keyed_problem_filters == ["knn","mash","mepo","mesh"] and
  .same_cache_for_seed_and_replay == true and
  .seeded_cache_manifest_sha256 == $cache and
  .cache_manifest_before_sha256 == $cache and
  .cache_manifest_after_sha256 == $cache and
  .producing_scripts == {seed_run_k_sha256:$seed_script,
    finish_k_sha256:$finish_script,run_k_current_sha256:$current_script} and
  .maintained_workflow == {run_k_sha256:$run_script} and
  .producing_inputs == {input_manifest_sha256:$input_manifest,
    provers_sha256:$provers,theory_directories_sha256:$theories} and
  .cache_unmodified_by_replay == true and
  .state_root == "/run/user/1003/holyhammer-phase3-task12/k-revised-v3" and
  .fresh_root_proof_sha256 == $fresh and
  .prime_root == (.state_root+"/prime-cache-check") and
  .replay_root == (.state_root+"/replay-witness") and
  .prime_and_replay_roots_absent_before_run == true and
  .prime_and_replay_non_resume == true and
  .state_removed_after_witness == true and .tuning_performed == false and
  .explicit_version_resolution == {
    provers:["e","vampire","zipperposition"],processes:27,
    expected_spawns:81,observed_spawns:$version_spawns,
    completed_before_prime_reset:true} and
  .cache_decomposition == {requested_cells:3072,cached_replay_cells:3072,
    physical_cache_files:$files,physical_cache_bytes:$bytes,
    filter_cells:{knn:2048,mash:256,mepo:256,mesh:512}}' \
  "$K/certificate.json" >/dev/null
jq -e --arg subset "$(sha256sum "$K/subset.tsv" | cut -d' ' -f1)" \
  --arg sample "$(sha256sum "$K/source-sample-certificate.json" |
    cut -d' ' -f1)" \
  --arg cache "$(sha256sum "$K/seed-cache-manifest.tsv" |
    cut -d' ' -f1)" \
  --arg script "$(sha256sum "$K/run-k-seed.sh" | cut -d' ' -f1)" '
  .schema == "hh-task12-k-seed-v2" and .status == "seeded" and
  .sample_certificate_sha256 == $sample and .subset_sha256 == $subset and
  .subset_goals == 128 and .initial_cache_files == 0 and
  .seeded_cache_manifest_sha256 == $cache and
  .producing_run_script_sha256 == $script and
  .state_root == "/run/user/1003/holyhammer-phase3-task12/k-revised-v3" and
  .state_retained_for_same_process_witness == true and
  .tuning_performed == false
' "$K/seed-certificate.json" >/dev/null
cmp "$K/seed-cache-manifest.tsv" "$K/cache-before.tsv"
[[ "$(sha256sum "$K/input-SHA256SUMS" | cut -d' ' -f1)" == \
  cc793e532c19105a722979a77c328e6391db27645df731b105586edf2cd530d2 ]]
[[ "$(sha256sum "$K/provers.tsv" | cut -d' ' -f1)" == \
  96b4668d24be83b3d2f112cb0593a34f0586d69c847c8b0b31dc5790907276ce ]]
[[ "$(sha256sum "$K/theory-directories.tsv" | cut -d' ' -f1)" == \
  f9309ef6db784e25b8717fc039fed4d3ef06c62b12ccfbb7ac8214740d8609f7 ]]
cmp "$K/cache-before.tsv" "$K/cache-after.tsv"
[[ "$(cut -f3 "$K/cache-before.tsv" | LC_ALL=C sort -u | wc -l)" == \
  "$cache_files" ]]
awk -F '\t' 'NF != 3 || length($1) != 64 || $1 !~ /^[0-9a-f]+$/ ||
  $2 !~ /^[0-9]+$/ || $3 == "" {exit 1}' "$K/cache-before.tsv"
jq -e --arg result "$(sha256sum "$K/certificate.json" | cut -d' ' -f1)" \
  --arg journal "$(sha256sum "$K/terminal-systemd.jsonl" | cut -d' ' -f1)" '
  .schema == "hh-task12-k-terminal-v5" and .status == "complete" and
  .start_job_result == "done" and .completion_artifact_observed == true and
  .observed_failure_records == 0 and .memory_swap_peak_bytes == 0 and
  .certificate_reconciled_from_sealed_journal == true and
  .k_certificate_sha256 == $result and
  .structured_journal_sha256 == $journal and
  .requested_envelope == {cpu_quota_percent:3200,
    memory_high_bytes:133143986176,memory_max_bytes:137438953472,
    memory_swap_max_bytes:0,oom_policy:"continue"}
' "$K/terminal-service.json" >/dev/null
jq -s -e --rawfile schedule "$SAMPLE/schedule.tsv" '
  def skey:
    [.prover,.filter,.format,.type_enc,.lam_trans,
     (.nfacts|tostring),(.slice_size|tostring),(.extra_opts|tojson)] |
    join("\t");
  ($schedule|split("\n")|map(select(length>0)|split("\t")|
    {prover:.[1],filter:.[2],format:.[3],type_enc:.[4],lam_trans:.[5],
     nfacts:(.[6]|tonumber),slice_size:(.[7]|tonumber),extra_opts:[]}|skey)|
    sort) as $expected |
  length == 128 and (map(.goal_id)|unique|length) == 128 and
  all(.[];.cond == "s30-v5" and .engine_params ==
    {provers:["e","vampire","zipperposition"],slices:24,cores:24,
     max_proofs:4} and .timeout == 30 and
    (.slices|length) == 24 and all(.slices[];.cached == true) and
    ((.slices|map(.slice|skey)|sort) == $expected))' \
  "$K/replay-journal.jsonl" >/dev/null
jq -s -e --rawfile schedule "$SAMPLE/schedule.tsv" '
  def skey:
    [.prover,.filter,.format,.type_enc,.lam_trans,
     (.nfacts|tostring),(.slice_size|tostring),(.extra_opts|tojson)] |
    join("\t");
  ($schedule|split("\n")|map(select(length>0)|split("\t")|
    {prover:.[1],filter:.[2],format:.[3],type_enc:.[4],lam_trans:.[5],
     nfacts:(.[6]|tonumber),slice_size:(.[7]|tonumber),extra_opts:[]}|skey)|
    sort) as $expected |
  length == 128 and (map(.goal_id)|unique|length) == 128 and
  all(.[];.cond == "s30-v5" and .engine_params ==
    {provers:["e","vampire","zipperposition"],slices:24,cores:24,
     max_proofs:4} and .timeout == 30 and
    (.slices|length) == 24 and all(.slices[];.cached == true) and
    ((.slices|map(.slice|skey)|sort) == $expected))' \
  "$K/prime-journal.jsonl" >/dev/null
jq -s -e --rawfile schedule "$SAMPLE/schedule.tsv" '
  def skey:
    [.prover,.filter,.format,.type_enc,.lam_trans,
     (.nfacts|tostring),(.slice_size|tostring),(.extra_opts|tojson)] |
    join("\t");
  ($schedule|split("\n")|map(select(length>0)|split("\t")|
    {prover:.[1],filter:.[2],format:.[3],type_enc:.[4],lam_trans:.[5],
     nfacts:(.[6]|tonumber),slice_size:(.[7]|tonumber),extra_opts:[]}|skey)|
    sort) as $expected |
  length == 128 and (map(.goal_id)|unique|length) == 128 and
  all(.[];.cond == "s30-v5" and .engine_params ==
    {provers:["e","vampire","zipperposition"],slices:24,cores:24,
     max_proofs:4} and .timeout == 30 and
    (.slices|length) == 24 and all(.slices[];.cached == false) and
    ((.slices|map(.slice|skey)|sort) == $expected))
' "$K/seed-journal.jsonl" >/dev/null
cut -f2 "$K/subset.tsv" | LC_ALL=C sort >"$TEMP/k-goals"
jq -r '.goal_id' "$K/seed-journal.jsonl" | LC_ALL=C sort \
  >"$TEMP/k-seed-goals"
jq -r '.goal_id' "$K/replay-journal.jsonl" | LC_ALL=C sort \
  >"$TEMP/k-replay-goals"
jq -r '.goal_id' "$K/prime-journal.jsonl" | LC_ALL=C sort \
  >"$TEMP/k-prime-goals"
cmp "$TEMP/k-goals" "$TEMP/k-seed-goals"
cmp "$TEMP/k-goals" "$TEMP/k-prime-goals"
cmp "$TEMP/k-goals" "$TEMP/k-replay-goals"
cut -f1 "$K/subset.tsv" | LC_ALL=C sort -u >"$TEMP/k-theories"
cut -f1 "$K/prime-spawns.tsv" | LC_ALL=C sort -u \
  >"$TEMP/k-prime-theories"
cut -f1 "$K/replay-spawns.tsv" | LC_ALL=C sort -u \
  >"$TEMP/k-replay-theories"
cut -f1 "$K/version-spawns.tsv" | LC_ALL=C sort -u \
  >"$TEMP/k-version-theories"
cmp "$TEMP/k-theories" "$TEMP/k-prime-theories"
cmp "$TEMP/k-theories" "$TEMP/k-replay-theories"
cmp "$TEMP/k-theories" "$TEMP/k-version-theories"
[[ "$(wc -l <"$K/prime-spawns.tsv")" == 27 &&
  "$(awk -F '\t' '$2 != 0 {bad++} {n += $2} END {
    if (bad) exit 1; print n+0}' "$K/prime-spawns.tsv")" == 0 ]]
[[ "$seed_spawns" == "$(jq -r '.seed_prover_spawns' \
  "$K/certificate.json")" ]]
[[ "$(awk -F '\t' '{n += $2} END {print n+0}' \
  "$K/replay-spawns.tsv")" == 0 ]]
[[ "$(wc -l <"$K/version-spawns.tsv")" == 27 &&
  "$version_spawns" == 81 ]]
awk -F '\t' '$2 != 3 {exit 1}' "$K/version-spawns.tsv"
while IFS= read -r theory; do
  awk -F '\t' -v theory="$theory" 'BEGIN {OFS="\t"}
    {print theory,$1,$2,$3,"true"}' "$K/provers.tsv"
done <"$TEMP/k-theories" | LC_ALL=C sort >"$TEMP/k-expected-versions"
LC_ALL=C sort "$K/resolved-versions.tsv" >"$TEMP/k-actual-versions"
cmp "$TEMP/k-expected-versions" "$TEMP/k-actual-versions"
printf '%s\n' hammer seed >"$TEMP/k-state-children"
cmp "$TEMP/k-state-children" "$K/state-children-before.tsv"
jq -e --arg state "/run/user/1003/holyhammer-phase3-task12/k-revised-v3" \
  --arg children "$(sha256sum "$K/state-children-before.tsv" |
    cut -d' ' -f1)" '
  .schema == "hh-task12-k-fresh-roots-v1" and .state_root == $state and
  .state_children_before_sha256 == $children and
  .state_children_before == ["hammer","seed"] and
  .prime_root == ($state+"/prime-cache-check") and
  .replay_root == ($state+"/replay-witness") and
  .prime_root_absent_before_run == true and
  .replay_root_absent_before_run == true and .resume_allowed == false
' "$K/fresh-root-proof.json" >/dev/null
[[ "$(jq -s '[.[]|.slices[]|.slice.filter]|group_by(.)|
  map({key:.[0],value:length})|from_entries' \
  "$K/replay-journal.jsonl" | jq -cS .)" == \
  '{"knn":2048,"mash":256,"mepo":256,"mesh":512}' ]]
jq -s -e --arg invocation "$(jq -r '.invocation_id' \
    "$K/terminal-service.json")" \
  --argjson cpu "$(jq -r '.cpu_usage_nsec' "$K/terminal-service.json")" \
  --argjson memory "$(jq -r '.memory_peak_bytes' \
    "$K/terminal-service.json")" '
  length == 2 and (map(.invocation_id)|unique) ==
    [$invocation] and
  all(.[];.unit == "phase3-task12-k-v10.service") and
  .[0].job_type == "start" and .[0].job_result == "done" and
  .[1].cpu_usage_nsec == $cpu and
  .[1].memory_peak_bytes == $memory and
  .[1].memory_swap_peak_bytes == 0 and
  ([.[]|select(.message|test("Failed|Main process exited"))]|length) == 0
' "$K/terminal-systemd.jsonl" >/dev/null

FINAL_CERT="$FINAL/final-certificate.json"
jq -e --arg sample "$(sha256sum "$SAMPLE/SHA256SUMS" | cut -d' ' -f1)" \
  --arg k "$(sha256sum "$K/SHA256SUMS" | cut -d' ' -f1)" \
  --arg verifier "$(sha256sum "$FINAL/verifier/SHA256SUMS" |
    cut -d' ' -f1)" \
  --arg provenance "$(sha256sum "$FINAL/provenance/SHA256SUMS" |
    cut -d' ' -f1)" \
  --arg report "$(sha256sum "$FINAL/report.md" | cut -d' ' -f1)" \
  --arg endurance "$(sha256sum \
    "$SAMPLE/endurance/terminal-certificate.json" | cut -d' ' -f1)" \
  --arg kterm "$(sha256sum "$K/terminal-service.json" | cut -d' ' -f1)" \
  --arg cleanup "$(sha256sum \
    "$FINAL/provenance/cleanup-certificate.json" | cut -d' ' -f1)" \
  --arg runtime "$(sha256sum \
    "$FINAL/provenance/runtime-provenance/certificate.json" | cut -d' ' -f1)" '
  .schema == "hh-task12-final-v5" and .status == "complete" and
  .sample_inventory_sha256 == $sample and .k_inventory_sha256 == $k and
  .verifier_inventory_sha256 == $verifier and
  .provenance_inventory_sha256 == $provenance and
  .report_sha256 == $report and
  .endurance_terminal_certificate_sha256 == $endurance and
  .k_terminal_certificate_sha256 == $kterm and
  .cleanup_certificate_sha256 == $cleanup and
  .runtime_provenance_certificate_sha256 == $runtime and
  .full_corpus_s30v5_measured == false and .no_full_corpus_claim == true and
  .endurance.status == "stopped-at-atomic-checkpoint" and
  .endurance.atoms == 408 and .endurance.goals == 3119 and
  .endurance.attempts == 410 and
  .endurance.restart_resume_events == 2 and
  .endurance.atomic_continuity == true and
  .endurance.restart_causes_retained == false and
  .endurance.restart_statuses_retained == false and
  .endurance.restart_cause_and_status == "unknown" and
  .endurance.empty_shards == 2 and
  .endurance.invocation_id == "492dbc2b61504a1398ce8b33cbced19d" and
  .endurance.start_realtime_usec == 1788539503796484 and
  .endurance.stop_realtime_usec == 1788636310148897 and
  .endurance.duration_usec == 96806352413 and
  .endurance.cpu_usage_nsec == 1279298591726000 and
  .endurance.memory_peak_bytes == 85072396288 and
  .endurance.swap_peak_bytes == 0 and
  .k.goals == 128 and .k.cached_cells == 3072 and
  .k.prime_cached_cells == 3072 and
  .k.version_resolution_spawns == 81 and
  .k.prime_cache_check_spawns == 0 and .k.replay_prover_spawns == 0 and
  .k.fresh_prime_and_replay_roots == true and
  .k.prime_and_replay_non_resume == true and
  .k.state_root ==
    "/run/user/1003/holyhammer-phase3-task12/k-revised-v3" and
  .k.cache_manifest_before_sha256 == .k.cache_manifest_after_sha256 and
  .tmpfs_cleanup == "complete" and .tuning_performed == false
' "$FINAL_CERT" >/dev/null
