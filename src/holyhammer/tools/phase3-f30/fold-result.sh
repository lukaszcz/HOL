#!/usr/bin/env bash
set -Eeuo pipefail

if (($# != 5)); then
  echo "usage: $0 RUN_DIR INPUT_SHA OUTPUT_JSON OUTPUT_INVENTORY GOALS" >&2
  exit 2
fi

RUN=$(realpath "$1")
INPUT_SHA=$2
OUTPUT=$3
INVENTORY=$4
GOALS=$(realpath "$5")
JOURNAL="$RUN/journal"
EXPECTED_GOALS=${HHEVAL_TASK11_EXPECTED_GOALS:-24721}
EXPECTED_THEORIES=${HHEVAL_TASK11_EXPECTED_THEORIES:-253}
EXPECTED_NONEMPTY=${HHEVAL_TASK11_EXPECTED_NONEMPTY:-229}
if [[ "$EXPECTED_GOALS:$EXPECTED_THEORIES:$EXPECTED_NONEMPTY" != \
      "24721:253:229" ]]; then
  [[ "${HHEVAL_TASK11_SELFTEST:-}" == 1 ]]
fi
TEMP_ROWS=$(mktemp)
TEMP_RESULT=$(mktemp)
TEMP_EXTRA=$(mktemp)
trap 'rm -f "$TEMP_ROWS" "$TEMP_RESULT" "$TEMP_EXTRA"' \
  EXIT HUP INT TERM

[[ -s "$GOALS" && ! -L "$GOALS" ]]
awk -F '\t' -v expected="$EXPECTED_GOALS" '
  NF != 2 || $1 == "" || $2 == "" || $2 !~ ("^" $1 "\\.") ||
  seen[$2]++ {exit 1}
  END {if (NR != expected) exit 1}
' "$GOALS"
goal_inventory_sha=$(sha256sum "$GOALS" | cut -d' ' -f1)

[[ -d "$JOURNAL" && -s "$RUN/run.json" ]]
(cd "$RUN" && find journal -type f -name '*.jsonl' -print0 |
  LC_ALL=C sort -z | xargs -0 sha256sum) >"$INVENTORY"
[[ "$(wc -l <"$INVENTORY")" -gt 0 ]]
inventory_files=$(wc -l <"$INVENTORY")

find "$JOURNAL" -type f -name '*.jsonl' -print0 |
  LC_ALL=C sort -z | xargs -0 cat | jq -c . >"$TEMP_ROWS"
awk -F '\t' 'NR == FNR {goals[$2] = 1; next} !goals[$1] {print $1}' \
  "$GOALS" <(jq -r '.goal_id' "$TEMP_ROWS" | LC_ALL=C sort -u) \
  >"$TEMP_EXTRA"
extra_goal_sha=$(sha256sum "$TEMP_EXTRA" | cut -d' ' -f1)
allow_superset=${HHEVAL_TASK11_ALLOW_SUPERSET:-0}
[[ "$allow_superset" == 0 || "$allow_superset" == 1 ]]

jq -s --slurpfile header "$RUN/run.json" \
  --arg input "$INPUT_SHA" \
  --arg run_sha "$(sha256sum "$RUN/run.json" | cut -d' ' -f1)" \
  --arg inventory_sha "$(sha256sum "$INVENTORY" | cut -d' ' -f1)" \
  --arg goal_inventory_sha "$goal_inventory_sha" \
  --arg extra_goal_sha "$extra_goal_sha" \
  --rawfile goal_rows "$GOALS" --rawfile extra_goal_rows "$TEMP_EXTRA" \
  --argjson allow_superset "$allow_superset" \
  --argjson expected_goals "$EXPECTED_GOALS" \
  --argjson expected_theories "$EXPECTED_THEORIES" \
  --argjson expected_nonempty "$EXPECTED_NONEMPTY" \
  --argjson inventory_files "$inventory_files" '
  def proved: .szs == "Theorem";
  def reconstructed: proved and .recon_ok == true;
  def metric($rows; $fresh):
    ($rows | map(select(.fresh == $fresh))) as $subset |
    {goals:($subset | length),
     proved:($subset | map(select(proved)) | length),
     reconstructed:($subset | map(select(reconstructed)) | length)};
  def condition_metric($all; $name):
    ($all | map(select(.cond == $name))) as $rows |
    ($rows[0]) as $first |
    {condition:$name,prover:$first.prover,
     filter:($first.selector | sub("[0-9]+$"; "")),
     selector:$first.selector,goals:($rows | length),
     proved:($rows | map(select(proved)) | length),
     reconstructed:($rows | map(select(reconstructed)) | length),
     seen:metric($rows; false),fresh:metric($rows; true)};
  def by($metrics; $prover; $filter):
    $metrics[] | select(.prover == $prover and .filter == $filter);
  def comparison($metrics; $prover; $count):
    (by($metrics; $prover; "mesh")) as $mesh |
    ["knn", "mepo", "mash"] as $single_filters |
    {prover:$prover,nfacts:$count,
     proved:{mesh:$mesh.proved,
       singles:[$single_filters[] as $filter |
         {filter:$filter,count:(by($metrics; $prover; $filter).proved)}],
       pass:([$single_filters[] as $filter |
         $mesh.proved >= by($metrics; $prover; $filter).proved] | all)},
     reconstructed:{mesh:$mesh.reconstructed,
       singles:[$single_filters[] as $filter |
         {filter:$filter,
          count:(by($metrics; $prover; $filter).reconstructed)}],
       pass:([$single_filters[] as $filter |
         $mesh.reconstructed >=
           by($metrics; $prover; $filter).reconstructed] | all)}};
  def shape($metrics; $prover):
    (by($metrics; $prover; "mepo")) as $mepo |
    (by($metrics; $prover; "mash")) as $mash |
    {prover:$prover,
     criterion_a:{description:"seen mash proved >= seen mepo proved",
       mash_seen_proved:$mash.seen.proved,
       mepo_seen_proved:$mepo.seen.proved,
       pass:($mash.seen.proved >= $mepo.seen.proved)},
     criterion_b:{description:
       "mepo/mash proved ratio higher on fresh than seen",
       fresh:{mepo:$mepo.fresh.proved,mash:$mash.fresh.proved},
       seen:{mepo:$mepo.seen.proved,mash:$mash.seen.proved},
       pass:(if $mash.fresh.proved == 0 or $mash.seen.proved == 0
         then false
         else ($mepo.fresh.proved * $mash.seen.proved) >
           ($mepo.seen.proved * $mash.fresh.proved)
         end)}};
  [{cond:"f30-vampire-knn",prover:"vampire",version:"5.0.1",
    selector:"knn96",max_facts:96},
   {cond:"f30-vampire-mepo",prover:"vampire",version:"5.0.1",
    selector:"mepo96",max_facts:96},
   {cond:"f30-vampire-mash",prover:"vampire",version:"5.0.1",
    selector:"mash96",max_facts:96},
   {cond:"f30-vampire-mesh",prover:"vampire",version:"5.0.1",
    selector:"mesh96",max_facts:96},
   {cond:"f30-e-knn",prover:"e",version:"3.2.5-ho",
    selector:"knn128",max_facts:128},
   {cond:"f30-e-mepo",prover:"e",version:"3.2.5-ho",
    selector:"mepo128",max_facts:128},
   {cond:"f30-e-mash",prover:"e",version:"3.2.5-ho",
    selector:"mash128",max_facts:128},
   {cond:"f30-e-mesh",prover:"e",version:"3.2.5-ho",
    selector:"mesh128",max_facts:128}] as $specs |
  ($specs | map(.cond)) as $names |
  ($goal_rows | split("\n") | map(select(length > 0) |
    split("\t") | {thy:.[0],goal_id:.[1]})) as $goal_specs |
  (reduce $goal_specs[] as $goal ({};
    .[$goal.goal_id] = $goal.thy)) as $goal_set |
  ($extra_goal_rows | split("\n") | map(select(length > 0))) as $extras |
  . as $observed_rows |
  ($observed_rows | map(select($goal_set[.goal_id] == .thy))) as $rows |
  ($observed_rows | map(select($goal_set[.goal_id] != .thy))) as $extra_rows |
  ($header[0]) as $run |
  ($names | map(condition_metric($rows; .))) as $metrics |
  (comparison($metrics; "vampire"; 96)) as $vampire |
  (comparison($metrics; "e"; 128)) as $e |
  (shape($metrics; "vampire")) as $vampire_shape |
  (shape($metrics; "e")) as $e_shape |
  ($rows | group_by([.goal_id,.cond]) |
    map(select(length != 1)) | length) as $duplicates |
  ($rows | group_by(.goal_id) |
    map(select((map(.fresh) | unique | length) != 1 or
      (map(.ho) | unique | length) != 1 or length != 8)) |
    length) as $subset_mismatches |
  ($extra_rows | group_by(.goal_id) |
    map(select(length != 8 or
      (map(.cond) | sort) != ($names | sort) or
      (map(.fresh) | unique | length) != 1 or
      (map(.ho) | unique | length) != 1)) | length) as $bad_extras |
  ($rows | group_by(.thy) |
    map({key:.[0].thy,value:(length / 8)}) | from_entries) as $theory_counts |
  ($run.corpus | map({key:.thy,value:.theorem_count}) |
    from_entries) as $expected_theory_counts |
  if ($goal_specs | length) != $expected_goals or
      ($goal_specs | map(.goal_id) | unique | length) != $expected_goals or
      ($goal_specs | group_by(.thy) |
        map({key:.[0].thy,value:length}) | from_entries) !=
      ($run.corpus | map(select(.theorem_count > 0) |
        {key:.thy,value:.theorem_count}) | from_entries) then
    error("canonical goal inventory is invalid")
  elif ($run.schema != 4 or $run.sample != 1 or
      ($run.conditions | length) != 8 or
      ($run.corpus | length) != $expected_theories or
      ([$run.corpus[].theorem_count] | add) != $expected_goals or
      ([$run.corpus[] | select(.theorem_count > 0)] | length) !=
        $expected_nonempty) then
    error("invalid F30 run header")
  elif ($rows | length) != ($expected_goals * 8) or $duplicates != 0 or
       $subset_mismatches != 0 or $theory_counts !=
       ($expected_theory_counts | with_entries(select(.value > 0))) then
    error("journal is incomplete, duplicated, or corpus-inconsistent")
  elif ($extras | length) * 8 != ($extra_rows | length) or
       $bad_extras != 0 or
       (($extras | length) > 0 and $allow_superset != 1) then
    error("journal contains an unapproved or malformed corpus superset")
  elif any($observed_rows[]; . as $row |
      (. | type) != "object" or .run != "experiment" or
      (.thy | type) != "string" or .thy == "" or
      (.thm | type) != "string" or .thm == "" or
      (.goal_id | type) != "string" or .goal_id != (.thy + "." + .thm) or
      ($run.corpus | map(.thy) | index($row.thy)) == null or
      (.cond | type) != "string" or ($names | index($row.cond)) == null or
      .engine != "prover" or .regime != "chainy" or .timeout != 30 or
      (.fresh | type) != "boolean" or (.ho | type) != "boolean" or
      (.nfacts | type) != "number" or .nfacts < 0 or
      .nfacts != (.nfacts | floor) or
      (.szs | type) != "string" or (.t_prover | type) != "number" or
      .t_prover < 0 or
      (if .szs == "Theorem" then
         (.axioms_used | type) != "array" or
         any(.axioms_used[]; (. | type) != "string") or
         (.recon_ok | type) != "boolean" or
         (.recon_method | type) != "string" or .recon_method == "" or
         (if .recon_ok then
            (.t_recon | type) != "number" or .t_recon < 0 or
            (.stac | type) != "string" or .stac == "" or .error != null
          else .t_recon != null or .stac != null end)
       else .axioms_used != null or .recon_ok != null or
         .recon_method != null or .t_recon != null or .stac != null
       end) or
      (.error != null and
        ((.error | type) != "string" or .error == "" or
         .szs != "Theorem" or
         .recon_ok != false))) then
    error("journal contains an invalid F30 cell")
  elif ([$specs[] as $spec | $observed_rows[] | select(
      .cond == $spec.cond and
      (.prover != $spec.prover or .prover_version != $spec.version or
       .selector != $spec.selector or .nfacts > $spec.max_facts))] |
      length) != 0 then
    error("journal condition/prover/selector binding is invalid")
  elif ([$names[] as $name |
      ($rows | map(select(.cond == $name)) | length) == $expected_goals] |
      all) != true then
    error("condition does not cover the full corpus")
  elif ([$specs[] as $spec |
      ($run.conditions | map(select(.cond_id == $spec.cond and
        .prover == $spec.prover and .selector == $spec.selector and
        .engine == "prover" and .regime == "chainy" and
        .timeout == 30 and .reconstruct == true)) | length) == 1] |
      all) != true then
    error("run header condition differs from frozen F30")
  elif $inventory_files != ($run.corpus |
      map(select(.theorem_count > 0) |
        ((.theorem_count + 7) / 8 | floor)) | add) then
    error("journal shard inventory differs from the frozen atom plan")
  else
    {schema:"hh-task11-f30-result-v1",status:"complete",
     input_inventory_sha256:$input,run_header_sha256:$run_sha,
     journal_inventory_sha256:$inventory_sha,
     canonical_goal_inventory_sha256:$goal_inventory_sha,
     canonical_goal_source:"accepted TASK10 A paired derivation",
     observed_cells:($observed_rows | length),
     excluded_extra_goals:($extras | length),
     excluded_extra_goal_ids_sha256:$extra_goal_sha,
     strict_superset_corrected:(($extras | length) > 0),
     journal_files:$inventory_files,
     cells:($rows | length),goals:$expected_goals,
     theories:$expected_theories,nonempty_theories:$expected_nonempty,
     conditions:$metrics,
     gate:{vampire:$vampire,e:$e,
       pass:($vampire.proved.pass and $vampire.reconstructed.pass and
         $e.proved.pass and $e.reconstructed.pass)},
     shape:{vampire:$vampire_shape,e:$e_shape,
       criterion_a_pass:($vampire_shape.criterion_a.pass and
         $e_shape.criterion_a.pass),
       criterion_b_pass:($vampire_shape.criterion_b.pass and
         $e_shape.criterion_b.pass)}}
  end
' "$TEMP_ROWS" | jq -S . >"$TEMP_RESULT"

mv "$TEMP_RESULT" "$OUTPUT"
trap 'rm -f "$TEMP_ROWS" "$TEMP_EXTRA"' EXIT HUP INT TERM
