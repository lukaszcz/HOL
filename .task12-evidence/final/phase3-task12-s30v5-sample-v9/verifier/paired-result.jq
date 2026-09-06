def proved: .szs == "Theorem";
def recon: proved and .recon_ok == true;
def interval($wins;$losses;$n):
  (($wins-$losses)/$n) as $mean |
  (((($wins+$losses)/$n - $mean*$mean) / ($n-1)) | sqrt) as $se |
  {low:($mean-1.959963984540054*$se),
   high:($mean+1.959963984540054*$se)};
def paired($old;$new):
  ($old|length) as $count |
  ([range(0;$count) | select($new[.] and ($old[.]|not))] | length) as $w |
  ([range(0;$count) | select(($new[.]|not) and $old[.])] | length) as $l |
  {phase2:([$old[]|select(.)]|length),phase3:([$new[]|select(.)]|length),
   wins:$w,losses:$l,ties:($count-$w-$l),delta:($w-$l),
   delta_rate:(($w-$l)/$count),ci95:interval($w;$l;$count)} |
  . + {credible_regression:(.ci95.high < 0)};
def skey:
  [.prover,.filter,.format,.type_enc,.lam_trans,
   (.nfacts|tostring),(.slice_size|tostring),(.extra_opts|tojson)] |
  join("\t");
($old | sort_by(.goal_id)) as $o |
($new | sort_by(.goal_id)) as $n |
if ($o|length) != 3000 or ($n|length) != 3000 or
   ($o|map(.goal_id)) != ($n|map(.goal_id)) then
  error("paired samples differ")
else
  ($schedule | split("\n") | map(select(length>0)|split("\t")|
    {index:(.[0]|tonumber),prover:.[1],filter:.[2],format:.[3],
     type_enc:.[4],lam_trans:.[5],nfacts:(.[6]|tonumber),
     slice_size:(.[7]|tonumber),extra_opts:[]})) as $specs |
  ($specs | map(skey)) as $schedule_keys |
  ($schedule_keys[0:16]) as $anchor_keys |
  if ($specs|length) != 24 or
     ($specs|map(.index)) != [range(1;25)] or
     ($schedule_keys|unique|length) != 24 or
     any($n[]; . as $row |
       ($row.slices|length) != 24 or
       (($row.slices|map(.slice|skey)|sort) != ($schedule_keys|sort)) or
       ($row.winner != null and
         (($schedule_keys|index(($row.winner|skey))) == null))) then
    error("S30-v5 row does not contain the exact frozen schedule keys")
  else
    [range(0;3000) | {goal_id:$n[.].goal_id,
      old_proved:($o[.]|proved),new_proved:($n[.]|proved),
      old_reconstructed:($o[.]|recon),new_reconstructed:($n[.]|recon)}]
      as $pairs |
    [$specs[16:24][] as $s | ($s|skey) as $key |
      {index:$s.index,prover:$s.prover,filter:$s.filter,
       format:$s.format,nfacts:$s.nfacts,
       winner_wins:([$n[] | select(.winner != null and
         (.winner|skey)==$key and proved)]|length),
       winner_reconstructed:([$n[] | select(.winner != null and
         (.winner|skey)==$key and recon)]|length),
       successes:([$n[] | .slices[] |
         select((.slice|skey)==$key and .szs=="Theorem")]|length),
       anchor_exclusive:([$n[] | select(
         any(.slices[];(.slice|skey)==$key and .szs=="Theorem") and
         all(.slices[]; . as $row |
           (($row.slice|skey) as $observed |
             (($anchor_keys|index($observed)) == null or
              $row.szs!="Theorem"))))]|length),
       anchor_exclusive_reconstructed:([$n[] | select(recon and
         any(.slices[];(.slice|skey)==$key and .szs=="Theorem") and
         all(.slices[]; . as $row |
           (($row.slice|skey) as $observed |
             (($anchor_keys|index($observed)) == null or
              $row.szs!="Theorem"))))]|length)}] as $slices |
    {schema:"hh-task12-paired-sample-v4",status:"complete",
   inference_scope:"sealed 3119-goal fixed-order endurance frame",
   sample_size:3000,selection:"lowest SHA-256(goal_id), bytewise",
   confidence_method:
     "paired binary-difference normal 95% interval (sample variance)",
   no_full_corpus_claim:true,full_corpus_s30v5_measured:false,
   proved:paired(($pairs|map(.old_proved));($pairs|map(.new_proved))),
   reconstructed:paired(($pairs|map(.old_reconstructed));
     ($pairs|map(.new_reconstructed))),
   new_slice_classification:"exact full schedule key, order independent",
   anchor_exclusive_counting:
     "slice-attributed; one goal may contribute to multiple slice/filter sums",
   new_slices:$slices,
   new_filter_aggregates:($slices | group_by(.filter) | map({
     filter:.[0].filter,slices:length,
     winner_wins:(map(.winner_wins)|add),
     winner_reconstructed:(map(.winner_reconstructed)|add),
     successes:(map(.successes)|add),
     anchor_exclusive:(map(.anchor_exclusive)|add),
     anchor_exclusive_reconstructed:
       (map(.anchor_exclusive_reconstructed)|add)}))}
  end
end
