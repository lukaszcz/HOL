signature clasetStep =
sig
  include Abbrev

  type node = clasetGoal.node
  type goalpos = int

  datatype rule_variant = datatype clasetReplay.rule_variant
  datatype step_kind = datatype clasetReplay.step_kind

  type created = clasetReplay.created
  type step_record = clasetReplay.step_record
  type step = node * goalpos -> (step_record * node) seq.seq

  val kind_of : step_record -> step_kind
  val target_of : step_record -> goalpos
  val consumed_of : step_record -> int option
  val created_of : step_record -> created
  val eigenvariables_of : step_record -> string list
  val validation_of : step_record -> validation

  val safe_step : clasetLib.claset -> step
  val clarify_step : clasetLib.claset -> step
  val inst0_step : clasetLib.claset -> step
  val instp_step : clasetLib.claset -> step
  val inst_step : clasetLib.claset -> step
  val unsafe_step : clasetLib.claset -> step
  val dup_step : clasetLib.claset -> step
  val step : clasetLib.claset -> step
  val slow_step : clasetLib.claset -> step

  (* Wrapper-free application of one supplied rule through the ordinary
     child policy.  Each sequence result is one application alternative. *)
  val rule_step :
    {theorem : thm, elim : bool, mode : clasetUnify.mode} -> step

  (* Exact, wrapper-free engine transitions used by blast reconstruction.
     Rule application uses the supplied canonical source rather than doing
     another claset lookup. *)
  val blast_assumption_step : step
  val blast_contradiction_step : step
  val blast_rule_step :
    clasetLib.claset -> {theorem : thm, elim : bool} -> step
  (* The additive [_at] forms select assumption occurrences before applying
     theorem/tactic logic.  Rule selectors use NONE only for introductions
     and a positive, in-range SOME position only for eliminations; a shape,
     range, polarity or matching error is clean nonapplication.  Internally
     all diagnostic families share this same singleton selection layer. *)
  val blast_assumption_step_at : int -> step
  val blast_contradiction_step_at :
    {negative : int, positive : int} -> step
  val blast_rule_step_at :
    clasetLib.claset ->
    {theorem : thm, elim : bool, major : int option} -> step

  val blast_disch_step : step
  val blast_gen_step : step
  val blast_ccontr_step : step
  val blast_hyp_subst_step : step
  val blast_hyp_subst_step_at :
    {equality : int, changed : bool list} -> step
  val blast_move_back_step : int -> step

  (* [depth_step cs part m] selects the duplicating or non-duplicating
     unsafe net through [part].  Safe and inst0 inferences cost nothing;
     an instp/part inference costs one unit. *)
  val depth_step : clasetLib.claset -> clasetLib.claset_part -> int -> step
end
