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
  val consumed_of : step_record -> int option
  val created_of : step_record -> created
  val eigenvariables_of : step_record -> string list
  val validation_of : step_record -> validation

  (* The declaration an applied theorem came from, and which of that
     declaration's derived forms the theorem is -- the origin and variant a
     RuleApplication record reports.  The boolean says the application came
     from a duplicating net, which is what tells a rule's duplicated form
     from its plain one where the two coincide.  A theorem no declaration
     derived is its own origin. *)
  val rule_origin :
    clasetLib.claset -> bool -> thm -> thm * rule_variant

  val safe_step : clasetLib.claset -> step
  val clarify_step : clasetLib.claset -> step
  val inst0_step : clasetLib.claset -> step
  val instp_step : clasetLib.claset -> step
  val inst_step : clasetLib.claset -> step
  val unsafe_step : clasetLib.claset -> step
  val dup_step : clasetLib.claset -> step
  val step : clasetLib.claset -> step
  val slow_step : clasetLib.claset -> step

  (* Every transition in a complete safe fixed point, in replay order. *)
  val safe_saturation :
    clasetLib.claset -> node -> (goalpos * step_record * node) list

  (* Wrapper-free application of one supplied rule through the ordinary
     child policy.  Each sequence result is one application alternative. *)
  val rule_step :
    {theorem : thm, elim : bool, mode : clasetUnify.mode} -> step

  (* Engine-native forward application.  The first [immediate] premises are
     discharged from assumptions without consuming them; the residual
     theorem is added as a new head assumption of the sole child.  NONE
     asks for every premise of the canonical rule, which is the count the
     step derives anyway: the theorem is canonicalized once here and reused
     by every application, so no caller needs to canonicalize it to supply
     that count.  Every combination of assumptions that discharges the
     immediate premises is an alternative, except that no result repeats
     an assumption the goal already has or an earlier result added. *)
  val forward_rule_step :
    {theorem : thm, immediate : int option,
     mode : clasetUnify.mode} -> step

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
