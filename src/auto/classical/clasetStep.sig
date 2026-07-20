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

  (* Exact, wrapper-free engine transitions used by blast reconstruction.
     Rule application uses the supplied canonical source rather than doing
     another claset lookup. *)
  val blast_assumption_step : step
  val blast_contradiction_step : step
  val blast_rule_step :
    clasetLib.claset -> {theorem : thm, elim : bool} -> step

  (* Measured exact stored-rule replay is a caller-neutral, parallel path.
     It leaves [blast_rule_step] unchanged and exposes only facts owned by
     the classical engine.  Pulling the abstract sequence preserves the
     ordinary sequence's laziness and order. *)
  datatype measured_rule_kind = IntroRule | ElimRule
  datatype measured_rule_phase =
      AttemptSelection
    | FresheningSetup
    | MinorUnification
    | EliminationMajorUnification
    | RuleInstantiation
    | ChildStoreConstruction
    | DirectResultConstruction
    | LazyResultYield
    | DirectChildReplacement
    | ReplayRecordConstruction
    | RecordInsertion
  datatype measured_rule_boundary = RuleEnter | RuleExit
  type measured_rule_observation =
    {boundary : measured_rule_boundary,
     phase : measured_rule_phase,
     goal_position : goalpos,
     rule_kind : measured_rule_kind,
     assumption_position : int option}
  type measured_rule_statistics =
    {cooperative_checkpoints : int,
     phase_entries : int,
     phase_exits : int,
     attempt_selections : int,
     freshening_setups : int,
     minor_unifications : int,
     elimination_major_unifications : int,
     rule_instantiations : int,
     child_store_constructions : int,
     direct_result_constructions : int,
     lazy_result_yields : int,
     direct_child_replacements : int,
     replay_record_constructions : int,
     record_insertions : int,
     intro_attempts : int,
     elim_attempts : int}
  type measured_rule_sequence
  datatype measured_rule_pull =
      MeasuredRuleEmpty
    | MeasuredRuleYield of
        (step_record * node) * measured_rule_sequence
    | MeasuredRuleInterrupted

  (* Phase semantics follow the exact lazy stored-rule path.

     AttemptSelection renders the selected goal after the supplied theorem
     and current positional elimination assumption have been selected; no
     claset candidate lookup occurs.  FresheningSetup canonicalizes and
     freshens that theorem.  MinorUnification matches its conclusion to the
     goal, and EliminationMajorUnification, when present, matches its major
     premise to the selected assumption.  RuleInstantiation collapses the
     store, instantiates and normalizes the rule, and aligns theorem
     hypotheses.  ChildStoreConstruction constructs engine children and
     their store.  DirectResultConstruction constructs validation/action and
     the internal direct result.  LazyResultYield exposes that result to the
     sequence map.  The final three phases replace the direct child, build
     its replay record, and insert that record respectively.

     Each Enter/Exit brackets one indivisible operation.  Rule failure or an
     exception can leave an unmatched Enter.  A true stop is returned by
     [measured_rule_cases] as [MeasuredRuleInterrupted].  Arbitrary
     observer/stop exceptions propagate unchanged rather than becoming rule
     failure, including HOL_ERR and runtime Interrupt. *)
  val blast_rule_step_measured :
    {observe : (measured_rule_observation -> unit) option,
     stop : unit -> bool} ->
    clasetLib.claset -> {theorem : thm, elim : bool} ->
    node * goalpos -> measured_rule_sequence
  val measured_rule_cases :
    measured_rule_sequence -> measured_rule_pull
  val measured_rule_current :
    measured_rule_sequence -> measured_rule_observation option
  val measured_rule_statistics :
    measured_rule_sequence -> measured_rule_statistics

  val blast_disch_step : step
  val blast_gen_step : step
  val blast_ccontr_step : step
  val blast_hyp_subst_step : step
  val blast_move_back_step : int -> step

  (* [depth_step cs part m] selects the duplicating or non-duplicating
     unsafe net through [part].  Safe and inst0 inferences cost nothing;
     an instp/part inference costs one unit. *)
  val depth_step : clasetLib.claset -> clasetLib.claset_part -> int -> step
end
