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

  (* Timed exact replay is a diagnostic-only extension of the measured
     sequence above.  The clock is read only after an Enter callback/poll and
     immediately before the corresponding Exit callback/poll.  Thus the
     accumulated intervals exclude observers and stop predicates, include
     failed/backtracked engine work, and never invent an Exit boundary.

     Time.now is the intended production clock.  Time.time is exact, but the
     Basis wall clock need not be monotonic on every platform; a backwards
     clock is detected and reported as HOL_ERR instead of being accumulated.
     Clock exceptions propagate unchanged.  Reading the clock and updating
     the diagnostic references are measurement overhead.  Classical phases
     are non-nested, so classical_time is exactly the sum of its eleven
     fields. *)
  type timed_rule_statistics =
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
     elim_attempts : int,
     attempt_selection_time : Time.time,
     freshening_setup_time : Time.time,
     minor_unification_time : Time.time,
     elimination_major_unification_time : Time.time,
     rule_instantiation_time : Time.time,
     child_store_construction_time : Time.time,
     direct_result_construction_time : Time.time,
     lazy_result_yield_time : Time.time,
     direct_child_replacement_time : Time.time,
     replay_record_construction_time : Time.time,
     record_insertion_time : Time.time,
     classical_time : Time.time}
  type timed_rule_sequence
  datatype timed_rule_pull =
      TimedRuleEmpty
    | TimedRuleYield of
        (step_record * node) * timed_rule_sequence
    | TimedRuleInterrupted
  val blast_rule_step_timed :
    {clock : unit -> Time.time,
     observe : (measured_rule_observation -> unit) option,
     stop : unit -> bool} ->
    clasetLib.claset -> {theorem : thm, elim : bool} ->
    node * goalpos -> timed_rule_sequence
  val timed_rule_cases : timed_rule_sequence -> timed_rule_pull
  val timed_rule_current :
    timed_rule_sequence -> measured_rule_observation option
  val timed_rule_statistics :
    timed_rule_sequence -> timed_rule_statistics

  (* Timed-v2 is additive.  It preserves the timed replay protocol while
     splitting MinorUnification according to the persistent unifier's
     actual work.  Failed cleanup is explicitly zero because failed stores
     are discarded immutable values, not rolled back. *)
  type minor_unification_times =
    {calls : int,
     failures : int,
     normalization_setup_time : Time.time,
     traversal_decomposition_binding_time : Time.time,
     failure_cleanup_time : Time.time,
     minor_unification_time : Time.time,
     max_normalization_setup_time : Time.time,
     max_traversal_decomposition_binding_time : Time.time,
     max_failure_cleanup_time : Time.time,
     max_minor_unification_time : Time.time}
  type timed_rule_statistics_v2 =
    {base : timed_rule_statistics,
     minor_unification_times : minor_unification_times}
  type timed_rule_sequence_v2
  datatype timed_rule_pull_v2 =
      TimedRuleEmptyV2
    | TimedRuleYieldV2 of
        (step_record * node) * timed_rule_sequence_v2
    | TimedRuleInterruptedV2
  val blast_rule_step_timed_v2 :
    {clock : unit -> Time.time,
     observe : (measured_rule_observation -> unit) option,
     stop : unit -> bool} ->
    clasetLib.claset -> {theorem : thm, elim : bool} ->
    node * goalpos -> timed_rule_sequence_v2
  val timed_rule_cases_v2 : timed_rule_sequence_v2 -> timed_rule_pull_v2
  val timed_rule_current_v2 :
    timed_rule_sequence_v2 -> measured_rule_observation option
  val timed_rule_statistics_v2 :
    timed_rule_sequence_v2 -> timed_rule_statistics_v2

  (* Timed-v3 preserves every earlier sequence/result shape and adds the
     operation-honest minor-unification partition.  Component times are
     mutually exclusive and sum exactly to the retained coarse traversal;
     immutable-store cleanup remains exactly zero. *)
  type minor_unification_times_v3 =
    {calls : int,
     failures : int,
     normalization_setup_events : int,
     persistent_store_lookup_walk_events : int,
     structural_decomposition_recursion_events : int,
     pattern_occurs_allow_decision_events : int,
     persistent_binding_update_events : int,
     binding_operation_failures : int,
     traversal_other_events : int,
     operation_phase_trace :
       (clasetUnify.timed_phase_boundary_v3 *
        clasetUnify.timed_phase_v3) list,
     normalization_setup_time : Time.time,
     persistent_store_lookup_walk_time : Time.time,
     structural_decomposition_recursion_time : Time.time,
     pattern_occurs_allow_decision_time : Time.time,
     persistent_binding_update_time : Time.time,
     traversal_other_time : Time.time,
     traversal_decomposition_binding_time : Time.time,
     failure_cleanup_time : Time.time,
     minor_unification_time : Time.time,
     max_normalization_setup_time : Time.time,
     max_persistent_store_lookup_walk_time : Time.time,
     max_structural_decomposition_recursion_time : Time.time,
     max_pattern_occurs_allow_decision_time : Time.time,
     max_persistent_binding_update_time : Time.time,
     max_traversal_other_time : Time.time,
     max_traversal_decomposition_binding_time : Time.time,
     max_failure_cleanup_time : Time.time,
     max_minor_unification_time : Time.time}
  type timed_rule_statistics_v3 =
    {base : timed_rule_statistics_v2,
     minor_unification_times : minor_unification_times_v3}
  type timed_rule_sequence_v3
  datatype timed_rule_pull_v3 =
      TimedRuleEmptyV3
    | TimedRuleYieldV3 of
        (step_record * node) * timed_rule_sequence_v3
    | TimedRuleInterruptedV3
  exception TIMED_RULE_CALLBACK_V3 of exn
  val blast_rule_step_timed_v3 :
    {clock : unit -> Time.time,
     observe : (measured_rule_observation -> unit) option,
     stop : unit -> bool} ->
    clasetLib.claset -> {theorem : thm, elim : bool} ->
    node * goalpos -> timed_rule_sequence_v3
  val blast_rule_step_timed_v3_with_sink :
    {classical_elapsed : Time.time -> unit,
     clock : unit -> Time.time,
     observe : (measured_rule_observation -> unit) option,
     stop : unit -> bool} ->
    clasetLib.claset -> {theorem : thm, elim : bool} ->
    node * goalpos -> timed_rule_sequence_v3
  val timed_rule_cases_v3 :
    timed_rule_sequence_v3 -> timed_rule_pull_v3
  val timed_rule_current_v3 :
    timed_rule_sequence_v3 -> measured_rule_observation option
  val timed_rule_statistics_v3 :
    timed_rule_sequence_v3 -> timed_rule_statistics_v3
  val timed_rule_statistics_reads_v3 : timed_rule_sequence_v3 -> int

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
