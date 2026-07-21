signature blastReconstruct =
sig
  include Abbrev

  type claset = clasetLib.claset
  type proof = blastSearch.proof

  (* Reconstruction executes the recorded tableau script left-to-right on a
     typed classical-engine node, then grounds and kernel-replays once. *)
  val reconstruct : goal -> proof -> (goal list * validation) option
  val reconstructWith :
    claset -> goal -> proof -> (goal list * validation) option

  datatype step_kind =
      HypSubstStep
    | CloseAssumeStep
    | CloseContradictionStep
    | SafeRuleStep
    | DeferGoalStep
    | UnsafeRuleStep

  datatype phase =
      ReplayRecursion
    | AlternativeEnumeration
    | TypedStep of step_kind
    | StoredRuleSetup
    | StoredRuleTransition
    | DuplicateChildMove
    | FinishOpenGoals
    | GroundReplay
    | KernelReplay
    | FinishResidualGoals

  datatype boundary = Enter | Exit
  type observation = {boundary : boundary, phase : phase}

  (* Phase meanings follow the actual lazy control flow.  ReplayRecursion
     brackets a replay invocation, including nested work.  TypedStep brackets
     setup of the typed step's lazy sequence; it does not imply that a typed
     transition has been forced.  AlternativeEnumeration brackets seq.cases,
     which forces enough of that lazy sequence to expose its next node and can
     therefore perform engine-transition work.  StoredRuleSetup constructs
     the mapped stored-rule sequence.  StoredRuleTransition is post-yield
     processing of an already exposed node (child counting and any duplicate
     movement), not the stored-rule engine call.  DuplicateChildMove forces
     the position-directed move transition. *)

  type statistics =
    {cooperative_checkpoints : int,
     phase_entries : int,
     phase_exits : int,
     replay_recursions : int,
     alternative_pulls : int,
     typed_steps : int,
     hyp_subst_steps : int,
     close_assume_steps : int,
     close_contradiction_steps : int,
     safe_rule_steps : int,
     defer_goal_steps : int,
     unsafe_rule_steps : int,
     stored_rule_setups : int,
     stored_rule_transitions : int,
     duplicate_child_moves : int,
     finish_open_goal_checks : int,
     grounding_attempts : int,
     kernel_replay_attempts : int,
     finish_residual_goal_checks : int}

  datatype completion = Completed | Interrupted
  type measured_result =
    {completion : completion,
     current_phase : observation option,
     result : (goal list * validation) option,
     statistics : statistics}

  (* This diagnostic path is separate from reconstruct/reconstructWith.
     stop is polled at every Enter and Exit boundary.  observe, when
     present, is called immediately before that poll and makes the current
     boundary externally visible (for example to a watchdog log).  A true
     stop returns Interrupted with no reconstruction result.  Exceptions
     from either callback, including HOL_ERR, propagate unchanged.

     Operation counters count Enter boundaries, including an operation
     whose Enter poll requests interruption.  cooperative_checkpoints is
     exactly the number of stop calls; phase_entries and phase_exits count
     the corresponding observations.  current_phase is the last observed
     boundary.  Every bracketed operation is indivisible between its Enter
     and Exit polls.  In particular, lazy sequence forcing, external typed
     transitions, grounding and Tactical.VALID kernel replay have no hard
     real-time bound supplied by this API.  An exception or replay
     backtracking path can leave an Enter without a matching Exit.  Thus the
     last observation is coherent boundary evidence, not a causal attribution
     or necessarily an operation still running. *)
  val reconstructWithMeasured :
    {observe : (observation -> unit) option, stop : unit -> bool} ->
    claset -> goal -> proof -> measured_result
  val reconstructMeasured :
    {observe : (observation -> unit) option, stop : unit -> bool} ->
    goal -> proof -> measured_result

  type stored_rule_observation =
    {script_position : int,
     step_kind : step_kind,
     duplicate : bool,
     rule : clasetStep.measured_rule_observation}

  type detailed_statistics =
    {cooperative_checkpoints : int,
     phase_entries : int,
     phase_exits : int,
     replay_recursions : int,
     alternative_pulls : int,
     typed_steps : int,
     hyp_subst_steps : int,
     close_assume_steps : int,
     close_contradiction_steps : int,
     safe_rule_steps : int,
     defer_goal_steps : int,
     unsafe_rule_steps : int,
     stored_rule_setups : int,
     stored_rule_transitions : int,
     duplicate_child_moves : int,
     finish_open_goal_checks : int,
     grounding_attempts : int,
     kernel_replay_attempts : int,
     finish_residual_goal_checks : int,
     stored_rule_checkpoints : int,
     stored_rule_phase_entries : int,
     stored_rule_phase_exits : int,
     stored_rule_attempt_selections : int,
     stored_rule_freshening_setups : int,
     stored_rule_minor_unifications : int,
     stored_rule_major_unifications : int,
     stored_rule_instantiations : int,
     stored_rule_child_store_constructions : int,
     stored_rule_direct_result_constructions : int,
     stored_rule_lazy_yields : int,
     stored_rule_direct_child_replacements : int,
     stored_rule_replay_record_constructions : int,
     stored_rule_record_insertions : int,
     stored_rule_intro_attempts : int,
     stored_rule_elim_attempts : int,
     stored_rule_safe_attempts : int,
     stored_rule_unsafe_attempts : int}

  type detailed_measured_result =
    {completion : completion,
     current_phase : observation option,
     current_stored_rule : stored_rule_observation option,
     result : (goal list * validation) option,
     statistics : detailed_statistics}

  (* The detailed entry points additionally publish classical exact-rule
     boundaries.  Their snapshot combines the caller-owned script index and
     safe/unsafe/duplicate label with the caller-neutral classical event.
     Stored-rule checkpoints are included in cooperative_checkpoints, while
     phase_entries/phase_exits continue to count outer reconstruction phases;
     stored_rule_phase_entries/stored_rule_phase_exits count the classical
     boundaries separately.  A classical interruption leaves the enclosing
     AlternativeEnumeration Enter unmatched and returns Interrupted. *)
  val reconstructWithMeasuredDetailed :
    {observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> detailed_measured_result
  val reconstructMeasuredDetailed :
    {observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    goal -> proof -> detailed_measured_result

  type classical_phase_times =
    {attempt_selection_time : Time.time,
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

  type timed_detailed_measured_result =
    {completion : completion,
     current_phase : observation option,
     current_stored_rule : stored_rule_observation option,
     result : (goal list * validation) option,
     statistics : detailed_statistics,
     classical_times : classical_phase_times,
     attempt_wall_time : Time.time}

  (* This is the timed-only form of the detailed diagnostic.  It preserves
     the detailed observer and polling protocol and adds exclusive elapsed
     time for the eleven non-nested classical phases.  attempt_wall_time is
     captured immediately when replay reaches Completed SOME, Completed NONE,
     or Interrupted, before statistics and classical timing snapshots are
     aggregated.  Thus subtracting classical_time gives the unaccounted
     outer-reconstruction, observer and timing share only up to that terminal
     outcome, without double counting or diagnostic report aggregation.

     The injected clock keeps exact tests deterministic; callers should use
     Time.now in production.  The wall clock is assumed not to move backwards.
     A negative delta is reported as HOL_ERR, and arbitrary clock exceptions
     propagate unchanged.  Clock reads and accumulator updates are part of
     the diagnostic's measurement overhead. *)
  val reconstructWithMeasuredTimedDetailed :
    {clock : unit -> Time.time,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> timed_detailed_measured_result
  val reconstructMeasuredTimedDetailed :
    {clock : unit -> Time.time,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    goal -> proof -> timed_detailed_measured_result

  type minor_unification_times = clasetStep.minor_unification_times
  type outer_reconstruction_times =
    {alternative_enumeration_time : Time.time,
     replay_continuation_time : Time.time,
     other_outer_time : Time.time,
     outer_reconstruction_time : Time.time}
  type timed_detailed_measured_result_v2 =
    {base : timed_detailed_measured_result,
     minor_unification_times : minor_unification_times,
     outer_reconstruction_times : outer_reconstruction_times}

  (* Additive timed-v2 diagnostic.  Alternative and replay/continuation
     fields are exclusive phase-owner times.  Classical intervals occur
     while AlternativeEnumeration forces stored rules and are subtracted
     exactly from that owner; consequently outer_reconstruction_time plus
     base.classical_times.classical_time equals base.attempt_wall_time.
     Other outer time retains top-level setup/terminal work and explicitly
     bracketed phases other than AlternativeEnumeration and ReplayRecursion.
     As with the earlier timed API, a phase clock begins after its Enter
     callback/poll and ends before its Exit callback/poll, so those boundary
     gaps belong to the enclosing exclusive owner.  This entry point
     inherits the timed diagnostic's clock-exception identity and explicit
     HOL_ERR on backwards movement. *)
  val reconstructWithMeasuredTimedDetailedV2 :
    {clock : unit -> Time.time,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> timed_detailed_measured_result_v2
  (* Diagnostic dependency-injection seam for deterministic validation of
     replay backtracking.  The ordinary V2 entry point above supplies exactly
     [Tactical.VALID (clasetReplay.REPLAY_TAC grounded)]; production search,
     reconstruction and tactic APIs do not pass through this seam. *)
  val reconstructWithMeasuredTimedDetailedV2UsingKernel :
    {clock : unit -> Time.time,
     kernel_replay :
       clasetReplay.grounded_script -> goal -> goal list * validation,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> timed_detailed_measured_result_v2
  val reconstructMeasuredTimedDetailedV2 :
    {clock : unit -> Time.time,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    goal -> proof -> timed_detailed_measured_result_v2

  type minor_unification_times_v3 = clasetStep.minor_unification_times_v3
  type alternative_pull_times =
    {completed_pulls : int,
     failed_pulls : int,
     interrupted_pulls : int,
     (* Two O(1) elapsed snapshots bracket each started pull.  Statistics
        reads occur only during the three terminal report aggregations. *)
     classical_elapsed_snapshots : int,
     sequence_statistics_reads : int,
     completed_pull_time : Time.time,
     failed_pull_time : Time.time,
     interrupted_pull_time : Time.time,
     alternative_pull_time : Time.time,
     alternative_residual_time : Time.time,
     max_completed_pull_time : Time.time,
     max_failed_pull_time : Time.time,
     max_interrupted_pull_time : Time.time,
     max_alternative_pull_time : Time.time}
  type timed_detailed_measured_result_v3 =
    {base : timed_detailed_measured_result_v2,
     minor_unification_times : minor_unification_times_v3,
     alternative_pull_times : alternative_pull_times}

  (* Timed-v3 is additive.  Every AlternativeEnumeration Enter that can
     produce a report has exactly one yielded/completed, exhausted/failed or
     interrupted outcome.  A caught operational exception is failed too.
     Pull times are exclusive of nested classical intervals;
     their sum plus alternative_residual_time equals the v2 Alternative
     total.  Observer/stop/clock exceptions retain identity, and operational
     failure/interruption closes timing ownership without fabricating Exit. *)
  val reconstructWithMeasuredTimedDetailedV3 :
    {clock : unit -> Time.time,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> timed_detailed_measured_result_v3
  val reconstructWithMeasuredTimedDetailedV3UsingKernel :
    {clock : unit -> Time.time,
     kernel_replay :
       clasetReplay.grounded_script -> goal -> goal list * validation,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> timed_detailed_measured_result_v3
  val reconstructWithMeasuredTimedDetailedV3UsingTransition :
    {clock : unit -> Time.time,
     kernel_replay :
       clasetReplay.grounded_script -> goal -> goal list * validation,
     transition :
       clasetStep.timed_rule_sequence_v3 -> clasetStep.timed_rule_pull_v3,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> timed_detailed_measured_result_v3
  val reconstructMeasuredTimedDetailedV3 :
    {clock : unit -> Time.time,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    goal -> proof -> timed_detailed_measured_result_v3

  (* Timed-v4 is the additive bounded-summary adapter.  It uses the same
     operation-honest phase scopes and per-pull accounting as v3, but never
     retains, reverses, concatenates or scans fine phase traces.  One shared
     O(1) classical summary replaces the retained sequence list. *)
  type minor_unification_times_v4 = clasetStep.minor_unification_times_v4
  type alternative_pull_times_v4 =
    {completed_pulls : int,
     failed_pulls : int,
     interrupted_pulls : int,
     classical_elapsed_snapshots : int,
     sequence_statistics_reads : int,
     summary_statistics_reads : int,
     retained_trace_allocations : int,
     completed_pull_time : Time.time,
     failed_pull_time : Time.time,
     interrupted_pull_time : Time.time,
     alternative_pull_time : Time.time,
     alternative_residual_time : Time.time,
     max_completed_pull_time : Time.time,
     max_failed_pull_time : Time.time,
     max_interrupted_pull_time : Time.time,
     max_alternative_pull_time : Time.time}
  type timed_detailed_measured_result_v4 =
    {base : timed_detailed_measured_result_v2,
     minor_unification_times : minor_unification_times_v4,
     alternative_pull_times : alternative_pull_times_v4}
  val reconstructWithMeasuredTimedDetailedV4 :
    {clock : unit -> Time.time,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> timed_detailed_measured_result_v4
  val reconstructWithMeasuredTimedDetailedV4UsingKernel :
    {clock : unit -> Time.time,
     kernel_replay :
       clasetReplay.grounded_script -> goal -> goal list * validation,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> timed_detailed_measured_result_v4
  val reconstructWithMeasuredTimedDetailedV4UsingTransition :
    {clock : unit -> Time.time,
     kernel_replay :
       clasetReplay.grounded_script -> goal -> goal list * validation,
     transition :
       clasetStep.timed_rule_sequence_v4 -> clasetStep.timed_rule_pull_v4,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    claset -> goal -> proof -> timed_detailed_measured_result_v4
  val reconstructMeasuredTimedDetailedV4 :
    {clock : unit -> Time.time,
     observe : (observation -> unit) option,
     observe_stored_rule :
       (stored_rule_observation -> unit) option,
     stop : unit -> bool} ->
    goal -> proof -> timed_detailed_measured_result_v4

  (* Search continuations reject failed reconstruction with
     blastSearch.PROOF_FAILED, so the tableau resumes at its choice stack. *)
  val searchGoal :
    claset -> int -> goal -> (proof * (goal list * validation)) option
  val deepenGoal :
    claset -> goal -> (proof * (goal list * validation)) option

  val DEPTH_TAC : claset -> int -> tactic
  val DEEPEN_TAC : claset -> tactic
end
