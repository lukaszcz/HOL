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

  (* Search continuations reject failed reconstruction with
     blastSearch.PROOF_FAILED, so the tableau resumes at its choice stack. *)
  val searchGoal :
    claset -> int -> goal -> (proof * (goal list * validation)) option
  val deepenGoal :
    claset -> goal -> (proof * (goal list * validation)) option

  val DEPTH_TAC : claset -> int -> tactic
  val DEEPEN_TAC : claset -> tactic
end
