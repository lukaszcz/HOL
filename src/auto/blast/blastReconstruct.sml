structure blastReconstruct :> blastReconstruct =
struct

open Abbrev HolKernel

type claset = clasetLib.claset
type proof = blastSearch.proof

fun first_result sequence =
  case seq.cases sequence of
      SOME (result, _) => result
    | NONE =>
        raise mk_HOL_ERR "blastReconstruct" "first_result"
          "the recorded step does not apply"

fun apply step node = seq.map #2 (step (node, 1))

fun move_children count node =
  let
    fun move position current =
      if position > count then current
      else
        move (position + 1)
          (#2
            (first_result
              (clasetStep.blast_move_back_step 1
                (current, position))))
  in
    move 1 node
  end

(* Static stored-rule prefixes may already account for an explicit tableau
   introduction.  Keep the zero-cost fallback for genuine tableau-only
   pseudo-steps, without adding another stored-rule replay action. *)
fun apply_pseudo step node =
  seq.append (apply step node) (seq.result node)

fun apply_rule cs duplicate major rule node =
  case #origin rule of
      blastRule.ImpIntro =>
        apply_pseudo clasetStep.blast_disch_step node
    | blastRule.AllIntro => apply_pseudo clasetStep.blast_gen_step node
    | blastRule.Stored {is_elim, theorem} =>
        let
          val replay_theorem =
            if duplicate andalso is_elim then
              clasetRules.REV_DUP_ELIM_RULE theorem
            else theorem
          val old_count = length (clasetGoal.goals node)
          val transitions =
            apply
              (clasetStep.blast_rule_step_at cs
                {theorem = replay_theorem, elim = is_elim,
                 major = major}) node

          fun finish next =
            let
              val child_count =
                length (clasetGoal.goals next) - old_count + 1
            in
              if duplicate andalso is_elim then
                move_children child_count next
              else next
            end
        in
          seq.mapPartial (total finish) transitions
        end

fun execute cs step node =
  case step of
      blastSearch.HypSubst {equality} =>
        apply (clasetStep.blast_hyp_subst_step_at equality) node
    | blastSearch.CloseAssume {assumption} =>
        apply (clasetStep.blast_assumption_step_at assumption) node
    | blastSearch.CloseContradiction positions =>
        apply (clasetStep.blast_contradiction_step_at positions) node
    | blastSearch.SafeRule {rule, major, ...} =>
        apply_rule cs false major rule node
    | blastSearch.DeferGoal =>
        apply clasetStep.blast_ccontr_step node
    | blastSearch.UnsafeRule {rule, duplicate, major, ...} =>
        apply_rule cs duplicate major rule node

(* Every ambiguous script step selects its exact typed assumption occurrence.
   Pull the resulting typed engine sequence lazily, but never fall back to a
   different assumption or rule position.  Only a completely grounded,
   kernel-valid replay is accepted; failure rejects this tableau through the
   search continuation's PROOF_FAILED hook. *)
fun perform_with cs goal ({script, ...} : proof) =
  let
    fun finish final =
      let
        val _ =
          if null (clasetGoal.goals final) then ()
          else
            raise mk_HOL_ERR "blastReconstruct" "finish"
              "the recorded script leaves open engine goals"
        val grounded =
          clasetReplay.ground (clasetGoal.store final)
            (clasetGoal.replay final)
        val result as (residuals, _) =
          Tactical.VALID (clasetReplay.REPLAY_TAC grounded) goal
        val _ =
          if null residuals then ()
          else
            raise mk_HOL_ERR "blastReconstruct" "finish"
              "kernel replay leaves open goals"
      in
        result
      end

    fun replay [] node = total finish node
      | replay (step :: rest) node =
          let
            fun alternatives sequence =
              case seq.cases sequence of
                  NONE => NONE
                | SOME (next, nodes) =>
                    (case replay rest next of
                         NONE => alternatives nodes
                       | result => result)
          in
            alternatives (execute cs step node)
          end
          handle HOL_ERR _ => NONE
  in
    case replay script (clasetGoal.from_goal goal) of
        SOME result => result
      | NONE =>
          raise mk_HOL_ERR "blastReconstruct" "perform_with"
            "the recorded tableau has no kernel-valid replay"
  end

fun reconstructWith cs goal proof =
  total (perform_with cs goal) proof

fun reconstruct goal proof =
  reconstructWith clasetLib.empty_cs goal proof

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

type stored_rule_observation =
  {script_position : int,
   step_kind : step_kind,
   duplicate : bool,
   rule : clasetStep.measured_rule_observation}

(* TypedStep covers lazy-sequence setup.  AlternativeEnumeration covers
   seq.cases and hence any lazy engine-transition forcing needed to expose a
   node.  StoredRuleTransition begins only after such a node is yielded and
   covers child counting plus optional duplicate movement.  Brackets emit an
   Exit only on a normal return, so exception/backtracking paths can leave an
   unmatched Enter.  See the signature for the complete phase contract. *)

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

type minor_unification_times_v3 = clasetStep.minor_unification_times_v3

type alternative_pull_times =
  {completed_pulls : int,
   failed_pulls : int,
   interrupted_pulls : int,
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

datatype detailed_timing =
    DetailedUntimed
  | DetailedTimed of (unit -> Time.time)
  | DetailedTimedV2 of
      {clock : unit -> Time.time,
       kernel_replay :
         clasetReplay.grounded_script -> goal -> goal list * validation}

datatype detailed_timing_v3 =
    DetailedTimedModeV3 of
      {clock : unit -> Time.time,
       kernel_replay :
         clasetReplay.grounded_script -> goal -> goal list * validation,
       transition :
         clasetStep.timed_rule_sequence_v3 ->
           clasetStep.timed_rule_pull_v3}
  | DetailedBoundedModeV4 of
      {clock : unit -> Time.time,
       kernel_replay :
         clasetReplay.grounded_script -> goal -> goal list * validation,
       transition :
         clasetStep.timed_rule_sequence_v4 ->
           clasetStep.timed_rule_pull_v4}

datatype detailed_diagnostic_result =
    UntimedDetailedResult of detailed_measured_result
  | TimedDetailedResult of timed_detailed_measured_result
  | TimedDetailedResultV2 of timed_detailed_measured_result_v2

datatype detailed_diagnostic_result_v3 =
    TimedDetailedResultV3 of timed_detailed_measured_result_v3
  | TimedDetailedResultV4 of timed_detailed_measured_result_v4

(* Measured reconstruction deliberately duplicates the small legacy worker
   above.  The ordinary entry points therefore retain their original call
   graph, allocation profile, and exception/control behavior. *)
fun reconstructWithMeasured {observe, stop} cs goal
      ({script, ...} : proof) =
  let
    exception INTERRUPTED
    exception CALLBACK of exn

    val current_phase = ref (NONE : observation option)
    val cooperative_checkpoints = ref 0
    val phase_entries = ref 0
    val phase_exits = ref 0
    val replay_recursions = ref 0
    val alternative_pulls = ref 0
    val typed_steps = ref 0
    val hyp_subst_steps = ref 0
    val close_assume_steps = ref 0
    val close_contradiction_steps = ref 0
    val safe_rule_steps = ref 0
    val defer_goal_steps = ref 0
    val unsafe_rule_steps = ref 0
    val stored_rule_setups = ref 0
    val stored_rule_transitions = ref 0
    val duplicate_child_moves = ref 0
    val finish_open_goal_checks = ref 0
    val grounding_attempts = ref 0
    val kernel_replay_attempts = ref 0
    val finish_residual_goal_checks = ref 0

    fun increment counter = counter := !counter + 1

    fun count_entry phase =
      (increment phase_entries;
       case phase of
           ReplayRecursion => increment replay_recursions
         | AlternativeEnumeration => increment alternative_pulls
         | TypedStep kind =>
             (increment typed_steps;
              case kind of
                  HypSubstStep => increment hyp_subst_steps
                | CloseAssumeStep => increment close_assume_steps
                | CloseContradictionStep =>
                    increment close_contradiction_steps
                | SafeRuleStep => increment safe_rule_steps
                | DeferGoalStep => increment defer_goal_steps
                | UnsafeRuleStep => increment unsafe_rule_steps)
         | StoredRuleSetup => increment stored_rule_setups
         | StoredRuleTransition => increment stored_rule_transitions
         | DuplicateChildMove => increment duplicate_child_moves
         | FinishOpenGoals => increment finish_open_goal_checks
         | GroundReplay => increment grounding_attempts
         | KernelReplay => increment kernel_replay_attempts
         | FinishResidualGoals =>
             increment finish_residual_goal_checks)

    fun invoke callback argument =
      callback argument handle error => raise CALLBACK error

    fun checkpoint boundary phase =
      let
        val observation = {boundary = boundary, phase = phase}
        val _ = current_phase := SOME observation
        val _ =
          (case boundary of
               Enter => count_entry phase
             | Exit => increment phase_exits)
        val _ =
          case observe of
              NONE => ()
            | SOME observer => invoke observer observation
        val _ = increment cooperative_checkpoints
      in
        if invoke stop () then raise INTERRUPTED else ()
      end

    fun bracket phase operation argument =
      let
        val _ = checkpoint Enter phase
        val result = operation argument
        val _ = checkpoint Exit phase
      in
        result
      end

    (* Lib.total is the legacy replay policy: it catches every exception
       except the runtime Interrupt.  Preserve that policy while allowing
       diagnostic control flow and callback exceptions to cross the same
       internal boundaries. *)
    fun total_m operation argument =
      SOME (operation argument)
      handle INTERRUPTED => raise INTERRUPTED
           | CALLBACK error => raise CALLBACK error
           | Interrupt => raise Interrupt
           | _ => NONE

    fun first_result_m phase sequence =
      case bracket phase seq.cases sequence of
          SOME (result, _) => result
        | NONE =>
            raise mk_HOL_ERR "blastReconstruct" "first_result_m"
              "the recorded step does not apply"

    fun apply_m kind step node =
      bracket (TypedStep kind)
        (fn () => seq.map #2 (step (node, 1))) ()

    fun move_children_m count node =
      let
        fun move position current =
          if position > count then current
          else
            move (position + 1)
              (#2
                (first_result_m DuplicateChildMove
                  (clasetStep.blast_move_back_step 1
                    (current, position))))
      in
        move 1 node
      end

    fun apply_pseudo_m kind step node =
      seq.append (apply_m kind step node) (seq.result node)

    fun apply_rule_m kind duplicate major rule node =
      case #origin rule of
          blastRule.ImpIntro =>
            apply_pseudo_m kind clasetStep.blast_disch_step node
        | blastRule.AllIntro =>
            apply_pseudo_m kind clasetStep.blast_gen_step node
        | blastRule.Stored {is_elim, theorem} =>
            bracket StoredRuleSetup
              (fn () =>
                let
                  val replay_theorem =
                    if duplicate andalso is_elim then
                      clasetRules.REV_DUP_ELIM_RULE theorem
                    else theorem
                  val old_count = length (clasetGoal.goals node)
                  val transitions =
                    apply_m kind
                      (clasetStep.blast_rule_step_at cs
                        {theorem = replay_theorem, elim = is_elim,
                         major = major}) node

                  fun finish next =
                    bracket StoredRuleTransition
                      (fn () =>
                        let
                          val child_count =
                            length (clasetGoal.goals next) - old_count + 1
                        in
                          if duplicate andalso is_elim then
                            move_children_m child_count next
                          else next
                        end) ()
                in
                  seq.mapPartial (total_m finish) transitions
                end) ()

    fun execute_m step node =
      case step of
          blastSearch.HypSubst {equality} =>
            apply_m HypSubstStep
              (clasetStep.blast_hyp_subst_step_at equality) node
        | blastSearch.CloseAssume {assumption} =>
            apply_m CloseAssumeStep
              (clasetStep.blast_assumption_step_at assumption) node
        | blastSearch.CloseContradiction positions =>
            apply_m CloseContradictionStep
              (clasetStep.blast_contradiction_step_at positions) node
        | blastSearch.SafeRule {rule, major, ...} =>
            apply_rule_m SafeRuleStep false major rule node
        | blastSearch.DeferGoal =>
            apply_m DeferGoalStep clasetStep.blast_ccontr_step node
        | blastSearch.UnsafeRule {rule, duplicate, major, ...} =>
            apply_rule_m UnsafeRuleStep duplicate major rule node

    fun finish final =
      let
        val _ =
          bracket FinishOpenGoals
            (fn () =>
              if null (clasetGoal.goals final) then ()
              else
                raise mk_HOL_ERR "blastReconstruct" "finish"
                  "the recorded script leaves open engine goals") ()
        val grounded =
          bracket GroundReplay
            (fn () =>
              clasetReplay.ground (clasetGoal.store final)
                (clasetGoal.replay final)) ()
        val result as (residuals, _) =
          bracket KernelReplay
            (fn () =>
              Tactical.VALID (clasetReplay.REPLAY_TAC grounded) goal) ()
        val _ =
          bracket FinishResidualGoals
            (fn () =>
              if null residuals then ()
              else
                raise mk_HOL_ERR "blastReconstruct" "finish"
                  "kernel replay leaves open goals") ()
      in
        result
      end

    fun replay [] node =
          bracket ReplayRecursion (fn () => total_m finish node) ()
      | replay (step :: rest) node =
          (bracket ReplayRecursion
            (fn () =>
              let
                fun alternatives sequence =
                  case bracket AlternativeEnumeration seq.cases sequence of
                      NONE => NONE
                    | SOME (next, nodes) =>
                        (case replay rest next of
                             NONE => alternatives nodes
                           | result => result)
              in
                alternatives (execute_m step node)
              end) ()
           handle HOL_ERR _ => NONE)

    fun statistics () : statistics =
      {cooperative_checkpoints = !cooperative_checkpoints,
       phase_entries = !phase_entries,
       phase_exits = !phase_exits,
       replay_recursions = !replay_recursions,
       alternative_pulls = !alternative_pulls,
       typed_steps = !typed_steps,
       hyp_subst_steps = !hyp_subst_steps,
       close_assume_steps = !close_assume_steps,
       close_contradiction_steps = !close_contradiction_steps,
       safe_rule_steps = !safe_rule_steps,
       defer_goal_steps = !defer_goal_steps,
       unsafe_rule_steps = !unsafe_rule_steps,
       stored_rule_setups = !stored_rule_setups,
       stored_rule_transitions = !stored_rule_transitions,
       duplicate_child_moves = !duplicate_child_moves,
       finish_open_goal_checks = !finish_open_goal_checks,
       grounding_attempts = !grounding_attempts,
       kernel_replay_attempts = !kernel_replay_attempts,
       finish_residual_goal_checks = !finish_residual_goal_checks}

    fun report completion result : measured_result =
      {completion = completion,
       current_phase = !current_phase,
       result = result,
       statistics = statistics ()}

    fun perform () =
      case replay script (clasetGoal.from_goal goal) of
          SOME result => result
        | NONE =>
            raise mk_HOL_ERR "blastReconstruct"
              "reconstructWithMeasured"
              "the recorded tableau has no kernel-valid replay"
  in
    ((report Completed (SOME (perform ()))
      handle INTERRUPTED => report Interrupted NONE
           | CALLBACK error => raise CALLBACK error
           | Interrupt => raise Interrupt
           | _ => report Completed NONE)
     handle CALLBACK error => raise error)
  end


fun reconstructWithMeasuredDetailedModeV3
      timing_mode
      {observe, observe_stored_rule, stop} cs goal
      ({script, ...} : proof) =
  let
    exception INTERRUPTED
    exception CALLBACK of exn

    val current_phase = ref (NONE : observation option)
    val current_stored_rule =
      ref (NONE : stored_rule_observation option)
    val cooperative_checkpoints = ref 0
    val phase_entries = ref 0
    val phase_exits = ref 0
    val replay_recursions = ref 0
    val alternative_pulls = ref 0
    val typed_steps = ref 0
    val hyp_subst_steps = ref 0
    val close_assume_steps = ref 0
    val close_contradiction_steps = ref 0
    val safe_rule_steps = ref 0
    val defer_goal_steps = ref 0
    val unsafe_rule_steps = ref 0
    val stored_rule_setups = ref 0
    val stored_rule_transitions = ref 0
    val duplicate_child_moves = ref 0
    val finish_open_goal_checks = ref 0
    val grounding_attempts = ref 0
    val kernel_replay_attempts = ref 0
    val finish_residual_goal_checks = ref 0
    val stored_rule_checkpoints = ref 0
    val stored_rule_phase_entries = ref 0
    val stored_rule_phase_exits = ref 0
    val stored_rule_attempt_selections = ref 0
    val stored_rule_freshening_setups = ref 0
    val stored_rule_minor_unifications = ref 0
    val stored_rule_major_unifications = ref 0
    val stored_rule_instantiations = ref 0
    val stored_rule_child_store_constructions = ref 0
    val stored_rule_direct_result_constructions = ref 0
    val stored_rule_lazy_yields = ref 0
    val stored_rule_direct_child_replacements = ref 0
    val stored_rule_replay_record_constructions = ref 0
    val stored_rule_record_insertions = ref 0
    val stored_rule_intro_attempts = ref 0
    val stored_rule_elim_attempts = ref 0
    val stored_rule_safe_attempts = ref 0
    val stored_rule_unsafe_attempts = ref 0
    val timed_rule_sequences_v3 =
      ref ([] : clasetStep.timed_rule_sequence_v3 list)
    val v3_classical_elapsed = ref Time.zeroTime
    val clock =
      case timing_mode of
          DetailedTimedModeV3 {clock = selected, ...} => selected
        | DetailedBoundedModeV4 {clock = selected, ...} => selected
    val kernel_replay =
      case timing_mode of
          DetailedTimedModeV3 {kernel_replay = selected, ...} => selected
        | DetailedBoundedModeV4 {kernel_replay = selected, ...} => selected
    val bounded_summary_v4 =
      case timing_mode of
          DetailedTimedModeV3 _ => NONE
        | DetailedBoundedModeV4 _ =>
            SOME
              (clasetStep.new_timed_rule_summary_v4
                {clock = fn () => clock (),
                 classical_elapsed =
                   fn elapsed =>
                     v3_classical_elapsed :=
                       Time.+ (!v3_classical_elapsed, elapsed)})
    datatype outer_owner =
        AlternativeOwner
      | ReplayOwner
      | OtherOwner
    val outer_last = ref (NONE : Time.time option)
    val outer_stack = ref ([] : outer_owner list)
    val raw_alternative_time = ref Time.zeroTime
    val raw_replay_time = ref Time.zeroTime
    val raw_other_time = ref Time.zeroTime
    val completed_alternative_pulls = ref 0
    val failed_alternative_pulls = ref 0
    val interrupted_alternative_pulls = ref 0
    val alternative_classical_snapshots = ref 0
    val completed_alternative_pull_time = ref Time.zeroTime
    val failed_alternative_pull_time = ref Time.zeroTime
    val interrupted_alternative_pull_time = ref Time.zeroTime
    val max_completed_alternative_pull_time = ref Time.zeroTime
    val max_failed_alternative_pull_time = ref Time.zeroTime
    val max_interrupted_alternative_pull_time = ref Time.zeroTime
    val max_alternative_pull_time = ref Time.zeroTime

    fun increment counter = counter := !counter + 1

    fun count_entry phase =
      (increment phase_entries;
       case phase of
           ReplayRecursion => increment replay_recursions
         | AlternativeEnumeration => increment alternative_pulls
         | TypedStep kind =>
             (increment typed_steps;
              case kind of
                  HypSubstStep => increment hyp_subst_steps
                | CloseAssumeStep => increment close_assume_steps
                | CloseContradictionStep =>
                    increment close_contradiction_steps
                | SafeRuleStep => increment safe_rule_steps
                | DeferGoalStep => increment defer_goal_steps
                | UnsafeRuleStep => increment unsafe_rule_steps)
         | StoredRuleSetup => increment stored_rule_setups
         | StoredRuleTransition => increment stored_rule_transitions
         | DuplicateChildMove => increment duplicate_child_moves
         | FinishOpenGoals => increment finish_open_goal_checks
         | GroundReplay => increment grounding_attempts
         | KernelReplay => increment kernel_replay_attempts
         | FinishResidualGoals =>
             increment finish_residual_goal_checks)

    fun invoke callback argument =
      callback argument handle error => raise CALLBACK error

    fun v3_transition sequence =
      case timing_mode of
          DetailedTimedModeV3 {transition, ...} => transition sequence
        | DetailedBoundedModeV4 _ =>
            raise mk_HOL_ERR "blastReconstruct" "v3_transition"
              "internal detailed diagnostic mode mismatch"

    fun v4_transition sequence =
      case timing_mode of
          DetailedBoundedModeV4 {transition, ...} => transition sequence
        | DetailedTimedModeV3 _ =>
            raise mk_HOL_ERR "blastReconstruct" "v4_transition"
              "internal detailed diagnostic mode mismatch"

    val make_timed_rule_v3 =
      clasetStep.blast_rule_step_timed_v3_with_sink_at
    val make_timed_rule_v4 =
      clasetStep.blast_rule_step_timed_v4_with_summary_at

    fun owner_of AlternativeEnumeration = AlternativeOwner
      | owner_of ReplayRecursion = ReplayOwner
      | owner_of _ = OtherOwner

    fun add_elapsed elapsed reference =
      reference := Time.+ (!reference, elapsed)

    fun maximum_elapsed elapsed reference =
      if Time.< (!reference, elapsed) then reference := elapsed else ()

    fun account_outer finished =
      case !outer_last of
          NONE => outer_last := SOME finished
        | SOME started =>
            let
              val _ =
                if Time.< (finished, started) then
                  raise CALLBACK
                    (mk_HOL_ERR "blastReconstruct" "account_outer"
                      "the timed diagnostic clock moved backwards")
                else ()
              val elapsed = Time.- (finished, started)
              val _ = outer_last := SOME finished
            in
              case !outer_stack of
                  AlternativeOwner :: _ =>
                    add_elapsed elapsed raw_alternative_time
                | ReplayOwner :: _ => add_elapsed elapsed raw_replay_time
                | OtherOwner :: _ => add_elapsed elapsed raw_other_time
                | [] => add_elapsed elapsed raw_other_time
            end

    fun outer_enter phase =
      (account_outer (invoke clock ());
       outer_stack := owner_of phase :: !outer_stack)

    (* This stack is timing state, not observer state.  In particular, an
       operational failure deliberately has no fabricated Exit observation,
       but it must still close its exclusive interval and restore exactly the
       owner stack seen on entry before replay catches the failure. *)
    fun outer_restore saved =
      ((account_outer (invoke clock ()); outer_stack := saved)
       handle error => (outer_stack := saved; raise error))

    fun count_stored_rule_entry step_kind
          (rule : clasetStep.measured_rule_observation) =
      let
        val _ = increment stored_rule_phase_entries
        val _ =
          case #phase rule of
              clasetStep.AttemptSelection =>
                (increment stored_rule_attempt_selections;
                 case #rule_kind rule of
                     clasetStep.IntroRule =>
                       increment stored_rule_intro_attempts
                   | clasetStep.ElimRule =>
                       increment stored_rule_elim_attempts;
                 case step_kind of
                     SafeRuleStep => increment stored_rule_safe_attempts
                   | UnsafeRuleStep =>
                       increment stored_rule_unsafe_attempts
                   | _ =>
                       raise mk_HOL_ERR "blastReconstruct"
                         "count_stored_rule_entry"
                         "a stored rule has a non-rule script kind")
            | clasetStep.FresheningSetup =>
                increment stored_rule_freshening_setups
            | clasetStep.MinorUnification =>
                increment stored_rule_minor_unifications
            | clasetStep.EliminationMajorUnification =>
                increment stored_rule_major_unifications
            | clasetStep.RuleInstantiation =>
                increment stored_rule_instantiations
            | clasetStep.ChildStoreConstruction =>
                increment stored_rule_child_store_constructions
            | clasetStep.DirectResultConstruction =>
                increment stored_rule_direct_result_constructions
            | clasetStep.LazyResultYield =>
                increment stored_rule_lazy_yields
            | clasetStep.DirectChildReplacement =>
                increment stored_rule_direct_child_replacements
            | clasetStep.ReplayRecordConstruction =>
                increment stored_rule_replay_record_constructions
            | clasetStep.RecordInsertion =>
                increment stored_rule_record_insertions
      in
        ()
      end

    fun observe_stored script_position step_kind duplicate rule =
      let
        val combined : stored_rule_observation =
          {script_position = script_position,
           step_kind = step_kind, duplicate = duplicate, rule = rule}
        val _ = current_stored_rule := SOME combined
        val _ =
          case #boundary rule of
              clasetStep.RuleEnter =>
                count_stored_rule_entry step_kind rule
            | clasetStep.RuleExit =>
                increment stored_rule_phase_exits
      in
        case observe_stored_rule of
            NONE => ()
          | SOME observer => invoke observer combined
      end

    fun stop_stored_rule () =
      (increment stored_rule_checkpoints;
       increment cooperative_checkpoints;
       invoke stop ())

    fun checkpoint boundary phase =
      let
        val observation = {boundary = boundary, phase = phase}
        val _ = current_phase := SOME observation
        val _ =
          (case boundary of
               Enter => count_entry phase
             | Exit => increment phase_exits)
        val _ =
          case observe of
              NONE => ()
            | SOME observer => invoke observer observation
        val _ = increment cooperative_checkpoints
      in
        if invoke stop () then raise INTERRUPTED else ()
      end

    datatype alternative_outcome =
        AlternativeCompleted
      | AlternativeFailed
      | AlternativeInterrupted

    fun record_alternative outcome elapsed =
      let
        val _ = maximum_elapsed elapsed max_alternative_pull_time
      in
        case outcome of
            AlternativeCompleted =>
              (increment completed_alternative_pulls;
               add_elapsed elapsed completed_alternative_pull_time;
               maximum_elapsed elapsed
                 max_completed_alternative_pull_time)
          | AlternativeFailed =>
              (increment failed_alternative_pulls;
               add_elapsed elapsed failed_alternative_pull_time;
               maximum_elapsed elapsed max_failed_alternative_pull_time)
          | AlternativeInterrupted =>
              (increment interrupted_alternative_pulls;
               add_elapsed elapsed interrupted_alternative_pull_time;
               maximum_elapsed elapsed
                 max_interrupted_alternative_pull_time)
      end

    fun alternative_start () =
      (increment alternative_classical_snapshots;
       (!raw_alternative_time, !v3_classical_elapsed))

    fun finish_alternative (raw_started, classical_started) outcome =
      let
        val _ = increment alternative_classical_snapshots
        val raw_finished = !raw_alternative_time
        val classical_finished = !v3_classical_elapsed
        val raw_elapsed =
          if Time.< (raw_finished, raw_started) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "finish_alternative"
                "AlternativeEnumeration raw time moved backwards")
          else Time.- (raw_finished, raw_started)
        val classical_elapsed =
          if Time.< (classical_finished, classical_started) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "finish_alternative"
                "AlternativeEnumeration classical time moved backwards")
          else Time.- (classical_finished, classical_started)
        val exclusive =
          if Time.< (raw_elapsed, classical_elapsed) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "finish_alternative"
                "classical time exceeds its enclosing pull")
          else Time.- (raw_elapsed, classical_elapsed)
      in
        record_alternative outcome exclusive
      end

    fun bracket phase operation argument =
      let
        val _ = checkpoint Enter phase
        val saved_outer_stack = !outer_stack
        val _ = outer_enter phase
        val result =
          operation argument
          handle error =>
            (outer_restore saved_outer_stack; raise error)
        val _ = outer_restore saved_outer_stack
        val _ = checkpoint Exit phase
      in
        result
      end

    fun alternative_bracket_v3 operation argument =
      let
        val _ =
          checkpoint Enter AlternativeEnumeration
          handle INTERRUPTED =>
            (record_alternative AlternativeInterrupted Time.zeroTime;
             raise INTERRUPTED)
        val saved_outer_stack = !outer_stack
        val alternative = alternative_start ()
        val _ = outer_enter AlternativeEnumeration
        val result =
          operation argument
          handle error =>
            (outer_restore saved_outer_stack;
             (case error of
                  CALLBACK _ => ()
                | INTERRUPTED =>
                    finish_alternative alternative AlternativeInterrupted
                | Interrupt =>
                    finish_alternative alternative AlternativeInterrupted
                | _ => finish_alternative alternative AlternativeFailed);
             raise error)
        val _ = outer_restore saved_outer_stack
        val _ =
          checkpoint Exit AlternativeEnumeration
          handle INTERRUPTED =>
            (finish_alternative alternative AlternativeInterrupted;
             raise INTERRUPTED)
        val _ =
          finish_alternative alternative
            (case result of
                 NONE => AlternativeFailed
               | SOME _ => AlternativeCompleted)
      in
        result
      end

    (* Lib.total is the legacy replay policy: it catches every exception
       except the runtime Interrupt.  Preserve that policy while allowing
       diagnostic control flow and callback exceptions to cross the same
       internal boundaries. *)
    fun total_m operation argument =
      SOME (operation argument)
      handle INTERRUPTED => raise INTERRUPTED
           | CALLBACK error => raise CALLBACK error
           | Interrupt => raise Interrupt
           | _ => NONE

    fun first_result_m phase sequence =
      case bracket phase seq.cases sequence of
          SOME (result, _) => result
        | NONE =>
            raise mk_HOL_ERR "blastReconstruct" "first_result_m"
              "the recorded step does not apply"

    fun apply_m kind step node =
      bracket (TypedStep kind)
        (fn () => seq.map #2 (step (node, 1))) ()

    fun move_children_m count node =
      let
        fun move position current =
          if position > count then current
          else
            move (position + 1)
              (#2
                (first_result_m DuplicateChildMove
                  (clasetStep.blast_move_back_step 1
                    (current, position))))
      in
        move 1 node
      end

    fun apply_pseudo_m kind step node =
      seq.append (apply_m kind step node) (seq.result node)

    datatype measured_transitions =
        OrdinaryTransitionsV3 of clasetGoal.node seq.seq
      | TimedStoredRuleTransitionsV3 of
          {sequence : clasetStep.timed_rule_sequence_v3,
           old_count : int,
           duplicate : bool,
           is_elim : bool}
      | TimedStoredRuleTransitionsV4 of
          {sequence : clasetStep.timed_rule_sequence_v4,
           old_count : int,
           duplicate : bool,
           is_elim : bool}

    fun apply_rule_m script_position kind duplicate major rule node =
      case #origin rule of
          blastRule.ImpIntro =>
            OrdinaryTransitionsV3
              (apply_pseudo_m kind clasetStep.blast_disch_step node)
        | blastRule.AllIntro =>
            OrdinaryTransitionsV3
              (apply_pseudo_m kind clasetStep.blast_gen_step node)
        | blastRule.Stored {is_elim, theorem} =>
            bracket StoredRuleSetup
              (fn () =>
                let
                  val replay_theorem =
                    if duplicate andalso is_elim then
                      clasetRules.REV_DUP_ELIM_RULE theorem
                    else theorem
                  val old_count = length (clasetGoal.goals node)
                  fun observe_rule observation =
                    observe_stored script_position kind duplicate
                      observation
                in
                  case timing_mode of
                      DetailedTimedModeV3 _ =>
                        let
                          val sequence =
                            bracket (TypedStep kind)
                              (fn () =>
                                make_timed_rule_v3
                                  {classical_elapsed =
                                     fn elapsed =>
                                       add_elapsed elapsed
                                         v3_classical_elapsed,
                                   clock = fn () => invoke clock (),
                                   observe = SOME observe_rule,
                                   stop = stop_stored_rule}
                                  cs
                                  {theorem = replay_theorem,
                                   elim = is_elim, major = major}
                                  (node, 1)) ()
                          val _ =
                            timed_rule_sequences_v3 :=
                              sequence :: !timed_rule_sequences_v3
                        in
                          TimedStoredRuleTransitionsV3
                            {sequence = sequence,
                             old_count = old_count,
                             duplicate = duplicate, is_elim = is_elim}
                        end
                    | DetailedBoundedModeV4 _ =>
                        let
                          val sequence =
                            bracket (TypedStep kind)
                              (fn () =>
                                make_timed_rule_v4
                                  {summary = valOf bounded_summary_v4,
                                   observe = SOME observe_rule,
                                   stop = stop_stored_rule}
                                  cs
                                  {theorem = replay_theorem,
                                   elim = is_elim, major = major}
                                  (node, 1)) ()
                        in
                          TimedStoredRuleTransitionsV4
                            {sequence = sequence,
                             old_count = old_count,
                             duplicate = duplicate, is_elim = is_elim}
                        end
                end) ()

    fun execute_m script_position step node =
      case step of
          blastSearch.HypSubst {equality} =>
            OrdinaryTransitionsV3
              (apply_m HypSubstStep
                (clasetStep.blast_hyp_subst_step_at equality) node)
        | blastSearch.CloseAssume {assumption} =>
            OrdinaryTransitionsV3
              (apply_m CloseAssumeStep
                (clasetStep.blast_assumption_step_at assumption) node)
        | blastSearch.CloseContradiction positions =>
            OrdinaryTransitionsV3
              (apply_m CloseContradictionStep
                (clasetStep.blast_contradiction_step_at positions) node)
        | blastSearch.SafeRule {rule, major, ...} =>
            apply_rule_m script_position SafeRuleStep false major rule node
        | blastSearch.DeferGoal =>
            OrdinaryTransitionsV3
              (apply_m DeferGoalStep clasetStep.blast_ccontr_step node)
        | blastSearch.UnsafeRule {rule, duplicate, major, ...} =>
            apply_rule_m script_position UnsafeRuleStep duplicate major rule
              node

    fun finish_stored_rule old_count duplicate is_elim next =
      bracket StoredRuleTransition
        (fn () =>
          let
            val child_count =
              length (clasetGoal.goals next) - old_count + 1
          in
            if duplicate andalso is_elim then
              move_children_m child_count next
            else next
          end) ()

    fun cases_m transitions =
      case transitions of
          OrdinaryTransitionsV3 sequence =>
            (case alternative_bracket_v3 seq.cases sequence of
                 NONE => NONE
               | SOME (next, tail) =>
                   SOME (next, OrdinaryTransitionsV3 tail))
        | TimedStoredRuleTransitionsV3
            {sequence, old_count, duplicate, is_elim} =>
            alternative_bracket_v3
              (fn () =>
                let
                  fun pull current =
                    case
                      (v3_transition current
                       handle clasetStep.TIMED_RULE_CALLBACK_V3 error =>
                         raise CALLBACK error)
                    of
                        clasetStep.TimedRuleEmptyV3 => NONE
                      | clasetStep.TimedRuleInterruptedV3 =>
                          raise INTERRUPTED
                      | clasetStep.TimedRuleYieldV3
                          ((_, next), tail) =>
                          (case total_m
                            (finish_stored_rule old_count duplicate
                              is_elim) next
                           of
                               SOME finished =>
                                 SOME
                                   (finished,
                                    TimedStoredRuleTransitionsV3
                                      {sequence = tail,
                                       old_count = old_count,
                                       duplicate = duplicate,
                                       is_elim = is_elim})
                             | NONE => pull tail)
                in
                  pull sequence
                end) ()
        | TimedStoredRuleTransitionsV4
            {sequence, old_count, duplicate, is_elim} =>
            alternative_bracket_v3
              (fn () =>
                let
                  fun pull current =
                    case
                      (v4_transition current
                       handle clasetStep.TIMED_RULE_CALLBACK_V4 error =>
                         raise CALLBACK error)
                    of
                        clasetStep.TimedRuleEmptyV4 => NONE
                      | clasetStep.TimedRuleInterruptedV4 =>
                          raise INTERRUPTED
                      | clasetStep.TimedRuleYieldV4
                          ((_, next), tail) =>
                          (case total_m
                            (finish_stored_rule old_count duplicate
                              is_elim) next
                           of
                               SOME finished =>
                                 SOME
                                   (finished,
                                    TimedStoredRuleTransitionsV4
                                      {sequence = tail,
                                       old_count = old_count,
                                       duplicate = duplicate,
                                       is_elim = is_elim})
                             | NONE => pull tail)
                in
                  pull sequence
                end) ()

    fun finish final =
      let
        val _ =
          bracket FinishOpenGoals
            (fn () =>
              if null (clasetGoal.goals final) then ()
              else
                raise mk_HOL_ERR "blastReconstruct" "finish"
                  "the recorded script leaves open engine goals") ()
        val grounded =
          bracket GroundReplay
            (fn () =>
              clasetReplay.ground (clasetGoal.store final)
                (clasetGoal.replay final)) ()
        val result as (residuals, _) =
          bracket KernelReplay
            (fn () => kernel_replay grounded goal) ()
        val _ =
          bracket FinishResidualGoals
            (fn () =>
              if null residuals then ()
              else
                raise mk_HOL_ERR "blastReconstruct" "finish"
                  "kernel replay leaves open goals") ()
      in
        result
      end

    fun replay _ [] node =
          bracket ReplayRecursion (fn () => total_m finish node) ()
      | replay script_position (step :: rest) node =
          (bracket ReplayRecursion
            (fn () =>
              let
                fun alternatives sequence =
                  case cases_m sequence of
                      NONE => NONE
                    | SOME (next, nodes) =>
                        (case replay (script_position + 1) rest next of
                             NONE => alternatives nodes
                           | result => result)
              in
                alternatives (execute_m script_position step node)
              end) ()
           handle HOL_ERR _ => NONE)

    fun statistics () : detailed_statistics =
      {cooperative_checkpoints = !cooperative_checkpoints,
       phase_entries = !phase_entries,
       phase_exits = !phase_exits,
       replay_recursions = !replay_recursions,
       alternative_pulls = !alternative_pulls,
       typed_steps = !typed_steps,
       hyp_subst_steps = !hyp_subst_steps,
       close_assume_steps = !close_assume_steps,
       close_contradiction_steps = !close_contradiction_steps,
       safe_rule_steps = !safe_rule_steps,
       defer_goal_steps = !defer_goal_steps,
       unsafe_rule_steps = !unsafe_rule_steps,
       stored_rule_setups = !stored_rule_setups,
       stored_rule_transitions = !stored_rule_transitions,
       duplicate_child_moves = !duplicate_child_moves,
       finish_open_goal_checks = !finish_open_goal_checks,
       grounding_attempts = !grounding_attempts,
       kernel_replay_attempts = !kernel_replay_attempts,
       finish_residual_goal_checks = !finish_residual_goal_checks,
       stored_rule_checkpoints = !stored_rule_checkpoints,
       stored_rule_phase_entries = !stored_rule_phase_entries,
       stored_rule_phase_exits = !stored_rule_phase_exits,
       stored_rule_attempt_selections =
         !stored_rule_attempt_selections,
       stored_rule_freshening_setups =
         !stored_rule_freshening_setups,
       stored_rule_minor_unifications =
         !stored_rule_minor_unifications,
       stored_rule_major_unifications =
         !stored_rule_major_unifications,
       stored_rule_instantiations = !stored_rule_instantiations,
       stored_rule_child_store_constructions =
         !stored_rule_child_store_constructions,
       stored_rule_direct_result_constructions =
         !stored_rule_direct_result_constructions,
       stored_rule_lazy_yields = !stored_rule_lazy_yields,
       stored_rule_direct_child_replacements =
         !stored_rule_direct_child_replacements,
       stored_rule_replay_record_constructions =
         !stored_rule_replay_record_constructions,
       stored_rule_record_insertions = !stored_rule_record_insertions,
       stored_rule_intro_attempts = !stored_rule_intro_attempts,
       stored_rule_elim_attempts = !stored_rule_elim_attempts,
       stored_rule_safe_attempts = !stored_rule_safe_attempts,
       stored_rule_unsafe_attempts = !stored_rule_unsafe_attempts}

    fun add_time (value, total) = Time.+ (value, total)

    fun classical_times () : classical_phase_times =
      let
        val snapshots =
          map
            (#base o #base o clasetStep.timed_rule_statistics_v3)
            (!timed_rule_sequences_v3)
      in
        {attempt_selection_time =
           List.foldl
             (fn (item, total) =>
               add_time (#attempt_selection_time item, total))
             Time.zeroTime snapshots,
         freshening_setup_time =
           List.foldl
             (fn (item, total) =>
               add_time (#freshening_setup_time item, total))
             Time.zeroTime snapshots,
         minor_unification_time =
           List.foldl
             (fn (item, total) =>
               add_time (#minor_unification_time item, total))
             Time.zeroTime snapshots,
         elimination_major_unification_time =
           List.foldl
             (fn (item, total) =>
               add_time
                 (#elimination_major_unification_time item, total))
             Time.zeroTime snapshots,
         rule_instantiation_time =
           List.foldl
             (fn (item, total) =>
               add_time (#rule_instantiation_time item, total))
             Time.zeroTime snapshots,
         child_store_construction_time =
           List.foldl
             (fn (item, total) =>
               add_time (#child_store_construction_time item, total))
             Time.zeroTime snapshots,
         direct_result_construction_time =
           List.foldl
             (fn (item, total) =>
               add_time (#direct_result_construction_time item, total))
             Time.zeroTime snapshots,
         lazy_result_yield_time =
           List.foldl
             (fn (item, total) =>
               add_time (#lazy_result_yield_time item, total))
             Time.zeroTime snapshots,
         direct_child_replacement_time =
           List.foldl
             (fn (item, total) =>
               add_time (#direct_child_replacement_time item, total))
             Time.zeroTime snapshots,
         replay_record_construction_time =
           List.foldl
             (fn (item, total) =>
               add_time (#replay_record_construction_time item, total))
             Time.zeroTime snapshots,
         record_insertion_time =
           List.foldl
             (fn (item, total) =>
               add_time (#record_insertion_time item, total))
             Time.zeroTime snapshots,
         classical_time =
           List.foldl
             (fn (item, total) =>
               add_time (#classical_time item, total))
             Time.zeroTime snapshots}
      end

    fun maximum_time (left, right) =
      if Time.< (left, right) then right else left

    fun minor_unification_times () : minor_unification_times =
      let
        val snapshots =
          map
            (#minor_unification_times o #base o
             clasetStep.timed_rule_statistics_v3)
            (!timed_rule_sequences_v3)
      in
        {calls = List.foldl (fn (item, n) => #calls item + n) 0 snapshots,
         failures =
           List.foldl (fn (item, n) => #failures item + n) 0 snapshots,
         normalization_setup_time =
           List.foldl
             (fn (item, total) =>
               add_time (#normalization_setup_time item, total))
             Time.zeroTime snapshots,
         traversal_decomposition_binding_time =
           List.foldl
             (fn (item, total) =>
               add_time
                 (#traversal_decomposition_binding_time item, total))
             Time.zeroTime snapshots,
         failure_cleanup_time =
           List.foldl
             (fn (item, total) =>
               add_time (#failure_cleanup_time item, total))
             Time.zeroTime snapshots,
         minor_unification_time =
           List.foldl
             (fn (item, total) =>
               add_time (#minor_unification_time item, total))
             Time.zeroTime snapshots,
         max_normalization_setup_time =
           List.foldl
             (fn (item, current) =>
               maximum_time
                 (#max_normalization_setup_time item, current))
             Time.zeroTime snapshots,
         max_traversal_decomposition_binding_time =
           List.foldl
             (fn (item, current) =>
               maximum_time
                 (#max_traversal_decomposition_binding_time item,
                  current))
             Time.zeroTime snapshots,
         max_failure_cleanup_time =
           List.foldl
             (fn (item, current) =>
               maximum_time (#max_failure_cleanup_time item, current))
             Time.zeroTime snapshots,
         max_minor_unification_time =
           List.foldl
             (fn (item, current) =>
               maximum_time (#max_minor_unification_time item, current))
             Time.zeroTime snapshots}
      end

    fun minor_unification_times_v3 () : minor_unification_times_v3 =
      let
        val snapshots =
          map
            (#minor_unification_times o
             clasetStep.timed_rule_statistics_v3)
            (!timed_rule_sequences_v3)
        fun sum_time field =
          List.foldl
            (fn (item, total) => add_time (field item, total))
            Time.zeroTime snapshots
        fun sum_int field =
          List.foldl (fn (item, total) => field item + total) 0 snapshots
        fun max_time field =
          List.foldl
            (fn (item, current) =>
              maximum_time (field item, current))
            Time.zeroTime snapshots
      in
        {calls = sum_int #calls,
         failures = sum_int #failures,
         normalization_setup_events =
           sum_int #normalization_setup_events,
         persistent_store_lookup_walk_events =
           sum_int #persistent_store_lookup_walk_events,
         structural_decomposition_recursion_events =
           sum_int #structural_decomposition_recursion_events,
         pattern_occurs_allow_decision_events =
           sum_int #pattern_occurs_allow_decision_events,
         persistent_binding_update_events =
           sum_int #persistent_binding_update_events,
         binding_operation_failures =
           sum_int #binding_operation_failures,
         traversal_other_events = sum_int #traversal_other_events,
         operation_phase_trace =
           List.concat
             (map #operation_phase_trace (rev snapshots)),
         normalization_setup_time = sum_time #normalization_setup_time,
         persistent_store_lookup_walk_time =
           sum_time #persistent_store_lookup_walk_time,
         structural_decomposition_recursion_time =
           sum_time #structural_decomposition_recursion_time,
         pattern_occurs_allow_decision_time =
           sum_time #pattern_occurs_allow_decision_time,
         persistent_binding_update_time =
           sum_time #persistent_binding_update_time,
         traversal_other_time = sum_time #traversal_other_time,
         traversal_decomposition_binding_time =
           sum_time #traversal_decomposition_binding_time,
         failure_cleanup_time = sum_time #failure_cleanup_time,
         minor_unification_time = sum_time #minor_unification_time,
         max_normalization_setup_time =
           max_time #max_normalization_setup_time,
         max_persistent_store_lookup_walk_time =
           max_time #max_persistent_store_lookup_walk_time,
         max_structural_decomposition_recursion_time =
           max_time #max_structural_decomposition_recursion_time,
         max_pattern_occurs_allow_decision_time =
           max_time #max_pattern_occurs_allow_decision_time,
         max_persistent_binding_update_time =
           max_time #max_persistent_binding_update_time,
         max_traversal_other_time = max_time #max_traversal_other_time,
         max_traversal_decomposition_binding_time =
           max_time #max_traversal_decomposition_binding_time,
         max_failure_cleanup_time = max_time #max_failure_cleanup_time,
         max_minor_unification_time = max_time #max_minor_unification_time}
      end

    fun read_clock clock = invoke clock ()

    fun elapsed_at started finished =
      if Time.< (finished, started) then
        raise CALLBACK
          (mk_HOL_ERR "blastReconstruct"
            "reconstructWithMeasuredTimedDetailed"
            "the timed diagnostic clock moved backwards")
      else Time.- (finished, started)

    fun make_v3_base_report attempt_wall_time completion result =
      let
        val classical = classical_times ()
        val classical_time = #classical_time classical
        val alternative_time =
          if Time.< (!raw_alternative_time, classical_time) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v3"
                "classical time exceeds enclosing alternative time")
          else Time.- (!raw_alternative_time, classical_time)
        val outer_time =
          Time.+
            (alternative_time,
             Time.+ (!raw_replay_time, !raw_other_time))
        val expected_outer =
          if Time.< (attempt_wall_time, classical_time) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v3"
                "classical time exceeds whole-attempt time")
          else Time.- (attempt_wall_time, classical_time)
        val _ =
          if outer_time = expected_outer then ()
          else
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v3"
                "exclusive reconstruction accounting is inconsistent")
        val base : timed_detailed_measured_result =
          {completion = completion,
           current_phase = !current_phase,
           current_stored_rule = !current_stored_rule,
           result = result,
           statistics = statistics (),
           classical_times = classical,
           attempt_wall_time = attempt_wall_time}
        val outer : outer_reconstruction_times =
          {alternative_enumeration_time = alternative_time,
           replay_continuation_time = !raw_replay_time,
           other_outer_time = !raw_other_time,
           outer_reconstruction_time = outer_time}
      in
        {base = base,
         minor_unification_times = minor_unification_times (),
         outer_reconstruction_times = outer}
      end

    fun timed_report_v3 attempt_wall_time completion result =
      let
        val base =
          make_v3_base_report attempt_wall_time completion result
        val alternative_time =
          #alternative_enumeration_time
            (#outer_reconstruction_times base)
        val pull_time =
          Time.+
            (!completed_alternative_pull_time,
             Time.+
               (!failed_alternative_pull_time,
                !interrupted_alternative_pull_time))
        val residual =
          if Time.< (alternative_time, pull_time) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v3"
                "per-pull time exceeds AlternativeEnumeration time")
          else Time.- (alternative_time, pull_time)
        val pull_count =
          !completed_alternative_pulls + !failed_alternative_pulls +
          !interrupted_alternative_pulls
        val expected_count =
          #alternative_pulls (#statistics (#base base))
        val _ =
          if pull_count = expected_count then ()
          else
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v3"
                "per-pull outcome counts are inconsistent")
        val minor_v3 = minor_unification_times_v3 ()
        val sequence_statistics_reads =
          List.foldl
            (fn (sequence, total) =>
              clasetStep.timed_rule_statistics_reads_v3 sequence + total)
            0 (!timed_rule_sequences_v3)
        val pulls : alternative_pull_times =
          {completed_pulls = !completed_alternative_pulls,
           failed_pulls = !failed_alternative_pulls,
           interrupted_pulls = !interrupted_alternative_pulls,
           classical_elapsed_snapshots =
             !alternative_classical_snapshots,
           sequence_statistics_reads = sequence_statistics_reads,
           completed_pull_time = !completed_alternative_pull_time,
           failed_pull_time = !failed_alternative_pull_time,
           interrupted_pull_time = !interrupted_alternative_pull_time,
           alternative_pull_time = pull_time,
           alternative_residual_time = residual,
           max_completed_pull_time =
             !max_completed_alternative_pull_time,
           max_failed_pull_time = !max_failed_alternative_pull_time,
           max_interrupted_pull_time =
             !max_interrupted_alternative_pull_time,
           max_alternative_pull_time = !max_alternative_pull_time}
      in
        TimedDetailedResultV3
          {base = base,
           minor_unification_times = minor_v3,
           alternative_pull_times = pulls}
      end

    fun timed_report_v4 attempt_wall_time completion result =
      let
        val summary = valOf bounded_summary_v4
        (* This is the sole terminal summary read.  It neither materializes
           nor scans a per-operation or per-sequence trace. *)
        val summary_statistics =
          clasetStep.timed_rule_statistics_v4 summary
        val timed = #base (#base summary_statistics)
        val classical : classical_phase_times =
          {attempt_selection_time = #attempt_selection_time timed,
           freshening_setup_time = #freshening_setup_time timed,
           minor_unification_time = #minor_unification_time timed,
           elimination_major_unification_time =
             #elimination_major_unification_time timed,
           rule_instantiation_time = #rule_instantiation_time timed,
           child_store_construction_time =
             #child_store_construction_time timed,
           direct_result_construction_time =
             #direct_result_construction_time timed,
           lazy_result_yield_time = #lazy_result_yield_time timed,
           direct_child_replacement_time =
             #direct_child_replacement_time timed,
           replay_record_construction_time =
             #replay_record_construction_time timed,
           record_insertion_time = #record_insertion_time timed,
           classical_time = #classical_time timed}
        val classical_time = #classical_time classical
        val alternative_time =
          if Time.< (!raw_alternative_time, classical_time) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v4"
                "classical time exceeds enclosing alternative time")
          else Time.- (!raw_alternative_time, classical_time)
        val outer_time =
          Time.+
            (alternative_time,
             Time.+ (!raw_replay_time, !raw_other_time))
        val expected_outer =
          if Time.< (attempt_wall_time, classical_time) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v4"
                "classical time exceeds whole-attempt time")
          else Time.- (attempt_wall_time, classical_time)
        val _ =
          if outer_time = expected_outer then ()
          else
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v4"
                "exclusive reconstruction accounting is inconsistent")
        val detailed : timed_detailed_measured_result =
          {completion = completion,
           current_phase = !current_phase,
           current_stored_rule = !current_stored_rule,
           result = result,
           statistics = statistics (),
           classical_times = classical,
           attempt_wall_time = attempt_wall_time}
        val outer : outer_reconstruction_times =
          {alternative_enumeration_time = alternative_time,
           replay_continuation_time = !raw_replay_time,
           other_outer_time = !raw_other_time,
           outer_reconstruction_time = outer_time}
        val base : timed_detailed_measured_result_v2 =
          {base = detailed,
           minor_unification_times =
             #minor_unification_times (#base summary_statistics),
           outer_reconstruction_times = outer}
        val pull_time =
          Time.+
            (!completed_alternative_pull_time,
             Time.+
               (!failed_alternative_pull_time,
                !interrupted_alternative_pull_time))
        val residual =
          if Time.< (alternative_time, pull_time) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v4"
                "per-pull time exceeds AlternativeEnumeration time")
          else Time.- (alternative_time, pull_time)
        val pull_count =
          !completed_alternative_pulls + !failed_alternative_pulls +
          !interrupted_alternative_pulls
        val _ =
          if pull_count = #alternative_pulls (#statistics detailed) then ()
          else
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v4"
                "per-pull outcome counts are inconsistent")
        val pulls : alternative_pull_times_v4 =
          {completed_pulls = !completed_alternative_pulls,
           failed_pulls = !failed_alternative_pulls,
           interrupted_pulls = !interrupted_alternative_pulls,
           classical_elapsed_snapshots = !alternative_classical_snapshots,
           sequence_statistics_reads = 0,
           summary_statistics_reads =
             clasetStep.timed_rule_statistics_reads_v4 summary,
           retained_trace_allocations =
             clasetStep.timed_rule_trace_allocations_v4 summary,
           completed_pull_time = !completed_alternative_pull_time,
           failed_pull_time = !failed_alternative_pull_time,
           interrupted_pull_time = !interrupted_alternative_pull_time,
           alternative_pull_time = pull_time,
           alternative_residual_time = residual,
           max_completed_pull_time =
             !max_completed_alternative_pull_time,
           max_failed_pull_time = !max_failed_alternative_pull_time,
           max_interrupted_pull_time =
             !max_interrupted_alternative_pull_time,
           max_alternative_pull_time = !max_alternative_pull_time}
      in
        TimedDetailedResultV4
          {base = base,
           minor_unification_times =
             #minor_unification_times summary_statistics,
           alternative_pull_times = pulls}
      end

    fun perform () =
      case replay 1 script (clasetGoal.from_goal goal) of
          SOME result => result
        | NONE =>
            raise mk_HOL_ERR "blastReconstruct"
              "reconstructWithMeasured"
              "the recorded tableau has no kernel-valid replay"
  in
    ((let
        val started = read_clock clock
        val _ = outer_last := SOME started
        fun terminal_report completion result =
          let
            val finished = read_clock clock
            val _ = account_outer finished
            val attempt_wall_time = elapsed_at started finished
          in
            case timing_mode of
                DetailedTimedModeV3 _ =>
                  timed_report_v3 attempt_wall_time completion result
              | DetailedBoundedModeV4 _ =>
                  timed_report_v4 attempt_wall_time completion result
          end
      in
        (let
           val result = perform ()
         in
           terminal_report Completed (SOME result)
         end
         handle INTERRUPTED => terminal_report Interrupted NONE
              | CALLBACK error => raise CALLBACK error
              | Interrupt => raise Interrupt
              | _ => terminal_report Completed NONE)
      end)
     handle CALLBACK error => raise error)
  end


fun reconstructWithMeasuredDetailedMode timing_mode
      {observe, observe_stored_rule, stop} cs goal
      ({script, ...} : proof) =
  let
    exception INTERRUPTED
    exception CALLBACK of exn

    val current_phase = ref (NONE : observation option)
    val current_stored_rule =
      ref (NONE : stored_rule_observation option)
    val cooperative_checkpoints = ref 0
    val phase_entries = ref 0
    val phase_exits = ref 0
    val replay_recursions = ref 0
    val alternative_pulls = ref 0
    val typed_steps = ref 0
    val hyp_subst_steps = ref 0
    val close_assume_steps = ref 0
    val close_contradiction_steps = ref 0
    val safe_rule_steps = ref 0
    val defer_goal_steps = ref 0
    val unsafe_rule_steps = ref 0
    val stored_rule_setups = ref 0
    val stored_rule_transitions = ref 0
    val duplicate_child_moves = ref 0
    val finish_open_goal_checks = ref 0
    val grounding_attempts = ref 0
    val kernel_replay_attempts = ref 0
    val finish_residual_goal_checks = ref 0
    val stored_rule_checkpoints = ref 0
    val stored_rule_phase_entries = ref 0
    val stored_rule_phase_exits = ref 0
    val stored_rule_attempt_selections = ref 0
    val stored_rule_freshening_setups = ref 0
    val stored_rule_minor_unifications = ref 0
    val stored_rule_major_unifications = ref 0
    val stored_rule_instantiations = ref 0
    val stored_rule_child_store_constructions = ref 0
    val stored_rule_direct_result_constructions = ref 0
    val stored_rule_lazy_yields = ref 0
    val stored_rule_direct_child_replacements = ref 0
    val stored_rule_replay_record_constructions = ref 0
    val stored_rule_record_insertions = ref 0
    val stored_rule_intro_attempts = ref 0
    val stored_rule_elim_attempts = ref 0
    val stored_rule_safe_attempts = ref 0
    val stored_rule_unsafe_attempts = ref 0
    val timed_rule_sequences =
      ref ([] : clasetStep.timed_rule_sequence list)
    val timed_rule_sequences_v2 =
      ref ([] : clasetStep.timed_rule_sequence_v2 list)
    datatype outer_owner =
        AlternativeOwner
      | ReplayOwner
      | OtherOwner
    val outer_last = ref (NONE : Time.time option)
    val outer_stack = ref ([] : outer_owner list)
    val raw_alternative_time = ref Time.zeroTime
    val raw_replay_time = ref Time.zeroTime
    val raw_other_time = ref Time.zeroTime

    fun increment counter = counter := !counter + 1

    fun count_entry phase =
      (increment phase_entries;
       case phase of
           ReplayRecursion => increment replay_recursions
         | AlternativeEnumeration => increment alternative_pulls
         | TypedStep kind =>
             (increment typed_steps;
              case kind of
                  HypSubstStep => increment hyp_subst_steps
                | CloseAssumeStep => increment close_assume_steps
                | CloseContradictionStep =>
                    increment close_contradiction_steps
                | SafeRuleStep => increment safe_rule_steps
                | DeferGoalStep => increment defer_goal_steps
                | UnsafeRuleStep => increment unsafe_rule_steps)
         | StoredRuleSetup => increment stored_rule_setups
         | StoredRuleTransition => increment stored_rule_transitions
         | DuplicateChildMove => increment duplicate_child_moves
         | FinishOpenGoals => increment finish_open_goal_checks
         | GroundReplay => increment grounding_attempts
         | KernelReplay => increment kernel_replay_attempts
         | FinishResidualGoals =>
             increment finish_residual_goal_checks)

    fun invoke callback argument =
      callback argument handle error => raise CALLBACK error

    fun timing_clock () =
      case timing_mode of
          DetailedTimedV2 {clock, ...} => SOME clock
        | _ => NONE

    fun owner_of AlternativeEnumeration = AlternativeOwner
      | owner_of ReplayRecursion = ReplayOwner
      | owner_of _ = OtherOwner

    fun add_elapsed elapsed reference =
      reference := Time.+ (!reference, elapsed)

    fun account_outer finished =
      case !outer_last of
          NONE => outer_last := SOME finished
        | SOME started =>
            let
              val _ =
                if Time.< (finished, started) then
                  raise CALLBACK
                    (mk_HOL_ERR "blastReconstruct" "account_outer"
                      "the timed diagnostic clock moved backwards")
                else ()
              val elapsed = Time.- (finished, started)
              val _ = outer_last := SOME finished
            in
              case !outer_stack of
                  AlternativeOwner :: _ =>
                    add_elapsed elapsed raw_alternative_time
                | ReplayOwner :: _ => add_elapsed elapsed raw_replay_time
                | OtherOwner :: _ => add_elapsed elapsed raw_other_time
                | [] => add_elapsed elapsed raw_other_time
            end

    fun outer_enter phase =
      case timing_clock () of
          NONE => ()
        | SOME clock =>
            (account_outer (invoke clock ());
             outer_stack := owner_of phase :: !outer_stack)

    (* This stack is timing state, not observer state.  In particular, an
       operational failure deliberately has no fabricated Exit observation,
       but it must still close its exclusive interval and restore exactly the
       owner stack seen on entry before replay catches the failure. *)
    fun outer_restore saved =
      case timing_clock () of
          NONE => outer_stack := saved
        | SOME clock =>
            ((account_outer (invoke clock ()); outer_stack := saved)
             handle error => (outer_stack := saved; raise error))

    fun count_stored_rule_entry step_kind
          (rule : clasetStep.measured_rule_observation) =
      let
        val _ = increment stored_rule_phase_entries
        val _ =
          case #phase rule of
              clasetStep.AttemptSelection =>
                (increment stored_rule_attempt_selections;
                 case #rule_kind rule of
                     clasetStep.IntroRule =>
                       increment stored_rule_intro_attempts
                   | clasetStep.ElimRule =>
                       increment stored_rule_elim_attempts;
                 case step_kind of
                     SafeRuleStep => increment stored_rule_safe_attempts
                   | UnsafeRuleStep =>
                       increment stored_rule_unsafe_attempts
                   | _ =>
                       raise mk_HOL_ERR "blastReconstruct"
                         "count_stored_rule_entry"
                         "a stored rule has a non-rule script kind")
            | clasetStep.FresheningSetup =>
                increment stored_rule_freshening_setups
            | clasetStep.MinorUnification =>
                increment stored_rule_minor_unifications
            | clasetStep.EliminationMajorUnification =>
                increment stored_rule_major_unifications
            | clasetStep.RuleInstantiation =>
                increment stored_rule_instantiations
            | clasetStep.ChildStoreConstruction =>
                increment stored_rule_child_store_constructions
            | clasetStep.DirectResultConstruction =>
                increment stored_rule_direct_result_constructions
            | clasetStep.LazyResultYield =>
                increment stored_rule_lazy_yields
            | clasetStep.DirectChildReplacement =>
                increment stored_rule_direct_child_replacements
            | clasetStep.ReplayRecordConstruction =>
                increment stored_rule_replay_record_constructions
            | clasetStep.RecordInsertion =>
                increment stored_rule_record_insertions
      in
        ()
      end

    fun observe_stored script_position step_kind duplicate rule =
      let
        val combined : stored_rule_observation =
          {script_position = script_position,
           step_kind = step_kind, duplicate = duplicate, rule = rule}
        val _ = current_stored_rule := SOME combined
        val _ =
          case #boundary rule of
              clasetStep.RuleEnter =>
                count_stored_rule_entry step_kind rule
            | clasetStep.RuleExit =>
                increment stored_rule_phase_exits
      in
        case observe_stored_rule of
            NONE => ()
          | SOME observer => invoke observer combined
      end

    fun stop_stored_rule () =
      (increment stored_rule_checkpoints;
       increment cooperative_checkpoints;
       invoke stop ())

    fun checkpoint boundary phase =
      let
        val observation = {boundary = boundary, phase = phase}
        val _ = current_phase := SOME observation
        val _ =
          (case boundary of
               Enter => count_entry phase
             | Exit => increment phase_exits)
        val _ =
          case observe of
              NONE => ()
            | SOME observer => invoke observer observation
        val _ = increment cooperative_checkpoints
      in
        if invoke stop () then raise INTERRUPTED else ()
      end

    fun bracket phase operation argument =
      let
        val _ = checkpoint Enter phase
        val saved_outer_stack = !outer_stack
        val _ = outer_enter phase
        val result =
          operation argument
          handle error =>
            (outer_restore saved_outer_stack; raise error)
        val _ = outer_restore saved_outer_stack
        val _ = checkpoint Exit phase
      in
        result
      end

    (* Lib.total is the legacy replay policy: it catches every exception
       except the runtime Interrupt.  Preserve that policy while allowing
       diagnostic control flow and callback exceptions to cross the same
       internal boundaries. *)
    fun total_m operation argument =
      SOME (operation argument)
      handle INTERRUPTED => raise INTERRUPTED
           | CALLBACK error => raise CALLBACK error
           | Interrupt => raise Interrupt
           | _ => NONE

    fun first_result_m phase sequence =
      case bracket phase seq.cases sequence of
          SOME (result, _) => result
        | NONE =>
            raise mk_HOL_ERR "blastReconstruct" "first_result_m"
              "the recorded step does not apply"

    fun apply_m kind step node =
      bracket (TypedStep kind)
        (fn () => seq.map #2 (step (node, 1))) ()

    fun move_children_m count node =
      let
        fun move position current =
          if position > count then current
          else
            move (position + 1)
              (#2
                (first_result_m DuplicateChildMove
                  (clasetStep.blast_move_back_step 1
                    (current, position))))
      in
        move 1 node
      end

    fun apply_pseudo_m kind step node =
      seq.append (apply_m kind step node) (seq.result node)

    datatype measured_transitions =
        OrdinaryTransitions of clasetGoal.node seq.seq
      | StoredRuleTransitions of
          {sequence : clasetStep.measured_rule_sequence,
           old_count : int,
           duplicate : bool,
           is_elim : bool}
      | TimedStoredRuleTransitions of
          {sequence : clasetStep.timed_rule_sequence,
           old_count : int,
           duplicate : bool,
           is_elim : bool}
      | TimedStoredRuleTransitionsV2 of
          {sequence : clasetStep.timed_rule_sequence_v2,
           old_count : int,
           duplicate : bool,
           is_elim : bool}

    fun apply_rule_m script_position kind duplicate major rule node =
      case #origin rule of
          blastRule.ImpIntro =>
            OrdinaryTransitions
              (apply_pseudo_m kind clasetStep.blast_disch_step node)
        | blastRule.AllIntro =>
            OrdinaryTransitions
              (apply_pseudo_m kind clasetStep.blast_gen_step node)
        | blastRule.Stored {is_elim, theorem} =>
            bracket StoredRuleSetup
              (fn () =>
                let
                  val replay_theorem =
                    if duplicate andalso is_elim then
                      clasetRules.REV_DUP_ELIM_RULE theorem
                    else theorem
                  val old_count = length (clasetGoal.goals node)
                  fun observe_rule observation =
                    observe_stored script_position kind duplicate
                      observation
                in
                  case timing_mode of
                      DetailedUntimed =>
                        let
                          val sequence =
                            bracket (TypedStep kind)
                              (fn () =>
                                clasetStep.blast_rule_step_measured_at
                                  {observe = SOME observe_rule,
                                   stop = stop_stored_rule}
                                  cs
                                  {theorem = replay_theorem,
                                   elim = is_elim, major = major}
                                  (node, 1)) ()
                        in
                          StoredRuleTransitions
                            {sequence = sequence,
                             old_count = old_count,
                             duplicate = duplicate, is_elim = is_elim}
                        end
                    | DetailedTimed clock =>
                        let
                          val sequence =
                            bracket (TypedStep kind)
                              (fn () =>
                                clasetStep.blast_rule_step_timed_at
                                  {clock = fn () => invoke clock (),
                                   observe = SOME observe_rule,
                                   stop = stop_stored_rule}
                                  cs
                                  {theorem = replay_theorem,
                                   elim = is_elim, major = major}
                                  (node, 1)) ()
                          val _ =
                            timed_rule_sequences :=
                              sequence :: !timed_rule_sequences
                        in
                          TimedStoredRuleTransitions
                            {sequence = sequence,
                             old_count = old_count,
                             duplicate = duplicate, is_elim = is_elim}
                        end
                    | DetailedTimedV2 {clock, ...} =>
                        let
                          val sequence =
                            bracket (TypedStep kind)
                              (fn () =>
                                clasetStep.blast_rule_step_timed_v2_at
                                  {clock = fn () => invoke clock (),
                                   observe = SOME observe_rule,
                                   stop = stop_stored_rule}
                                  cs
                                  {theorem = replay_theorem,
                                   elim = is_elim, major = major}
                                  (node, 1)) ()
                          val _ =
                            timed_rule_sequences_v2 :=
                              sequence :: !timed_rule_sequences_v2
                        in
                          TimedStoredRuleTransitionsV2
                            {sequence = sequence,
                             old_count = old_count,
                             duplicate = duplicate, is_elim = is_elim}
                        end
                end) ()

    fun execute_m script_position step node =
      case step of
          blastSearch.HypSubst {equality} =>
            OrdinaryTransitions
              (apply_m HypSubstStep
                (clasetStep.blast_hyp_subst_step_at equality) node)
        | blastSearch.CloseAssume {assumption} =>
            OrdinaryTransitions
              (apply_m CloseAssumeStep
                (clasetStep.blast_assumption_step_at assumption) node)
        | blastSearch.CloseContradiction positions =>
            OrdinaryTransitions
              (apply_m CloseContradictionStep
                (clasetStep.blast_contradiction_step_at positions) node)
        | blastSearch.SafeRule {rule, major, ...} =>
            apply_rule_m script_position SafeRuleStep false major rule node
        | blastSearch.DeferGoal =>
            OrdinaryTransitions
              (apply_m DeferGoalStep clasetStep.blast_ccontr_step node)
        | blastSearch.UnsafeRule {rule, duplicate, major, ...} =>
            apply_rule_m script_position UnsafeRuleStep duplicate major rule
              node

    fun finish_stored_rule old_count duplicate is_elim next =
      bracket StoredRuleTransition
        (fn () =>
          let
            val child_count =
              length (clasetGoal.goals next) - old_count + 1
          in
            if duplicate andalso is_elim then
              move_children_m child_count next
            else next
          end) ()

    fun cases_m transitions =
      case transitions of
          OrdinaryTransitions sequence =>
            (case bracket AlternativeEnumeration seq.cases sequence of
                 NONE => NONE
               | SOME (next, tail) =>
                   SOME (next, OrdinaryTransitions tail))
        | StoredRuleTransitions
            {sequence, old_count, duplicate, is_elim} =>
            bracket AlternativeEnumeration
              (fn () =>
                let
                  fun pull current =
                    case clasetStep.measured_rule_cases current of
                        clasetStep.MeasuredRuleEmpty => NONE
                      | clasetStep.MeasuredRuleInterrupted =>
                          raise INTERRUPTED
                      | clasetStep.MeasuredRuleYield
                          ((_, next), tail) =>
                          (case total_m
                            (finish_stored_rule old_count duplicate
                              is_elim) next
                           of
                               SOME finished =>
                                 SOME
                                   (finished,
                                    StoredRuleTransitions
                                      {sequence = tail,
                                       old_count = old_count,
                                       duplicate = duplicate,
                                       is_elim = is_elim})
                             | NONE => pull tail)
                in
                  pull sequence
                end) ()
        | TimedStoredRuleTransitions
            {sequence, old_count, duplicate, is_elim} =>
            bracket AlternativeEnumeration
              (fn () =>
                let
                  fun pull current =
                    case
                      (clasetStep.timed_rule_cases current
                       handle CALLBACK error => raise CALLBACK error
                            | error => raise CALLBACK error)
                    of
                        clasetStep.TimedRuleEmpty => NONE
                      | clasetStep.TimedRuleInterrupted =>
                          raise INTERRUPTED
                      | clasetStep.TimedRuleYield
                          ((_, next), tail) =>
                          (case total_m
                            (finish_stored_rule old_count duplicate
                              is_elim) next
                           of
                               SOME finished =>
                                 SOME
                                   (finished,
                                    TimedStoredRuleTransitions
                                      {sequence = tail,
                                       old_count = old_count,
                                       duplicate = duplicate,
                                       is_elim = is_elim})
                             | NONE => pull tail)
                in
                  pull sequence
                end) ()
        | TimedStoredRuleTransitionsV2
            {sequence, old_count, duplicate, is_elim} =>
            bracket AlternativeEnumeration
              (fn () =>
                let
                  fun pull current =
                    case
                      (clasetStep.timed_rule_cases_v2 current
                       handle CALLBACK error => raise CALLBACK error
                            | error => raise CALLBACK error)
                    of
                        clasetStep.TimedRuleEmptyV2 => NONE
                      | clasetStep.TimedRuleInterruptedV2 =>
                          raise INTERRUPTED
                      | clasetStep.TimedRuleYieldV2
                          ((_, next), tail) =>
                          (case total_m
                            (finish_stored_rule old_count duplicate
                              is_elim) next
                           of
                               SOME finished =>
                                 SOME
                                   (finished,
                                    TimedStoredRuleTransitionsV2
                                      {sequence = tail,
                                       old_count = old_count,
                                       duplicate = duplicate,
                                       is_elim = is_elim})
                             | NONE => pull tail)
                in
                  pull sequence
                end) ()

    fun finish final =
      let
        val _ =
          bracket FinishOpenGoals
            (fn () =>
              if null (clasetGoal.goals final) then ()
              else
                raise mk_HOL_ERR "blastReconstruct" "finish"
                  "the recorded script leaves open engine goals") ()
        val grounded =
          bracket GroundReplay
            (fn () =>
              clasetReplay.ground (clasetGoal.store final)
                (clasetGoal.replay final)) ()
        val result as (residuals, _) =
          bracket KernelReplay
            (fn () =>
              case timing_mode of
                  DetailedTimedV2 {kernel_replay, ...} =>
                    kernel_replay grounded goal
                | _ =>
                    Tactical.VALID
                      (clasetReplay.REPLAY_TAC grounded) goal) ()
        val _ =
          bracket FinishResidualGoals
            (fn () =>
              if null residuals then ()
              else
                raise mk_HOL_ERR "blastReconstruct" "finish"
                  "kernel replay leaves open goals") ()
      in
        result
      end

    fun replay _ [] node =
          bracket ReplayRecursion (fn () => total_m finish node) ()
      | replay script_position (step :: rest) node =
          (bracket ReplayRecursion
            (fn () =>
              let
                fun alternatives sequence =
                  case cases_m sequence of
                      NONE => NONE
                    | SOME (next, nodes) =>
                        (case replay (script_position + 1) rest next of
                             NONE => alternatives nodes
                           | result => result)
              in
                alternatives (execute_m script_position step node)
              end) ()
           handle HOL_ERR _ => NONE)

    fun statistics () : detailed_statistics =
      {cooperative_checkpoints = !cooperative_checkpoints,
       phase_entries = !phase_entries,
       phase_exits = !phase_exits,
       replay_recursions = !replay_recursions,
       alternative_pulls = !alternative_pulls,
       typed_steps = !typed_steps,
       hyp_subst_steps = !hyp_subst_steps,
       close_assume_steps = !close_assume_steps,
       close_contradiction_steps = !close_contradiction_steps,
       safe_rule_steps = !safe_rule_steps,
       defer_goal_steps = !defer_goal_steps,
       unsafe_rule_steps = !unsafe_rule_steps,
       stored_rule_setups = !stored_rule_setups,
       stored_rule_transitions = !stored_rule_transitions,
       duplicate_child_moves = !duplicate_child_moves,
       finish_open_goal_checks = !finish_open_goal_checks,
       grounding_attempts = !grounding_attempts,
       kernel_replay_attempts = !kernel_replay_attempts,
       finish_residual_goal_checks = !finish_residual_goal_checks,
       stored_rule_checkpoints = !stored_rule_checkpoints,
       stored_rule_phase_entries = !stored_rule_phase_entries,
       stored_rule_phase_exits = !stored_rule_phase_exits,
       stored_rule_attempt_selections =
         !stored_rule_attempt_selections,
       stored_rule_freshening_setups =
         !stored_rule_freshening_setups,
       stored_rule_minor_unifications =
         !stored_rule_minor_unifications,
       stored_rule_major_unifications =
         !stored_rule_major_unifications,
       stored_rule_instantiations = !stored_rule_instantiations,
       stored_rule_child_store_constructions =
         !stored_rule_child_store_constructions,
       stored_rule_direct_result_constructions =
         !stored_rule_direct_result_constructions,
       stored_rule_lazy_yields = !stored_rule_lazy_yields,
       stored_rule_direct_child_replacements =
         !stored_rule_direct_child_replacements,
       stored_rule_replay_record_constructions =
         !stored_rule_replay_record_constructions,
       stored_rule_record_insertions = !stored_rule_record_insertions,
       stored_rule_intro_attempts = !stored_rule_intro_attempts,
       stored_rule_elim_attempts = !stored_rule_elim_attempts,
       stored_rule_safe_attempts = !stored_rule_safe_attempts,
       stored_rule_unsafe_attempts = !stored_rule_unsafe_attempts}

    fun report completion result : detailed_measured_result =
      {completion = completion,
       current_phase = !current_phase,
       current_stored_rule = !current_stored_rule,
       result = result,
       statistics = statistics ()}

    fun add_time (value, total) = Time.+ (value, total)

    fun classical_times () : classical_phase_times =
      let
        val snapshots =
          case timing_mode of
              DetailedTimedV2 _ =>
                map
                  (#base o clasetStep.timed_rule_statistics_v2)
                  (!timed_rule_sequences_v2)
            | _ =>
                map clasetStep.timed_rule_statistics
                  (!timed_rule_sequences)
      in
        {attempt_selection_time =
           List.foldl
             (fn (item, total) =>
               add_time (#attempt_selection_time item, total))
             Time.zeroTime snapshots,
         freshening_setup_time =
           List.foldl
             (fn (item, total) =>
               add_time (#freshening_setup_time item, total))
             Time.zeroTime snapshots,
         minor_unification_time =
           List.foldl
             (fn (item, total) =>
               add_time (#minor_unification_time item, total))
             Time.zeroTime snapshots,
         elimination_major_unification_time =
           List.foldl
             (fn (item, total) =>
               add_time
                 (#elimination_major_unification_time item, total))
             Time.zeroTime snapshots,
         rule_instantiation_time =
           List.foldl
             (fn (item, total) =>
               add_time (#rule_instantiation_time item, total))
             Time.zeroTime snapshots,
         child_store_construction_time =
           List.foldl
             (fn (item, total) =>
               add_time (#child_store_construction_time item, total))
             Time.zeroTime snapshots,
         direct_result_construction_time =
           List.foldl
             (fn (item, total) =>
               add_time (#direct_result_construction_time item, total))
             Time.zeroTime snapshots,
         lazy_result_yield_time =
           List.foldl
             (fn (item, total) =>
               add_time (#lazy_result_yield_time item, total))
             Time.zeroTime snapshots,
         direct_child_replacement_time =
           List.foldl
             (fn (item, total) =>
               add_time (#direct_child_replacement_time item, total))
             Time.zeroTime snapshots,
         replay_record_construction_time =
           List.foldl
             (fn (item, total) =>
               add_time (#replay_record_construction_time item, total))
             Time.zeroTime snapshots,
         record_insertion_time =
           List.foldl
             (fn (item, total) =>
               add_time (#record_insertion_time item, total))
             Time.zeroTime snapshots,
         classical_time =
           List.foldl
             (fn (item, total) =>
               add_time (#classical_time item, total))
             Time.zeroTime snapshots}
      end

    fun maximum_time (left, right) =
      if Time.< (left, right) then right else left

    fun minor_unification_times () : minor_unification_times =
      let
        val snapshots =
          map
            (#minor_unification_times o
             clasetStep.timed_rule_statistics_v2)
            (!timed_rule_sequences_v2)
      in
        {calls = List.foldl (fn (item, n) => #calls item + n) 0 snapshots,
         failures =
           List.foldl (fn (item, n) => #failures item + n) 0 snapshots,
         normalization_setup_time =
           List.foldl
             (fn (item, total) =>
               add_time (#normalization_setup_time item, total))
             Time.zeroTime snapshots,
         traversal_decomposition_binding_time =
           List.foldl
             (fn (item, total) =>
               add_time
                 (#traversal_decomposition_binding_time item, total))
             Time.zeroTime snapshots,
         failure_cleanup_time =
           List.foldl
             (fn (item, total) =>
               add_time (#failure_cleanup_time item, total))
             Time.zeroTime snapshots,
         minor_unification_time =
           List.foldl
             (fn (item, total) =>
               add_time (#minor_unification_time item, total))
             Time.zeroTime snapshots,
         max_normalization_setup_time =
           List.foldl
             (fn (item, current) =>
               maximum_time
                 (#max_normalization_setup_time item, current))
             Time.zeroTime snapshots,
         max_traversal_decomposition_binding_time =
           List.foldl
             (fn (item, current) =>
               maximum_time
                 (#max_traversal_decomposition_binding_time item,
                  current))
             Time.zeroTime snapshots,
         max_failure_cleanup_time =
           List.foldl
             (fn (item, current) =>
               maximum_time (#max_failure_cleanup_time item, current))
             Time.zeroTime snapshots,
         max_minor_unification_time =
           List.foldl
             (fn (item, current) =>
               maximum_time (#max_minor_unification_time item, current))
             Time.zeroTime snapshots}
      end

    fun read_clock clock = invoke clock ()

    fun elapsed_at started finished =
      if Time.< (finished, started) then
        raise CALLBACK
          (mk_HOL_ERR "blastReconstruct"
            "reconstructWithMeasuredTimedDetailed"
            "the timed diagnostic clock moved backwards")
      else Time.- (finished, started)

    fun terminal_elapsed clock started =
      elapsed_at started (read_clock clock)

    fun timed_report attempt_wall_time completion result =
      TimedDetailedResult
        {completion = completion,
         current_phase = !current_phase,
         current_stored_rule = !current_stored_rule,
         result = result,
         statistics = statistics (),
         classical_times = classical_times (),
         attempt_wall_time = attempt_wall_time}

    fun timed_report_v2 attempt_wall_time completion result =
      let
        val classical = classical_times ()
        val classical_time = #classical_time classical
        val alternative_time =
          if Time.< (!raw_alternative_time, classical_time) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v2"
                "classical time exceeds enclosing alternative time")
          else Time.- (!raw_alternative_time, classical_time)
        val outer_time =
          Time.+
            (alternative_time,
             Time.+ (!raw_replay_time, !raw_other_time))
        val expected_outer =
          if Time.< (attempt_wall_time, classical_time) then
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v2"
                "classical time exceeds whole-attempt time")
          else Time.- (attempt_wall_time, classical_time)
        val _ =
          if outer_time = expected_outer then ()
          else
            raise CALLBACK
              (mk_HOL_ERR "blastReconstruct" "timed_report_v2"
                "exclusive reconstruction accounting is inconsistent")
        val base : timed_detailed_measured_result =
          {completion = completion,
           current_phase = !current_phase,
           current_stored_rule = !current_stored_rule,
           result = result,
           statistics = statistics (),
           classical_times = classical,
           attempt_wall_time = attempt_wall_time}
        val outer : outer_reconstruction_times =
          {alternative_enumeration_time = alternative_time,
           replay_continuation_time = !raw_replay_time,
           other_outer_time = !raw_other_time,
           outer_reconstruction_time = outer_time}
      in
        TimedDetailedResultV2
          {base = base,
           minor_unification_times = minor_unification_times (),
           outer_reconstruction_times = outer}
      end

    fun perform () =
      case replay 1 script (clasetGoal.from_goal goal) of
          SOME result => result
        | NONE =>
            raise mk_HOL_ERR "blastReconstruct"
              "reconstructWithMeasured"
              "the recorded tableau has no kernel-valid replay"
  in
    ((case timing_mode of
          DetailedUntimed =>
            UntimedDetailedResult
              ((report Completed (SOME (perform ()))
               handle INTERRUPTED => report Interrupted NONE
                    | CALLBACK error => raise CALLBACK error
                    | Interrupt => raise Interrupt
                    | _ => report Completed NONE))
        | DetailedTimed clock =>
            let
              val started = read_clock clock
              fun terminal_report completion result =
                let
                  val attempt_wall_time = terminal_elapsed clock started
                in
                  timed_report attempt_wall_time completion result
                end
            in
              (let
                 val result = perform ()
               in
                 terminal_report Completed (SOME result)
               end
               handle INTERRUPTED =>
                        terminal_report Interrupted NONE
                    | CALLBACK error => raise CALLBACK error
                    | Interrupt => raise Interrupt
                    | _ => terminal_report Completed NONE)
            end
        | DetailedTimedV2 {clock, ...} =>
            let
              val started = read_clock clock
              val _ = outer_last := SOME started
              fun terminal_report completion result =
                let
                  val finished = read_clock clock
                  val _ = account_outer finished
                  val attempt_wall_time = elapsed_at started finished
                in
                  timed_report_v2 attempt_wall_time completion result
                end
            in
              (let
                 val result = perform ()
               in
                 terminal_report Completed (SOME result)
               end
               handle INTERRUPTED =>
                        terminal_report Interrupted NONE
                    | CALLBACK error => raise CALLBACK error
                    | Interrupt => raise Interrupt
                    | _ => terminal_report Completed NONE)
            end)
     handle CALLBACK error => raise error)
  end



fun reconstructWithMeasuredDetailed controls cs goal proof =
  case reconstructWithMeasuredDetailedMode DetailedUntimed controls cs
    goal proof
  of
      UntimedDetailedResult result => result
    | TimedDetailedResult _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredDetailed"
          "internal detailed diagnostic mode mismatch"
    | TimedDetailedResultV2 _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredDetailed"
          "internal detailed diagnostic mode mismatch"

fun reconstructWithMeasuredTimedDetailed
      {clock, observe, observe_stored_rule, stop} cs goal proof =
  case reconstructWithMeasuredDetailedMode (DetailedTimed clock)
    {observe = observe, observe_stored_rule = observe_stored_rule,
     stop = stop} cs goal proof
  of
      TimedDetailedResult result => result
    | UntimedDetailedResult _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailed"
          "internal detailed diagnostic mode mismatch"
    | TimedDetailedResultV2 _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailed"
          "internal detailed diagnostic mode mismatch"

fun reconstructWithMeasuredTimedDetailedV2
      {clock, observe, observe_stored_rule, stop} cs goal proof =
  case reconstructWithMeasuredDetailedMode
    (DetailedTimedV2
      {clock = clock,
       kernel_replay =
         fn grounded =>
           Tactical.VALID (clasetReplay.REPLAY_TAC grounded)})
    {observe = observe, observe_stored_rule = observe_stored_rule,
     stop = stop} cs goal proof
  of
      TimedDetailedResultV2 result => result
    | UntimedDetailedResult _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV2"
          "internal detailed diagnostic mode mismatch"
    | TimedDetailedResult _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV2"
          "internal detailed diagnostic mode mismatch"

fun reconstructWithMeasuredTimedDetailedV2UsingKernel
      {clock, kernel_replay, observe, observe_stored_rule, stop}
      cs goal proof =
  case reconstructWithMeasuredDetailedMode
    (DetailedTimedV2
      {clock = clock, kernel_replay = kernel_replay})
    {observe = observe, observe_stored_rule = observe_stored_rule,
     stop = stop} cs goal proof
  of
      TimedDetailedResultV2 result => result
    | UntimedDetailedResult _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV2UsingKernel"
          "internal detailed diagnostic mode mismatch"
    | TimedDetailedResult _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV2UsingKernel"
          "internal detailed diagnostic mode mismatch"

fun reconstructWithMeasuredTimedDetailedV3
      {clock, observe, observe_stored_rule, stop} cs goal proof =
  case reconstructWithMeasuredDetailedModeV3
    (DetailedTimedModeV3
      {clock = clock,
       kernel_replay =
         fn grounded =>
           Tactical.VALID (clasetReplay.REPLAY_TAC grounded),
       transition = clasetStep.timed_rule_cases_v3})
    {observe = observe, observe_stored_rule = observe_stored_rule,
     stop = stop} cs goal proof
  of
      TimedDetailedResultV3 result => result
    | TimedDetailedResultV4 _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV3"
          "internal detailed diagnostic mode mismatch"

fun reconstructWithMeasuredTimedDetailedV3UsingKernel
      {clock, kernel_replay, observe, observe_stored_rule, stop}
      cs goal proof =
  case reconstructWithMeasuredDetailedModeV3
    (DetailedTimedModeV3
      {clock = clock, kernel_replay = kernel_replay,
       transition = clasetStep.timed_rule_cases_v3})
    {observe = observe, observe_stored_rule = observe_stored_rule,
     stop = stop} cs goal proof
  of
      TimedDetailedResultV3 result => result
    | TimedDetailedResultV4 _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV3UsingKernel"
          "internal detailed diagnostic mode mismatch"

fun reconstructWithMeasuredTimedDetailedV3UsingTransition
      {clock, kernel_replay, transition, observe, observe_stored_rule, stop}
      cs goal proof =
  case reconstructWithMeasuredDetailedModeV3
    (DetailedTimedModeV3
      {clock = clock, kernel_replay = kernel_replay,
       transition = transition})
    {observe = observe, observe_stored_rule = observe_stored_rule,
     stop = stop} cs goal proof
  of
      TimedDetailedResultV3 result => result
    | TimedDetailedResultV4 _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV3UsingTransition"
          "internal detailed diagnostic mode mismatch"

fun reconstructWithMeasuredTimedDetailedV4
      {clock, observe, observe_stored_rule, stop} cs goal proof =
  case reconstructWithMeasuredDetailedModeV3
    (DetailedBoundedModeV4
      {clock = clock,
       kernel_replay =
         fn grounded =>
           Tactical.VALID (clasetReplay.REPLAY_TAC grounded),
       transition = clasetStep.timed_rule_cases_v4})
    {observe = observe, observe_stored_rule = observe_stored_rule,
     stop = stop} cs goal proof
  of
      TimedDetailedResultV4 result => result
    | TimedDetailedResultV3 _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV4"
          "internal detailed diagnostic mode mismatch"

fun reconstructWithMeasuredTimedDetailedV4UsingKernel
      {clock, kernel_replay, observe, observe_stored_rule, stop}
      cs goal proof =
  case reconstructWithMeasuredDetailedModeV3
    (DetailedBoundedModeV4
      {clock = clock, kernel_replay = kernel_replay,
       transition = clasetStep.timed_rule_cases_v4})
    {observe = observe, observe_stored_rule = observe_stored_rule,
     stop = stop} cs goal proof
  of
      TimedDetailedResultV4 result => result
    | TimedDetailedResultV3 _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV4UsingKernel"
          "internal detailed diagnostic mode mismatch"

fun reconstructWithMeasuredTimedDetailedV4UsingTransition
      {clock, kernel_replay, transition, observe, observe_stored_rule, stop}
      cs goal proof =
  case reconstructWithMeasuredDetailedModeV3
    (DetailedBoundedModeV4
      {clock = clock, kernel_replay = kernel_replay,
       transition = transition})
    {observe = observe, observe_stored_rule = observe_stored_rule,
     stop = stop} cs goal proof
  of
      TimedDetailedResultV4 result => result
    | TimedDetailedResultV3 _ =>
        raise mk_HOL_ERR "blastReconstruct"
          "reconstructWithMeasuredTimedDetailedV4UsingTransition"
          "internal detailed diagnostic mode mismatch"

fun reconstructMeasured controls goal proof =
  reconstructWithMeasured controls clasetLib.empty_cs goal proof

fun reconstructMeasuredDetailed controls goal proof =
  reconstructWithMeasuredDetailed controls clasetLib.empty_cs goal proof

fun reconstructMeasuredTimedDetailed controls goal proof =
  reconstructWithMeasuredTimedDetailed controls clasetLib.empty_cs goal
    proof

fun reconstructMeasuredTimedDetailedV2 controls goal proof =
  reconstructWithMeasuredTimedDetailedV2 controls clasetLib.empty_cs goal
    proof

fun reconstructMeasuredTimedDetailedV3 controls goal proof =
  reconstructWithMeasuredTimedDetailedV3 controls clasetLib.empty_cs goal
    proof

fun reconstructMeasuredTimedDetailedV4 controls goal proof =
  reconstructWithMeasuredTimedDetailedV4 controls clasetLib.empty_cs goal
    proof

fun accept cs goal proof =
  case reconstructWith cs goal proof of
      SOME result => (proof, result)
    | NONE => raise blastSearch.PROOF_FAILED

fun searchGoal cs depth goal =
  blastSearch.searchGoal cs depth goal (accept cs goal)

fun deepenGoal cs goal =
  blastSearch.deepenGoal cs goal (accept cs goal)

fun tactic_result function_name result =
  case result of
      SOME (_, tactic_result) => tactic_result
    | NONE =>
        raise mk_HOL_ERR "blastReconstruct" function_name
          "blast search found no reconstructible proof"

fun DEPTH_TAC cs depth goal =
  tactic_result "DEPTH_TAC" (searchGoal cs depth goal)

fun DEEPEN_TAC cs goal =
  tactic_result "DEEPEN_TAC" (deepenGoal cs goal)

end
