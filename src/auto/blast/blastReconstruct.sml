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

(* Typed child construction strips implication/forall prefixes after rule
   metavariables are instantiated.  The untyped tableau can therefore
   record a pseudo-step that replay has already performed. *)
fun apply_pseudo step node =
  seq.append (apply step node) (seq.result node)

fun apply_rule cs duplicate rule node =
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
              (clasetStep.blast_rule_step cs
                {theorem = replay_theorem, elim = is_elim}) node

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
      blastSearch.HypSubst =>
        apply clasetStep.blast_hyp_subst_step node
    | blastSearch.CloseAssume =>
        apply clasetStep.blast_assumption_step node
    | blastSearch.CloseContradiction =>
        apply clasetStep.blast_contradiction_step node
    | blastSearch.SafeRule {rule, ...} =>
        apply_rule cs false rule node
    | blastSearch.DeferGoal =>
        apply clasetStep.blast_ccontr_step node
    | blastSearch.UnsafeRule {rule, duplicate, ...} =>
        apply_rule cs duplicate rule node

(* The tableau records rule provenance, but an elimination theorem can
   resolve against several assumptions.  Explore those typed engine
   transitions lazily; only a completely grounded, kernel-valid replay is
   accepted.  Exhausting them still rejects this tableau through the search
   continuation's PROOF_FAILED hook. *)
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

    fun apply_rule_m kind duplicate rule node =
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
                      (clasetStep.blast_rule_step cs
                        {theorem = replay_theorem, elim = is_elim}) node

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
          blastSearch.HypSubst =>
            apply_m HypSubstStep clasetStep.blast_hyp_subst_step node
        | blastSearch.CloseAssume =>
            apply_m CloseAssumeStep clasetStep.blast_assumption_step node
        | blastSearch.CloseContradiction =>
            apply_m CloseContradictionStep
              clasetStep.blast_contradiction_step node
        | blastSearch.SafeRule {rule, ...} =>
            apply_rule_m SafeRuleStep false rule node
        | blastSearch.DeferGoal =>
            apply_m DeferGoalStep clasetStep.blast_ccontr_step node
        | blastSearch.UnsafeRule {rule, duplicate, ...} =>
            apply_rule_m UnsafeRuleStep duplicate rule node

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


fun reconstructWithMeasuredDetailed
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

    datatype measured_transitions =
        OrdinaryTransitions of clasetGoal.node seq.seq
      | StoredRuleTransitions of
          {sequence : clasetStep.measured_rule_sequence,
           old_count : int,
           duplicate : bool,
           is_elim : bool}

    fun apply_rule_m script_position kind duplicate rule node =
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
                  val sequence =
                    bracket (TypedStep kind)
                      (fn () =>
                        clasetStep.blast_rule_step_measured
                          {observe = SOME observe_rule,
                           stop = stop_stored_rule}
                          cs
                          {theorem = replay_theorem, elim = is_elim}
                          (node, 1)) ()
                in
                  StoredRuleTransitions
                    {sequence = sequence, old_count = old_count,
                     duplicate = duplicate, is_elim = is_elim}
                end) ()

    fun execute_m script_position step node =
      case step of
          blastSearch.HypSubst =>
            OrdinaryTransitions
              (apply_m HypSubstStep
                clasetStep.blast_hyp_subst_step node)
        | blastSearch.CloseAssume =>
            OrdinaryTransitions
              (apply_m CloseAssumeStep
                clasetStep.blast_assumption_step node)
        | blastSearch.CloseContradiction =>
            OrdinaryTransitions
              (apply_m CloseContradictionStep
                clasetStep.blast_contradiction_step node)
        | blastSearch.SafeRule {rule, ...} =>
            apply_rule_m script_position SafeRuleStep false rule node
        | blastSearch.DeferGoal =>
            OrdinaryTransitions
              (apply_m DeferGoalStep clasetStep.blast_ccontr_step node)
        | blastSearch.UnsafeRule {rule, duplicate, ...} =>
            apply_rule_m script_position UnsafeRuleStep duplicate rule node

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

    fun perform () =
      case replay 1 script (clasetGoal.from_goal goal) of
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

fun reconstructMeasured controls goal proof =
  reconstructWithMeasured controls clasetLib.empty_cs goal proof

fun reconstructMeasuredDetailed controls goal proof =
  reconstructWithMeasuredDetailed controls clasetLib.empty_cs goal proof

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
