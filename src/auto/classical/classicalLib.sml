structure classicalLib :> classicalLib =
struct

open Abbrev HolKernel

type run_state =
  {node : clasetGoal.node,
   validation : validation}

fun rendered_goals node =
  let
    fun render _ [] = []
      | render pos (_ :: rest) =
          clasetGoal.render node pos :: render (pos + 1) rest
  in
    render 1 (clasetGoal.goals node)
  end

fun initial_validation [theorem] = theorem
  | initial_validation _ =
      raise mk_HOL_ERR "classicalLib" "initial_validation"
        "validation expected one theorem"

fun replace_validation old_count pos child_count step_validation
    old_validation theorem_list =
  if length theorem_list <> old_count - 1 + child_count then
    raise mk_HOL_ERR "classicalLib" "replace_validation"
      "validation received the wrong number of theorems"
  else
    let
      val prefix = List.take (theorem_list, pos - 1)
      val after_prefix = List.drop (theorem_list, pos - 1)
      val children = List.take (after_prefix, child_count)
      val suffix = List.drop (after_prefix, child_count)
      val parent = step_validation children
    in
      old_validation (prefix @ (parent :: suffix))
    end

fun accept_safe_transition
      ((pos, record, next), {node, validation} : run_state) =
  let
    val old_count = length (clasetGoal.goals node)
    val child_count = clasetGoal.child_count node next
    val validation' =
      replace_validation old_count pos child_count
        (clasetStep.validation_of record) validation
  in
    {node=next, validation=validation'}
  end

fun safe_saturate cs goal =
  let
    val initial =
      {node = clasetGoal.from_goal goal,
       validation = initial_validation}
    val transitions = clasetStep.safe_saturation cs (#node initial)
    val final = List.foldl accept_safe_transition initial transitions
    val goals = rendered_goals (#node final)
  in
    if boolSyntax.goals_eq goals [goal] then seq.empty
    else seq.result (goals, #validation final)
  end

fun step_ntactic step cs goal =
  let
    val node = clasetGoal.from_goal goal
  in
    seq.map
      (fn (record, next) =>
        (rendered_goals next, clasetStep.validation_of record))
      (step cs (node, 1))
  end

fun CS_SAFE_STEP_TAC cs = step_ntactic clasetStep.safe_step cs
fun CS_CLARIFY_STEP_TAC cs = step_ntactic clasetStep.clarify_step cs
fun CS_SAFE_TAC cs = safe_saturate cs

fun CS_CLARIFY_TAC cs =
  NTactical.NCHANGED
    (NTactical.NREPEAT (CS_CLARIFY_STEP_TAC cs))

fun replay_node original node =
  let
    val grounded =
      clasetReplay.ground (clasetGoal.store node)
        (clasetGoal.replay node)
  in
    seq.result (clasetReplay.REPLAY_TAC grounded original)
  end
  handle HOL_ERR error =>
    let
      val _ = clasetReplay.trace 1
        (fn () =>
          "kernel replay failed for an engine solution; backtracking: " ^
          Feedback.message_of error)
    in
      seq.empty
    end

fun replay_step step cs goal =
  let val initial = clasetGoal.from_goal goal
  in
    seq.bind (step cs (initial, 1))
      (fn (_, node) => replay_node goal node)
  end

fun CS_STEP_TAC cs = replay_step clasetStep.step cs
fun CS_SLOW_STEP_TAC cs = replay_step clasetStep.slow_step cs
fun CS_INST_STEP_TAC cs = replay_step clasetStep.inst_step cs

fun project_steps steps =
  seq.map (fn (_, node) => node) steps

fun expand_at step cs pos node =
  project_steps (step cs (node, pos))

fun expand_first step cs node =
  let
    fun first pos =
      if pos > length (clasetGoal.goals node) then seq.empty
      else
        seq.delay
          (fn () =>
            case seq.cases (expand_at step cs pos node) of
                NONE => first (pos + 1)
              | SOME (result, rest) => seq.cons result rest)
  in
    first 1
  end

(* Isabelle's safe_depth_tac saturates the complete selected state before
   depth search.  Keeping the resulting goals visible to DEPTH_SOLVE also
   lets its D25 commitment test run between safely generated siblings. *)
fun safe_saturate_node cs initial =
  case List.rev (clasetStep.safe_saturation cs initial) of
      [] => initial
    | (_, _, final) :: _ => final

fun solved node = List.null (clasetGoal.goals node)

fun solve search goal =
  let val initial = clasetGoal.from_goal goal
  in
    seq.bind (search initial)
      (fn node =>
        if solved node then replay_node goal node else seq.empty)
  end

fun depth_driver step cs =
  clasetSearch.DEPTH_SOLVE (expand_at step cs 1)

fun best_driver step cs =
  clasetSearch.BEST_FIRST solved (expand_at step cs 1)

fun astar_driver step cs =
  clasetSearch.ASTAR solved (expand_at step cs 1)

fun CS_FAST_TAC cs = solve (depth_driver clasetStep.step cs)
fun CS_SLOW_TAC cs = solve (depth_driver clasetStep.slow_step cs)
fun CS_BEST_TAC cs = solve (best_driver clasetStep.step cs)
fun CS_SLOW_BEST_TAC cs = solve (best_driver clasetStep.slow_step cs)

fun CS_FIRST_BEST_TAC cs =
  solve (clasetSearch.BEST_FIRST solved
    (expand_first clasetStep.step cs))

fun CS_ASTAR_TAC cs = solve (astar_driver clasetStep.step cs)
fun CS_SLOW_ASTAR_TAC cs = solve (astar_driver clasetStep.slow_step cs)

fun bounded_depth {dup} cs bound initial =
  let
    val part =
      if dup then clasetLib.dup_part cs else clasetLib.unsafe_part cs
    val saturated = safe_saturate_node cs initial
    val search =
      clasetSearch.DEPTH_SOLVE
        (fn node =>
          project_steps
            (clasetStep.depth_step cs part bound (node, 1)))
  in
    search saturated
  end

fun CS_DEPTH_SOLVE_TAC config bound cs =
  solve (bounded_depth config cs bound)

fun CS_DEEPEN_TAC cs {start} =
  solve
    (clasetSearch.DEEPEN (2, 10)
      (bounded_depth {dup = true} cs) start)

fun no_extra_markers theorems cs = (cs, theorems)

fun invocation body theorems =
  clasetLib.with_invocation_args
    {iff_prefix="", extra_markers=no_extra_markers}
    (fn cs => fn _ => fn _ => body cs)
    (clasetLib.the_claset ())
    (NONE : unit clasetLib.invocation_simpset option) theorems

fun public tactic = invocation (NTactical.DETERM o tactic)

(* The saturating tactics report a no-op as failure, and inserting a fact is
   not a no-op, so their progress test spans the whole invocation: an engine
   that finds no step leaves the supplied facts in the residue instead of
   discarding them.  With nothing to insert this is exactly the engine's own
   test.  The step tactics keep theirs, since one that could "succeed" by
   inserting alone would make NREPEAT insert for ever. *)
fun progress tactic theorems =
  Tactical.CHANGED_TAC
    (invocation (NTactical.DETERM o NTactical.NTRY o tactic) theorems)

fun SAFE_TAC theorems = progress CS_SAFE_TAC theorems
fun CLARIFY_TAC theorems = progress CS_CLARIFY_TAC theorems
fun SAFE_STEP_TAC theorems = public CS_SAFE_STEP_TAC theorems
fun CLARIFY_STEP_TAC theorems = public CS_CLARIFY_STEP_TAC theorems
fun STEP_TAC theorems = public CS_STEP_TAC theorems
fun SLOW_STEP_TAC theorems = public CS_SLOW_STEP_TAC theorems
fun INST_STEP_TAC theorems = public CS_INST_STEP_TAC theorems

fun FAST_TAC theorems = public CS_FAST_TAC theorems
fun SLOW_TAC theorems = public CS_SLOW_TAC theorems
fun BEST_TAC theorems = public CS_BEST_TAC theorems
fun SLOW_BEST_TAC theorems = public CS_SLOW_BEST_TAC theorems
fun FIRST_BEST_TAC theorems = public CS_FIRST_BEST_TAC theorems
fun ASTAR_TAC theorems = public CS_ASTAR_TAC theorems
fun SLOW_ASTAR_TAC theorems = public CS_SLOW_ASTAR_TAC theorems
fun DEEPEN_TAC theorems =
  public (fn cs => CS_DEEPEN_TAC cs {start = 4}) theorems

end
