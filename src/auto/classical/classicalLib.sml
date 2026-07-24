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

fun goal_lists_equal (left, right) =
  ListPair.allEq (fn (goal1, goal2) =>
    boolSyntax.goal_eq goal1 goal2) (left, right)

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

fun apply_first step pos ({node, validation} : run_state) =
  case seq.cases (step (node, pos)) of
      NONE => NONE
    | SOME ((record, next), _) =>
        let
          val old_count = length (clasetGoal.goals node)
          val new_count = length (clasetGoal.goals next)
          val child_count = new_count - old_count + 1
          val validation' =
            replace_validation old_count pos child_count
              (clasetStep.validation_of record) validation
        in
          SOME {node = next, validation = validation'}
        end

fun safe_saturate cs goal =
  let
    val step = clasetStep.safe_step cs
    val initial =
      {node = clasetGoal.from_goal goal,
       validation = initial_validation}

    fun repeat_at pos state =
      if pos > length (clasetGoal.goals (#node state)) then state
      else
        case apply_first step pos state of
            NONE => state
          | SOME next => repeat_at pos next

    fun safe_steps pos state =
      case apply_first step pos state of
          NONE => NONE
        | SOME next => SOME (repeat_at pos next)

    fun first_goal pos state =
      if pos > length (clasetGoal.goals (#node state)) then NONE
      else
        case safe_steps pos state of
            NONE => first_goal (pos + 1) state
          | result => result

    fun saturate state =
      case first_goal 1 state of
          NONE => state
        | SOME next => saturate next

    val final = saturate initial
    val goals = rendered_goals (#node final)
  in
    if goal_lists_equal (goals, [goal]) then seq.empty
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

fun safe_step_tac cs = step_ntactic clasetStep.safe_step cs
fun clarify_step_tac cs = step_ntactic clasetStep.clarify_step cs
fun safe_tac cs = safe_saturate cs

fun clarify_tac cs =
  NTactical.NCHANGED
    (NTactical.NREPEAT (clarify_step_tac cs))

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
      val _ =
        if Feedback.current_trace "classical" >= 1 then
          Feedback.HOL_MESG
            ("Classical reasoner: kernel replay failed for an engine " ^
             "solution; backtracking: " ^ Feedback.message_of error)
        else ()
    in
      seq.empty
    end

fun replay_step step cs goal =
  let val initial = clasetGoal.from_goal goal
  in
    seq.bind (step cs (initial, 1))
      (fn (_, node) => replay_node goal node)
  end

fun step_tac cs = replay_step clasetStep.step cs
fun slow_step_tac cs = replay_step clasetStep.slow_step cs
fun inst_step_tac cs = replay_step clasetStep.inst_step cs

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
  let
    fun first_goal pos node =
      if pos > length (clasetGoal.goals node) then NONE
      else
        case seq.cases
          (expand_at clasetStep.safe_step cs pos node)
        of
            NONE => first_goal (pos + 1) node
          | SOME (next, _) => SOME next

    fun saturate node =
      case first_goal 1 node of
          NONE => node
        | SOME next => saturate next
  in
    saturate initial
  end

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

fun fast_tac cs = solve (depth_driver clasetStep.step cs)
fun slow_tac cs = solve (depth_driver clasetStep.slow_step cs)
fun best_tac cs = solve (best_driver clasetStep.step cs)
fun slow_best_tac cs = solve (best_driver clasetStep.slow_step cs)

fun first_best_tac cs =
  solve (clasetSearch.BEST_FIRST solved
    (expand_first clasetStep.step cs))

fun astar_tac cs = solve (astar_driver clasetStep.step cs)
fun slow_astar_tac cs = solve (astar_driver clasetStep.slow_step cs)

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

fun depth_solve_tac config bound cs =
  solve (bounded_depth config cs bound)

fun deepen_tac cs {start} =
  solve
    (clasetSearch.DEEPEN (2, 10)
      (bounded_depth {dup = true} cs) start)

val CS_SAFE_TAC = safe_tac
val CS_CLARIFY_TAC = clarify_tac
val CS_SAFE_STEP_TAC = safe_step_tac
val CS_CLARIFY_STEP_TAC = clarify_step_tac
val CS_STEP_TAC = step_tac
val CS_SLOW_STEP_TAC = slow_step_tac
val CS_INST_STEP_TAC = inst_step_tac
val CS_FAST_TAC = fast_tac
val CS_SLOW_TAC = slow_tac
val CS_BEST_TAC = best_tac
val CS_SLOW_BEST_TAC = slow_best_tac
val CS_FIRST_BEST_TAC = first_best_tac
val CS_ASTAR_TAC = astar_tac
val CS_SLOW_ASTAR_TAC = slow_astar_tac
val CS_DEPTH_SOLVE_TAC = depth_solve_tac
val CS_DEEPEN_TAC = deepen_tac

fun invocation_claset theorems =
  clasetLib.invocation_claset {prefix = "__classical_extra_"}
    (clasetLib.the_claset ()) theorems

fun public_raw tactic theorems goal =
  NTactical.DETERM (tactic (invocation_claset theorems)) goal

fun public tactic = markerLib.ABBRS_THEN (public_raw tactic)

fun SAFE_TAC theorems = public safe_tac theorems
fun CLARIFY_TAC theorems = public clarify_tac theorems
fun SAFE_STEP_TAC theorems = public safe_step_tac theorems
fun CLARIFY_STEP_TAC theorems = public clarify_step_tac theorems
fun STEP_TAC theorems = public step_tac theorems
fun SLOW_STEP_TAC theorems = public slow_step_tac theorems
fun INST_STEP_TAC theorems = public inst_step_tac theorems

fun FAST_TAC theorems = public fast_tac theorems
fun SLOW_TAC theorems = public slow_tac theorems
fun BEST_TAC theorems = public best_tac theorems
fun SLOW_BEST_TAC theorems = public slow_best_tac theorems
fun FIRST_BEST_TAC theorems = public first_best_tac theorems
fun ASTAR_TAC theorems = public astar_tac theorems
fun SLOW_ASTAR_TAC theorems = public slow_astar_tac theorems
fun DEEPEN_TAC theorems =
  public (fn cs => deepen_tac cs {start = 4}) theorems

end
