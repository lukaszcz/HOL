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

fun has_marker_head marker theorem =
  let val (head, _) = strip_comb (concl theorem)
  in same_const marker head end
  handle HOL_ERR _ => false

fun is_bounded theorem =
  Option.isSome (total BoundedRewrites.DEST_BOUNDED theorem)

fun is_passthrough_marker theorem =
  has_marker_head markerSyntax.AC_tm theorem orelse
  has_marker_head markerSyntax.Cong_tm theorem orelse
  has_marker_head markerSyntax.Split_tm theorem orelse
  Option.isSome (markerLib.destExcl theorem) orelse
  Option.isSome (markerLib.destExclSF theorem) orelse
  Option.isSome (markerLib.destFRAG theorem) orelse
  is_bounded theorem

fun rule_name_exists name cs =
  List.exists (fn (_, (old_name, _)) => name = old_name)
    (clasetLib.rules_of cs)

fun next_extra_name cs index =
  let val name = "__classical_extra_" ^ Int.toString index
  in
    if rule_name_exists name cs then next_extra_name cs (index + 1)
    else (name, index + 1)
  end

fun add_plain_theorems theorems cs =
  let
    fun add (theorem, (current, index)) =
      if is_passthrough_marker theorem then (current, index)
      else
        let val (name, next) = next_extra_name current index
        in
          (clasetLib.add_intros [(name, theorem)] current, next)
        end
  in
    #1 (List.foldl add (cs, 0) theorems)
  end

fun invocation_claset theorems =
  let
    val (tagged, leftovers) =
      clasetLib.process_claset_tags theorems (clasetLib.the_claset ())
  in
    add_plain_theorems leftovers tagged
  end

fun public tactic theorems goal =
  NTactical.DETERM (tactic (invocation_claset theorems)) goal

fun SAFE_TAC theorems = public safe_tac theorems
fun CLARIFY_TAC theorems = public clarify_tac theorems
fun SAFE_STEP_TAC theorems = public safe_step_tac theorems
fun CLARIFY_STEP_TAC theorems = public clarify_step_tac theorems

end
