structure clasetGoal :> clasetGoal =
struct

open Abbrev HolKernel boolSyntax

type store = clasetMeta.store
type meta = clasetMeta.meta
type tymeta = clasetMeta.tymeta

type cgoal = {params : term list, asl : term list, w : term}
type replay_script = validation list
type binding_mark = {terms : meta list, types : tymeta list}
type binding_marks = binding_mark list

datatype node =
  Node of {goals : cgoal list,
           store : store,
           replay : replay_script,
           size : int,
           level : int,
           marks : binding_marks,
           avoids : term list}

fun norm_term store tm =
  let
    fun recurse current =
      let val current' = clasetMeta.walk store current
      in
        case dest_term current' of
          COMB (operator, operand) =>
            let
              val combination =
                mk_comb (recurse operator, recurse operand)
            in
              if is_abs (#1 (dest_comb combination)) then
                recurse (beta_conv combination)
              else combination
            end
        | LAMB (bvar, body) => mk_abs (bvar, recurse body)
        | _ => current'
      end
  in
    recurse tm
  end

fun term_size tm =
  case dest_term tm of
    COMB (rator, rand) => term_size rator + term_size rand
  | LAMB (_, body) => 1 + term_size body
  | _ => 1

fun cgoal_size store ({asl, w, ...} : cgoal) =
  List.foldl
    (fn (asm, total) => term_size (norm_term store asm) + total)
    (term_size (norm_term store w)) asl

fun goals_size store goals =
  List.foldl (fn (cgoal, total) => cgoal_size store cgoal + total)
    0 goals

val empty_mark = {terms = [], types = []}
fun fresh_marks goals = map (fn _ => empty_mark) goals

fun cgoal_terms ({params, asl, w} : cgoal) = params @ (w :: asl)
fun goal_frees goals = free_varsl (List.concat (map cgoal_terms goals))

fun register_param (param, store) =
  if clasetMeta.is_eigen store param then store
  else
    case clasetMeta.register_eigen param store of
      SOME store' => store'
    | NONE =>
        raise mk_HOL_ERR "clasetGoal" "make_node"
          "a goal parameter is not a fresh variable"

fun register_params goals store =
  List.foldl register_param store (List.concat (map #params goals))

fun make_node goals store replay level marks avoids =
  if length goals <> length marks then
    raise mk_HOL_ERR "clasetGoal" "make_node"
      "binding marks do not correspond to the open goals"
  else
    let
      val store' = register_params goals store
      val avoids' = free_varsl (avoids @ goal_frees goals)
    in
      Node {goals = goals, store = store', replay = replay,
            size = goals_size store' goals, level = level, marks = marks,
            avoids = avoids'}
    end

fun from_goal (asl, w) =
  let val cgoals = [{params = [], asl = asl, w = w}]
  in
    make_node cgoals clasetMeta.empty [] 0 (fresh_marks cgoals)
      (goal_frees cgoals)
  end

fun create {goals, store, level} =
  make_node goals store [] level (fresh_marks goals) (goal_frees goals)

fun goals (Node {goals, ...}) = goals
fun store (Node {store, ...}) = store
fun replay (Node {replay, ...}) = replay
fun replay_length node = length (replay node)
fun level (Node {level, ...}) = level
fun binding_marks (Node {marks, ...}) = marks
fun size (Node {size, ...}) = size
fun avoids (Node {avoids, ...}) = avoids

val empty_binding_marks = []

fun set_goals goals'
  (Node {store, replay, level, avoids, ...}) =
  make_node goals' store replay level (fresh_marks goals') avoids

fun set_store store'
  (Node {goals, replay, level, marks, avoids, ...}) =
  make_node goals store' replay level marks avoids

fun set_level level'
  (Node {goals, store, replay, marks, avoids, ...}) =
  make_node goals store replay level' marks avoids

fun set_binding_marks marks'
  (Node {goals, store, replay, level, avoids, ...}) =
  make_node goals store replay level marks' avoids

fun nth1 function_name values pos =
  if pos < 1 then
    raise mk_HOL_ERR "clasetGoal" function_name
      "positions are one-based"
  else
    List.nth (values, pos - 1)
    handle Subscript =>
      raise mk_HOL_ERR "clasetGoal" function_name "position out of range"

fun goal_at node pos = nth1 "goal_at" (goals node) pos

fun splice1 function_name values pos replacements =
  if pos < 1 then
    raise mk_HOL_ERR "clasetGoal" function_name
      "positions are one-based"
  else
    let
      val prefix = List.take (values, pos - 1)
      val suffix = List.drop (values, pos)
    in
      prefix @ replacements @ suffix
    end
    handle Subscript =>
      raise mk_HOL_ERR "clasetGoal" function_name "position out of range"

fun replicate 0 _ = []
  | replicate n value = value :: replicate (n - 1) value

fun replace_goal node {pos, children, store = store'} =
  let
    val old_goals = goals node
    val old_marks = binding_marks node
    val inherited_mark = nth1 "replace_goal" old_marks pos
    val goals' = splice1 "replace_goal" old_goals pos children
    val marks' = splice1 "replace_goal" old_marks pos
      (replicate (length children) inherited_mark)
  in
    make_node goals' store' (replay node) (level node) marks'
      (avoids node)
  end

fun cons_assumption asm ({params, asl, w} : cgoal) =
  {params = params, asl = asm :: asl, w = w}

fun cons_assumptions assumptions cgoal =
  List.foldl (fn (asm, child) => cons_assumption asm child)
    cgoal assumptions

fun delete_nth function_name pos values =
  if pos < 1 then
    raise mk_HOL_ERR "clasetGoal" function_name
      "assumption positions are one-based"
  else
    let
      val prefix = List.take (values, pos - 1)
      val suffix = List.drop (values, pos)
    in
      prefix @ suffix
    end
    handle Subscript =>
      raise mk_HOL_ERR "clasetGoal" function_name
        "assumption position out of range"

fun delete_assumption pos ({params, asl, w} : cgoal) =
  {params = params, asl = delete_nth "delete_assumption" pos asl, w = w}

fun children_from initial_avoids
  {parent, premises, consumed, store} =
  let
    val parent' =
      case consumed of
        NONE => parent
      | SOME pos => delete_assumption pos parent
    val normalized = map (norm_term store) premises
    val initial_avoids =
      free_varsl (initial_avoids @ cgoal_terms parent @ normalized)

    fun register_fresh bound avoids current_store =
      let val fresh = variant avoids bound
      in
        if clasetMeta.is_meta fresh then
          raise mk_HOL_ERR "clasetGoal" "children"
            "a rule binder uses the reserved metavariable prefix"
        else
          case clasetMeta.register_eigen fresh current_store of
            SOME store' => (fresh, store')
          | NONE => register_fresh bound (fresh :: avoids) current_store
      end

    fun freshen_bound (bound, (avoids, subst, params, current_store)) =
      let
        val (fresh, next_store) =
          register_fresh bound avoids current_store
      in
        (fresh :: avoids,
         {redex = bound, residue = fresh} :: subst,
         params @ [fresh], next_store)
      end

    fun make_child (premise, (rev_children, avoids, current_store)) =
      let
        val (bounds, body) = strip_forall premise
        val (avoids', subst, params', next_store) =
          List.foldl freshen_bound
            (avoids, [], #params parent', current_store) bounds
        val body' = Term.subst subst body
        val (antecedents, conclusion) = strip_imp_only body'
        val base =
          {params = params', asl = #asl parent', w = conclusion}
        val child = cons_assumptions antecedents base
      in
        (child :: rev_children, avoids', next_store)
      end

    val (rev_children, _, final_store) =
      List.foldl make_child ([], initial_avoids, store) normalized
  in
    (List.rev rev_children, final_store)
  end

fun children node {pos, premises, consumed} =
  children_from (avoids node)
    {parent = goal_at node pos, premises = premises,
     consumed = consumed, store = store node}

fun elim_children node {pos, premises} =
  let
    val parent = goal_at node pos
    fun alternatives _ [] = []
      | alternatives assumption (major :: rest) =
          let
            val (new_goals, store') =
              children node
                {pos = pos, premises = premises,
                 consumed = SOME assumption}
          in
            {assumption = assumption, major = major,
             children = new_goals, store = store'} ::
            alternatives (assumption + 1) rest
          end
  in
    alternatives 1 (#asl parent)
  end

fun encode_list values =
  List.foldr
    (fn (value, rest) => mk_disj (mk_conj (T, value), rest))
    F values

fun canonical_cgoal store ({params, asl, w} : cgoal) =
  let
    val params' = map (norm_term store) params
    val asl' = map (norm_term store) asl
    val w' = norm_term store w
    val body = mk_conj (encode_list asl', mk_conj (T, w'))
  in
    list_mk_forall (params', body)
  end

fun canonical_rendering node =
  encode_list (map (canonical_cgoal (store node)) (goals node))

fun equal (left, right) =
  size left = size right andalso
  aconv (canonical_rendering left) (canonical_rendering right)

fun compare (left, right) =
  case Int.compare (size left, size right) of
    EQUAL => Term.compare (canonical_rendering left,
                           canonical_rendering right)
  | order => order

fun render node pos =
  let
    val {asl, w, ...} = goal_at node pos
    val store = store node
  in
    (map (norm_term store) asl, norm_term store w)
  end

fun contains_marked_free terms =
  List.exists clasetMeta.is_meta (free_varsl terms)

fun unrender node pos (new_goals, validation) =
  let
    val (asl, w) = render node pos
    val {params, ...} = goal_at node pos
    val input_frees = free_varsl (params @ (w :: asl))
    val clean_input = not (contains_marked_free (w :: asl))
    val clean_output =
      List.all
        (fn (child_asl, child_w) =>
          not (contains_marked_free (child_w :: child_asl)))
        new_goals
    fun is_new variable =
      not (List.exists (fn known => aconv variable known) input_frees)
    fun lift_child (child_asl, child_w) =
      let
        val new_params =
          List.filter is_new (free_varsl (child_w :: child_asl))
      in
        ({params = params @ new_params,
          asl = child_asl, w = child_w}, new_params)
      end
    val lifted = map lift_child new_goals
    val output_params = List.concat (map #2 lifted)
    val globally_fresh =
      List.all
        (fn variable =>
          not (List.exists (fn old => aconv variable old) (avoids node)))
        output_params
  in
    if not clean_input orelse not clean_output orelse not globally_fresh
    then NONE
    else
      let
        val children = map #1 lifted
        val store' =
          List.foldl register_param (store node) output_params
        val node' = replace_goal node
          {pos = pos, children = children, store = store'}
        val Node {goals, store, replay, level, marks, avoids, ...} = node'
      in
        SOME
          (make_node goals store (replay @ [validation]) level marks avoids)
      end
  end

end
