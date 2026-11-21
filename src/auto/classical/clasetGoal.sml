structure clasetGoal :> clasetGoal =
struct

open Abbrev HolKernel boolSyntax

type store = clasetMeta.store
type meta = clasetMeta.meta
type tymeta = clasetMeta.tymeta

type cgoal = {params : term list, asl : term list, w : term}
type replay_script = clasetReplay.script
type exact_prefix_descriptor = clasetReplay.exact_prefix_descriptor
type exact_prefix_rebuild = clasetReplay.exact_prefix_rebuild
type binding_mark = {terms : meta list, types : tymeta list}
type binding_marks = binding_mark list
type spellings = {conclusion : term list, assumptions : term list list}

datatype node =
  Node of {goals : cgoal list,
           store : store,
           replay : replay_script,
           size : {total : int, unchanged : bool} option ref,
           level : int,
           paths : int list list,
           marks : binding_marks,
           avoids : term HOLset.set,
           rendering : term option ref,
           (* A rendering and its lookup spellings are pure functions of
              the node's goals and store, and every rule query of an
              expansion asks for both, so each is computed once per
              position. *)
           renders : (int * (term list * term)) list ref,
           spellings : (int * spellings) list ref}

fun norm_term store tm =
  let
    (* Preserve structure sharing when the store leaves a term alone. *)
    fun recurse current =
      case dest_term current of
          COMB (operator, operand) =>
            let
              val operator' = recurse operator
              val operand' = recurse operand
              val combination =
                if Portable.pointer_eq (operator', operator) andalso
                   Portable.pointer_eq (operand', operand)
                then current
                else mk_comb (operator', operand')
            in
              if is_abs operator' then recurse (beta_conv combination)
              else combination
            end
        | LAMB (bvar, body) =>
            let
              val body' = recurse body
            in
              if Portable.pointer_eq (body', body) then current
              else mk_abs (bvar, body')
            end
        | _ => current
  in
    recurse (clasetMeta.instantiate store tm)
  end

val term_size = HolKernel.term_size

fun cgoal_size size_of ({asl, w, ...} : cgoal) =
  List.foldl
    (fn (asm, total) => size_of asm + total)
    (size_of w) asl

fun goals_size store goals =
  let
    val unchanged = ref true
    fun normalized_size tm =
      let
        val normalized = norm_term store tm
        val _ =
          if !unchanged andalso not (Portable.pointer_eq (tm, normalized))
          then unchanged := false
          else ()
      in
        term_size normalized
      end
    val total =
      List.foldl (fn (goal, total) => cgoal_size normalized_size goal + total)
        0 goals
  in
    {total = total, unchanged = !unchanged}
  end

val empty_mark = {terms = [], types = []}
fun fresh_marks goals = map (fn _ => empty_mark) goals

fun cgoal_terms ({params, asl, w} : cgoal) = params @ (w :: asl)

fun avoid_goals goals avoids =
  Term.FVL (List.concat (map cgoal_terms goals)) avoids

fun register_eigens [] store = SOME store
  | register_eigens (param :: rest) store =
      if clasetMeta.is_eigen store param then register_eigens rest store
      else
        case clasetMeta.register_eigen param store of
            NONE => NONE
          | SOME next => register_eigens rest next

fun register_params goals store =
  case register_eigens (List.concat (map #params goals)) store of
      SOME store' => store'
    | NONE =>
        raise mk_HOL_ERR "clasetGoal" "make_node"
          "a goal parameter is not a fresh variable"

fun register_fresh bound avoids store =
  let
    fun attempt names =
      let
        val fresh = variant names bound
      in
        if clasetMeta.is_meta fresh then
          raise mk_HOL_ERR "clasetGoal" "register_fresh"
            "a binder uses the reserved metavariable prefix"
        else
          case clasetMeta.register_eigen fresh store of
              SOME store' => (fresh, store')
            | NONE => attempt (fresh :: names)
      end
  in
    attempt (HOLset.listItems avoids)
  end

fun make_node goals store replay level paths marks avoids =
  if length goals <> length marks orelse length goals <> length paths then
    raise mk_HOL_ERR "clasetGoal" "make_node"
      "search bookkeeping does not correspond to the open goals"
  else
    let
      val store' = register_params goals store
    in
      Node {goals = goals, store = store', replay = replay,
            size = ref NONE, level = level, paths = paths,
            marks = marks, avoids = avoids, rendering = ref NONE,
            renders = ref [], spellings = ref []}
    end

fun root_paths goals =
  let
    fun enumerate _ [] = []
      | enumerate index (_ :: rest) =
          [index] :: enumerate (index + 1) rest
  in
    enumerate 0 goals
  end

(* The engine's terms are reduced; a goal used to arrive as written, so a
   redex the goal carried stayed in the state and no step could see past
   it.  [reduce_conv] is the same normal form an instantiated rule is
   put in, which is what lets a rule and a goal position meet.  A
   residual goal is carried back to the form the caller posed by
   [clasetNorm.align_conclusion]. *)
fun reduced term = rhs (concl (clasetNorm.goal_reduce_conv term))

fun from_goal (asl, w) =
  let val cgoals = [{params = [], asl = map reduced asl, w = reduced w}]
  in
    make_node cgoals clasetMeta.empty (clasetReplay.empty 1) 0
      (root_paths cgoals) (fresh_marks cgoals)
      (avoid_goals cgoals Term.empty_tmset)
  end

fun create {goals, store, level} =
  make_node goals store (clasetReplay.empty (length goals)) level
    (root_paths goals) (fresh_marks goals) (avoid_goals goals Term.empty_tmset)

fun goals (Node {goals, ...}) = goals
fun child_count parent child =
  Int.max (0, length (goals child) - length (goals parent) + 1)
fun store (Node {store, ...}) = store
fun replay (Node {replay, ...}) = replay
fun replay_length node = clasetReplay.length (replay node)
fun level (Node {level, ...}) = level
fun goal_paths (Node {paths, ...}) = paths
fun binding_marks (Node {marks, ...}) = marks
fun size (Node {size, goals, store, ...}) =
  case !size of
      SOME {total, ...} => total
    | NONE =>
        let
          val computed = goals_size store goals
          val _ = size := SOME computed
        in
          #total computed
        end
fun avoids (Node {avoids, ...}) = avoids

fun fresh_eigen node bound =
  register_fresh bound (avoids node) (store node)

fun set_store store'
  (Node {goals, replay, level, paths, marks, avoids, ...}) =
  make_node goals store' replay level paths marks avoids

fun set_level level'
  (Node {goals, store, replay, size, paths, marks, avoids,
         rendering, renders, spellings, ...}) =
  (* Goals and store are unchanged, so their cached derivatives remain
     valid. *)
  Node {goals = goals, store = store, replay = replay, size = size,
        level = level', paths = paths, marks = marks, avoids = avoids,
        rendering = rendering, renders = renders, spellings = spellings}

fun set_binding_marks marks'
  (Node {goals, store, replay, size, level, paths, avoids,
         rendering, renders, spellings, ...}) =
  Node {goals = goals, store = store, replay = replay, size = size,
        level = level, paths = paths, marks = marks', avoids = avoids,
        rendering = rendering, renders = renders, spellings = spellings}

fun record_step record
  (Node {goals, store, replay, size, level, paths, marks, avoids,
         rendering, renders, spellings}) =
  Node
    {goals = goals, store = store,
     replay = clasetReplay.append replay record, size = size,
     level = level, paths = paths, marks = marks, avoids = avoids,
     rendering = rendering, renders = renders, spellings = spellings}

fun nth1 function_name =
  clasetNorm.nth1 ("clasetGoal", function_name)

fun goal_at node pos = nth1 "goal_at" (goals node) pos

(* Whether what the goal at [pos] claims still carries an unknown.
   Nothing in such a conclusion constrains that unknown, so the only
   step that closes the goal is one that guesses it; an unknown in the
   assumptions is the opposite case, since a step reading the
   assumption against the conclusion settles it. *)
fun stands_on_unknown node pos =
  let
    val {w, ...} = goal_at node pos : cgoal
  in
    not (null (clasetMeta.metas_of (store node) w))
  end

fun delete_nth function_name pos values =
  clasetNorm.delete_nth ("clasetGoal", function_name) values pos

fun splice1 function_name =
  clasetNorm.splice_nth ("clasetGoal", function_name)

fun child_paths parent count =
  if count = 1 then [parent]
  else
    let
      fun enumerate index =
        if index = count then []
        else (parent @ [index]) :: enumerate (index + 1)
    in
      enumerate 0
    end

fun replace_goal node {pos, children, store = store'} =
  let
    val old_goals = goals node
    val old_paths = goal_paths node
    val old_marks = binding_marks node
    val inherited_path = nth1 "replace_goal" old_paths pos
    val inherited_mark = nth1 "replace_goal" old_marks pos
    val goals' = splice1 "replace_goal" old_goals pos children
    val paths' = splice1 "replace_goal" old_paths pos
      (child_paths inherited_path (length children))
    val marks' = splice1 "replace_goal" old_marks pos
      (List.tabulate (length children, fn _ => inherited_mark))
  in
    make_node goals' store' (replay node) (level node) paths' marks'
      (avoid_goals children (avoids node))
  end

fun cons_assumption asm ({params, asl, w} : cgoal) =
  {params = params, asl = asm :: asl, w = w}

fun cons_assumptions assumptions cgoal =
  List.foldl (fn (asm, child) => cons_assumption asm child)
    cgoal assumptions

fun delete_assumption pos ({params, asl, w} : cgoal) =
  {params = params, asl = delete_nth "delete_assumption" pos asl, w = w}

fun append_fresh params [] = params
  | append_fresh params reversed = params @ List.rev reversed

fun children_from initial_avoids
  {parent, premises, consumed, store} =
  let
    val parent' =
      case consumed of
        NONE => parent
      | SOME pos => delete_assumption pos parent
    val normalized = map (norm_term store) premises
    val initial_avoids = Term.FVL normalized initial_avoids

    fun freshen_bound (bound, (avoids, subst, reversed, current_store)) =
      let
        val (fresh, next_store) =
          register_fresh bound avoids current_store
      in
        (HOLset.add (avoids, fresh),
         {redex = bound, residue = fresh} :: subst,
         fresh :: reversed, next_store)
      end

    fun make_child (premise, (rev_children, avoids, current_store)) =
      let
        val (bounds, body) = strip_forall premise
        val (avoids', subst, fresh, next_store) =
          List.foldl freshen_bound (avoids, [], [], current_store) bounds
        val body' = Term.subst subst body
        val (antecedents, conclusion) = strip_imp_only body'
        val base =
          {params = append_fresh (#params parent') fresh,
           asl = #asl parent', w = conclusion}
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

fun exact_blast_children node {pos, premises, prefixes, consumed} =
  let
    val parent = goal_at node pos
    val parent' =
      case consumed of
          NONE => parent
        | SOME assumption => delete_assumption assumption parent
    val normalized = map (norm_term (store node)) premises
    val initial_avoids = Term.FVL normalized (avoids node)

    fun freshen_bound (bound, (avoids, fresh, current_store)) =
      let
        val (variable, next_store) =
          register_fresh bound avoids current_store
      in
        (HOLset.add (avoids, variable), variable :: fresh, next_store)
      end

    fun make_child
          ((premise, descriptor),
           (rev_children, rev_rebuilds, avoids, current_store)) =
      let
        val bounds =
          clasetReplay.exact_prefix_bounds descriptor premise
        val (avoids', reversed, next_store) =
          List.foldl freshen_bound (avoids, [], current_store) bounds
        val fresh = List.rev reversed
        val {assumptions, residual, rebuild} =
          clasetReplay.split_exact_prefix
            {descriptor = descriptor, premise = premise, fresh = fresh}
        val base =
          {params = if null fresh then #params parent'
                    else #params parent' @ fresh,
           asl = #asl parent', w = residual}
        val child = cons_assumptions assumptions base
      in
        (child :: rev_children, rebuild :: rev_rebuilds,
         avoids', next_store)
      end

    val _ =
      if length normalized = length prefixes then ()
      else
        raise mk_HOL_ERR "clasetGoal" "exact_blast_children"
          "premise and prefix-descriptor arities differ"
    val (rev_children, rev_rebuilds, _, final_store) =
      List.foldl make_child ([], [], initial_avoids, store node)
        (ListPair.zip (normalized, prefixes))
  in
    (List.rev rev_children, final_store, List.rev rev_rebuilds)
  end

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

fun render_cgoal (Node {size, store, ...}) ({asl, w, ...} : cgoal) =
  (* Sizing already normalized all of these terms.  A flag suffices to
     reuse the originals when normalization left them unchanged. *)
  case !size of
      SOME {unchanged = true, ...} => (asl, w)
    | _ => (map (norm_term store) asl, norm_term store w)

fun canonical_cgoal node (goal as {params, ...} : cgoal) =
  let
    val params' = map (norm_term (store node)) params
    val (asl, w) = render_cgoal node goal
    val body = mk_conj (encode_list asl, mk_conj (T, w))
  in
    list_mk_forall (params', body)
  end

fun canonical_rendering
      (node as Node {rendering, ...}) =
  case !rendering of
      SOME cached => cached
    | NONE =>
        let
          val computed =
            encode_list (map (canonical_cgoal node) (goals node))
          val _ = rendering := SOME computed
        in
          computed
        end

fun equal (left, right) =
  size left = size right andalso
  aconv (canonical_rendering left) (canonical_rendering right)

fun compare (left, right) =
  case Int.compare (size left, size right) of
    EQUAL => Term.compare (canonical_rendering left,
                           canonical_rendering right)
  | order => order

fun render (node as Node {renders, ...}) pos =
  case List.find (fn (cached, _) => cached = pos) (!renders) of
      SOME (_, rendered) => rendered
    | NONE =>
        let
          (* Unbound engine metavariables survive normalization as their
             marked frees.  HOL4 tactics consequently see rigid variables,
             not holes. *)
          val rendered = render_cgoal node (goal_at node pos)
          val _ = renders := (pos, rendered) :: !renders
        in
          rendered
        end

fun lookup_spellings (node as Node {spellings, ...}) pos =
  case List.find (fn (cached, _) => cached = pos) (!spellings) of
      SOME (_, forms) => forms
    | NONE =>
        let
          val (asl, w) = render node pos
          fun spelling conversion tm = rhs (concl (conversion tm))
          fun forms tm =
            Lib.op_mk_set aconv
              [tm, spelling clasetNorm.membership_conv tm,
               spelling clasetNorm.crossed_conv tm,
               spelling clasetNorm.applied_conv tm]
          val computed = {conclusion = forms w, assumptions = map forms asl}
          val _ = spellings := (pos, computed) :: !spellings
        in
          computed
        end

fun marked_terms terms =
  List.filter clasetMeta.is_meta (free_varsl terms)

fun marked_types terms =
  List.filter clasetMeta.is_tymeta
    (List.concat (map type_vars_in_term terms))

fun variable_name variable = fst (dest_var variable)

fun lift_children node pos new_goals =
  let
    val (asl, w) = render node pos
    val {params, ...} = goal_at node pos
    val input_frees = free_varsl (params @ (w :: asl))
    fun lift_child (child_asl, child_w) =
      let
        val new_params =
          List.filter (fn variable => not (tmem variable input_frees))
            (free_varsl (child_w :: child_asl))
      in
        ({params = params @ new_params,
          asl = child_asl, w = child_w}, new_params)
      end
  in
    map lift_child new_goals
  end

fun unrender node pos (result as (new_goals, validation)) =
  let
    val (asl, w) = render node pos
    val input_terms = w :: asl
    val output_terms =
      List.concat
        (map (fn (child_asl, child_w) => child_w :: child_asl)
          new_goals)
    val received_terms = marked_terms input_terms
    val received_types = marked_types input_terms
    val returned_terms = marked_terms output_terms
    val returned_types = marked_types output_terms
    val known_markers =
      List.all (fn tm => tmem tm received_terms) returned_terms
      andalso
      List.all (fn ty => Lib.mem ty received_types) returned_types

    val lifted = lift_children node pos new_goals
    val output_params = List.concat (map #2 lifted)
    val known_variables = avoids node
    val globally_fresh =
      List.all
        (fn variable => not (HOLset.member (known_variables, variable)))
        output_params
  in
    if not known_markers orelse not globally_fresh then NONE
    else
      case register_eigens output_params (store node) of
          NONE => NONE
        | SOME store' =>
            let
              val next =
                replace_goal node
                  {pos = pos, children = map #1 lifted, store = store'}
            in
              if List.null received_terms andalso
                 List.null received_types
              then SOME next
              else
                let
                  val eigenvariables =
                    map (map variable_name o #2) lifted
                  val record =
                    clasetReplay.make_record
                      {kind = clasetReplay.Wrapper, target = pos,
                       consumed = NONE,
                       created = {terms = [], types = []},
                       eigenvariables = eigenvariables,
                       validation = validation,
                       action =
                         clasetReplay.fixed_action_on (asl, w) result,
                       children = map (fn _ => NONE) new_goals}
                in
                  SOME (record_step record next)
                end
            end
  end

end
