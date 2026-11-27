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
type wrapper_input =
  {frees : term HOLset.set, types : hol_type list, needs_record : bool}

datatype node =
  Node of {goals : cgoal list,
           goal_count : int,
           store : store,
           replay : replay_script,
           size : {total : int, changed : goal Inttab.table} option ref,
           level : int,
           paths : int list list,
           marks : binding_marks,
           marks_aligned : bool,
           avoids : term HOLset.set,
           rendering : term option ref,
           (* A rendering and its lookup spellings are pure functions of
              the node's goals and store, and every rule query of an
              expansion asks for both, so each is computed once per
              position. *)
           renders : (goal * wrapper_input option) Inttab.table ref,
           spellings : spellings Inttab.table ref}

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

fun goals_size store goals =
  let
    val total = ref 0
    fun size_term tm =
      let
        val normalized = norm_term store tm
      in
        total := !total + term_size normalized;
        normalized
      end
    val size_assumptions =
      Lib.delta_map (fn asm =>
        let val normalized = size_term asm
        in
          if Portable.pointer_eq (asm, normalized) then Lib.SAME
          else Lib.DIFF normalized
        end)
    fun one ({asl, w, ...} : cgoal, (pos, changed)) =
      let
        val w' = size_term w
        val changed' =
          case size_assumptions asl of
              Lib.DIFF asl' => Inttab.update (pos, (asl', w')) changed
            | Lib.SAME =>
                if Portable.pointer_eq (w, w') then changed
                else Inttab.update (pos, (asl, w')) changed
      in
        (pos + 1, changed')
      end
    val (_, changed) = List.foldl one (1, Inttab.empty) goals
  in
    {total = !total, changed = changed}
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

(* Keep the error deferred until a caller uses a mismatched mark list. *)
fun check_marks aligned =
  if aligned then ()
  else
    raise mk_HOL_ERR "clasetGoal" "make_node"
      "search bookkeeping does not correspond to the open goals"

fun make_node goals goal_count store replay level paths marks avoids =
  Node {goals = goals, goal_count = goal_count, store = store, replay = replay,
        size = ref NONE, level = level, paths = paths, marks = marks,
        marks_aligned = true,
        avoids = avoids, rendering = ref NONE, renders = ref Inttab.empty,
        spellings = ref Inttab.empty}

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

fun create {goals, store, level} =
  let val count = length goals
  in
    make_node goals count (register_params goals store)
      (clasetReplay.empty count) level (root_paths goals) (fresh_marks goals)
      (avoid_goals goals Term.empty_tmset)
  end

fun from_goal (asl, w) =
  create
    {goals = [{params = [], asl = map reduced asl, w = reduced w}],
     store = clasetMeta.empty, level = 0}

fun goals (Node {goals, ...}) = goals
fun goal_count (Node {goal_count, ...}) = goal_count
fun child_count parent child =
  Int.max (0, goal_count child - goal_count parent + 1)
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
  (node as Node {goals, goal_count, store, replay, level, paths, marks,
                 marks_aligned, avoids, ...}) =
  (check_marks marks_aligned;
   if Portable.pointer_eq (store, store') then node
   else
     make_node goals goal_count (register_params goals store')
       replay level paths marks avoids)

fun set_level level'
  (Node {goals, goal_count, store, replay, size, paths, marks,
         marks_aligned, avoids, rendering, renders, spellings, ...}) =
  (* Goals and store are unchanged, so their cached derivatives remain
     valid. *)
  Node {goals = goals, goal_count = goal_count, store = store, replay = replay,
        size = size, level = level', paths = paths, marks = marks,
        marks_aligned = marks_aligned,
        avoids = avoids, rendering = rendering, renders = renders,
        spellings = spellings}

fun set_binding_marks marks'
  (Node {goals, goal_count, store, replay, size, level, paths, marks,
         marks_aligned, avoids, rendering, renders, spellings}) =
  let
    (* Search transitions only change a short prefix of an aligned list. *)
    fun same_length (left, right) =
      Portable.pointer_eq (left, right) orelse
      (case (left, right) of
           ([], []) => true
         | (_ :: lefts, _ :: rights) => same_length (lefts, rights)
         | _ => false)
    val aligned =
      if marks_aligned then same_length (marks, marks')
      else length marks' = goal_count
  in
    Node {goals = goals, goal_count = goal_count, store = store,
          replay = replay, size = size, level = level, paths = paths,
          marks = marks', marks_aligned = aligned, avoids = avoids,
          rendering = rendering, renders = renders, spellings = spellings}
  end

fun record_step record
  (Node {goals, goal_count, store, replay, size, level, paths, marks,
         marks_aligned, avoids, rendering, renders, spellings}) =
  Node
    {goals = goals, goal_count = goal_count, store = store,
     replay = clasetReplay.append replay record, size = size,
     level = level, paths = paths, marks = marks,
     marks_aligned = marks_aligned, avoids = avoids,
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

fun replace_goal (node as Node {marks_aligned, ...})
      {pos, children, store = store'} =
  let
    val old_goals = goals node
    val old_paths = goal_paths node
    val old_marks = binding_marks node
    val inherited_path = nth1 "replace_goal" old_paths pos
    val inherited_mark = nth1 "replace_goal" old_marks pos
    val children_count = length children
    val goals' = splice1 "replace_goal" old_goals pos children
    val paths' = splice1 "replace_goal" old_paths pos
      (child_paths inherited_path children_count)
    val marks' = splice1 "replace_goal" old_marks pos
      (List.tabulate (children_count, fn _ => inherited_mark))
    val count' = goal_count node - 1 + children_count
    (* Both the goal and mark lists lost one element and gained one per
       child, so the splice preserves alignment. *)
    val _ = check_marks marks_aligned
    (* The shared store already owns every inherited goal parameter. *)
    val register =
      if Portable.pointer_eq (store node, store') then children else goals'
  in
    make_node goals' count' (register_params register store')
      (replay node) (level node) paths' marks'
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

(* Every premise contributes to freshness, but none need scanning unless
   a child actually introduces a parameter. *)
fun premise_avoids premises initial_avoids NONE =
      Term.FVL premises initial_avoids
  | premise_avoids _ _ (SOME avoids) = avoids

fun children_from initial_avoids
  {parent, premises, consumed, store} =
  let
    val parent' =
      case consumed of
        NONE => parent
      | SOME pos => delete_assumption pos parent
    val normalized = map (norm_term store) premises

    fun freshen_bound (bound, (previous, subst, reversed, current_store)) =
      let
        val avoids = premise_avoids normalized initial_avoids previous
        val (fresh, next_store) =
          register_fresh bound avoids current_store
      in
        (SOME (HOLset.add (avoids, fresh)),
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
      List.foldl make_child ([], NONE, store) normalized
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

    fun freshen_bound (bound, (previous, fresh, current_store)) =
      let
        val avoids = premise_avoids normalized (avoids node) previous
        val (variable, next_store) =
          register_fresh bound avoids current_store
      in
        (SOME (HOLset.add (avoids, variable)), variable :: fresh, next_store)
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
      List.foldl make_child ([], [], NONE, store node)
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

fun render_cgoal (Node {size, store, ...}) pos ({asl, w, ...} : cgoal) =
  case !size of
      SOME {changed, ...} =>
        Option.getOpt (Inttab.lookup changed pos, (asl, w))
    | NONE => (map (norm_term store) asl, norm_term store w)

fun canonical_cgoal node index (goal as {params, ...} : cgoal) =
  let
    val params' = map (norm_term (store node)) params
    val (asl, w) = render_cgoal node (index + 1) goal
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
            encode_list (Lib.mapi (canonical_cgoal node) (goals node))
          val _ = rendering := SOME computed
        in
          computed
        end

fun equal (left, right) =
  goal_count left = goal_count right andalso size left = size right andalso
  aconv (canonical_rendering left) (canonical_rendering right)

fun compare (left, right) =
  case Int.compare (size left, size right) of
    EQUAL => Term.compare (canonical_rendering left,
                           canonical_rendering right)
  | order => order

fun render_entry (node as Node {renders, ...}) pos =
  case Inttab.lookup (!renders) pos of
      SOME rendered => rendered
    | NONE =>
        let
          (* Unbound engine metavariables survive normalization as their
             marked frees.  HOL4 tactics consequently see rigid variables,
             not holes. *)
          val entry = (render_cgoal node pos (goal_at node pos), NONE)
          val _ = renders := Inttab.update (pos, entry) (!renders)
        in
          entry
        end

fun render node pos = #1 (render_entry node pos)

fun render_goals (node as Node {renders, ...}) =
  let
    fun render index goal =
      let val pos = index + 1
      in
        case Inttab.lookup (!renders) pos of
            SOME (rendered, _) => rendered
          | NONE => render_cgoal node pos goal
      end
  in
    Lib.mapi render (goals node)
  end

fun lookup_spellings (node as Node {spellings, ...}) pos =
  case Inttab.lookup (!spellings) pos of
      SOME forms => forms
    | NONE =>
        let
          val (asl, w) = render node pos
          fun spelling conversion tm = rhs (concl (conversion tm))
          fun has_membership tm =
            case dest_term tm of
                CONST _ => same_const tm IN_tm
              | COMB (rator, rand) =>
                  has_membership rator orelse has_membership rand
              | LAMB (_, body) => has_membership body
              | VAR _ => false
          fun applied tm =
            (* Rendering has already reduced beta redexes. An applied
               spelling can change only at a membership subterm. *)
            if has_membership tm then spelling clasetNorm.applied_conv tm
            else tm
          fun forms tm =
            case dest_term tm of
                VAR _ => [tm]
              | CONST _ => [tm]
              | _ =>
                  Lib.op_mk_set aconv
                    [tm, spelling clasetNorm.membership_conv tm,
                     spelling clasetNorm.crossed_conv tm, applied tm]
          val computed = {conclusion = forms w, assumptions = map forms asl}
          val _ = spellings := Inttab.update (pos, computed) (!spellings)
        in
          computed
        end

fun marked_terms terms =
  List.filter clasetMeta.is_meta (free_varsl terms)

fun marked_types terms =
  List.filter clasetMeta.is_tymeta
    (List.concat (map type_vars_in_term terms))

(* Each alternative from a rendered tactic checks the same input frees and
   type markers. Share that scan across alternatives at the same position. *)
fun wrapper_input (Node {renders, ...}) pos (rendered as (asl, w), cached) =
  case cached of
      SOME input => input
    | NONE =>
        let
          val terms = w :: asl
          val frees = FVLset terms
          val types = marked_types terms
          val input =
            {frees = frees, types = types,
             needs_record =
               not (null types) orelse
               Option.isSome (HOLset.find clasetMeta.is_meta frees)}
          val _ =
            renders := Inttab.update (pos, (rendered, SOME input)) (!renders)
        in
          input
        end

fun variable_name variable = fst (dest_var variable)

fun goal_frees (asl, w) = free_varsl (w :: asl)

fun lift_child known params (asl, w) frees =
  let
    val new_params =
      List.filter (fn variable => not (HOLset.member (known, variable))) frees
  in
    ({params = params @ new_params, asl = asl, w = w}, new_params)
  end

fun lift_children node pos new_goals =
  let
    val ((asl, w), cached) = render_entry node pos
    val {params, ...} = goal_at node pos
  in
    if null new_goals then []
    else
      let
        val frees =
          case cached of
              SOME input => #frees input
            | NONE => FVLset (w :: asl)
        val lift = lift_child (Term.FVL params frees) params
      in
        map (fn child => lift child (goal_frees child)) new_goals
      end
  end

local
  exception EscapedMarker
in
fun unrender node pos (result as (new_goals, validation)) =
  let
    val entry as ((asl, w), _) = render_entry node pos
    val {frees = input_frees, types = received_types, needs_record} =
      wrapper_input node pos entry
    val output_terms =
      List.concat
        (map (fn (child_asl, child_w) => child_w :: child_asl)
          new_goals)
    val returned_types = marked_types output_terms
    fun unknown_marker tm =
      clasetMeta.is_meta tm andalso not (HOLset.member (input_frees, tm))
    val known_types = List.all (fn ty => Lib.mem ty received_types)
      returned_types

    val {params, ...} = goal_at node pos
    val lifted =
      if null new_goals then []
      else
        let
          val lift = lift_child (Term.FVL params input_frees) params
          fun check_and_lift child =
            let val frees = goal_frees child
            in
              if List.exists unknown_marker frees then raise EscapedMarker
              else lift child frees
            end
        in
          map check_and_lift new_goals
        end
    val output_params = List.concat (map #2 lifted)
    val known_variables = avoids node
    val globally_fresh =
      List.all
        (fn variable => not (HOLset.member (known_variables, variable)))
        output_params
  in
    if not known_types orelse not globally_fresh then NONE
    else
      case register_eigens output_params (store node) of
          NONE => NONE
        | SOME store' =>
            let
              val next =
                replace_goal node
                  {pos = pos, children = map #1 lifted, store = store'}
            in
              if not needs_record
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
  handle EscapedMarker => NONE
end

end
