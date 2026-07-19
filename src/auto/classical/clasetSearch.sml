(*
  Search drivers for the classical reasoner.

  DEPTH_FIRST and DEPTH_SOLVE follow Pure/search.ML lines 38--75:
  an explicit stack of lazy child sequences and duplicate-solution
  suppression.  BEST_FIRST follows lines 180--199, including eager child
  enumeration and deletion of all equal minima.  ASTAR follows lines
  226--249: its sorted frontier inserts new equal-cost entries first and
  suppresses only the first equal-cost duplicate.  DEEPEN follows lines
  147--154 and restarts the bounded search until its first successful bound.

  DEPTH_SOLVE additionally implements dynamic, lossless commitment.  A node
  carries the bindings made while solving its first open goal.  When that
  goal disappears, alternatives in its subtree are discarded exactly when
  no such binding occurs in a remaining goal or in a binding reachable from
  one.  This is the persistent-store counterpart of blast's trail-based
  clashVar/prune test.  Frontier searches do not make per-goal commitments,
  so BEST_FIRST and ASTAR deliberately do not prune.

  This dynamic test supersedes the old static safe_depth_tac DETERM test.
  Isabelle 2005 made rigid goals deterministic, as its comment says.  A 2009
  refactoring inverted that branch and releases since then have cut choices
  precisely for goals containing shared schematic variables.  Keeping the
  actual binding dependency is both stronger and more selective: rigid
  subtrees commit, while shared metavariables retain the needed choices.

  The "classical" trace family is registered by clasetReplay.  Level 1
  reports exhausted/bounded searches, level 2 reports expansions, bounds,
  and pruning, and level 3 prints complete candidate nodes.
*)
structure clasetSearch :> clasetSearch =
struct

open HolKernel

type node = clasetGoal.node
type expansion = node -> node seq.seq

val node_limit = ref 100000
val last_node_count = ref 0
val last_pruning_count = ref 0

fun node_count () = !last_node_count
fun pruning_count () = !last_pruning_count

(* The message is a thunk: at the default trace level neither the goal
   rendering nor the string concatenation is evaluated, and expansion
   tracing runs once per node over the whole search. *)
fun trace level message =
  if level <= Feedback.current_trace "classical" then
    Feedback.HOL_MESG ("Classical reasoner: " ^ message ())
  else ()

fun show_node node =
  Parse.term_to_string (clasetGoal.canonical_rendering node)

fun expansion_trace driver count node =
  (trace 2
     (fn () =>
       driver ^ " expansion " ^ Int.toString count ^
       ", goals=" ^ Int.toString (length (clasetGoal.goals node)) ^
       ", size=" ^ Int.toString (clasetGoal.size node));
   trace 3 (fn () => driver ^ " candidate: " ^ show_node node))

fun member_node node = List.exists (fn old => clasetGoal.equal (node, old))

fun DEPTH_FIRST satisfied expand initial =
  let
    fun depth _ [] = seq.empty
      | depth used (states :: rest) =
          seq.delay
            (fn () =>
              case seq.cases states of
                  NONE => depth used rest
                | SOME (current, siblings) =>
                    if satisfied current andalso
                       not (member_node current used)
                    then
                      seq.cons current
                        (depth (current :: used) (siblings :: rest))
                    else
                      (expansion_trace "depth-first"
                         (length used + 1) current;
                       depth used
                         (expand current :: siblings :: rest)))
  in
    depth [] [seq.result initial]
  end

(* Type instantiation changes the type attached to a marked free.  Its
   reserved name, like a persistent-store key, is its stable identity. *)
fun same_meta left right =
  clasetMeta.is_meta left andalso clasetMeta.is_meta right andalso
  fst (dest_var left) = fst (dest_var right)

fun same_tymeta left right =
  clasetMeta.is_tymeta left andalso clasetMeta.is_tymeta right andalso
  dest_vartype left = dest_vartype right

fun member_meta meta = List.exists (fn old => same_meta meta old)
fun member_tymeta meta = List.exists (fn old => same_tymeta meta old)

fun add_meta (meta, metas) =
  if member_meta meta metas then metas else meta :: metas

fun add_tymeta (meta, metas) =
  if member_tymeta meta metas then metas else meta :: metas

fun union_metas left right = List.foldl add_meta right left
fun union_tymetas left right = List.foldl add_tymeta right left

fun binding_diff old_store new_store =
  let
    val old = clasetMeta.bindings old_store
    val new = clasetMeta.bindings new_store
    fun old_term (meta, _) =
      List.exists (fn (known, _) => same_meta meta known) (#terms old)
    fun old_type (meta, _) =
      List.exists (fn (known, _) => same_tymeta meta known) (#types old)
  in
    {terms = map #1 (List.filter (not o old_term) (#terms new)),
     types = map #1 (List.filter (not o old_type) (#types new))}
  end

fun add_mark
      ({terms = more_terms, types = more_types} : clasetGoal.binding_mark)
      ({terms, types} : clasetGoal.binding_mark) =
  {terms = union_metas more_terms terms,
   types = union_tymetas more_types types}

val empty_mark : clasetGoal.binding_mark = {terms = [], types = []}

fun replicate 0 _ = []
  | replicate count value = value :: replicate (count - 1) value

(* Pruned depth search expands the first open goal.  A one-child transition
   stays in the same subtree and accumulates its bindings.  Branch children
   start fresh marks: bindings made by their parent inference belong to the
   enclosing choice point, whose store diff is checked separately. *)
fun note_transition parent child =
  let
    val difference =
      binding_diff (clasetGoal.store parent) (clasetGoal.store child)
    val old_count = length (clasetGoal.goals parent)
    val new_count = length (clasetGoal.goals child)
    val child_count = Int.max (0, new_count - old_count + 1)
    val inherited = clasetGoal.binding_marks child
    val marks =
      if child_count = 1 then
        (case inherited of
             [] => []
           | mark :: rest => add_mark difference mark :: rest)
      else if child_count > 1 then
        replicate child_count empty_mark @
        List.drop (inherited, child_count)
      else inherited
  in
    clasetGoal.set_binding_marks marks
      (clasetGoal.set_level (clasetGoal.level parent + 1) child)
  end

fun goal_terms ({params, asl, w} : clasetGoal.cgoal) =
  params @ (w :: asl)

fun marked_terms terms =
  List.filter clasetMeta.is_meta (free_varsl terms)

fun marked_types terms =
  List.filter clasetMeta.is_tymeta
    (List.concat (map type_vars_in_term terms))

fun dependency_closure store goals =
  let
    val all_terms = List.concat (map goal_terms goals)
    val bindings = clasetMeta.bindings store
    val initial_terms = marked_terms all_terms
    val initial_types = marked_types all_terms

    fun term_dependencies known_terms known_types =
      let
        fun add ((redex, residue), (terms, types)) =
          if member_meta redex known_terms then
            (union_metas (marked_terms [residue]) terms,
             union_tymetas (marked_types [residue]) types)
          else (terms, types)
      in
        List.foldl add (known_terms, known_types) (#terms bindings)
      end

    fun type_dependencies known_types =
      let
        fun add ((redex, residue), types) =
          if member_tymeta redex known_types then
            union_tymetas
              (List.filter clasetMeta.is_tymeta (type_vars residue))
              types
          else types
      in
        List.foldl add known_types (#types bindings)
      end

    fun close (terms, types) =
      let
        val (terms', types') = term_dependencies terms types
        val types'' = type_dependencies types'
      in
        if length terms' = length terms andalso
           length types'' = length types
        then (terms', types'')
        else close (terms', types'')
      end
  in
    close (initial_terms, initial_types)
  end

fun mark_clashes child
      ({terms, types} : clasetGoal.binding_mark) =
  let
    val (visible_terms, visible_types) =
      dependency_closure (clasetGoal.store child)
        (clasetGoal.goals child)
  in
    List.exists (fn meta => member_meta meta visible_terms) terms orelse
    List.exists (fn meta => member_tymeta meta visible_types) types
  end

type frame = {source : node option, states : node seq.seq}

fun path_prefix [] _ = true
  | path_prefix _ [] = false
  | path_prefix (part :: path) (other :: candidate) =
      part = other andalso path_prefix path candidate

fun active_completed source child =
  case clasetGoal.goal_paths source of
      [] => false
    | active :: _ =>
        not
          (List.exists (path_prefix active)
            (clasetGoal.goal_paths child))

fun discard_subtree child frames =
  let
    fun discard count [] = (count, [])
      | discard count (frame :: rest) =
          (case #source frame of
               NONE => (count, frame :: rest)
             | SOME source =>
                 if not (active_completed source child) then
                   (count, frame :: rest)
                 else
                   let
                     val difference =
                       binding_diff (clasetGoal.store source)
                         (clasetGoal.store child)
                   in
                     if mark_clashes child difference then
                       (count, frame :: rest)
                     else discard (count + 1) rest
                   end)
  in
    discard 0 frames
  end

fun DEPTH_SOLVE expand initial =
  let
    fun frame_for source =
      {source = SOME source,
       states = seq.map (note_transition source) (expand source)}

    fun depth _ [] = seq.empty
      | depth used ((frame : frame) :: rest) =
          seq.delay
            (fn () =>
              case seq.cases (#states frame) of
                  NONE => depth used rest
                | SOME (current, siblings) =>
                    let
                      val rest0 =
                        {source = #source frame, states = siblings} :: rest
                      val completed =
                        case #source frame of
                            NONE => false
                          | SOME source => active_completed source current
                      val rest1 =
                        if completed then
                          let
                            val (discarded, kept) =
                              discard_subtree current rest0
                            val _ =
                              last_pruning_count :=
                                !last_pruning_count + discarded
                            val _ =
                              if discarded = 0 then ()
                              else
                                trace 2
                                  (fn () =>
                                    "dynamic pruning discarded " ^
                                    Int.toString discarded ^
                                    " choice points")
                          in
                            kept
                          end
                        else rest0
                    in
                      if List.null (clasetGoal.goals current) andalso
                         not (member_node current used)
                      then
                        seq.cons current
                          (depth (current :: used) rest1)
                      else
                        (expansion_trace "depth-solve"
                           (length used + 1) current;
                         depth used (frame_for current :: rest1))
                    end)
  in
    seq.delay
      (fn () =>
        (last_pruning_count := 0;
         depth []
           [{source = NONE, states = seq.result initial}]))
  end

fun list_of sequence =
  case seq.cases sequence of
      NONE => []
    | SOME (value, rest) => value :: list_of rest

fun split_satisfied predicate values =
  let
    fun split [] sats nonsats = (List.rev sats, List.rev nonsats)
      | split (value :: rest) sats nonsats =
          if predicate value then split rest (value :: sats) nonsats
          else split rest sats (value :: nonsats)
  in
    split values [] []
  end

val check_period = 100

fun limit_reached count =
  !node_limit > 0 andalso count >= !node_limit andalso
  (count = !node_limit orelse count mod check_period = 0)

fun allow_expansion driver count node =
  if limit_reached count then
    (last_node_count := count;
     trace 1
       (fn () =>
         driver ^ " stopped at node limit " ^
         Int.toString (!node_limit));
     false)
  else
    (last_node_count := count + 1;
     expansion_trace driver (count + 1) node;
     true)

fun add_nodes values heap =
  List.foldr (fn (node, current) => searchHeap.add node current)
    heap values

fun BEST_FIRST satisfied expand initial =
  let
    fun classify (news, heap, count) =
      let val (solutions, pending) = split_satisfied satisfied news
      in
        if List.null solutions then
          next (add_nodes pending heap, count)
        else seq.fromList solutions
      end

    and next (heap, count) =
      if searchHeap.is_empty heap then
        (last_node_count := count;
         trace 1 (fn () => "best-first search exhausted");
         seq.empty)
      else
        let
          val (minima, remaining) = searchHeap.delete_all_min heap
          val current = hd minima
        in
          if not (allow_expansion "best-first" count current) then
            seq.empty
          else
            classify
              (list_of
                 (seq.map (note_transition current) (expand current)),
               remaining, count + 1)
        end

    fun start () =
      (last_node_count := 0;
       classify
         ([clasetGoal.set_level 0 initial],
          searchHeap.empty clasetGoal.compare, 0))
  in
    seq.delay start
  end

type astar_entry = int * node

fun astar_insert (entry as (cost, node)) [] = [entry]
  | astar_insert (entry as (cost, node))
      ((first as (old_cost, old_node)) :: rest) =
      if old_cost < cost then first :: astar_insert entry rest
      else if old_cost = cost andalso clasetGoal.equal (node, old_node)
      then first :: rest
      else entry :: first :: rest

fun astar_cost node =
  clasetGoal.size node + 5 * clasetGoal.level node

fun astar_add values frontier =
  List.foldr
    (fn (node, current) =>
      astar_insert (astar_cost node, node) current)
    frontier values

fun ASTAR satisfied expand initial =
  let
    fun classify (news, frontier, count) =
      let val (solutions, pending) = split_satisfied satisfied news
      in
        if List.null solutions then next (astar_add pending frontier, count)
        else seq.fromList solutions
      end

    and next ([], count) =
          (last_node_count := count;
           trace 1 (fn () => "A* search exhausted");
           seq.empty)
      | next ((_, current) :: rest, count) =
          if not (allow_expansion "A*" count current) then seq.empty
          else
            classify
              (list_of
                 (seq.map (note_transition current) (expand current)),
               rest, count + 1)

    fun start () =
      (last_node_count := 0;
       classify ([clasetGoal.set_level 0 initial], [], 0))
  in
    seq.delay start
  end

fun DEEPEN (increment, limit) bounded start initial =
  let
    val _ =
      if increment > 0 then ()
      else
        raise mk_HOL_ERR "clasetSearch" "DEEPEN"
          "the increment must be positive"

    fun deepen bound =
      seq.delay
        (fn () =>
          if List.null (clasetGoal.goals initial) then seq.empty
          else if bound > limit then
            (trace 1
               (fn () =>
                 "deepening exhausted at bound " ^ Int.toString limit);
             seq.empty)
          else
            let
              val _ =
                trace 2
                  (fn () => "trying depth bound " ^ Int.toString bound)
            in
              case seq.cases (bounded bound initial) of
                  NONE => deepen (bound + increment)
                | SOME (result, rest) => seq.cons result rest
            end)
  in
    deepen start
  end

end
