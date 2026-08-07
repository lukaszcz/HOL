structure aesopTree :> aesopTree =
struct

open HolKernel

type term = Term.term
type cgoal = clasetGoal.cgoal
type store = clasetMeta.store
type step_record = clasetReplay.step_record
type rule = aesopRule.rule

type gid = int
type rid = int
type cid = int

datatype node_state = Unknown | Proved | Stuck

type dependencies =
  {terms : clasetMeta.meta HOLset.set,
   types : clasetMeta.tymeta HOLset.set}

datatype norm_state =
    Unnormalised
  | Normalised of
      {records : step_record list, cgoal : cgoal, store : store}
  | NormProved of {records : step_record list, store : store}

type rapp_data =
  {rule : string, phase : aesopRule.rphase,
   records : step_record list, node : clasetGoal.node,
   forwarded : term option}

type goal =
  {id : gid, cgoal : cgoal, store : store, level : int,
   prio : real, deps : dependencies, copy_of : gid option,
   parent : rid option, cluster : cid, norm : norm_state,
   safe_done : bool, unsafe_cursor : rule list,
   postponed : rapp_data list, forwarded : term list,
   state : node_state}

type rapp =
  {id : rid, parent : gid, rule : string, prob : int,
   records : step_record list, store : store,
   created : dependencies, assigned : dependencies,
   clusters : cid list, state : node_state}

type cluster =
  {id : cid, parent : rid, goals : gid list, state : node_state}

type queue_entry = {goal : gid, prio : real, insertion : int}

(* The parent links of goals and rapps, inverted, plus the copy links of
   goals inverted alongside them: [copy_children] sends an original goal to
   the copies of it installed elsewhere in the tree.  All three maps list
   their entries in creation order, which is ascending id order because
   [install_rapp] is the only place either kind of child, or a copy, ever
   appears.  Inverting the copy links matters for cost, not just
   convenience: [derive_goal] reads them on every node of every refresh
   round, and scanning the goal table for [copy_of] there would make each
   round quadratic in trees that routinely reach hundreds of goals. *)
type parent_index =
  {rapp_children : (gid, rid list) Redblackmap.dict,
   goal_children : (rid, gid list) Redblackmap.dict,
   copy_children : (gid, gid list) Redblackmap.dict}

datatype tree =
  Tree of
    {root : gid,
     goals : (gid, goal) Redblackmap.dict,
     rapps : (rid, rapp) Redblackmap.dict,
     clusters : (cid, cluster) Redblackmap.dict,
     index : parent_index,
     queue : queue_entry searchHeap.heap,
     next_gid : int, next_rid : int, next_cid : int,
     next_insertion : int}

val ERR = mk_HOL_ERR "aesopTree"
val root_cluster = 0

(* Dependency sets are keyed on metavariable identity, not on the term
   spelling: the same metavariable reaches them both as [clasetMeta.bindings]
   created it and as a normalized goal now spells it, and those differ once a
   type metavariable inside its type is bound.  Under [Term.compare] the two
   spellings do not meet, and every intersection below silently reports no
   dependency at all. *)
fun empty_dependencies () =
  {terms = HOLset.empty clasetMeta.meta_compare,
   types = HOLset.empty Type.compare}

fun type_dependencies store terms =
  let
    fun from_term (tm, types) =
      HOLset.addList
        (types,
         List.filter clasetMeta.is_tymeta
           (type_vars_in_term (clasetMeta.norm store tm)))
  in
    List.foldl from_term (HOLset.empty Type.compare) terms
  end

(* [clasetMeta.norm] follows both term and type bindings transitively.
   Taking free metavariables after that walk therefore caches precisely the
   unassigned dependency frontier of the goal. *)
fun dependencies_of store ({params, asl, w} : cgoal) =
  let
    val formulas = asl @ [w]
    val terms =
      HOLset.fromList clasetMeta.meta_compare
        (List.concat (map (clasetMeta.metas_of store) formulas))
    val formula_types = type_dependencies store formulas
    fun parameter_type (parameter, types) =
      HOLset.addList
        (types,
         List.filter clasetMeta.is_tymeta
           (Type.type_vars
             (clasetMeta.norm_type store (type_of parameter))))
    val types = List.foldl parameter_type formula_types params
  in
    {terms = terms, types = types}
  end

fun dependencies_overlap
      ({terms = left_terms, types = left_types} : dependencies)
      ({terms = right_terms, types = right_types} : dependencies) =
  not
    (HOLset.isEmpty
       (HOLset.intersection (left_terms, right_terms))) orelse
  not
    (HOLset.isEmpty
       (HOLset.intersection (left_types, right_types)))

fun dependencies_union
      ({terms = left_terms, types = left_types} : dependencies)
      ({terms = right_terms, types = right_types} : dependencies) =
  {terms = HOLset.union (left_terms, right_terms),
   types = HOLset.union (left_types, right_types)}

fun dependencies_intersection
      ({terms = left_terms, types = left_types} : dependencies)
      ({terms = right_terms, types = right_types} : dependencies) =
  {terms = HOLset.intersection (left_terms, right_terms),
   types = HOLset.intersection (left_types, right_types)}

fun dependencies_difference
      ({terms = left_terms, types = left_types} : dependencies)
      ({terms = right_terms, types = right_types} : dependencies) =
  {terms = HOLset.difference (left_terms, right_terms),
   types = HOLset.difference (left_types, right_types)}

fun dependencies_empty ({terms, types} : dependencies) =
  HOLset.isEmpty terms andalso HOLset.isEmpty types

fun extend_priority priority aesopRule.RSafe = priority
  | extend_priority priority (aesopRule.RNorm _) = priority
  | extend_priority priority (aesopRule.RUnsafe percent) =
      if 1 <= percent andalso percent <= 100 then
        priority + Math.ln (Real.fromInt percent / 100.0)
      else
        raise ERR "extend_priority"
          "an unsafe rule percentage must be in the range 1--100"

fun queue_compare
      ({prio = left, insertion = left_count, ...} : queue_entry,
       {prio = right, insertion = right_count, ...} : queue_entry) =
  case Real.compare (right, left) of
      EQUAL => Int.compare (left_count, right_count)
    | result => result

(* Every field but the root is replaced, so a caller that changes the goal
   or rapp table has to say what the parent index becomes. *)
fun tree_with (Tree {root, ...})
      {goals, rapps, clusters, index, queue, next_gid, next_rid,
       next_cid, next_insertion} =
  Tree
    {root = root, goals = goals, rapps = rapps, clusters = clusters,
     index = index, queue = queue, next_gid = next_gid,
     next_rid = next_rid, next_cid = next_cid,
     next_insertion = next_insertion}

fun root (Tree {root, ...}) = root

fun goal (Tree {goals, ...}) id =
  case Redblackmap.peek (goals, id) of
      SOME value => value
    | NONE => raise ERR "goal" ("unknown goal id " ^ Int.toString id)

fun rapp (Tree {rapps, ...}) id =
  case Redblackmap.peek (rapps, id) of
      SOME value => value
    | NONE => raise ERR "rapp" ("unknown rapp id " ^ Int.toString id)

fun cluster (Tree {clusters, ...}) id =
  case Redblackmap.peek (clusters, id) of
      SOME value => value
    | NONE =>
        raise ERR "cluster" ("unknown cluster id " ^ Int.toString id)

fun goals (Tree {goals, ...}) = Redblackmap.listItems' goals
fun rapps (Tree {rapps, ...}) = Redblackmap.listItems' rapps
fun clusters (Tree {clusters, ...}) = Redblackmap.listItems' clusters

fun rapp_count (Tree {rapps, ...}) = Redblackmap.numItems rapps

fun empty_index () : parent_index =
  {rapp_children = Redblackmap.mkDict Int.compare,
   goal_children = Redblackmap.mkDict Int.compare,
   copy_children = Redblackmap.mkDict Int.compare}

fun index_lookup table key =
  case Redblackmap.peek (table, key) of
      NONE => []
    | SOME entries => entries

(* [copy] is fresh and larger than every copy already recorded against
   [original], so appending keeps the copies in id order too. *)
fun index_copy ((original, copy), table) =
  Redblackmap.insert
    (table, original, index_lookup table original @ [copy])

(* [rid] is fresh and larger than every rapp already recorded under
   [parent], so appending keeps the sibling list in id order. *)
fun index_install {parent, rid, children, copies}
      ({rapp_children, goal_children, copy_children} : parent_index)
      : parent_index =
  {rapp_children =
     Redblackmap.insert
       (rapp_children, parent, index_lookup rapp_children parent @ [rid]),
   goal_children = Redblackmap.insert (goal_children, rid, children),
   copy_children = List.foldl index_copy copy_children copies}

fun child_rapps (Tree {index, ...}) parent =
  index_lookup (#rapp_children index) parent

fun rapp_goals (Tree {index, ...}) parent =
  index_lookup (#goal_children index) parent

(* The copies of [original] installed anywhere in the tree.  [install_rapp]
   canonicalises the key through [original_goal], so a copy never keys
   copies of its own and this relation is one level deep. *)
fun copy_goals (Tree {index, ...}) original =
  index_lookup (#copy_children index) original

fun active_cgoal ({cgoal, norm, ...} : goal) =
  case norm of
      Unnormalised => cgoal
    | Normalised {cgoal = result, ...} => result
    | NormProved _ =>
        raise ERR "active_cgoal" "a norm-proved goal has no open cgoal"

fun active_store ({store, norm, ...} : goal) =
  case norm of
      Unnormalised => store
    | Normalised {store = result, ...} => result
    | NormProved {store = result, ...} => result

fun is_normalised ({norm = Unnormalised, ...} : goal) = false
  | is_normalised _ = true

(* Normalisation rewrites a goal in place, so its node keeps the goal's
   level; a rule application descends one level. *)
fun node_at level (goal : goal) =
  clasetGoal.create
    {goals = [active_cgoal goal], store = active_store goal,
     level = level}

fun goal_node (goal : goal) = node_at (#level goal) goal
fun child_node (goal : goal) = node_at (#level goal + 1) goal

fun changed node next =
  null (clasetGoal.goals next) orelse
  not (clasetGoal.equal (node, next))

fun new_free_names (asl, w) goals =
  let
    val old_frees = free_varsl (w :: asl)
    fun is_new variable =
      not (List.exists (fn old => aconv variable old) old_frees)
    fun names (child_asl, child_w) =
      map (fst o dest_var)
        (List.filter is_new (free_varsl (child_w :: child_asl)))
  in
    map names goals
  end

(* One rendered-tactic alternative, as the single-goal replay record that
   reproduces it.  [rendered] is the parent goal the tactic ran on. *)
fun rendered_record node rendered (result as (goals, validation)) =
  Option.map
    (fn next =>
      (clasetReplay.make_record
         {kind = clasetReplay.Wrapper, target = 1, consumed = NONE,
          created = {terms = [], types = []},
          eigenvariables = new_free_names rendered goals,
          validation = validation,
          action = clasetReplay.fixed_action result,
          children = map (fn _ => NONE) goals},
       next))
    (clasetGoal.unrender node 1 result)

fun engine_results step node =
  seq.map
    (fn (record, next) => ([record], next))
    (step (node, 1))

fun rendered_results tactic node =
  let
    val rendered = clasetGoal.render node 1
  in
    seq.mapPartial
      (fn result =>
        Option.map
          (fn (record, next) => ([record], next))
          (rendered_record node rendered result))
      (tactic rendered)
  end

(* One reading of a rule's alternatives for both engine phases: [aesopNorm]
   takes the unique one, the safe phase of [aesopSearch] commits to one and
   its unsafe phase installs them all. *)
fun rule_results ({apply, ...} : rule) node =
  case apply of
      aesopRule.EngineStep step => engine_results step node
    | aesopRule.RenderedTactic tactic =>
        rendered_results tactic node
    | aesopRule.MultiStep steps =>
        seq.flatten
          (seq.fromList (map (fn step => engine_results step node) steps))

fun unique_rule_result rule node =
  case seq.take 2 (rule_results rule node) of
      [result] => SOME result
    | _ => NONE

(* A copied goal discharges its original sibling but is not a child the
   rule action emitted, so replay never descends into one. *)
fun direct_children tree rid =
  List.filter
    (fn id => not (Option.isSome (#copy_of (goal tree id))))
    (rapp_goals tree rid)

fun goal_with_state state
      ({id, cgoal, store, level, prio, deps, copy_of, parent, cluster,
        norm, safe_done, unsafe_cursor, postponed, forwarded, ...} :
       goal) : goal =
  {id = id, cgoal = cgoal, store = store, level = level, prio = prio,
   deps = deps, copy_of = copy_of, parent = parent, cluster = cluster,
   norm = norm, safe_done = safe_done, unsafe_cursor = unsafe_cursor,
   postponed = postponed, forwarded = forwarded, state = state}

fun rapp_with_state state
      ({id, parent, rule, prob, records, store, created, assigned,
        clusters, ...} : rapp) : rapp =
  {id = id, parent = parent, rule = rule, prob = prob,
   records = records, store = store, created = created,
   assigned = assigned, clusters = clusters, state = state}

fun cluster_with_state state
      ({id, parent, goals, ...} : cluster) : cluster =
  {id = id, parent = parent, goals = goals, state = state}

fun same_states left right =
  ListPair.allEq (fn (x, y) => x = y) (left, right)

(* The goals of a cluster are the conjunctive subgoals one rule application
   emitted, coupled by shared metavariables, so all of them must hold.  A
   member proved in a branch that assigned the shared metavariables
   discharges its siblings through the copies [install_rapp] makes of them
   in that branch, and [derive_goal] reads those copies back; the coupling
   therefore needs no weakening here.  Sticking stays the conservative
   all-members reading: a stuck member may yet be discharged by a copy the
   search is still working on. *)
fun derive_cluster tree ({goals, ...} : cluster) =
  let
    val states = map (#state o goal tree) goals
  in
    if List.all (fn state => state = Proved) states then Proved
    else if List.all (fn state => state = Stuck) states then Stuck
    else Unknown
  end

fun derive_rapp tree ({clusters, ...} : rapp) =
  let
    val states = map (#state o cluster tree) clusters
  in
    if List.all (fn state => state = Proved) states then Proved
    else if List.exists (fn state => state = Stuck) states then Stuck
    else Unknown
  end

(* A copy carries the very obligation of its original under a store that
   has assigned more, so proving the copy proves the original.  Reading
   that back here is what lets a cluster be the plain conjunction its
   subgoals are: the branch that assigns the shared metavariables proves
   the copies it made, and the originals become proved with them.
   Sticking deliberately ignores copies -- a goal whose own alternatives
   are exhausted is stuck until some copy of it is actually proved, and
   the copy's branch may still be under search. *)
fun derive_goal tree (current : goal) =
  let
    val states = map (#state o rapp tree) (child_rapps tree (#id current))
    val copy_states = map (#state o goal tree) (copy_goals tree (#id current))
    val norm_proved =
      case #norm current of NormProved _ => true | _ => false
    val exhausted =
      is_normalised current andalso #safe_done current andalso
      null (#unsafe_cursor current) andalso null (#postponed current)
  in
    if norm_proved orelse
       List.exists (fn state => state = Proved) states orelse
       List.exists (fn state => state = Proved) copy_states
    then Proved
    else if exhausted andalso
            List.all (fn state => state = Stuck) states
    then Stuck
    else Unknown
  end

fun refresh_once
      (tree as
       Tree {goals, rapps, clusters, index, queue, next_gid, next_rid,
             next_cid, next_insertion, ...}) =
  let
    fun rebuild (new_goals, new_rapps, new_clusters) =
      tree_with tree
        {goals = new_goals, rapps = new_rapps, clusters = new_clusters,
         index = index, queue = queue, next_gid = next_gid,
         next_rid = next_rid, next_cid = next_cid,
         next_insertion = next_insertion}
    val clusters' =
      Redblackmap.map
        (fn (_, current) =>
          cluster_with_state (derive_cluster tree current) current)
        clusters
    val with_clusters = rebuild (goals, rapps, clusters')
    val rapps' =
      Redblackmap.map
        (fn (_, current) =>
          rapp_with_state (derive_rapp with_clusters current) current)
        rapps
    val with_rapps = rebuild (goals, rapps', clusters')
    val goals' =
      Redblackmap.map
        (fn (_, current) =>
          goal_with_state (derive_goal with_rapps current) current)
        goals
  in
    rebuild (goals', rapps', clusters')
  end

fun node_states tree =
  (map #state (goals tree),
   map #state (rapps tree),
   map #state (clusters tree))

fun states_equal
      ((left_goals, left_rapps, left_clusters),
       (right_goals, right_rapps, right_clusters)) =
  same_states left_goals right_goals andalso
  same_states left_rapps right_rapps andalso
  same_states left_clusters right_clusters

(* The states of the input are already known to every round but the first,
   so the fixpoint carries them instead of recomputing them. *)
fun refresh tree =
  let
    fun iterate (states, current) =
      let
        val next = refresh_once current
        val next_states = node_states next
      in
        if states_equal (states, next_states) then next
        else iterate (next_states, next)
      end
  in
    iterate (node_states tree, tree)
  end

fun enqueue_goal id
      (tree as
       Tree {goals, rapps, clusters, index, queue, next_gid, next_rid,
             next_cid, next_insertion, ...}) =
  let
    val current = goal tree id
    val entry =
      {goal = id, prio = #prio current, insertion = next_insertion}
  in
    tree_with tree
      {goals = goals, rapps = rapps, clusters = clusters,
       index = index, queue = searchHeap.add entry queue,
       next_gid = next_gid, next_rid = next_rid, next_cid = next_cid,
       next_insertion = next_insertion + 1}
  end

fun create {node, unsafe_cursor} =
  case clasetGoal.goals node of
      [cgoal] =>
        let
          val store = clasetGoal.store node
          val initial : goal =
            {id = 1, cgoal = cgoal, store = store,
             level = clasetGoal.level node, prio = 0.0,
             deps = dependencies_of store cgoal, copy_of = NONE,
             parent = NONE, cluster = root_cluster,
             norm = Unnormalised, safe_done = false,
             unsafe_cursor = unsafe_cursor, postponed = [],
             forwarded = [], state = Unknown}
          val queue =
            searchHeap.add
              {goal = 1, prio = 0.0, insertion = 0}
              (searchHeap.empty queue_compare)
        in
          Tree
            {root = 1,
             goals =
               Redblackmap.insert
                 (Redblackmap.mkDict Int.compare, 1, initial),
             rapps = Redblackmap.mkDict Int.compare,
             clusters = Redblackmap.mkDict Int.compare,
             index = empty_index (),
             queue = queue, next_gid = 2, next_rid = 1,
             next_cid = 1, next_insertion = 1}
        end
    | _ =>
        raise ERR "create" "the initial node must contain exactly one goal"

fun add_created
      (record, {terms, types} : dependencies) =
  let
    val created = clasetReplay.created_of record
  in
    {terms = HOLset.addList (terms, #terms created),
     types = HOLset.addList (types, #types created)}
  end

fun created_of records =
  List.foldl add_created (empty_dependencies ()) records

fun cgoal_under store ({params, asl, w} : cgoal) : cgoal =
  {params = map (clasetMeta.norm store) params,
   asl = map (clasetMeta.norm store) asl,
   w = clasetMeta.norm store w}

fun term_bound bindings meta =
  List.exists
    (fn (redex, _) => clasetMeta.meta_compare (redex, meta) = EQUAL)
    (#terms bindings)

fun type_bound bindings tymeta =
  List.exists
    (fn (redex, _) => Type.compare (redex, tymeta) = EQUAL)
    (#types bindings)

fun assigned_between parent_store child_store =
  let
    val parent = clasetMeta.bindings parent_store
    val child = clasetMeta.bindings child_store
  in
    {terms =
       HOLset.fromList clasetMeta.meta_compare
         (map #1
           (List.filter
             (fn (redex, _) => not (term_bound parent redex))
             (#terms child))),
     types =
       HOLset.fromList Type.compare
         (map #1
           (List.filter
             (fn (redex, _) => not (type_bound parent redex))
             (#types child)))}
  end

fun components tree ids =
  let
    fun overlaps selected candidate =
      List.exists
        (fn member =>
          dependencies_overlap
            (#deps (goal tree member)) (#deps (goal tree candidate)))
        selected

    fun close selected remaining =
      let
        val (added, untouched) =
          Lib.partition (overlaps selected) remaining
      in
        if null added then (selected, untouched)
        else close (selected @ added) untouched
      end

    fun partition [] groups = List.rev groups
      | partition (first :: rest) groups =
          let val (group, remaining) = close [first] rest
          in partition remaining (group :: groups)
          end
  in
    partition ids []
  end

fun goal_with_cluster cluster_id
      ({id, cgoal, store, level, prio, deps, copy_of, parent, norm,
        safe_done, unsafe_cursor, postponed, forwarded, state, ...} :
       goal) : goal =
  {id = id, cgoal = cgoal, store = store, level = level, prio = prio,
   deps = deps, copy_of = copy_of, parent = parent,
   cluster = cluster_id, norm = norm, safe_done = safe_done,
   unsafe_cursor = unsafe_cursor, postponed = postponed,
   forwarded = forwarded, state = state}

fun phase_probability aesopRule.RSafe = 100
  | phase_probability (aesopRule.RUnsafe percent) =
      if 1 <= percent andalso percent <= 100 then percent
      else
        raise ERR "install_rapp"
          "an unsafe rule percentage must be in the range 1--100"
  | phase_probability (aesopRule.RNorm _) =
      raise ERR "install_rapp" "normalisation does not create rapp nodes"

fun ancestry tree start =
  let
    fun walk seen id =
      if List.exists (fn known => known = id) seen then
        raise ERR "ancestry" "cycle in goal ancestry"
      else
        case #parent (goal tree id) of
            NONE => []
          | SOME parent =>
              (id, parent) ::
              walk (id :: seen) (#parent (rapp tree parent))
  in
    walk [] start
  end

fun original_goal tree start =
  let
    fun walk seen id =
      if List.exists (fn known => known = id) seen then
        raise ERR "original_goal" "cycle in copy links"
      else
        case #copy_of (goal tree id) of
            NONE => id
          | SOME source => walk (id :: seen) source
  in
    walk [] start
  end

fun take_through_rapp wanted [] = []
  | take_through_rapp wanted (entry :: rest) =
      let val (_, current) = entry
      in
        entry ::
        (if current = wanted then []
         else take_through_rapp wanted rest)
      end

fun copying_sources tree parent_id assigned child_store child_cgoals =
  let
    val parent = goal tree parent_id
    val path = ancestry tree parent_id
    val ancestor_created =
      List.foldl
        (fn ((_, rid), dependencies) =>
          dependencies_union
            dependencies (#created (rapp tree rid)))
        (empty_dependencies ()) path
    val child_dependencies =
      List.foldl
        (fn (cgoal, dependencies) =>
          dependencies_union
            dependencies (dependencies_of child_store cgoal))
        (empty_dependencies ()) child_cgoals
    val relevant_assigned =
      dependencies_intersection assigned (#deps parent)
    (* HOL types are inhabited, so a dropped metavariable needs no
       synthesis goal.  It still drives copying exactly like an
       assignment. *)
    val dropped =
      #deps parent
      |> (fn dependencies =>
            dependencies_difference dependencies relevant_assigned)
      |> (fn dependencies =>
            dependencies_difference dependencies child_dependencies)
      |> (fn dependencies =>
            dependencies_intersection dependencies ancestor_created)
    val copying =
      dependencies_union relevant_assigned dropped
    val not_created =
      dependencies_difference copying ancestor_created
    val creating_path =
      List.filter
        (fn (_, rid) =>
          dependencies_overlap copying (#created (rapp tree rid)))
        path
    val bounded_path =
      if dependencies_empty copying then []
      else if not (dependencies_empty not_created) then path
      else
        case List.rev creating_path of
            [] => path
          | (_, topmost) :: _ =>
              take_through_rapp topmost path
    val path_originals =
      map (fn (id, _) => original_goal tree id) bounded_path

    fun is_path_origin id =
      List.exists (fn path_id => path_id = id) path_originals

    fun sibling_sources (path_goal, parent_rapp) =
      List.filter
        (fn id =>
          id <> path_goal andalso
          dependencies_overlap copying (#deps (goal tree id)))
        (rapp_goals tree parent_rapp)

    fun add_source (id, (seen, sources)) =
      let val original = original_goal tree id
      in
        (* Canonical origins both skip copies of path goals and collapse
           multiple candidates copied from the same goal. *)
        if is_path_origin original orelse
           List.exists (fn known => known = original) seen
        then (seen, sources)
        else (original :: seen, id :: sources)
      end

    val (_, reversed_sources) =
      List.foldl add_source ([], [])
        (List.concat (map sibling_sources bounded_path))
  in
    List.rev reversed_sources
  end

fun install_rapp parent_id
      ({rule, phase, records, node, forwarded} : rapp_data)
      (tree as
       Tree {goals, rapps, clusters, index, queue, next_gid, next_rid,
             next_cid, next_insertion, ...}) =
  let
    val parent = goal tree parent_id
    val _ =
      if #state parent <> Stuck then ()
      else
        raise ERR "install_rapp"
          "a rapp cannot be installed below a stuck goal"
    val rid = next_rid
    val child_store = clasetGoal.store node
    val child_priority = extend_priority (#prio parent) phase
    val child_cgoals = clasetGoal.goals node
    val assigned =
      assigned_between (active_store parent) child_store
    val copy_sources =
      copying_sources tree parent_id assigned child_store child_cgoals
    val child_specs =
      map
        (fn cgoal =>
          (cgoal, NONE,
           case forwarded of
               NONE => #forwarded parent
             | SOME hypothesis => hypothesis :: #forwarded parent))
        child_cgoals
    val copy_specs =
      map
        (fn source =>
          let val source_goal = goal tree source
          in
            (cgoal_under child_store (#cgoal source_goal),
             SOME (original_goal tree source),
             #forwarded source_goal)
          end)
        copy_sources
    val all_specs = child_specs @ copy_specs

    fun make_child
          ((cgoal, copy_of, forwarded), (id, entries, ids)) =
      let
        val child : goal =
          {id = id, cgoal = cgoal, store = child_store,
           level = clasetGoal.level node, prio = child_priority,
           deps = dependencies_of child_store cgoal, copy_of = copy_of,
           parent = SOME rid, cluster = root_cluster,
           norm = Unnormalised, safe_done = false,
           unsafe_cursor = [], postponed = [],
           forwarded = forwarded, state = Unknown}
      in
        (id + 1, (id, child) :: entries, id :: ids)
      end

    val (next_gid', child_entries, reversed_child_ids) =
      List.foldl make_child (next_gid, [], []) all_specs
    val child_ids = List.rev reversed_child_ids
    val ordered_children = List.rev child_entries
    (* The copy links this application adds, for the inverted index.  This
       is the only place a copy is ever created, so the index needs no
       other maintenance. *)
    val copy_links =
      List.mapPartial
        (fn (id, {copy_of, ...} : goal) =>
          Option.map (fn source => (source, id)) copy_of)
        ordered_children
    val goals_with_children =
      Redblackmap.insertList (goals, ordered_children)
    (* The rapp itself is installed below, so [provisional] keeps the old
       index: it exists only to group the new goals by dependency
       overlap, which reads the goal table alone. *)
    val provisional =
      tree_with tree
        {goals = goals_with_children, rapps = rapps,
         clusters = clusters, index = index, queue = queue,
         next_gid = next_gid', next_rid = next_rid,
         next_cid = next_cid, next_insertion = next_insertion}
    val groups = components provisional child_ids

    fun make_cluster
          (members, (id, cluster_entries, goal_map, ids)) =
      let
        val current : cluster =
          {id = id, parent = rid, goals = members, state = Unknown}
        val goal_map' =
          List.foldl
            (fn (gid, map) =>
              Redblackmap.insert
                (map, gid, goal_with_cluster id (goal provisional gid)))
            goal_map members
      in
        (id + 1, (id, current) :: cluster_entries, goal_map',
         id :: ids)
      end

    val (next_cid', cluster_entries, clustered_goals,
         reversed_cluster_ids) =
      List.foldl make_cluster
        (next_cid, [], goals_with_children, []) groups
    val cluster_ids = List.rev reversed_cluster_ids
    val current_rapp : rapp =
      {id = rid, parent = parent_id, rule = rule,
       prob = phase_probability phase, records = records,
       store = child_store, created = created_of records,
       assigned = assigned,
       clusters = cluster_ids, state = Unknown}
    val installed =
      tree_with tree
        {goals = clustered_goals,
         rapps = Redblackmap.insert (rapps, rid, current_rapp),
         clusters =
           Redblackmap.insertList
             (clusters, List.rev cluster_entries),
         index =
           index_install
             {parent = parent_id, rid = rid, children = child_ids,
              copies = copy_links}
             index,
         queue = queue, next_gid = next_gid',
         next_rid = next_rid + 1, next_cid = next_cid',
         next_insertion = next_insertion}
    val queued =
      List.foldl
        (fn (id, current) => enqueue_goal id current)
        installed child_ids
  in
    {rapp = rid, goals = child_ids, tree = refresh queued}
  end

(* [update] rewrites the fields of an existing goal; it neither adds nor
   removes one, and never touches the parent link, so the index stands. *)
fun map_goal id update
      (tree as
       Tree {goals, rapps, clusters, index, queue, next_gid, next_rid,
             next_cid, next_insertion, ...}) =
  let
    val current = goal tree id
  in
    tree_with tree
      {goals = Redblackmap.insert (goals, id, update current),
       rapps = rapps, clusters = clusters, index = index,
       queue = queue, next_gid = next_gid, next_rid = next_rid,
       next_cid = next_cid, next_insertion = next_insertion}
  end

fun replace_norm norm deps
      ({id, cgoal, store, level, prio, copy_of, parent, cluster,
        safe_done, unsafe_cursor, postponed, forwarded, state, ...} :
       goal) : goal =
  {id = id, cgoal = cgoal, store = store, level = level, prio = prio,
   deps = deps, copy_of = copy_of, parent = parent, cluster = cluster,
   norm = norm, safe_done = safe_done, unsafe_cursor = unsafe_cursor,
   postponed = postponed, forwarded = forwarded, state = state}

fun set_normalised id {records, cgoal, store} tree =
  refresh
    (map_goal id
      (replace_norm
        (Normalised {records = records, cgoal = cgoal, store = store})
        (dependencies_of store cgoal))
      tree)

fun set_norm_proved id {records, store} tree =
  refresh
    (map_goal id
      (fn current =>
        replace_norm
          (NormProved {records = records, store = store})
          (#deps current) current)
      tree)

fun replace_search_state {safe_done, unsafe_cursor, postponed}
      ({id, cgoal, store, level, prio, deps, copy_of, parent, cluster,
        norm, forwarded, state, ...} : goal) : goal =
  {id = id, cgoal = cgoal, store = store, level = level, prio = prio,
   deps = deps, copy_of = copy_of, parent = parent, cluster = cluster,
   norm = norm, safe_done = safe_done, unsafe_cursor = unsafe_cursor,
   postponed = postponed, forwarded = forwarded, state = state}

(* The whole safe-phase transition costs one refresh.  Field updates never
   change a derived state by themselves, and the state equations have a
   unique solution for given structural fields, so refreshing after each
   field separately would only repeat the same fixpoint. *)
fun set_search_state id fields tree =
  refresh (map_goal id (replace_search_state fields) tree)

fun set_safe_done id value tree =
  let val {unsafe_cursor, postponed, ...} = goal tree id
  in
    set_search_state id
      {safe_done = value, unsafe_cursor = unsafe_cursor,
       postponed = postponed} tree
  end

fun set_unsafe_cursor id value tree =
  let val {safe_done, postponed, ...} = goal tree id
  in
    set_search_state id
      {safe_done = safe_done, unsafe_cursor = value,
       postponed = postponed} tree
  end

fun exhaust_goal id tree =
  let
    val current = goal tree id
    val tree' =
      if is_normalised current then tree
      else
        set_normalised id
          {records = [], cgoal = #cgoal current, store = #store current}
          tree
  in
    set_search_state id
      {safe_done = true, unsafe_cursor = [], postponed = []} tree'
  end

fun nonterminal state = state = Unknown

fun goal_irrelevant tree id =
  let
    fun goal_path seen gid =
      if List.exists (fn known => known = gid) seen then
        raise ERR "goal_irrelevant" "cycle in goal ancestry"
      else
        let val current = goal tree gid
        in
          not (nonterminal (#state current)) orelse
          (case #parent current of
               NONE => false
             | SOME parent => rapp_path (gid :: seen) parent)
        end
    and rapp_path seen rid =
      let val current = rapp tree rid
      in
        not (nonterminal (#state current)) orelse
        goal_path seen (#parent current)
      end
  in
    goal_path [] id
  end

fun rapp_irrelevant tree id =
  let val current = rapp tree id
  in
    not (nonterminal (#state current)) orelse
    goal_irrelevant tree (#parent current)
  end

fun cluster_irrelevant tree id =
  let val current = cluster tree id
  in
    not (nonterminal (#state current)) orelse
    rapp_irrelevant tree (#parent current)
  end

fun pop_goal_with skip tree =
  let
    fun pop
          (current as
           Tree {goals, rapps, clusters, index, queue, next_gid,
                 next_rid, next_cid, next_insertion, ...}) =
      if searchHeap.is_empty queue then (NONE, current)
      else
        let
          val (entries, queue') = searchHeap.delete_all_min queue
          val entry = hd entries
          val queue'' =
            List.foldl
              (fn (entry, current) => searchHeap.add entry current)
              queue' (tl entries)
          val rest =
            tree_with current
              {goals = goals, rapps = rapps, clusters = clusters,
               index = index, queue = queue'', next_gid = next_gid,
               next_rid = next_rid, next_cid = next_cid,
               next_insertion = next_insertion}
          val id = #goal entry
        in
          if skip rest id then pop rest
          else (SOME id, rest)
        end
  in
    pop tree
  end

fun pop_goal tree = pop_goal_with goal_irrelevant tree

fun pop_goal_including_irrelevant tree =
  pop_goal_with (fn _ => fn _ => false) tree

end
