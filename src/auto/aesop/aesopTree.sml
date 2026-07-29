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
   records : step_record list, node : clasetGoal.node}

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

datatype tree =
  Tree of
    {root : gid,
     goals : (gid, goal) Redblackmap.dict,
     rapps : (rid, rapp) Redblackmap.dict,
     clusters : (cid, cluster) Redblackmap.dict,
     queue : queue_entry searchHeap.heap,
     next_gid : int, next_rid : int, next_cid : int,
     next_insertion : int}

val ERR = mk_HOL_ERR "aesopTree"
val root_cluster = 0

fun empty_dependencies () =
  {terms = HOLset.empty Term.compare,
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
      HOLset.fromList Term.compare
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

fun tree_with
      (Tree {root, goals, rapps, clusters, queue, next_gid, next_rid,
             next_cid, next_insertion})
      {goals = goals', rapps = rapps', clusters = clusters',
       queue = queue', next_gid = next_gid', next_rid = next_rid',
       next_cid = next_cid', next_insertion = next_insertion'} =
  Tree
    {root = root, goals = goals', rapps = rapps',
     clusters = clusters', queue = queue',
     next_gid = next_gid', next_rid = next_rid',
     next_cid = next_cid', next_insertion = next_insertion'}

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

fun child_rapps tree parent =
  map #id
    (List.filter
      (fn ({parent = candidate, ...} : rapp) => candidate = parent)
      (rapps tree))

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

fun states_of items get_state = map get_state items

fun same_states left right =
  ListPair.allEq (fn (x, y) => x = y) (left, right)

fun derive_cluster tree ({goals, ...} : cluster) =
  let
    val states = map (#state o goal tree) goals
  in
    if List.exists (fn state => state = Proved) states then Proved
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

fun derive_goal tree (current : goal) =
  let
    val states = map (#state o rapp tree) (child_rapps tree (#id current))
    val norm_proved =
      case #norm current of NormProved _ => true | _ => false
    val exhausted =
      is_normalised current andalso #safe_done current andalso
      null (#unsafe_cursor current) andalso null (#postponed current)
  in
    if norm_proved orelse
       List.exists (fn state => state = Proved) states
    then Proved
    else if exhausted andalso
            List.all (fn state => state = Stuck) states
    then Stuck
    else Unknown
  end

fun refresh_once
      (Tree {root, goals, rapps, clusters, queue, next_gid, next_rid,
             next_cid, next_insertion}) =
  let
    val original =
      Tree
        {root = root, goals = goals, rapps = rapps,
         clusters = clusters, queue = queue, next_gid = next_gid,
         next_rid = next_rid, next_cid = next_cid,
         next_insertion = next_insertion}
    val clusters' =
      Redblackmap.map
        (fn (_, current) =>
          cluster_with_state (derive_cluster original current) current)
        clusters
    val with_clusters =
      Tree
        {root = root, goals = goals, rapps = rapps,
         clusters = clusters', queue = queue, next_gid = next_gid,
         next_rid = next_rid, next_cid = next_cid,
         next_insertion = next_insertion}
    val rapps' =
      Redblackmap.map
        (fn (_, current) =>
          rapp_with_state (derive_rapp with_clusters current) current)
        rapps
    val with_rapps =
      Tree
        {root = root, goals = goals, rapps = rapps',
         clusters = clusters', queue = queue, next_gid = next_gid,
         next_rid = next_rid, next_cid = next_cid,
         next_insertion = next_insertion}
    val goals' =
      Redblackmap.map
        (fn (_, current) =>
          goal_with_state (derive_goal with_rapps current) current)
        goals
  in
    Tree
      {root = root, goals = goals', rapps = rapps',
       clusters = clusters', queue = queue, next_gid = next_gid,
       next_rid = next_rid, next_cid = next_cid,
       next_insertion = next_insertion}
  end

fun node_states tree =
  (states_of (goals tree) #state,
   states_of (rapps tree) #state,
   states_of (clusters tree) #state)

fun states_equal
      ((left_goals, left_rapps, left_clusters),
       (right_goals, right_rapps, right_clusters)) =
  same_states left_goals right_goals andalso
  same_states left_rapps right_rapps andalso
  same_states left_clusters right_clusters

fun refresh tree =
  let
    val next = refresh_once tree
  in
    if states_equal (node_states tree, node_states next) then next
    else refresh next
  end

fun enqueue_goal id
      (tree as
       Tree {goals, rapps, clusters, queue, next_gid, next_rid,
             next_cid, next_insertion, ...}) =
  let
    val current = goal tree id
    val entry =
      {goal = id, prio = #prio current, insertion = next_insertion}
  in
    tree_with tree
      {goals = goals, rapps = rapps, clusters = clusters,
       queue = searchHeap.add entry queue, next_gid = next_gid,
       next_rid = next_rid, next_cid = next_cid,
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

fun term_bound bindings meta =
  List.exists
    (fn (redex, _) => Term.compare (redex, meta) = EQUAL)
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
       HOLset.fromList Term.compare
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

fun split predicate values =
  let
    fun collect [] yes no = (List.rev yes, List.rev no)
      | collect (value :: rest) yes no =
          if predicate value then collect rest (value :: yes) no
          else collect rest yes (value :: no)
  in
    collect values [] []
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
        val (added, untouched) = split (overlaps selected) remaining
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

fun install_rapp parent_id
      ({rule, phase, records, node} : rapp_data)
      (tree as
       Tree {goals, rapps, clusters, queue, next_gid, next_rid,
             next_cid, next_insertion, ...}) =
  let
    val parent = goal tree parent_id
    val _ =
      if #state parent = Unknown then ()
      else
        raise ERR "install_rapp"
          "a rapp can only be installed below an unknown goal"
    val rid = next_rid
    val child_store = clasetGoal.store node
    val child_priority = extend_priority (#prio parent) phase
    val child_cgoals = clasetGoal.goals node

    fun make_child (cgoal, (id, entries, ids)) =
      let
        val child : goal =
          {id = id, cgoal = cgoal, store = child_store,
           level = clasetGoal.level node, prio = child_priority,
           deps = dependencies_of child_store cgoal, copy_of = NONE,
           parent = SOME rid, cluster = root_cluster,
           norm = Unnormalised, safe_done = false,
           unsafe_cursor = [], postponed = [],
           forwarded = #forwarded parent, state = Unknown}
      in
        (id + 1, (id, child) :: entries, id :: ids)
      end

    val (next_gid', child_entries, reversed_child_ids) =
      List.foldl make_child (next_gid, [], []) child_cgoals
    val child_ids = List.rev reversed_child_ids
    val goals_with_children =
      Redblackmap.insertList (goals, List.rev child_entries)
    val provisional =
      Tree
        {root = root tree, goals = goals_with_children, rapps = rapps,
         clusters = clusters, queue = queue, next_gid = next_gid',
         next_rid = next_rid, next_cid = next_cid,
         next_insertion = next_insertion}
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
       assigned = assigned_between (active_store parent) child_store,
       clusters = cluster_ids, state = Unknown}
    val installed =
      Tree
        {root = root tree, goals = clustered_goals,
         rapps = Redblackmap.insert (rapps, rid, current_rapp),
         clusters =
           Redblackmap.insertList
             (clusters, List.rev cluster_entries),
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

fun map_goal id update
      (tree as
       Tree {goals, rapps, clusters, queue, next_gid, next_rid,
             next_cid, next_insertion, ...}) =
  let
    val current = goal tree id
  in
    tree_with tree
      {goals = Redblackmap.insert (goals, id, update current),
       rapps = rapps, clusters = clusters, queue = queue,
       next_gid = next_gid, next_rid = next_rid,
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

fun replace_safe_done safe_done
      ({id, cgoal, store, level, prio, deps, copy_of, parent, cluster,
        norm, unsafe_cursor, postponed, forwarded, state, ...} :
       goal) : goal =
  {id = id, cgoal = cgoal, store = store, level = level, prio = prio,
   deps = deps, copy_of = copy_of, parent = parent, cluster = cluster,
   norm = norm, safe_done = safe_done, unsafe_cursor = unsafe_cursor,
   postponed = postponed, forwarded = forwarded, state = state}

fun set_safe_done id value tree =
  refresh (map_goal id (replace_safe_done value) tree)

fun replace_unsafe_cursor unsafe_cursor
      ({id, cgoal, store, level, prio, deps, copy_of, parent, cluster,
        norm, safe_done, postponed, forwarded, state, ...} : goal) :
      goal =
  {id = id, cgoal = cgoal, store = store, level = level, prio = prio,
   deps = deps, copy_of = copy_of, parent = parent, cluster = cluster,
   norm = norm, safe_done = safe_done, unsafe_cursor = unsafe_cursor,
   postponed = postponed, forwarded = forwarded, state = state}

fun set_unsafe_cursor id value tree =
  refresh (map_goal id (replace_unsafe_cursor value) tree)

fun replace_postponed postponed
      ({id, cgoal, store, level, prio, deps, copy_of, parent, cluster,
        norm, safe_done, unsafe_cursor, forwarded, state, ...} : goal) :
      goal =
  {id = id, cgoal = cgoal, store = store, level = level, prio = prio,
   deps = deps, copy_of = copy_of, parent = parent, cluster = cluster,
   norm = norm, safe_done = safe_done, unsafe_cursor = unsafe_cursor,
   postponed = postponed, forwarded = forwarded, state = state}

fun set_postponed id value tree =
  refresh (map_goal id (replace_postponed value) tree)

fun replace_forwarded forwarded
      ({id, cgoal, store, level, prio, deps, copy_of, parent, cluster,
        norm, safe_done, unsafe_cursor, postponed, state, ...} : goal) :
      goal =
  {id = id, cgoal = cgoal, store = store, level = level, prio = prio,
   deps = deps, copy_of = copy_of, parent = parent, cluster = cluster,
   norm = norm, safe_done = safe_done, unsafe_cursor = unsafe_cursor,
   postponed = postponed, forwarded = forwarded, state = state}

fun set_forwarded id value tree =
  map_goal id (replace_forwarded value) tree

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
    tree'
    |> set_safe_done id true
    |> set_unsafe_cursor id []
    |> set_postponed id []
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

fun pop_goal tree =
  let
    fun pop
          (current as
           Tree {goals, rapps, clusters, queue, next_gid, next_rid,
                 next_cid, next_insertion, ...}) =
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
               queue = queue'', next_gid = next_gid,
               next_rid = next_rid, next_cid = next_cid,
               next_insertion = next_insertion}
          val id = #goal entry
        in
          if goal_irrelevant rest id then pop rest
          else (SOME id, rest)
        end
  in
    pop tree
  end

end
