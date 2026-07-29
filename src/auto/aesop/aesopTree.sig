signature aesopTree =
sig
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

  type tree

  val empty_dependencies : unit -> dependencies
  val dependencies_of : store -> cgoal -> dependencies
  val dependencies_overlap : dependencies -> dependencies -> bool
  val dependencies_empty : dependencies -> bool
  val assigned_between : store -> store -> dependencies

  (* Priorities are log probabilities.  Norm and safe rules have cost zero. *)
  val extend_priority : real -> aesopRule.rphase -> real

  (* The initial node must contain exactly one goal. *)
  val create :
    {node : clasetGoal.node, unsafe_cursor : rule list} -> tree

  val root : tree -> gid
  val goal : tree -> gid -> goal
  val rapp : tree -> rid -> rapp
  val cluster : tree -> cid -> cluster
  val goals : tree -> goal list
  val rapps : tree -> rapp list
  val clusters : tree -> cluster list

  val child_rapps : tree -> gid -> rid list
  val active_cgoal : goal -> cgoal
  val active_store : goal -> store
  val is_normalised : goal -> bool

  (* Installation creates ordinary children.  Copying extends this single
     boundary in aesopTree without requiring search clients to change. *)
  val install_rapp :
    gid -> rapp_data -> tree ->
    {rapp : rid, goals : gid list, tree : tree}

  val set_normalised :
    gid -> {records : step_record list, cgoal : cgoal, store : store} ->
    tree -> tree
  val set_norm_proved :
    gid -> {records : step_record list, store : store} -> tree -> tree
  val set_safe_done : gid -> bool -> tree -> tree
  val set_unsafe_cursor : gid -> rule list -> tree -> tree
  val set_postponed : gid -> rapp_data list -> tree -> tree
  val set_forwarded : gid -> term list -> tree -> tree

  (* Marks every search phase complete without asserting a state directly.
     The ordinary state equations then decide whether the goal is stuck. *)
  val exhaust_goal : gid -> tree -> tree

  val enqueue_goal : gid -> tree -> tree
  val pop_goal : tree -> gid option * tree

  val goal_irrelevant : tree -> gid -> bool
  val rapp_irrelevant : tree -> rid -> bool
  val cluster_irrelevant : tree -> cid -> bool
end
