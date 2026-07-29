signature aesopSearch =
sig
  type cgoal = clasetGoal.cgoal
  type store = clasetMeta.store
  type tree = aesopTree.tree
  type gid = aesopTree.gid
  type tactic = Abbrev.tactic

  type aesop_config = {max_rapps : int, max_depth : int}
  val default_config : aesop_config

  type rule_source =
    {mode : clasetUnify.mode, cgoal : cgoal, store : store} ->
    aesopRule.ruleset

  datatype next_outcome =
      QueueEmpty of tree
    | ReadyForUnsafe of {goal : gid, tree : tree}
    | DepthLimit of {goal : gid, tree : tree}
    | NormalisationLimit of
        {goal : gid, tree : tree, iterations : int, rule : string}

  datatype safe_outcome =
      SafeSaturated of tree
    | SafeDepthLimit of {goal : gid, tree : tree}
    | SafeNormalisationLimit of
        {goal : gid, tree : tree, iterations : int, rule : string}

  datatype failure_reason =
      SearchExhausted
    | RappLimitReached
    | DepthLimitReached

  datatype search_outcome =
      SearchProved of tree
    | SearchFailed of
        {tree : tree, safe_goals : (gid * cgoal) list,
         reason : failure_reason}

  (* Process queued goals through normalisation and committed safe
     applications until one goal is ready for unsafe search. *)
  val next_safe :
    {max_depth : int, rules : rule_source} -> tree -> next_outcome

  (* Deterministic normalisation-and-safe saturation.  Goals returned by
     [safe_frontier] are the exact residual frontier. *)
  val safe_saturate :
    {max_depth : int, rules : rule_source} -> tree -> safe_outcome
  val safe_frontier : tree -> (gid * cgoal) list

  (* Best-first normalisation/safe/unsafe search.  A failed result contains
     the exhaustive normalisation-and-safe frontier of the initial tree. *)
  val search :
    aesop_config -> rule_source -> tree -> search_outcome

  (* Select the winning forest of a proved tree and merge its final stores.
     Replay is exact: a failure after search success is an engine error. *)
  val extract : tree -> clasetReplay.grounded_script
  val REPLAY_TAC : tree -> tactic
end
