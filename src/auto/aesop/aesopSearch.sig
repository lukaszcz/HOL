signature aesopSearch =
sig
  type cgoal = clasetGoal.cgoal
  type store = clasetMeta.store
  type tree = aesopTree.tree
  type gid = aesopTree.gid

  type rule_source =
    {mode : clasetUnify.mode, cgoal : cgoal, store : store} ->
    aesopRule.ruleset

  datatype next_outcome =
      QueueEmpty of tree
    | ReadyForUnsafe of {goal : gid, tree : tree}
    | NormalisationLimit of
        {goal : gid, tree : tree, iterations : int, rule : string}

  datatype safe_outcome =
      SafeSaturated of tree
    | SafeNormalisationLimit of
        {goal : gid, tree : tree, iterations : int, rule : string}

  (* Process queued goals through normalisation and committed safe
     applications until one goal is ready for unsafe search. *)
  val next_safe :
    {max_depth : int, rules : rule_source} -> tree -> next_outcome

  (* Deterministic normalisation-and-safe saturation.  Goals returned by
     [safe_frontier] are the exact residual frontier. *)
  val safe_saturate :
    {max_depth : int, rules : rule_source} -> tree -> safe_outcome
  val safe_frontier : tree -> (gid * cgoal) list
end
