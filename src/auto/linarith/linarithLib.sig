signature linarithLib =
sig
  include Abbrev

  type linarith_config = linarithData.linarith_config
  val default_config : linarith_config

  type search_stats =
    {nodes : int,
     refutations : int,
     disjunction_splits : int,
     operator_splits : int,
     augmentations : int}
  val last_search_stats : unit -> search_stats

  val LINARITH_TAC : thm list -> tactic
  val SIMPLE_LINARITH_TAC : thm list -> tactic
  val CFG_LINARITH_TAC : linarith_config -> thm list -> tactic

  val LINARITH_PROVE : term -> thm
  val LINARITH_CONV : conv

  datatype budget_outcome =
      LinarithProved of thm
    | LinarithExhausted
    | LinarithLimitReached of
        {kind : searchBudget.kind, usage : searchBudget.usage}

  (* The full splitting search shares one invocation budget with every
     nested certificate search and guard proof.  A proof is returned
     only after replay and reconstruction validate the original term. *)
  val LINARITH_PROVE_BUDGETED :
    searchBudget.budget -> term -> budget_outcome
  (* The explicit-context form composes inside another proof without
     installing an ambient context override. *)
  val LINARITH_PROVE_BUDGETED_IN :
    Context.t -> searchBudget.budget -> term -> budget_outcome

  val CACHED_LINARITH : thm list -> conv
  val LINARITH_REDUCER : Traverse.reducer
  val LINARITH_ss : simpLib.ssfrag
  val linarith_solver : Traverse.ssolver
  val clear_linarith_caches : unit -> unit
end
