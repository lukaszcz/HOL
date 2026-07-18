signature blastSearch =
sig
  type pterm = blastTerm.term
  type var = blastTerm.var
  type goal = Abbrev.goal
  type claset = clasetLib.claset
  type tableau_rule = blastRule.tableau_rule

  type level =
    (pterm * bool) list * (pterm * bool) list

  type branch =
    {pairs : level list,
     lits : pterm list,
     vars : var list,
     lim : int}

  (* T1--T6 of the blast report.  Rule steps always rotate their new
     material; this is implicit because the search has no other mode. *)
  datatype script_step =
      HypSubst
    | CloseAssume
    | CloseContradiction
    | SafeRule of {rule : tableau_rule, updated : bool}
    | DeferGoal
    | UnsafeRule of
        {rule : tableau_rule, updated : bool, duplicate : bool}

  type script = script_step list

  type proof =
    {script : script,
     trace : branch list list,
     depth : int,
     branches_created : int,
     branches_closed : int,
     choices_pruned : int}

  type debug_result =
    {fullTrace : branch list list,
     result : proof option}

  val depth_limit : int ref

  (* Raising this exception in the continuation re-enters the newest
     surviving choice point in prv. *)
  exception PROOF_FAILED

  (* Initial formulae all receive md = true, as in blast.ML:1180-1184. *)
  val initBranch : pterm list * int -> branch

  val searchTerms :
    claset -> int -> pterm list -> (proof -> 'a) -> 'a option
  val searchGoal :
    claset -> int -> goal -> (proof -> 'a) -> 'a option
  val tryGoal : claset -> int -> goal -> proof option
  val debugGoal : claset -> int -> goal -> debug_result

  (* Bounds 0, 1, ... through !depth_limit, as DEEPEN (1, limit). *)
  val deepenGoal : claset -> goal -> (proof -> 'a) -> 'a option

  (* Focused observations of the port's search heuristics. *)
  val instantiationPenalty : int -> int
  val recursivePremise : pterm -> pterm list -> bool
  val requeueGamma :
    pterm * bool -> (pterm * bool) list -> bool ->
    (pterm * bool) list
  val killsAllAlternatives : int -> pterm list list -> bool
  val mayUndo :
    {other_rules : bool, updated : bool,
     old_vars : var list, new_vars : var list} -> bool
  val clashVar : var list -> int * var list -> bool
  val prunePlan :
    {branches : int,
     next_vars : var list,
     trail_mark : int,
     trail : var list,
     choices : (int * int) list} -> (int * int) list
end
