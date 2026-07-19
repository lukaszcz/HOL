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

  type statistics =
    {configured_depth : int,
     maximum_resource_cost : int,
     inferences_performed : int,
     branches_created : int,
     branches_closed : int,
     choices_pruned : int,
     rule_cache_hits : int,
     rule_conversions : int}

  datatype completion = Completed | Interrupted

  type 'a measured_result =
    {completion : completion,
     fullTrace : branch list list,
     result : 'a option,
     statistics : statistics}

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
  (* This and the measured/debug entry points enable internal
     instrumentation.  The legacy searchTerms, searchGoal, tryGoal and
     deepenGoal entry points do not poll a stop predicate or maintain the
     inference/resource counters below.

     Statistics cover the complete fixed-depth run, including work before
     failed reconstruction or final search failure.  configured_depth is
     the supplied bound.  maximum_resource_cost is the largest admitted
     lim charge: configured_depth - lim after a safe or unsafe rule
     application.  It is not ML recursion depth, a formula count, or an
     inference count.  md controls gamma requeueing, but is not itself a
     depth charge.  A closing rule can be admitted with a negative successor
     lim, so the maximum can exceed a nonnegative configured_depth.

     inferences_performed counts committed search transitions: successful
     equality substitutions, literal closures, and safe or unsafe rule
     applications admitted by search control.  Candidate unification failures,
     candidates that unify but are killed by the bound, branch creation,
     queue manipulation and reconstruction are not inferences under this
     counter.  branches_created separately counts tableau branches.

     These are internal search-engine metrics.  For comparison with
     Isabelle's published Table 1, only configured_depth and the
     branches_created value from one completed, fixed-depth run correspond
     to its depth and ntried columns.  maximum_resource_cost and
     inferences_performed are not published Isabelle/Blast statistics, and
     values accumulated across iterative-deepening runs are not Table-1
     values. *)
  val searchGoalWithStats :
    claset -> int -> goal -> (proof -> 'a) ->
    {result : 'a option, statistics : statistics}

  (* Cooperative fixed-depth search.  stop is polled once at every prv
     entry.  A true result ends the run with completion = Interrupted and
     returns counters accumulated up to that poll.  A completed exhaustion
     has completion = Completed and result = NONE.  If debug is false,
     fullTrace is empty.  Exceptions raised by stop propagate unchanged;
     they are never interpreted as search-control exceptions. *)
  val searchGoalMeasured :
    {debug : bool, stop : unit -> bool} ->
    claset -> int -> goal -> (proof -> 'a) -> 'a measured_result
  val searchTermsMeasured :
    {debug : bool, stop : unit -> bool} ->
    claset -> int -> pterm list ->
    (proof -> 'a) -> 'a measured_result
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
