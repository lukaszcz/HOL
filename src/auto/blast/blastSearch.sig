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
     rule_conversions : int,
     emergency_cleanup_assignments : int,
     remaining_trail_assignments : int,
     cooperative_checkpoints : int,
     candidate_rules_enumerated : int,
     candidate_conversions_attempted : int,
     safe_rule_attempts : int,
     unsafe_rule_attempts : int,
     rule_unification_attempts : int,
     rule_unification_successes : int,
     equality_substitution_attempts : int,
     equality_substitution_successes : int,
     literal_close_attempts : int,
     literal_close_successes : int}

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

     The phase counters are measured-search diagnostics.  Candidate counts
     exclude pseudo-rules and cache hits; conversion attempts include
     elimination rules rejected during conversion.  Rule-unification counts
     exclude literal closing, which has its own counters.  Equality success
     means a complete substituted branch was produced.  Literal-close
     success means unification found a closer, whether or not later
     backtracking retains it.  cooperative_checkpoints is exactly the number
     of stop-predicate calls.  searchGoalWithStats and ordinary search report
     zero for these measured-only fields.  An attempt is recorded only after
     its immediately preceding cooperative poll succeeds, just before the
     candidate conversion, rule unification, equality substitution, or
     literal-close operation starts.

     These are internal search-engine metrics.  For comparison with
     Isabelle's published Table 1, only configured_depth and the
     branches_created value from one completed, fixed-depth run correspond
     to its depth and ntried columns.  maximum_resource_cost and
     inferences_performed, all phase counters, and values accumulated across
     iterative-deepening runs are not published Isabelle/Blast statistics. *)
  val searchGoalWithStats :
    claset -> int -> goal -> (proof -> 'a) ->
    {result : 'a option, statistics : statistics}

  (* Cooperative fixed-depth search.  stop is polled while translating and
     collecting variables from the initial goal, at every prv entry, and
     between recursive items in normalization, premise construction, gamma
     requeueing, pruning/clash checks, literal insertion and closing, equality
     substitution, rule iteration/unification, net edge/result traversal,
     candidate ordering/conversion, and cached-rule copying.  Measured theorem
     conversion also polls its HOL/type translation, canonical free-variable
     walk, each quantified SPEC/GEN stage, and blast-term bound-variable walks.
     A true result ends the run with completion = Interrupted and returns a
     coherent partial snapshot.  A completed exhaustion has completion =
     Completed and result = NONE.  If debug is false, fullTrace is empty.
     Exceptions raised by stop propagate unchanged; they are never interpreted
     as search-control exceptions.  searchTermsMeasured treats its prototerms
     as caller-owned: interruption and stop-predicate exceptions restore all
     trailed assignments before returning or escaping.  In contrast,
     searchGoalMeasured translates the HOL goal into fresh engine-owned
     prototerms.  On the explicit Interrupted path only, it abandons those
     engine-owned assignments instead of traversing their trail.  With debug
     enabled, fullTrace can expose those prototerms as part of the returned
     snapshot; their cutoff-time bindings are intentionally left intact, but
     no caller-supplied reference is involved.  Predicate and continuation
     exceptions still restore before they propagate unchanged.
     emergency_cleanup_assignments records assignments traversed by exception
     cleanup; normal search backtracking is excluded.
     remaining_trail_assignments records the engine-local trail size when the
     snapshot is assembled.  It is zero after a restored interruption, but
     may be nonzero after an owned interruption or successful continuation.

     This is cooperative timing, not a hard real-time bound.  Polling excludes
     time spent in the arbitrary caller-supplied stop predicate, the arbitrary
     successful continuation and proof reconstruction it may invoke, one
     indivisible HOL kernel or other primitive operation between checkpoints,
     and caller-owned emergency rollback cleanup.  Consequently none of those
     intervals has a latency bound supplied by this API.  Goal-owned explicit
     interruption has no trail-cleanup interval, so once its checkpoint is
     reached the coherent snapshot is assembled without a trail traversal.
     Ordinary and statistics-only search select the original unmeasured worker
     families and do not construct measured local workers. *)
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
