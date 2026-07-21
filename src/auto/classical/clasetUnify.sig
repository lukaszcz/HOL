signature clasetUnify =
sig
  type term = Term.term
  type hol_type = Type.hol_type
  type meta = clasetMeta.meta
  type tymeta = clasetMeta.tymeta
  type store = clasetMeta.store

  datatype mode = Match | Unify
  type rule_metas = {terms : meta list, types : tymeta list}
  type config = {mode : mode, rule_metas : rule_metas}

  val unify_types : store -> config -> hol_type * hol_type -> store option
  val unify : store -> config -> term * term -> store option

  (* Diagnostic-only unification timing.  The ordinary unifier above is
     unchanged.  NormalizationSetup covers store-driven type/term
     normalization and the setup immediately surrounding it;
     TraversalDecompositionBinding covers structural descent, store lookup,
     pattern checks and persistent binding construction.  Stores are
     immutable, so a failed call has no rollback traversal or cleanup. *)
  type timed_unification
  type timed_unification_statistics =
    {calls : int,
     failures : int,
     normalization_setup_time : Time.time,
     traversal_decomposition_binding_time : Time.time,
     failure_cleanup_time : Time.time,
     unification_time : Time.time,
     max_normalization_setup_time : Time.time,
     max_traversal_decomposition_binding_time : Time.time,
     max_failure_cleanup_time : Time.time,
     max_unification_time : Time.time}
  type timed_unification_branch_statistics =
    {rigid_type_constructor_mismatches : int,
     protected_applied_meta_unequal_head_fallbacks : int,
     right_pattern_binding_failure_fallbacks : int,
     structural_lambda_descents : int,
     structural_wildcard_mismatches : int}
  (* Clock reads and phase-switch accumulation are diagnostic overhead.
     Clock exceptions are wrapped only so the caller can tunnel them across
     legacy catch-all boundaries; backwards movement is wrapped HOL_ERR. *)
  exception TIMED_UNIFICATION_CALLBACK of exn
  val new_timed_unification : (unit -> Time.time) -> timed_unification
  val unify_timed :
    timed_unification -> store -> config -> term * term -> store option
  val timed_unification_statistics :
    timed_unification -> timed_unification_statistics
  val timed_unification_branch_statistics :
    timed_unification -> timed_unification_branch_statistics

  (* Timed-v3 is an additive, measured-only fork.  Its mutually exclusive
     traversal components are selected at actual operation boundaries;
     [traversal_other] covers only explicit residual operations such as
     free-variable collection and dictionary folding.  There is no
     synthetic initial interval.  Event counts count scoped operation
     intervals, not recursive unifier calls; operation_phase_trace records
     their properly nested Enter/Exit order.
     [binding_operation_failures] counts diagnostic bind, bind_ty and
     register_eigen operations that return NONE; an immutable map update
     itself cannot fail and is never described as rollback. *)
  datatype timed_phase_v3 =
      V3NormalizationSetup
    | V3PersistentStoreLookupWalk
    | V3StructuralDecompositionRecursion
    | V3PatternOccursAllowDecision
    | V3PersistentBindingUpdate
    | V3TraversalOther
  datatype timed_phase_boundary_v3 = V3PhaseEnter | V3PhaseExit
  type timed_unification_v3
  type timed_unification_statistics_v3 =
    {calls : int,
     failures : int,
     normalization_setup_events : int,
     persistent_store_lookup_walk_events : int,
     structural_decomposition_recursion_events : int,
     pattern_occurs_allow_decision_events : int,
     persistent_binding_update_events : int,
     binding_operation_failures : int,
     traversal_other_events : int,
     operation_phase_trace :
       (timed_phase_boundary_v3 * timed_phase_v3) list,
     normalization_setup_time : Time.time,
     persistent_store_lookup_walk_time : Time.time,
     structural_decomposition_recursion_time : Time.time,
     pattern_occurs_allow_decision_time : Time.time,
     persistent_binding_update_time : Time.time,
     traversal_other_time : Time.time,
     traversal_decomposition_binding_time : Time.time,
     failure_cleanup_time : Time.time,
     unification_time : Time.time,
     max_normalization_setup_time : Time.time,
     max_persistent_store_lookup_walk_time : Time.time,
     max_structural_decomposition_recursion_time : Time.time,
     max_pattern_occurs_allow_decision_time : Time.time,
     max_persistent_binding_update_time : Time.time,
     max_traversal_other_time : Time.time,
     max_traversal_decomposition_binding_time : Time.time,
     max_failure_cleanup_time : Time.time,
     max_unification_time : Time.time}
  val new_timed_unification_v3 :
    (unit -> Time.time) -> timed_unification_v3
  val new_timed_unification_v3_with_sink :
    {clock : unit -> Time.time,
     elapsed : Time.time -> unit} -> timed_unification_v3
  val unify_timed_v3 :
    timed_unification_v3 -> store -> config -> term * term -> store option
  val timed_unification_statistics_v3 :
    timed_unification_v3 -> timed_unification_statistics_v3
  val timed_unification_branch_statistics_v3 :
    timed_unification_v3 -> timed_unification_branch_statistics

  (* Timed-v4 is the bounded-summary form of timed-v3.  It uses the same
     operation scopes and counters, but its public statistics type has no
     trace field and its worker never allocates a trace node. *)
  type timed_unification_v4
  type timed_unification_statistics_v4 =
    {calls : int,
     failures : int,
     normalization_setup_events : int,
     persistent_store_lookup_walk_events : int,
     structural_decomposition_recursion_events : int,
     pattern_occurs_allow_decision_events : int,
     persistent_binding_update_events : int,
     binding_operation_failures : int,
     traversal_other_events : int,
     normalization_setup_time : Time.time,
     persistent_store_lookup_walk_time : Time.time,
     structural_decomposition_recursion_time : Time.time,
     pattern_occurs_allow_decision_time : Time.time,
     persistent_binding_update_time : Time.time,
     traversal_other_time : Time.time,
     traversal_decomposition_binding_time : Time.time,
     failure_cleanup_time : Time.time,
     unification_time : Time.time,
     max_normalization_setup_time : Time.time,
     max_persistent_store_lookup_walk_time : Time.time,
     max_structural_decomposition_recursion_time : Time.time,
     max_pattern_occurs_allow_decision_time : Time.time,
     max_persistent_binding_update_time : Time.time,
     max_traversal_other_time : Time.time,
     max_traversal_decomposition_binding_time : Time.time,
     max_failure_cleanup_time : Time.time,
     max_unification_time : Time.time}
  val new_timed_unification_v4 :
    (unit -> Time.time) -> timed_unification_v4
  val new_timed_unification_v4_with_sink :
    {clock : unit -> Time.time,
     elapsed : Time.time -> unit} -> timed_unification_v4
  val unify_timed_v4 :
    timed_unification_v4 -> store -> config -> term * term -> store option
  val timed_unification_statistics_v4 :
    timed_unification_v4 -> timed_unification_statistics_v4
  val timed_unification_branch_statistics_v4 :
    timed_unification_v4 -> timed_unification_branch_statistics
  (* Test seam: this is zero for every bounded timer, independent of work. *)
  val timed_unification_trace_allocations_v4 :
    timed_unification_v4 -> int
end
