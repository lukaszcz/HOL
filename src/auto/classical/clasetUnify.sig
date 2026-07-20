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
end
