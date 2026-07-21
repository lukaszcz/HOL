signature clasetMeta =
sig
  type term = Term.term
  type hol_type = Type.hol_type
  type ('a, 'b) subst = ('a, 'b) Lib.subst

  type meta = term
  type tymeta = hol_type
  type store

  val empty : store
  val new_meta : {allow : term list, ty : hol_type} -> store ->
                 meta * store
  val new_tymeta : store -> tymeta * store
  val bind : meta * term -> store -> store option
  val bind_ty : tymeta * hol_type -> store -> store option
  val register_eigen : term -> store -> store option
  val walk : store -> term -> term
  val norm : store -> term -> term
  val norm_type : store -> hol_type -> hol_type
  val metas_of : store -> term -> meta list
  val is_meta : term -> bool
  val is_tymeta : hol_type -> bool
  val is_eigen : store -> term -> bool
  val ground : store -> store

  (* Measured-only versions used by the timed-v3 unifier.  Each callback
     announces the actual kind of store operation about to run.  Ordinary
     unification continues to use the operations above and acquires no
     callback dispatch. *)
  datatype diagnostic_phase =
      DiagnosticNormalizationSetup
    | DiagnosticStoreLookupWalk
    | DiagnosticPatternOccursAllowDecision
    | DiagnosticPersistentBindingUpdate
    | DiagnosticTraversalOther
  datatype diagnostic_boundary = DiagnosticEnter | DiagnosticExit
  type diagnostic_switch = diagnostic_boundary * diagnostic_phase -> unit
  val norm_type_diagnostic : diagnostic_switch -> store -> hol_type ->
                             hol_type
  val norm_diagnostic : diagnostic_switch -> store -> term -> term
  val is_eigen_diagnostic : diagnostic_switch -> store -> term -> bool
  val bind_diagnostic : diagnostic_switch -> meta * term -> store ->
                        store option
  val bind_ty_diagnostic : diagnostic_switch -> tymeta * hol_type -> store ->
                           store option
  val register_eigen_diagnostic : diagnostic_switch -> term -> store ->
                                  store option

  (* Raw persistent bindings support search-subtree diffs.  Unlike
     [collapse], residues are not normalized, so dependency chains remain
     visible to dynamic pruning. *)
  val bindings : store ->
                 {terms : (meta * term) list,
                  types : (tymeta * hol_type) list}
  val collapse : store ->
                 (hol_type, hol_type) subst * (term, term) subst
end
