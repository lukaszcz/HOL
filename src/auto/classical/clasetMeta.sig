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
  (* Capture-safe transitive store substitution, without beta/eta
     normalization. *)
  val instantiate : store -> term -> term
  val norm : store -> term -> term
  val norm_type : store -> hol_type -> hol_type
  val metas_of : store -> term -> meta list
  val is_meta : term -> bool
  val is_tymeta : hol_type -> bool
  val is_eigen : store -> term -> bool
  val ground : store -> store

  (* Persistent bindings support search-subtree diffs.  Each residue is
     semantically normalized when accepted; as-yet unbound dependencies
     remain visible to dynamic pruning. *)
  val bindings : store ->
                 {terms : (meta * term) list,
                  types : (tymeta * hol_type) list}
  val collapse : store ->
                 (hol_type, hol_type) subst * (term, term) subst
end
