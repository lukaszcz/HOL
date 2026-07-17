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
  val walk : store -> term -> term
  val norm : store -> term -> term
  val metas_of : store -> term -> meta list
  val is_meta : term -> bool
  val ground : store -> store
  val collapse : store ->
                 (hol_type, hol_type) subst * (term, term) subst
end
