open HolKernel boolLib
structure PublicTravrules : LegacyTravrules = Travrules
val _ = Paired.check "complete Travrules ascription" true
structure PublicTravReplica =
struct
  datatype preorder = datatype Travrules.preorder
  datatype travrules = datatype Travrules.travrules
end
val PublicTravReplica.PREORDER (relation, trans, refl) =
  PublicTravrules.EQ_preorder
val p = mk_var ("public_p", bool)
val th = trans (refl {Rinst = relation, arg = p}) (REFL p)
val tr : Travrules.travrules = PublicTravReplica.TRAVRULES
  {relations = [PublicTravrules.EQ_preorder],
   congprocs = [Opening.EQ_CONGPROC], weakenprocs = []}
val PublicTravrules.TRAVRULES {relations, congprocs, weakenprocs} =
  PublicTravrules.merge_travrules [tr, PublicTravrules.EQ_tr]
val found : PublicTravrules.preorder =
  PublicTravrules.find_relation relation relations
val rebuilt : PublicTravrules.travrules = PublicTravrules.gen_mk_travrules
  {relations = [found], congprocs = congprocs, weakenprocs = weakenprocs}
val _ : Travrules.travrules =
  PublicTravrules.mk_travrules [found] []
val _ = Paired.check "original traversal datatypes and type identities"
  (PublicTravrules.samerel relation boolSyntax.equality andalso
   not (null relations) andalso not (null congprocs) andalso
   aconv (concl th) (mk_eq (p, p)) andalso null (hyp th))
