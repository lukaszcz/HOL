open HolKernel boolLib
structure PublicCong : LegacyCongLib
  where type congset = congLib.congset = congLib
val _ = Paired.check "complete congLib ascription" true
structure PublicCongReplica =
struct
  datatype congsetfrag = datatype congLib.congsetfrag
end
val fragment : PublicCong.congsetfrag = PublicCongReplica.CSFRAG
  {relations = [Travrules.EQ_preorder], rewrs = [], congs = [], dprocs = []}
val _ : congLib.congsetfrag = fragment
val PublicCong.CSFRAG {relations, rewrs, congs, dprocs} = fragment
val cs : PublicCong.congset = PublicCong.mk_congset
  [PublicCong.merge_cs [fragment, PublicCong.csfrag_rewrites []]]
val _ : congLib.congset = cs
val p = mk_var ("public_p", bool)
val input = mk_conj (T, p)
val th = PublicCong.CONGRUENCE_EQ_SIMP_CONV cs boolSimps.bool_ss [] input
val _ = Paired.check "original congruence datatype and simpset identity"
  (length relations = 1 andalso null rewrs andalso null congs andalso
   null dprocs andalso aconv (concl th) (mk_eq (input, p)) andalso
   null (hyp th))
