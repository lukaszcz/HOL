(* Public-API trigger: the compiler listing comes from private simpLib's
   source use, never closures, heap scanning, or timed workloads. *)
local
  open HolKernel Parse boolLib simpLib
  val _ = new_theory "core_assembly"
  fun constant name = (new_constant (name,bool); mk_const (name,bool))
  val p = constant "assembly_p"
  val q = constant "assembly_q"
  val r = constant "assembly_r"
  val s = constant "assembly_s"
  val pq = ASSUME (mk_eq (p,q))
  val rs = ASSUME (mk_eq (r,s))
  val both = CONJ pq rs
  val pq = CONJUNCT1 both
  val rs = CONJUNCT2 both
  fun same (a,b) = aconv (concl a) (concl b) andalso
    HOLset.equal (hypset a,hypset b)
  fun apply ss tm = Conv.QCONV (SIMP_CONV ss []) tm
  val named = rewrites_with_names
    [({Thy="bool",Name="assembly_source"},both)]
  val installed = pureSimps.pure_ss ++ named
  val limited = unlimit (limit 0 (installed ++ empty_ssfrag))
  val bounded = pureSimps.pure_ss ++ rewrites [Once both]
  val first = apply bounded p
  val second = apply bounded r
  fun user tm = if aconv tm p then pq else raise Conv.UNCHANGED
  fun cv name key = {name=name,key=key,trace=2,conv=K (K user)}
  val keyed = empty_ss ++ conv_ss (cv "assembly_keyed" (SOME ([],p)))
  val unkeyed = empty_ss ++ conv_ss (cv "assembly_unkeyed" NONE)
  val updated = ssf_upd_rewrs List.rev named
  val ac = empty_ss ++ ac_ss [(boolTheory.CONJ_ASSOC,boolTheory.CONJ_SYM)]
in
  val _ = Paired.check "assembly reset"
    (not (!PolyML.Compiler.assemblyCode) andalso
     not (!PolyML.Compiler.codetreeAfterOpt) andalso
     not (!PolyML.Compiler.icode))
  val _ = Paired.check "empty/updaters"
    (same (apply limited p,pq) andalso
     same (apply (empty_ss ++ empty_ssfrag) p,REFL p) andalso
     length (ssfrags_of (installed ++ empty_ssfrag)) =
       length (ssfrags_of installed) + 1 andalso
     length (frag_rewrites updated) = 1)
  val _ = Paired.check "named rewrite maker"
    (same (apply installed p,pq) andalso same (apply installed r,rs))
  val _ = Paired.check "bounded appconv"
    (same (first,pq) andalso same (second,REFL r))
  val _ = Paired.check "user keyed/unkeyed conversions"
    (same (apply keyed p,pq) andalso same (apply unkeyed p,pq))
  val _ = Paired.check "AC compilation" (length (ssfrags_of ac) = 1)
  val _ = Paired.check "persistent original"
    (same (apply installed p,pq) andalso length (frag_rewrites named) = 1)
  val _ = Paired.observe "complete" "TASK16-core-assembly-v1"
end
