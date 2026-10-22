(* Minimal public-API dependency trigger for the regression harness. *)
local
  open simpLib
  val rules = [boolTheory.CONJ_ASSOC, boolTheory.CONJ_SYM]
  fun same (a,b) =
    HolKernel.aconv (Thm.concl a) (Thm.concl b) andalso
    HOLset.equal (Thm.hypset a,Thm.hypset b)
  fun verify label name expected fragment =
    Paired.check label
      (frag_name fragment = name andalso
       ListPair.allEq same (frag_rewrites fragment,expected))
  val original = name_ss "assembly" (rewrites rules)
  val raw = SSFRAG {name=NONE,rewrs=map (fn th => (NONE,th)) rules,
                   convs=[],ac=[],filter=NONE,dprocs=[],congs=[]}
in
  val _ = Paired.check "assembly reset" (not (!PolyML.Compiler.assemblyCode))
  val _ = verify "rewrites/name_ss" (SOME "assembly") rules original
  val _ = verify "SSFRAG" NONE rules raw
  val _ = verify "ssf_upd_rewrs" (SOME "assembly") (List.rev rules)
    (ssf_upd_rewrs List.rev original)
  val _ = verify "merge_ss" (SOME "assembly, assembly") (rules @ rules)
    (merge_ss [original,original])
  val _ = verify "ac_ss" NONE []
    (ac_ss [(boolTheory.CONJ_ASSOC,boolTheory.CONJ_SYM)])
  val _ = verify "persistent original" (SOME "assembly") rules original
  val _ = Paired.observe "complete" "fragment-assembly-v1"
end
