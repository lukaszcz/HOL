open HolKernel boolLib
structure PublicSimp : LegacySimpLib
  where type ssfrag = simpLib.ssfrag
  where type simpset = simpLib.simpset = simpLib
val _ = Paired.check "complete simpLib ascription" true
val p = mk_var ("public_p", bool)
val rule = CONJUNCT1 (SPEC p boolTheory.AND_CLAUSES)
val kernelname : PublicSimp.thname = {Thy = "bool", Name = "AND_CLAUSES"}
val cd : PublicSimp.convdata =
  {name = "public-conv", key = SOME ([], p), trace = 0,
   conv = fn solver => fn stack => REFL}
val std : PublicSimp.stdconvdata =
  {name = "public-std", pats = [p], conv = REFL}
val relsimp : PublicSimp.relsimpdata =
  {refl = REFL p, trans = REFL p, weakenings = [], subsets = [], rewrs = []}
val controlled : PublicSimp.controlled_thm =
  (boolTheory.AND_CLAUSES, BoundedRewrites.UNBOUNDED)
val _ : BoundedRewrites.controlled_thm = controlled
val reducer = Traverse.REDUCER
  {name = SOME "public-dproc", initial = Fail "public-context",
   addcontext = fn (ctxt, thms) => ctxt,
   apply = fn {solver, conv, context, stack, relation} =>
     fn tm => NO_CONV tm}
val weakener : PublicSimp.weakener_data =
  ([Travrules.EQ_preorder], [], reducer)
val fragment : PublicSimp.ssfrag = PublicSimp.SSFRAG
  {name = SOME "public-frag", convs = [],
   rewrs = [(SOME kernelname, rule)], ac = [],
   filter = NONE, dprocs = [reducer], congs = []}
val _ : simpLib.ssfrag = fragment
val ss : PublicSimp.simpset = PublicSimp.++ (PublicSimp.empty_ss, fragment)
val _ : simpLib.simpset = ss
val cfg : PublicSimp.simptac_config =
  {strip = false, elimvars = false, droptrues = false, oldestfirst = true}
val _ : Abbrev.tactic = PublicSimp.global_simp_tac cfg ss []
val td : Traverse.traverse_data = PublicSimp.traversedata_for_ss ss
val th = PublicSimp.SIMP_CONV ss [] (mk_conj (T, p))
val (number, _) = PublicSimp.track (fn n : int => n + 1) 2
val _ = Paired.check "original simplifier records and ordinary execution"
  (PublicSimp.frag_name fragment = SOME "public-frag" andalso
   length (PublicSimp.frag_rewrites fragment) = 1 andalso number = 3 andalso
   aconv (concl th) (mk_eq (mk_conj (T, p), p)) andalso null (hyp th))
