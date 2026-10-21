open HolKernel boolLib
structure PublicOpening : LegacyOpening = Opening
val _ = Paired.check "complete Opening ascription" true
val p = mk_var ("public_p", bool)
val q = mk_var ("public_q", bool)
val eq = boolSyntax.equality
val cg = DISCH (mk_eq (p, q))
  (AP_TERM (rator (mk_neg p)) (ASSUME (mk_eq (p, q))))
val proc : PublicOpening.congproc =
  PublicOpening.CONGPROC (fn {Rinst, arg} => REFL arg) cg
val _ : Opening.congproc = proc
val th = PublicOpening.EQ_CONGPROC eq
  {solver = ASSUME, freevars = [p], depther = fn _ => REFL} (mk_neg p)
val _ = Paired.check "original congruence procedure record and execution"
  (PublicOpening.samerel eq (PublicOpening.rel_of_congrule cg) andalso
   PublicOpening.nconds_of_congrule cg = 1 andalso
   aconv (concl th) (mk_eq (mk_neg p, mk_neg p)) andalso null (hyp th))
