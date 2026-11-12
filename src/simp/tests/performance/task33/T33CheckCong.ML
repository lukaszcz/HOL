(* load-congLib: one CONGRUENCE_EQ_SIMP_CONV kernel check. *)
val _ = let
  open HolKernel boolLib
  val a = mk_var ("t33_a", bool)
  val rule = ASSUME (mk_eq (a, mk_var ("t33_b", bool)))
  val cs = congLib.mk_congset [congLib.csfrag_rewrites [rule]]
  val th = congLib.CONGRUENCE_EQ_SIMP_CONV cs simpLib.empty_ss [] a
in t33_check "CONGRUENCE_EQ_SIMP_CONV rule" (t33_same (th, rule))
     (Parse.thm_to_string th) end
