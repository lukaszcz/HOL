(* load-simpLib: one SIMP_CONV kernel check, equality and hypotheses. *)
val _ = let
  open HolKernel boolLib simpLib
  val a = mk_var ("t33_a", bool)
  val rule = ASSUME (mk_eq (a, mk_var ("t33_b", bool)))
  val th = SIMP_CONV (empty_ss ++ rewrites [rule]) [] a
in t33_check "SIMP_CONV rule" (t33_same (th, rule))
     (Parse.thm_to_string th) end
