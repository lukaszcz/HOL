(* first-use: first and second SIMP_CONV and SIMP_TAC (pure_ss,
   AND_CLAUSES), timed, each with a kernel check. *)
val _ = let
  open HolKernel boolLib
  val p = mk_var ("t33_p", bool)
  val tm = mk_conj (T, p)
  val goal = mk_eq (tm, p)
  fun ok th tm = null (hyp th) andalso aconv (concl th) tm
  fun conv label = let
    val th = t33_time label (fn () =>
      simpLib.SIMP_CONV pureSimps.pure_ss [boolTheory.AND_CLAUSES] tm)
  in t33_check label (ok th goal) (Parse.thm_to_string th) end
  val tgoal = mk_conj (T, T)
  fun tac label = let
    val th = t33_time label (fn () => t33_solve
      (simpLib.SIMP_TAC pureSimps.pure_ss [boolTheory.AND_CLAUSES])
      ([], tgoal))
  in t33_check label (ok th tgoal) (Parse.thm_to_string th) end
in conv "first-conv"; conv "second-conv"; tac "first-tac";
   tac "second-tac" end
