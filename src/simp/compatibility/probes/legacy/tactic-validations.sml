(* Supplement, never modify, the pinned develop tactic tests. *)
open HolKernel Parse boolLib simpLib testutils LegacyFailures
val _ = new_theory "tacticvalidations"

(* Every residual goal is proved with kernel inference, not mk_thm/cheat.
   Run VALID as well, then explicitly exercise the returned validation. *)
fun run label tac (goal as (asms,w)) expected = let
  val (subgoals,validate) = during (label ^ ".apply")
    (fn () => runtac (VALID tac) goal)
  val _ = observe (label ^ ".subgoals")
    (String.concatWith ";" (map (fn (asl,g) =>
      "[" ^ String.concatWith "," (map term_to_string asl) ^ "] |- " ^
      term_to_string g) subgoals))
  val _ = check (label ^ " residual goals")
    (length subgoals = 1 andalso aconv (#2 (hd subgoals)) expected)
  val proofs = map
    (fn (_,g) => prove (g, DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC)) subgoals
  val th = during (label ^ ".validate") (fn () => validate proofs)
  val _ = theorem (label ^ ".validation") th
in
  check (label ^ " reconstructed conclusion and hypotheses")
    (aconv (concl th) w andalso
     HOLset.equal (hypset th,HOLset.addList (HOLset.empty Term.compare,asms)))
end

val p = ``validation_p:bool``
val x = ``validation_x:bool``
val xt = mk_eq (x,T)
val taut = mk_imp (p,p)
val goal = ([xt],mk_conj (x,taut))
val rules = [boolTheory.AND_CLAUSES]
val ss = pureSimps.pure_ss
val _ = run "simp" (SIMP_TAC ss (ASSUME xt :: rules)) goal taut
val _ = run "asm" (ASM_SIMP_TAC ss rules) goal taut
val _ = run "full" (full_simp_tac ss rules) goal taut
val _ = run "reverse-full" (rev_full_simp_tac ss rules) goal taut
val _ = List.app (fn oldest => run
  ("global-oldest-" ^ Bool.toString oldest)
  (global_simp_tac {droptrues=true,elimvars=false,strip=true,
                    oldestfirst=oldest} ss rules) goal taut) [true,false]
val _ = finish ()
