open HolKernel Parse boolLib bossLib;
open HolSmtLib;

val _ = new_theory "HolSmtBasics";

(* Z3_TAC is the usual entry point: Z3 produces a proof and HOL replays it. *)
Theorem propositional_example:
  (p ==> q) /\ (q ==> r) ==> (p ==> r)
Proof
  Z3_TAC
QED

(* Assumptions in the goal are sent to the solver automatically. *)
Theorem assumptions_example:
  (x : int) <= y /\ y < z ==> x < z
Proof
  Z3_TAC
QED

(* Quantified formulas and equality reasoning are supported too. *)
Theorem quantified_example:
  (!x. P x ==> Q x) /\ (!x. Q x ==> R x) ==>
  !x. P x ==> R x
Proof
  Z3_TAC
QED

(* z3_tac supplies HOL theorems as additional solver assumptions. *)
Theorem add_nonnegative:
  !x y : int. 0 <= x /\ 0 <= y ==> 0 <= x + y
Proof
  Z3_TAC
QED

Theorem supplied_lemma_example:
  !x : int. 0 <= x ==> 0 <= x + x
Proof
  z3_tac [add_nonnegative]
QED

val _ = export_theory ();
