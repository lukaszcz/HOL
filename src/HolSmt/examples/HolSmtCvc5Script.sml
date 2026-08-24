open HolKernel Parse boolLib bossLib;
open HolSmtLib;

val _ = new_theory "HolSmtCvc5";

(* CVC_TAC is the checked cvc5 counterpart of Z3_TAC. *)
Theorem cvc_integer_example:
  (x : int) < y /\ y <= z ==> x < z
Proof
  CVC_TAC
QED

Theorem bag_membership:
  BAG_IN (x : bool) (BAG_INSERT y EMPTY_BAG) <=> x = y
Proof
  CVC_TAC
QED

Theorem cvc_supplied_lemma:
  !x : int. 0 <= x ==> 0 <= x + x
Proof
  cvc_tac [HolSmtBasicsTheory.add_nonnegative]
QED

val cvc_checked_thm =
  CVC_PROVE ``!x : int. x <= x + 1``;

val _ = save_thm ("cvc_prove_example", cvc_checked_thm);

val _ = export_theory ();
