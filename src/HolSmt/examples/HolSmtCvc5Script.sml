Theory HolSmtCvc5
Ancestors
  HolSmtBasics bag
Libs
  HolSmtLib

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

Theorem cvc_prove_example =
  CVC_PROVE ``!x : int. x <= x + 1``
