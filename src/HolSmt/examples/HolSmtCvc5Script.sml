Theory HolSmtCvc5
Ancestors
  HolSmtBasics bag smtfloat
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

(* Solver capabilities differ (see the parent README): this quantified
   floating-point fact replays through cvc5's CPC proofs in milliseconds.
   IEEE addition is commutative even for NaN inputs here, because smtfp is
   the canonical-NaN carrier, so the conclusion is a plain equality. *)
Theorem fp_addition_commutes:
  !x y : (4, 3) smtfp. smtfp_add RNE x y = smtfp_add RNE y x
Proof
  CVC_TAC
QED
