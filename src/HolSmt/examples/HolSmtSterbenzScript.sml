Theory HolSmtSterbenz
Ancestors
  smtfloat
Libs
  HolSmtLib

(* Sterbenz subtraction is exact for finite operands within a factor of two.
   IEEE equality is used because exact zero may have a mode-dependent sign. *)
Theorem sterbenz_positive_cvc:
  !mode1 mode2 x y : (4, 3) smtfp.
    smtfp_is_finite x /\ smtfp_is_finite y /\
    smtfp_le x (smtfp_add RNE y y) /\
    smtfp_le y (smtfp_add RNE x x) ==>
    smtfp_eq (smtfp_sub mode1 x y) (smtfp_sub mode2 x y)
Proof
  CVC_TAC
QED

Theorem sterbenz_positive_z3:
  !mode1 mode2 x y : (4, 3) smtfp.
    smtfp_is_finite x /\ smtfp_is_finite y /\
    smtfp_le x (smtfp_add RNE y y) /\
    smtfp_le y (smtfp_add RNE x x) ==>
    smtfp_eq (smtfp_sub mode1 x y) (smtfp_sub mode2 x y)
Proof
  Z3_TAC
QED

Theorem sterbenz_negative_cvc:
  !mode1 mode2 x y : (4, 3) smtfp.
    smtfp_is_finite x /\ smtfp_is_finite y /\
    smtfp_le (smtfp_add RNE y y) x /\
    smtfp_le (smtfp_add RNE x x) y ==>
    smtfp_eq (smtfp_sub mode1 x y) (smtfp_sub mode2 x y)
Proof
  CVC_TAC
QED

Theorem sterbenz_negative_z3:
  !mode1 mode2 x y : (4, 3) smtfp.
    smtfp_is_finite x /\ smtfp_is_finite y /\
    smtfp_le (smtfp_add RNE y y) x /\
    smtfp_le (smtfp_add RNE x x) y ==>
    smtfp_eq (smtfp_sub mode1 x y) (smtfp_sub mode2 x y)
Proof
  Z3_TAC
QED

val _ = export_theory ();
