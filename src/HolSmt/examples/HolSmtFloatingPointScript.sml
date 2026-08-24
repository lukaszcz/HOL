open HolKernel Parse boolLib bossLib;
open HolSmtLib;
open smtfloatTheory;

val _ = new_theory "HolSmtFloatingPoint";

(* smtfp is the canonical-NaN carrier for SMT FloatingPoint.  Its two type
   parameters determine the significand and exponent widths. *)
Theorem ground_addition:
  smtfp_add RNE
    (smtfp_bits 0w 3w 0w : (4, 3) smtfp)
    (smtfp_bits 0w 3w 0w : (4, 3) smtfp) =
  smtfp_bits 0w 4w 0w
Proof
  Z3_TAC
QED

Theorem comparison_asymmetry:
  smtfp_lt (x : (10, 5) smtfp) y ==> ~smtfp_lt y x
Proof
  Z3_TAC
QED

Theorem canonical_nan:
  (smtfp_bits 1w 7w 1w : (4, 3) smtfp) = smtfp_nan
Proof
  Z3_TAC
QED

val _ = export_theory ();
