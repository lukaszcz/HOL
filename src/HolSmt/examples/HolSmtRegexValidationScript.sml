Theory HolSmtRegexValidation
Ancestors
  smtstringz3
Libs
  HolSmtLib

open smtstringTheory smtstringz3Theory

(* The application accepts exactly two ASCII decimal digits: [0-9]{2}. *)
Definition two_decimal_digits_def:
  two_decimal_digits s <=>
    smt_in_re s
      (reglan_power
        (reglan_range (SmtStr [48]) (SmtStr [57])) 2)
End

Definition decimal_digit_def:
  decimal_digit s <=>
    48 <= smtstr_to_code s /\ smtstr_to_code s <= 57
End

Definition two_digit_validation_def:
  two_digit_validation s <=>
    smtstr_len s = 2 /\
    decimal_digit (smtstr_at s 0) /\
    decimal_digit (smtstr_at s 1)
End

Theorem smt_in_re_power_range_singletons[local]:
  lo <= 196607 /\ hi <= 196607 ==>
  (smt_in_re s
     (reglan_power (reglan_range (SmtStr [lo]) (SmtStr [hi])) n) <=>
   LENGTH (smtstr_rep s) = n /\
   EVERY (\c. lo <= c /\ c <= hi) (smtstr_rep s))
Proof
  strip_tac >>
  `EVERY (\c. c <= 196607) (smtstr_rep s)` by simp [] >>
  simp [smt_in_re_def, re_lang_def, reglan_repeat_singletons3,
        smtstr_rep_def] >>
  fs [listTheory.EVERY_MEM] >>
  eq_tac
  >- rw []
  >> rw [] >>
  `c <= hi` by fs [] >>
  `hi <= 196607` by fs [] >>
  decide_tac
QED

Theorem two_digit_validation_z3:
  !s. two_decimal_digits s ==> two_digit_validation s
Proof
  PURE_REWRITE_TAC [two_decimal_digits_def, two_digit_validation_def,
                    decimal_digit_def] >>
  Z3_TAC
QED

Theorem two_digit_validation_cvc5:
  !s. two_decimal_digits s ==> two_digit_validation s
Proof
  PURE_REWRITE_TAC [two_decimal_digits_def, two_digit_validation_def,
                    decimal_digit_def] >>
  CVC_TAC
QED

(* A solver-independent row documents the reusable semantic reduction and
   keeps the example useful when no external prover is configured. *)
Theorem two_digit_validation_hol:
  !s. two_decimal_digits s ==> two_digit_validation s
Proof
  rw [two_decimal_digits_def, two_digit_validation_def,
      decimal_digit_def] >>
  fs [smt_in_re_power_range_singletons] >>
  Cases_on `smtstr_rep s` >> fs [] >>
  Cases_on `t` >> fs [] >>
  Cases_on `t'` >> fs [] >>
  simp [smtstr_len_def, smtstr_at_def, smtstr_substr_def,
        smtstr_to_code_def, smtstr_rep_def]
QED

val _ = export_theory ();
