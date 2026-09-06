Theory HolSmtStringSanitizer
Ancestors
  smtstring
Libs
  HolSmtLib

(* A quote-free fragment contains no Unicode quotation-mark code point. *)
Definition quote_free_def:
  quote_free s <=> ~smtstr_contains s (SmtStr [34])
End

(* Sanitized fragments are assembled without changing their contents. *)
Definition sanitized_concat_def:
  sanitized_concat left right = smtstr_concat left right
End

(* A quotation mark cannot straddle a concatenation boundary, so assembling
   two fragments is quote-free exactly when each fragment is quote-free. *)
Theorem sanitized_concat_quote_free_z3:
  !left right.
    quote_free (sanitized_concat left right) <=>
    quote_free left /\ quote_free right
Proof
  PURE_REWRITE_TAC [quote_free_def, sanitized_concat_def] >> Z3_TAC
QED

Theorem sanitized_concat_quote_free_cvc5:
  !left right.
    quote_free (sanitized_concat left right) <=>
    quote_free left /\ quote_free right
Proof
  PURE_REWRITE_TAC [quote_free_def, sanitized_concat_def] >> CVC_TAC
QED
