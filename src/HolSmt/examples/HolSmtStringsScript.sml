Theory HolSmtStrings
Ancestors
  smtstring
Libs
  HolSmtLib

(* smtstr is HolSmt's native SMT-LIB Unicode-string carrier.  Code points are
   represented by natural numbers; 97 and 98 are "a" and "b". *)
Theorem concatenation_length:
  smtstr_len (smtstr_concat (SmtStr [97]) (SmtStr [98])) =
  smtstr_len (SmtStr [97]) + smtstr_len (SmtStr [98])
Proof
  Z3_TAC
QED

Theorem prefix_example:
  smtstr_prefixof (SmtStr [97])
    (smtstr_concat (SmtStr [97]) (SmtStr [98]))
Proof
  Z3_TAC
QED

Theorem regular_language_example:
  smt_in_re (SmtStr [97]) (reglan_to_re (SmtStr [97]))
Proof
  Z3_TAC
QED

Theorem string_to_integer:
  smtstr_to_int (SmtStr [49; 50]) = 12
Proof
  Z3_TAC
QED
