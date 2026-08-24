Theory HolSmtWords
Ancestors
  words
Libs
  HolSmtLib

(* Fixed-width HOL words are translated to SMT bit vectors. *)
Theorem bitwise_example:
  ((x : word32) && y) && z = x && (y && z)
Proof
  Z3_TAC
QED

Theorem modular_arithmetic:
  (x : word32) + y = y + x
Proof
  Z3_TAC
QED

Theorem shift_example:
  (x : word32) << 99 = 0w
Proof
  Z3_TAC
QED

Theorem extract_example:
  (31 >< 0) (x : word32) = x
Proof
  Z3_TAC
QED
