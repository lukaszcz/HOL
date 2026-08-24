Theory HolSmtData
Ancestors
  integer
Libs
  HolSmtLib

Datatype:
  traffic_light = Red | Amber | Green
End

Datatype:
  appointment = <| start : int; finish : int; confirmed : bool |>
End

(* Constructors, selectors, case expressions and records are translated as
   SMT datatypes. *)
Theorem distinct_constructors:
  Red <> Green
Proof
  Z3_TAC
QED

Theorem case_example:
  (case light of Red => (0 : int) | Amber => 1 | Green => 2) <= 2
Proof
  Z3_TAC
QED

Theorem record_extensionality:
  (x = y) <=>
  x.start = y.start /\ x.finish = y.finish /\
  x.confirmed = y.confirmed
Proof
  Z3_TAC
QED

Theorem record_update:
  (x with confirmed := b).start = x.start /\
  (x with confirmed := b).confirmed = b
Proof
  Z3_TAC
QED

Theorem option_shape:
  option_CASE value (n : bool) s = n ==>
  value = NONE \/ ?x. value = SOME x
Proof
  Z3_TAC
QED
