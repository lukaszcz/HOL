Theory HolSmtArithmetic
Ancestors
  integer real
Libs
  HolSmtLib

(* Linear integer arithmetic is a core SMT use case. *)
Theorem integer_bounds:
  (x : int) <= y /\ y <= z ==> 3 * x <= 3 * z
Proof
  Z3_TAC
QED

(* HOL naturals are transferred to constrained SMT integers. *)
Theorem natural_subtraction:
  (x : num) - (y + 1) <= x
Proof
  Z3_TAC
QED

(* Division is total in HOL; assumptions state the mathematical side
   conditions that an application normally needs. *)
Theorem real_division:
  (y : real) <> 0 ==> (x / y) * y = x
Proof
  Z3_TAC
QED

(* This nonlinear real fact is covered by checked Z3 replay. *)
Theorem square_nonnegative:
  0 <= (x : real) * x
Proof
  Z3_TAC
QED
