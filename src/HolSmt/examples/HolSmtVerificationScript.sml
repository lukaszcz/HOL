Theory HolSmtVerification
Ancestors
  integer combin
Libs
  HolSmtLib

(* Discharging verification conditions is the paradigmatic industrial use of
   SMT solvers: program verifiers (Boogie/Dafny, Why3, ESC/Java) reduce each
   proof obligation to a first-order formula and hand it to a solver.  The
   theorems below are typical obligations, proved by the checked Z3 tactic
   and replayed in HOL. *)

(* The midpoint computation at the heart of binary search.  Provided the
   bounds are ordered, `lo + (hi - lo) / 2` stays within them — exactly the
   in-bounds obligation a verifier emits for the subsequent array access.
   HOL's `/` on int rounds towards negative infinity, and `hi - lo` is
   non-negative here, so it matches machine division of non-negative
   operands. *)
Theorem binary_search_midpoint_in_bounds:
  !lo hi : int.
    lo <= hi ==>
    lo <= lo + (hi - lo) / 2 /\ lo + (hi - lo) / 2 <= hi
Proof
  Z3_TAC
QED

(* Specification of a clamp routine: the result is within range, and inputs
   already in range are returned unchanged. *)
Theorem clamp_in_range:
  !v lo hi : int.
    lo <= hi ==>
    lo <= int_max lo (int_min v hi) /\ int_max lo (int_min v hi) <= hi
Proof
  Z3_TAC
QED

Theorem clamp_identity:
  !v lo hi : int.
    lo <= v /\ v <= hi ==> int_max lo (int_min v hi) = v
Proof
  Z3_TAC
QED

(* Memories and arrays are modelled as functions, updated with `=+`; the
   translation maps them to the SMT theory of arrays (McCarthy's read/write
   axioms).  This verifies the classic three-assignment swap:

     t := a[i]; a[i] := a[j]; a[j] := t

   The final memory holds the exchanged values and is untouched elsewhere. *)
Theorem swap_correct:
  !a : int -> int. !i j.
    i <> j ==>
    ((j =+ a i) ((i =+ a j) a)) i = a j /\
    ((j =+ a i) ((i =+ a j) a)) j = a i /\
    !k. k <> i /\ k <> j ==> ((j =+ a i) ((i =+ a j) a)) k = a k
Proof
  Z3_TAC
QED
