open HolKernel Parse boolLib bossLib;
open HolSmtLib;

val _ = new_theory "HolSmtCollections";

(* HOL lists use the SMT sequence encoding. *)
Theorem append_length:
  LENGTH ((xs : int list) ++ ys) = LENGTH xs + LENGTH ys
Proof
  Z3_TAC
QED

Theorem map_append:
  MAP (\x : int. x + 1) (xs ++ ys) =
  MAP (\x. x + 1) xs ++ MAP (\x. x + 1) ys
Proof
  Z3_TAC
QED

(* Sets are predicates.  State set properties through membership. *)
Theorem union_membership:
  (x : int) IN (s UNION t) <=> x IN s \/ x IN t
Proof
  Z3_TAC
QED

Theorem union_commutative_at_element:
  (x : bool) IN (s UNION t) <=> x IN (t UNION s)
Proof
  Z3_TAC
QED

val _ = export_theory ();
