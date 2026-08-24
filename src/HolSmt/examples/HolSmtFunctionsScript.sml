open HolKernel Parse boolLib bossLib;
open HolSmtLib;

val _ = new_theory "HolSmtFunctions";

(* Functions without a supported definition are treated as uninterpreted. *)
Theorem congruence_example:
  (x = y) ==> (f (g x) = f (g y))
Proof
  Z3_TAC
QED

(* Function updates are translated as SMT arrays. *)
Theorem update_other_index:
  i <> j ==> ((i =+ e) (a : int -> int)) j = a j
Proof
  Z3_TAC
QED

Theorem commuting_updates:
  i <> j ==>
  (j =+ f) ((i =+ e) (a : int -> int)) =
  (i =+ e) ((j =+ f) a)
Proof
  Z3_TAC
QED

(* Extensional equality is available for translated functions. *)
Theorem function_extensionality:
  (!i. (a : int -> int) i = b i) ==> (a = b)
Proof
  Z3_TAC
QED

(* Checked Z3 also supports the relevant higher-order lambda surface. *)
Theorem lambda_example:
  (H : (int -> int) -> bool) (\x. x + 1) /\ p ==>
  H (\y. y + 1)
Proof
  Z3_TAC
QED

val _ = export_theory ();
