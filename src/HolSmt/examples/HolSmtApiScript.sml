open HolKernel Parse boolLib bossLib;
open HolSmtLib;

val _ = new_theory "HolSmtApi";

(* The *_PROVE functions are convenient outside tactic proofs. *)
val checked_thm =
  Z3_PROVE ``!x : int. x <= x + 1``;

val _ = save_thm ("checked_prove_example", checked_thm);

(* Oracle calls trust the solver result and add a HolSmtLib oracle tag. *)
val oracle_thm =
  Z3_ORACLE_PROVE ``!p q. p /\ q ==> q /\ p``;

val _ = save_thm ("oracle_prove_example", oracle_thm);

(* Prefer checked calls.  Oracle calls are useful for experimentation or for
   supported translations whose solver proof cannot yet be replayed. *)
Theorem native_string_oracle_example:
  STRCAT (STRCAT (s : string) t) u = STRCAT s (STRCAT t u)
Proof
  Z3_ORACLE_TAC
QED

val _ = export_theory ();
