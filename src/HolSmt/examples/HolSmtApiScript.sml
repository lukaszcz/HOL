Theory HolSmtApi
Ancestors
  integer string
Libs
  HolSmtLib

(* The *_PROVE functions are convenient outside tactic proofs. *)
Theorem checked_prove_example =
  Z3_PROVE ``!x : int. x <= x + 1``

(* Oracle calls trust the solver result and add a HolSmtLib oracle tag. *)
Theorem oracle_prove_example =
  Z3_ORACLE_PROVE ``!p q. p /\ q ==> q /\ p``

(* Prefer checked calls.  Oracle calls are useful for experimentation or for
   supported translations whose solver proof cannot yet be replayed. *)
Theorem native_string_oracle_example:
  STRCAT (STRCAT (s : string) t) u = STRCAT s (STRCAT t u)
Proof
  Z3_ORACLE_TAC
QED
