(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayWordProgram =
sig
  (* Admit the complete original Boolean graph before returning its native
     producer. This performs the same source checks as propositional_prove. *)
  val prepare_source : SmtSkeletonProve.sat_context -> Term.term ->
    unit -> Thm.thm

  (* Admission always runs, including on a cache hit. Only its returned
     producer may be skipped. The checked compact theorem and ordinary SAT
     certificates share the owner's existing total allowance. *)
  val prove_in : SmtSkeletonProve.sat_context ->
    (int -> Type.hol_type -> Term.term) -> Term.term ->
    (unit -> unit -> Thm.thm) -> Thm.thm
end
