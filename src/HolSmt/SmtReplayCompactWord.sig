(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayCompactWord =
sig
  exception Declined
  val bounded_source : Term.term -> bool
  val eligible : Term.term -> bool
  (* Callers retain their original source and Type admissions. *)
  val prove_schema : SmtBitBlastProve.context ->
    (Term.term -> (unit -> Thm.thm) -> Thm.thm) ->
    (Term.term -> (unit -> Thm.thm) -> Thm.thm) -> Term.term -> Thm.thm
  val prove_in : SmtSkeletonProve.sat_context ->
    (Term.term -> Thm.thm) -> (int -> Type.hol_type -> Term.term) ->
    Term.term -> (Term.term,Term.term) Lib.subst -> Term.term -> Thm.thm
  val measure_normalized_for_test : Term.term ->
    {tree_nodes:int,dag_nodes:int}
end
