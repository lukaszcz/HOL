signature linarithDecomp =
sig
  (* An application of a binary operator, as (operator, left, right).
     Raises on anything else. *)
  val binary_parts : Term.term -> Term.term * Term.term * Term.term

  val demult :
    Term.term * Arbrat.rat -> Term.term option * Arbrat.rat
  val decomp : Term.term -> linarithSolve.decomp option
  val is_nonnegative : Term.term -> bool
  val is_relevant : Term.term -> bool

  (* Development instrumentation, not read by the layer: how many terms
     decomp has traversed.  Decomposition is the term-traversal half of
     the solver and the search asks about the same literals repeatedly,
     so the cost that matters is decompositions per tactic call; set
     this to 0 before one to measure it. *)
  val decomp_count : int ref
end
