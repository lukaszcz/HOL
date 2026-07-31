signature linarithDecomp =
sig
  val demult :
    Term.term * Arbrat.rat -> Term.term option * Arbrat.rat
  val decomp : Term.term -> linarithSolve.decomp option
  val is_nonnegative : Term.term -> bool
  val is_relevant : Term.term -> bool
end
