signature linarithDecomp =
sig
  type polynomial =
    (Term.term * Arbrat.rat) list * Arbrat.rat

  val demult :
    Term.term * Arbrat.rat -> Term.term option * Arbrat.rat
  val poly : Term.term -> polynomial
  val decomp : Term.term -> linarithSolve.decomp option
  val is_nonnegative : Term.term -> bool
  val is_relevant : Term.term -> bool
end
