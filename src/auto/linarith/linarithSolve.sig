signature linarithSolve =
sig
  datatype relation = REL_LE | REL_LT | REL_EQ | REL_NEQ

  datatype decomp = Decomp of {
    lhs : (Term.term * Arbrat.rat) list,
    lhs_const : Arbrat.rat,
    rel : relation,
    rhs : (Term.term * Arbrat.rat) list,
    rhs_const : Arbrat.rat,
    discrete : bool,
    negated : bool
  }

  datatype lineq_type = Eq | Le | Lt

  datatype injust =
      Asm of int
    | Nonneg of int
    | LessD of injust
    | NotLessD of injust
    | NotLeD of injust
    | NotLeDD of injust
    | Multiplied of Arbint.int * injust
    | Added of injust * injust

  datatype lineq =
    Lineq of Arbint.int * lineq_type * Arbint.int list * injust

  type history = (int * lineq list) list
  datatype result = Success of injust | Failure of history

  type linarith_config = linarithData.linarith_config

  val elim : lineq list * history -> result
  val mklineq : Term.term list -> decomp * int -> lineq

  (* The atom ordering that Nonneg justifications index into. *)
  val atoms_of_decomps : decomp list -> Term.term list

  val negate : Term.term -> Term.term

  val elim_neq :
    (Term.term * decomp option) list ->
    (Term.term * decomp option) list list

  val split_items :
    bool -> (Term.term * decomp option) list -> (decomp * int) list list

  val prove :
    linarith_config -> (Term.term -> decomp option) ->
    (Term.term -> bool) -> Term.term list -> Term.term ->
    bool * injust list option
end
