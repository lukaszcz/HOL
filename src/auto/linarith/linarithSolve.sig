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

  type linarith_config = {neq_limit : int, split_limit : int}

  type int_decomp = {
    lhs : (Term.term * Arbint.int) list,
    lhs_const : Arbint.int,
    rel : relation,
    rhs : (Term.term * Arbint.int) list,
    rhs_const : Arbint.int,
    discrete : bool,
    negated : bool
  }

  type neq_selector = Term.term -> bool option

  val elim : lineq list * history -> result
  val integ : decomp -> Arbint.int * int_decomp
  val mklineq : Term.term list -> decomp * int -> lineq
  val mknonneg :
    (Term.term -> bool) -> int list -> Term.term * int -> lineq option

  val elim_neq :
    neq_selector ->
    (Term.term * decomp option) list ->
    (Term.term * decomp option) list list

  val split_items :
    neq_selector -> bool -> (Term.term -> decomp option) ->
    Term.term list -> (decomp * int) list list

  val prove :
    linarith_config -> (Term.term -> decomp option) -> Term.term list ->
    Term.term -> bool * injust list option
end
