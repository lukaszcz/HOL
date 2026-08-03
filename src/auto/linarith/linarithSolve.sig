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

  (* Asm indexes the assumption list replay is given; Nonneg carries
     the atom itself, whose own instance supplies its theorem. *)
  datatype injust =
      Asm of int
    | Nonneg of Term.term
    | LessD of injust
    | NotLessD of injust
    | NotLeD of injust
    | NotLeDD of injust
    | Multiplied of Arbint.int * injust
    | Added of injust * injust

  datatype lineq =
    Lineq of Arbint.int * lineq_type * Arbint.int list * injust

  (* The columns eliminated so far, most recent first.  Search discards
     a failure, so the rows of each round are not carried with it. *)
  type history = int list
  datatype result = Success of injust | Failure of history

  type linarith_config = linarithData.linarith_config

  val elim : lineq list * history -> result

  (* The column each atom's coefficient occupies.  Built once per split
     system from that system's atom ordering; rows scatter into it
     rather than searching their polynomial once per column. *)
  type atom_index
  val atom_index : Term.term list -> atom_index

  val mklineq : atom_index -> decomp * int -> lineq

  (* The atom ordering that coefficient rows follow. *)
  val atoms_of_decomps : decomp list -> Term.term list

  val negate : Term.term -> Term.term

  val elim_neq :
    (Term.term * decomp option) list ->
    (Term.term * decomp option) list list

  val split_items :
    bool -> (Term.term * decomp option) list -> (decomp * int) list list

  (* The flag reports whether disequalities were split: when it is
     true there is one justification per case, in the order the cases
     are generated, and the caller must reproduce that case split. *)
  val prove :
    linarith_config -> (Term.term -> decomp option) ->
    (Term.term -> bool) -> Term.term list -> Term.term ->
    bool * injust list option

  (* prove is this applied to its decomposed hypotheses.  A caller that
     asks the same question repeatedly about one fixed hypothesis set
     decomposes that set once and calls this directly; the negated
     conclusion is still decomposed per call, since it varies. *)
  val prove_decomposed :
    linarith_config -> (Term.term -> decomp option) ->
    (Term.term -> bool) -> (Term.term * decomp option) list ->
    Term.term -> bool * injust list option
end
