(* Selected typed public rule events; DATA only, never Work authority. *)
signature SmtReplayRuleObservation =
sig
  type statistics =
    {selected_returns:IntInf.int,
     theorem_operand_edges:IntInf.int,
     zero_premise_returns:IntInf.int,
     one_premise_returns:IntInf.int,
     two_premise_returns:IntInf.int,
     three_premise_returns:IntInf.int}
  val with_statistics : (unit -> 'a) -> 'a * statistics
  val ASSUME : Term.term -> Thm.thm
  val REFL : Term.term -> Thm.thm
  val ALPHA : Term.term -> Term.term -> Thm.thm
  val SYM : Thm.thm -> Thm.thm
  val TRANS : Thm.thm -> Thm.thm -> Thm.thm
  val EQ_MP : Thm.thm -> Thm.thm -> Thm.thm
  val MP : Thm.thm -> Thm.thm -> Thm.thm
  val DISCH : Term.term -> Thm.thm -> Thm.thm
  val SPEC : Term.term -> Thm.thm -> Thm.thm
  val AP_TERM : Term.term -> Thm.thm -> Thm.thm
  val AP_THM : Thm.thm -> Term.term -> Thm.thm
  val MK_COMB : Thm.thm * Thm.thm -> Thm.thm
  val CONJ : Thm.thm -> Thm.thm -> Thm.thm
  val CONJUNCT1 : Thm.thm -> Thm.thm
  val CONJUNCT2 : Thm.thm -> Thm.thm
  val DISJ1 : Thm.thm -> Term.term -> Thm.thm
  val DISJ2 : Term.term -> Thm.thm -> Thm.thm
  val DISJ_CASES : Thm.thm -> Thm.thm -> Thm.thm -> Thm.thm
  val NOT_ELIM : Thm.thm -> Thm.thm
  val CCONTR : Term.term -> Thm.thm -> Thm.thm
  val D_CONTR : Term.term -> Thm.thm -> Thm.thm
  val D_EQF_ELIM : Thm.thm -> Thm.thm
  val D_PROVE_HYP : Thm.thm -> Thm.thm -> Thm.thm
  val D_SPECL : Term.term list -> Thm.thm -> Thm.thm
  (* One replacement equality and one source theorem: exactly two
     public theorem-operand incidences, regardless of pointer identity. *)
  val SUBST_LITERAL : Term.term -> Thm.thm -> Term.term -> Thm.thm ->
    Thm.thm
  val INST : (Term.term,Term.term) Lib.subst -> Thm.thm -> Thm.thm
  val INST_TYPE : (Type.hol_type,Type.hol_type) Lib.subst -> Thm.thm -> Thm.thm
  val inst_ty_term : (Term.term,Term.term) Lib.subst *
    (Type.hol_type,Type.hol_type) Lib.subst -> Thm.thm -> Thm.thm
end
