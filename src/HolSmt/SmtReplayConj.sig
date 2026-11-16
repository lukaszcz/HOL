signature SmtReplayConj =
sig
  (* HolSmt's own public derivation of the fixed implication/conjunction
     law. This is not a decoder certificate or the simplifier's cache. *)
  type conj_discharge_template
  val conj_discharge_template : unit -> conj_discharge_template
  val conj_discharge_template_data : conj_discharge_template ->
    {proof:Thm.thm,first:Term.term,second:Term.term,third:Term.term}
  val conj_discharge_constructor_data : conj_discharge_template ->
    {statement:Term.term,tag:Tag.tag,bare:bool,closed:bool}

  (* The simplifier's fixed laws for F, T = F and F = T conclusions, read
     through Cond_rewr.IMP_EQ_CANON, so they share its private variable. *)
  datatype false_template_kind = FalseConclusion | TruthEqualsFalse
    | FalseEqualsTruth
  type false_template
  val false_template : false_template_kind -> false_template
  val false_template_data : false_template ->
    {proof:Thm.thm,condition:Term.term,result:Term.term}

  (* boolTheory.EQ_SYM_EQ, the law the simplifier flips equations with. *)
  type eq_sym_template
  val eq_sym_template : unit -> eq_sym_template
  val eq_sym_template_data : eq_sym_template ->
    {proof:Thm.thm,statement:Term.term}
end
