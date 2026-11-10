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
end
