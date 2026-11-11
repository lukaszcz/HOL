signature SmtLib_OwnedConditionQuantifierSelection =
sig
  type selection
  datatype decision=Identity | Singleton of Term.term | NotCovered of string
  val prepare : SmtReplayInvocationWork.portfolio ->
    {completed:SmtLib_OwnedConditionalPredicate.completed,
     check_type:Type.hol_type -> unit} -> selection
  (* Action-free guarded metadata. No native GEN/HO permission is issued. *)
  val selection_for : SmtReplayInvocationWork.portfolio -> selection ->
    {evidence:SmtReplayProof.source_condition_evidence,
     selected:Term.term list,decision:decision,
     condition_variables:Term.term list,equation_variables:Term.term list,
     hypothesis_variables:Term.term list,unknown:SmtReplayGraph.node list}
end
