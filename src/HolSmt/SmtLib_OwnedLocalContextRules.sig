(* Genuine local assumptions AFTER this owned query's GEN/DISCH phase.
   Rules are conditional semantic proof seeds, never closed PURE facts. *)
signature SmtLib_OwnedLocalContextRules =
sig
  type owner
  type plan
  type catalogue
  type rule
  val begin : SmtReplayInvocationWork.portfolio ->
    {query:SmtLib_OwnedStrippedNaturalQuery.query,
     check_type:Type.hol_type -> unit} -> owner
  val prepare : owner -> plan
  val execute : plan -> catalogue
  val validate_for : SmtReplayInvocationWork.portfolio -> catalogue -> unit
  val context_for : SmtReplayInvocationWork.portfolio -> catalogue ->
    {query:SmtLib_OwnedStrippedNaturalQuery.query,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     assumptions:SmtReplayGraph.node list}
  val rules_for : SmtReplayInvocationWork.portfolio -> catalogue -> rule list
  val describe_for : SmtReplayInvocationWork.portfolio -> rule ->
    {query:SmtLib_OwnedStrippedNaturalQuery.query,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     original_assumptions:SmtReplayGraph.node list,
     assumption_slot:int,assumption:SmtReplayGraph.node,
     fixed_variables:Term.term list,generalized_variables:Term.term list,
     conditional:SmtReplayProof.closed_fact}
end
