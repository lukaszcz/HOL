(* Exact incoming raw receipt Hyp metadata; never conclusion-union FV. *)
signature SmtLib_OwnedIncomingHypFV =
sig
  type receipt
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtLib_OwnedContextImpCanon.receipt_validation -> receipt
  (* Safe inside an already active SAME Work action. Explicit unknown is
     retained; the known list alone is never a complete absence policy. *)
  val entries_for : SmtReplayInvocationWork.portfolio -> receipt ->
    {ordinal:int,assumption_slot:int,source_occurrence:int,
     entries:{evidence:SmtReplayProof.source_condition_evidence,
       frame:SmtReplayOwnedScopeReceipt.receipt,statement:Term.term,
       variables:Term.term list,unknown:SmtReplayGraph.node list}list}
end
