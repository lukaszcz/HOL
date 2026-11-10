signature SmtLib_OwnedConditionalPredicate =
sig
  type plan
  val prepare : SmtReplayInvocationWork.portfolio ->
    {incoming:SmtLib_OwnedContextImpCanon.receipt_validation,index:int,
     check_type:Type.hol_type -> unit} -> plan
  val execute : SmtReplayInvocationWork.portfolio -> plan ->
    SmtReplayProof.source_condition_evidence
  (* Retains authentic post-DISCH output and SAME original O/C backing.
     No caller evidence/context pair can construct this receipt. *)
  type completed
  val execute_retained : SmtReplayInvocationWork.portfolio -> plan -> completed
  val completed_for : SmtReplayInvocationWork.portfolio -> completed ->
    {evidence:SmtReplayProof.source_condition_evidence,
     lower:SmtReplayProof.source_predicate_conditional_completed,
     incoming:SmtLib_OwnedContextImpCanon.receipt_validation,index:int,
     frame:SmtReplayOwnedScopeReceipt.receipt}

end
