signature SmtLib_OwnedPairedEqTFlip =
sig
  type plan
  val prepare : SmtReplayInvocationWork.portfolio ->
    {incoming:SmtLib_OwnedContextImpCanon.receipt_validation,index:int,
     check_type:Type.hol_type -> unit} -> plan
  val execute : SmtReplayInvocationWork.portfolio -> plan ->
    SmtReplayProof.source_condition_evidence list
end
