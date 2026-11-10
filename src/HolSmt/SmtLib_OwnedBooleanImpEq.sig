signature SmtLib_OwnedBooleanImpEq =
sig
  type plan
  type receipt
  (* Explicit bounded primitive slice of original unbounded Gamma rules.
     Unsupported stock branches fail explicitly; no default selects it. *)
  val prepare : SmtReplayInvocationWork.portfolio ->
    {raw:SmtLib_OwnedContextImpCanon.receipt,
     check_type:Type.hol_type -> unit} -> plan
  val execute : SmtReplayInvocationWork.portfolio -> plan -> receipt
  val entries_for : SmtReplayInvocationWork.portfolio -> receipt ->
    {ordinal:int,assumption_slot:int,source_occurrence:int,
     entries:SmtReplayProof.source_condition_evidence list}
end
