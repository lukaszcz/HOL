signature SmtLib_OwnedOrderedExistentialClause =
sig
  type owner
  type selection
  type plan
  type receipt
  (* The complete genuine C portfolio owns each ordered selection. *)
  val begin : SmtReplayInvocationWork.portfolio ->
    {catalogue:SmtLib_OwnedNamedContextSeeds.catalogue,
     check_type:Type.hol_type -> unit} -> owner
  val selections_for : SmtReplayInvocationWork.portfolio -> owner ->
    selection list
  (* Supported boundary: ordinary linear implication prefix, one actual
     existential antecedent, positive atomic consequent. Other stock
     IMP_CANON frontiers explicitly refuse before argument mint. *)
  val prepare : SmtReplayInvocationWork.portfolio -> selection -> plan
  val execute : SmtReplayInvocationWork.portfolio -> plan -> receipt
  val evidence_for : SmtReplayInvocationWork.portfolio -> receipt ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,ordinal:int,
     assumption_slot:int,source_occurrence:int,
     evidence:SmtReplayProof.source_condition_evidence}
end
