signature SmtLib_OwnedContextImpCanon =
sig
  type owner
  type selection
  type receipt
  val begin : SmtReplayInvocationWork.portfolio ->
    {catalogue:SmtLib_OwnedNamedContextSeeds.catalogue,
     check_type:Type.hol_type -> unit} -> owner
  val selections_for : SmtReplayInvocationWork.portfolio -> owner ->
    selection list
  (* Exact stock IMP_CANON branch order for this genuine selected clause,
     including the authentic fixed restricted-forall continuation.
     IMP_EQ_CANON/QUANTIFY/solver/SIMPLE are separate later phases. *)
  val execute : SmtReplayInvocationWork.portfolio -> selection -> receipt
  val entries_for : SmtReplayInvocationWork.portfolio -> receipt ->
    {ordinal:int,assumption_slot:int,source_occurrence:int,
     entries:SmtReplayProof.source_condition_evidence list}
  (* Snapshot only privately retained raw entries; prepare owns actions.
     Validation itself is safe inside an already active SAME Work action. *)
  type receipt_validation
  val prepare_receipt_validation : SmtReplayInvocationWork.portfolio ->
    receipt -> receipt_validation
  val receipt_validation_for : SmtReplayInvocationWork.portfolio ->
    receipt_validation ->
    {ordinal:int,assumption_slot:int,source_occurrence:int,
     entries:SmtReplayProof.source_condition_evidence list}

  (* SAME validation's private selected-context metadata; guarded DATA.
     No caller context/evidence pair is accepted by the Hyp resolver. *)
  val receipt_context_for : SmtReplayInvocationWork.portfolio ->
    receipt_validation -> SmtLib_OwnedNamedContextSeeds.context_metadata

end
