signature SmtLib_OwnedContextFreshChoice =
sig
  type choice
  val prepare_existential : SmtReplayInvocationWork.portfolio ->
    {evidence:SmtReplayProof.source_condition_evidence,
     context:SmtLib_OwnedNamedContextSeeds.context_metadata} -> choice
  (* DATA only. The fixed proof producer must quote its WHOLE future
     primitive profile before constructing this variable or graph closure. *)
  val describe_for : SmtReplayInvocationWork.portfolio -> choice ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,name:string,ty:Type.hol_type}
  type antecedent_plan
  val prepare_antecedent : SmtReplayInvocationWork.portfolio -> choice ->
    {check_type:Type.hol_type -> unit} -> antecedent_plan
  val execute_antecedent : SmtReplayInvocationWork.portfolio ->
    antecedent_plan -> SmtReplayProof.source_condition_evidence

  type canonical_plan
  val prepare_canonical_exists : SmtReplayInvocationWork.portfolio ->
    {state:SmtReplayProof.source_canonical_state,
     context:SmtLib_OwnedNamedContextSeeds.context_metadata,
     check_type:Type.hol_type -> unit} -> canonical_plan
  val prepare_canonical_universals : SmtReplayInvocationWork.portfolio ->
    {state:SmtReplayProof.source_canonical_state,
     context:SmtLib_OwnedNamedContextSeeds.context_metadata,
     check_type:Type.hol_type -> unit} -> canonical_plan
  val execute_canonical : SmtReplayInvocationWork.portfolio ->
    canonical_plan -> SmtReplayProof.source_canonical_state

end
