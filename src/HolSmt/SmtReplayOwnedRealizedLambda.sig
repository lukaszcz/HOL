(* Local definitions are already closed by the SAME opaque Core result. *)
signature SmtReplayOwnedRealizedLambda =
sig
  type plan
  type result
  val prepare_admitted : SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     admission : SmtReplayFocusAdmission.focus,
     body : SmtReplayOwnedLargeProofCore.result,ordinal : int,
     check_type : Type.hol_type -> unit} -> plan
  val execute : SmtReplayInvocationWork.portfolio -> plan -> result
  val conversion_description_for : SmtReplayInvocationWork.portfolio ->
    result -> {graph : SmtReplayGraph.graph,root : SmtReplayGraph.scope,
      scope : SmtReplayGraph.scope,sources : SmtReplaySource.sources,
      source : SmtReplayGraph.node,target : SmtReplayGraph.node}
  val theorem_for : SmtReplayInvocationWork.portfolio -> result -> Thm.thm
  type policy_plan
  type policy_result
  val prepare_admitted_with_policy : SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     admission:SmtReplayFocusAdmission.policy_focus,
     body:SmtReplayOwnedLargeProofCore.policy_result,ordinal:int,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> policy_plan
  val execute_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_plan -> policy_result
  val conversion_description_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_result ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     source:SmtReplayGraph.node,target:SmtReplayGraph.node}
  val theorem_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_result -> Thm.thm
  val native_contract_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_result ->
    SmtReplayNativeContract.contract

end
