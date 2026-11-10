(* Primitive conditional discharge, not a supplied simplifier callback. *)
signature SmtLib_GraphNumericConditional =
sig
  type owner
  type plan
  type result
  val begin : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphNumericCanonical.catalogue ->
    {check_type : Type.hol_type -> unit} -> owner
  (* Conditions are checked semantic evidence ONLY. No prior Work credit.
     The future fixed-context recursive solver must produce these internally;
     original Source assumptions are never accepted as condition proofs. *)
  val prepare : owner ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     instance : SmtLib_GraphNumericRuleMatch.instance,
     conditions : SmtReplayProof.closed_fact list} -> plan
  val prepare_owned : owner ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     instance : SmtLib_GraphNumericRuleMatch.instance,
     conditions : SmtReplayOwnedLargeProofCore.result list} -> plan
  val lambda_conversion_for : SmtReplayInvocationWork.portfolio -> owner ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     result : SmtReplayOwnedRealizedLambda.result} ->
    SmtReplayProof.closed_conversion
  val execute : plan -> result
  (* Same private instance source, never a caller theorem/node pair. *)
  val conversion_for : SmtReplayInvocationWork.portfolio -> result ->
    SmtReplayProof.closed_conversion
  val fact_for : SmtReplayInvocationWork.portfolio -> result ->
    SmtReplayProof.closed_fact
  type policy_owner
  type policy_plan
  type policy_result
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphNumericCanonical.policy_catalogue ->
    {profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type->unit} -> policy_owner
  val prepare_owned_with_policy : policy_owner ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     instance:SmtLib_GraphNumericRuleMatch.policy_instance,
     conditions:SmtReplayOwnedLargeProofCore.policy_result list,
     ordinal:int} -> policy_plan
  val execute_with_policy : policy_plan -> policy_result
  val conversion_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_result -> SmtReplayProof.closed_conversion

  (* Actual owned Lambda result only. This adapter owns a Work action for
     its independently admitted identity-view native programme. *)
  val lambda_conversion_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_owner ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     result:SmtReplayOwnedRealizedLambda.policy_result} ->
    SmtReplayProof.closed_conversion

end
