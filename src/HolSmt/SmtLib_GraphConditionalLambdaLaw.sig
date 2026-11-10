(* A genuine conditional lambda receipt becomes an existing closed fact. *)
signature SmtLib_GraphConditionalLambdaLaw =
sig
  type recorded
  type recording_request =
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     native_contract:SmtReplayNativeContract.contract,
     conversion:SmtReplayOwnedLambda.conditional_policy_conversion,
     profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit}
  (* Outside an action. The exact parent Scope and original native contract
     are authenticated before the receipt's endpoints/theorem are read.
     Its condition must already be visible in that parent. This operation
     neither rehomes a private condition nor turns a conditional proof into
     an unconditional conversion. Actual input, ALPHA/REFL equations and
     repeated Type portfolios meet the SAME finite caller caps before any
     statement/recording native effect. No raw theorem/endpoint input. *)
  val record_with_policy : SmtReplayInvocationWork.portfolio ->
    recording_request -> SmtReplayProof.closed_fact
  (* SAME recording programme, with an opaque tie to its actual result.
     No independent fact can be paired with a conversion by the caller. *)
  val record_receipt_with_policy : SmtReplayInvocationWork.portfolio ->
    recording_request -> recorded
  (* Caller owns the SAME active action. Expected Work is fenced before
     any held conversion/metric backing; retained observed metric guards
     keep their actual Work charges. Exact frame and contract are derived
     from the genuine recording, rather than supplied scalar labels. *)
  val recorded_with_policy_for : SmtReplayInvocationWork.portfolio ->
    recorded ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     native_contract:SmtReplayNativeContract.contract,
     conversion:SmtReplayOwnedLambda.conditional_policy_conversion,
     fact:SmtReplayProof.closed_fact,condition:SmtReplayGraph.node,
     source:SmtReplayGraph.node,target:SmtReplayGraph.node}
end
