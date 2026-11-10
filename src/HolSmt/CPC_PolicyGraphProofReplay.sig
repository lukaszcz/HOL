(* Actual owned packet replay, additive to the legacy receiver. *)
signature CPC_PolicyGraphProofReplay =
sig
  type invocation
  type request=
    {packet:CPC_ProofParser.graph_proof SmtLib_GraphProof.packet,
     preprocessing:SmtLib_GraphPreprocess.validation,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,ordinal:int}
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayNativeContract.contract -> request -> invocation
  val replay_next_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> {serial:int,id:string,node:SmtReplayGraph.node} option
  (* The returned edge belongs to the returned actual current Block;
     Consuming it invalidates subsequent operations on this invocation.
     A replacement Block revokes all earlier published Block handles. *)
  val step_with_policy_for : SmtReplayInvocationWork.portfolio ->
    invocation -> string ->
    {block:SmtReplayProof.block,node:SmtReplayGraph.node,
     edge:SmtReplayProof.edge}
  val finish_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> Thm.thm
  val prove_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayNativeContract.contract -> request -> Thm.thm
end
