(* An actual owned Z3 packet receiver; legacy receivers remain separate. *)
signature Z3_PolicyGraphProofReplay =
sig
  type invocation
  type request=
    {packet:Z3_GraphProofParser.proof SmtLib_GraphProof.packet,
     preprocessing:SmtLib_GraphPreprocess.validation,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,ordinal:int}
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayNativeContract.contract -> request -> invocation
  val replay_next_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation ->
    {id:Z3_GraphProofParser.proof_id,node:SmtReplayGraph.node} option
  val step_with_policy_for : SmtReplayInvocationWork.portfolio ->
    invocation -> Z3_GraphProofParser.proof_id ->
    {block:SmtReplayProof.block,node:SmtReplayGraph.node,
     edge:SmtReplayProof.edge}
  val finish_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> Thm.thm
  val prove_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayNativeContract.contract -> request -> Thm.thm
  (* Genuine raw compatibility receiver; the recorded entry is unchanged.
     Both factories retain the same original Work/Source/native contract. *)
  val begin_raw_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayNativeContract.contract -> request -> invocation

end
