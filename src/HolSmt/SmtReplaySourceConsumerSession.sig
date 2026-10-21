(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplaySourceConsumerSession =
sig
  (* Retain the exact scope that originally admitted the Source portfolio. *)
  val start : SmtReplaySource.sources -> Abbrev.goal ->
    SmtReplayWrapperSession.session
  val discover : SmtReplayWrapperSession.session ->
    (SmtReplaySource.sources -> SmtLib_GraphPreprocess.validation) -> unit
  val prepare : SmtReplaySource.sources -> Abbrev.goal ->
    SmtLib_GraphPreprocess.validation -> SmtReplayWrapperSession.session

  (* Replay, check the original result while its scope is live, then retire
     that exact scope. The caller retains the session for late immutable
     W.audit with the same original goal and returned theorem. *)
  val prove_cpc_using : SmtReplayWrapperSession.session ->
    {proof : CPC_ProofParser.graph_proof,ordinary_limit : int,
     template_limit : int,worker : CPC_GraphProofReplay.worker,
     force_worker : CPC_GraphProofReplay.worker option} -> Thm.thm
  val prove_z3_using : SmtReplayWrapperSession.session ->
    {proof : Z3_GraphProofParser.proof,template_limit : int,
     local_law : Z3_GraphProofReplay.local_request -> Thm.thm option,
     nnf : Z3_GraphProofReplay.nnf_request -> Thm.thm option} -> Thm.thm
  val discover_with_work : SmtReplayWrapperSession.session ->
    (SmtReplaySource.sources ->
      {work : SmtReplayInvocationWork.portfolio,
       preprocessing : SmtLib_GraphPreprocess.validation}) ->
    SmtReplayInvocationWork.portfolio
  val prove_cpc_with_work_using : SmtReplayInvocationWork.portfolio ->
    SmtReplayWrapperSession.session ->
    {proof : CPC_ProofParser.graph_proof,ordinary_limit : int,
     template_limit : int,worker : CPC_GraphProofReplay.worker,
     force_worker : CPC_GraphProofReplay.worker option} -> Thm.thm
  val prove_z3_with_work_using : SmtReplayInvocationWork.portfolio ->
    SmtReplayWrapperSession.session ->
    {proof : Z3_GraphProofParser.proof,template_limit : int,
     local_law : Z3_GraphProofReplay.local_request -> Thm.thm option,
     nnf : Z3_GraphProofReplay.nnf_request -> Thm.thm option} -> Thm.thm

  val prove_cpc_with_clauses_and_work_using :
    SmtReplayInvocationWork.portfolio -> SmtReplayWrapperSession.session ->
    {proof:CPC_ProofParser.graph_proof,ordinary_limit:int,
     template_limit:int,worker:CPC_GraphProofReplay.worker,
     clause_worker:CPC_GraphProofReplay.clause_worker,
     force_worker:CPC_GraphProofReplay.worker option} -> Thm.thm
  val discover_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayWrapperSession.session ->
    (SmtReplaySource.sources -> SmtLib_GraphPreprocess.validation) -> unit

  (* Packet cleanup stays with the parser owner. These calls perform live
     original Source acceptance and close this exact session on success.
     They do not run inside a caller-owned Work action. *)
  val prove_cpc_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayNativeContract.contract -> SmtReplayWrapperSession.session ->
    {packet:CPC_ProofParser.graph_proof SmtLib_GraphProof.packet,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,ordinal:int} -> Thm.thm
  val prove_z3_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayNativeContract.contract -> SmtReplayWrapperSession.session ->
    {packet:Z3_GraphProofParser.proof SmtLib_GraphProof.packet,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,ordinal:int} -> Thm.thm
end
