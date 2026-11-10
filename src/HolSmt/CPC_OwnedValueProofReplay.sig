(* One genuine named edge -> original Sources -> exact public Goal. *)
signature CPC_SparseOwnedValueProofReplay =
sig
  type invocation
  datatype preparation=Prepared of invocation
    | ReplayNeeds of CPC_OwnedValueNamedReplay.requirement list
  datatype completion=Proved of
      {theorem:Thm.thm,
       dependencies:SmtReplayOwnedValueProof.source_lineage list}
    | RealizationNeeds of SmtReplayValueRealization.requirement list
  (* Outside an action. Actual Work/query/packet headers precede adoption.
     ReplayNeeds retains caller packet ownership. No Source is fabricated. *)
  val prepare_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    CPC_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Outside an action, once only. Genuine RealizationNeeds retains the
     live invocation until close. Success returns exact original Goal and
     allowed canonical Source hypotheses, then closes receiver and packet. *)
  val finish_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> completion
  val close : invocation -> unit
end

(* One genuine named edge -> original Sources -> exact public Goal. *)
signature CPC_OwnedValueProofReplay =
sig
  type invocation
  datatype preparation=Prepared of invocation
    | ReplayNeeds of CPC_OwnedValueNamedReplay.requirement list
  datatype completion=Proved of
      {theorem:Thm.thm,
       dependencies:SmtReplayOwnedValueProof.source_lineage list}
    | RealizationNeeds of SmtReplayValueRealization.requirement list
  (* Outside an action. Actual Work/query/packet headers precede adoption.
     ReplayNeeds retains caller packet ownership. No Source is fabricated. *)
  val prepare_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    CPC_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Outside an action, once only. Genuine RealizationNeeds retains the
     live invocation until close. Success returns exact original Goal and
     allowed canonical Source hypotheses, then closes receiver and packet. *)
  val finish_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> completion
  val close : invocation -> unit
  (* Explicit individual-Hyp Source realization. The ordinary
     methods above retain their original static backend. *)
  structure Sparse : CPC_SparseOwnedValueProofReplay
end
