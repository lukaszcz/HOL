(* One actual CPC packet; unsupported programmes are DATA before inference. *)
signature CPC_OwnedValueNamedReplay =
sig
  type invocation
  datatype requirement =
      RuleProgramme of {id:string,rule:CPC_Proof.proof_rule,pop:bool}
    | ScopeProgramme of {id:string,assumption:bool}
    | RecordedConclusion of string
    | CurrentSourceTransport of
        {id:string,value:SmtLib_GraphParserValue.value}
    | SourceOpening of SmtReplayGraph.scope * SmtReplayGraph.node
  datatype preparation = Prepared of invocation | Needs of requirement list
  (* Outside an action. Assertions are the actual current ordered query
     assumptions followed by denial, checked by the existing private block.
     Matching duplicate values selects their first actual occurrence; ports
     themselves remain distinct. No original Source or Scope is invented. *)
  val prepare_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    CPC_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  val replay_next_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> {id:string,node:SmtLib_GraphParserValue.value} option
  val step_with_policy_for : SmtReplayInvocationWork.portfolio -> invocation ->
    string -> {block:SmtReplayOwnedValueProof.block,
      node:SmtLib_GraphParserValue.value,edge:SmtReplayOwnedValueProof.edge}
  val close : invocation -> unit
end
