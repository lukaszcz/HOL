(* Authentic scoped syntax inventory, not proof/native closure admission. *)
signature SmtReplayOwnedScopedValueContext =
sig
  type context
  type syntax = SmtLib_GraphParserValue.proof_term
  type command =
    {id:Z3_GraphProofParser.proof_id,target:syntax,
     plan:(syntax,SmtLib_GraphParserValue.value) Z3_SharedReplayPlan.plan}
  datatype requirement =
      EnclosingProgramme of Z3_GraphProofParser.proof_id
    | BindingProgramme of SmtLib_GraphFrontend.value_scoped_session
    | LocalSourceClosure of Z3_GraphProofParser.proof_id * syntax
    | NestedProgramme of Z3_GraphProofParser.proof_id
    | RawProgramme of Z3_GraphProofParser.proof_id
  datatype capture = Captured of context | Needs of requirement list
  (* Outside an action. Reads the actual enclosing quant-intro, immediate
     Bind and complete child DAG. No caller frame/body/rule/Source flag,
     callback, native term or readiness certificate is accepted. Captured
     means authenticated syntax only; all native/Hyp/Type and closure
     admission belongs to the subsequent sealed programme producer. *)
  val capture : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {id:Z3_GraphProofParser.proof_id,
     native_contract:SmtReplayNativeContract.contract} -> capture
  (* Caller owns the SAME action. Expected owner is checked before held
     syntax. Neither this DATA projection nor the Scope receipt authorizes
     adopting a caller proof, local hypothesis, or Source occurrence. *)
  val data_for : SmtReplayInvocationWork.portfolio -> context ->
    {query:SmtLib_GraphPreprocess.graph_query,
     packet:Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet,
     values:SmtLib_GraphParserValue.context,
     graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     child:SmtReplayGraph.scope,frame:SmtReplayOwnedScopeReceipt.receipt,
     binding:SmtLib_GraphValueProof.binding_frame,
     target:SmtLib_GraphParserValue.value,
     body:Z3_GraphProofParser.proof_id,lambda_blocks:int list,
     commands:command list,roots:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract}
end
