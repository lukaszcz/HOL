(* Genuine packet-owned finite child closure, then the actual BinderClose. *)
signature SmtReplayOwnedScopedValueLift =
sig
  type plan
  datatype requirement = Enclosing of
      SmtReplayOwnedScopedValueContext.requirement
    | ChildOpening of SmtLib_GraphParserValue.proof_term
    | BindingShape
    | TargetProgramme of SmtLib_GraphParserValue.value
    | TargetOpening of SmtReplayGraph.scope * SmtReplayGraph.node
  datatype preparation = Prepared of plan | Needs of requirement list
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {id:Z3_GraphProofParser.proof_id,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* SAME original action. Only the real Binder producer consumes this
     opaque plan; no caller body, native proof or generalization flag. *)
  val execute_in_action : SmtReplayInvocationWork.portfolio -> plan ->
    SmtReplayProof.closed_fact
  (* SAME action, immutable ports from the authentic packet/Bind. *)
  val data_for : SmtReplayInvocationWork.portfolio -> plan ->
    {query:SmtLib_GraphPreprocess.graph_query,
     context:SmtLib_GraphParserValue.context,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     binding:SmtLib_GraphValueProof.binding_frame,
     native_contract:SmtReplayNativeContract.contract,
     statement:SmtLib_GraphParserValue.value,law_node:SmtReplayGraph.node,
     aliases:(SmtLib_GraphParserValue.proof_term *
       SmtReplayGraph.node) list}
end
