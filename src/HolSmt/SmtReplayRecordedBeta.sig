signature SmtReplayRecordedBeta =
sig
  type plan
  type conversion
  type request =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio,ordinal : int,
     redex : SmtReplayGraph.closure_child,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit}
  type admitted_request =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio,ordinal : int,
     admission : SmtReplayFocusAdmission.focus,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit}
  val prepare_admitted : admitted_request -> plan
  val prepare : request -> plan
  val execute : plan -> conversion
  val validate : conversion -> unit
  (* Metadata-only, allowed in an existing action; no borrowed Work receipt. *)
  val validate_for :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio} -> conversion -> unit
  val endpoints : conversion ->
    {source : SmtReplayGraph.node,target : SmtReplayGraph.node,
     theorem : Thm.thm}
  (* Shared caller contract; no native credit or admission is minted here. *)
  type native_budget = SmtReplayNativeContract.contract

  type policy_plan
  type policy_conversion
  val prepare_admitted_with_policy :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio,
     ordinal:int,admission:SmtReplayFocusAdmission.policy_focus,
     native_budget:native_budget,check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit} -> policy_plan
  val execute_with_policy : policy_plan -> policy_conversion
  val validate_with_policy : policy_conversion -> unit
  val validate_with_policy_for :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio}
    -> policy_conversion -> unit
  val endpoints_with_policy : policy_conversion ->
    {source:SmtReplayGraph.node,target:SmtReplayGraph.node,theorem:Thm.thm}

end
