(* One root carrier step, not TOP_DEPTH traversal or a beta stage. *)
signature SmtLib_GraphCarrierRoot =
sig
  type plan
  type conversion
  type request =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio,ordinal : int,
     original : SmtReplayGraph.node,view : SmtReplayGraph.source,
     predicate_view : SmtReplayGraph.source,
     law : SmtReplayProof.closed_fact,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit}
  type closure_request =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,work : SmtReplayInvocationWork.portfolio,
     ordinal : int,original : SmtReplayGraph.closure_child,
     law : SmtReplayProof.closed_fact,check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit}
  type admitted_request =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,work : SmtReplayInvocationWork.portfolio,
     ordinal : int,admission : SmtReplayFocusAdmission.focus,
     law : SmtReplayProof.closed_fact,check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit}
  val prepare_closure_admitted : admitted_request -> plan
  (* Exact canonical closure; no fresh opened-view proof is requested. *)
  val prepare_closure : closure_request -> plan
  (* SAME Work owner may have a different original root scope; this scope
     is the actual traversal frame. All supplied views are genuine records.
     The selected original law is one of the four exact stock theorems. *)
  val prepare : request -> plan
  val execute : plan -> conversion
  val validate : conversion -> unit
  (* Metadata-only validation of the consumer's exact original receipt. *)
  val validate_for :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio} -> conversion -> unit
  val endpoints : conversion ->
    {source : SmtReplayGraph.node,target : SmtReplayGraph.node,
     theorem : Thm.thm}
  type policy_plan
  type policy_conversion
  type policy_admitted_request=
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio,
     ordinal:int,admission:SmtReplayFocusAdmission.policy_focus,
     law:SmtReplayProof.closed_fact,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type->unit,scope_opened:SmtReplayGraph.scope->unit}
  val prepare_closure_admitted_with_policy :
    policy_admitted_request -> policy_plan
  val execute_with_policy : policy_plan -> policy_conversion
  val validate_with_policy_for :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio} ->
    policy_conversion -> unit
  val endpoints_with_policy_for :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio} ->
    policy_conversion ->
    {source:SmtReplayGraph.node,target:SmtReplayGraph.node,theorem:Thm.thm}

  type profiled_policy_plan
  type profiled_policy_conversion
  val prepare_closure_profiled_admitted_with_policy :
    policy_admitted_request -> profiled_policy_plan
  val execute_profiled_with_policy :
    profiled_policy_plan -> profiled_policy_conversion
  val validate_profiled_with_policy_for :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio} ->
    profiled_policy_conversion -> unit
  val endpoints_profiled_with_policy_for :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio} ->
    profiled_policy_conversion ->
    {source:SmtReplayGraph.node,target:SmtReplayGraph.node,theorem:Thm.thm}

end
