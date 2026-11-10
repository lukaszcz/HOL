(* Closed local lambda lift; supplied P evidence is not a Work receipt. *)
signature SmtReplayOwnedLambda =
sig
  type plan
  type conversion
  type request =
    {graph : SmtReplayGraph.graph,caller : SmtReplayGraph.scope,
     scope : SmtReplayGraph.scope,sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio,ordinal : int,
     binder : SmtReplayGraph.binder_closure,
     body_fact : SmtReplayProof.closed_fact,
     check_type : Type.hol_type -> unit}
  (* caller is the fixed handle caller; scope is the active traversal frame.
     The body's actual frame comes ONLY from the genuine recorded closure.
     A future owned transport must validate its body conversion receipt
     before giving this semantic fact. No prior-work grant is inferred. *)
  val prepare : request -> plan
  type admitted_request =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio,ordinal : int,
     admission : SmtReplayFocusAdmission.focus,
     body_fact : SmtReplayProof.closed_fact,
     check_type : Type.hol_type -> unit}
  val prepare_admitted : admitted_request -> plan
  val execute : plan -> conversion
  (* Metadata validation, allowed inside an existing Work action. *)
  val validate_for :
    {graph : SmtReplayGraph.graph,caller : SmtReplayGraph.scope,
     scope : SmtReplayGraph.scope,sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio} -> conversion -> unit
  val endpoints : conversion ->
    {source : SmtReplayGraph.node,target : SmtReplayGraph.node,
     theorem : Thm.thm}
  type policy_plan
  type policy_conversion
  type policy_request=
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio,
     ordinal:int,admission:SmtReplayFocusAdmission.policy_focus,
     body_fact:SmtReplayProof.closed_fact,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type->unit}
  val prepare_admitted_with_policy : policy_request -> policy_plan
  val execute_with_policy : policy_plan -> policy_conversion
  val validate_with_policy_for :
    {graph:SmtReplayGraph.graph,caller:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     work:SmtReplayInvocationWork.portfolio} -> policy_conversion -> unit
  val endpoints_with_policy_for :
    {graph:SmtReplayGraph.graph,caller:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     work:SmtReplayInvocationWork.portfolio} -> policy_conversion ->
    {source:SmtReplayGraph.node,target:SmtReplayGraph.node,theorem:Thm.thm}

  type canonical_policy_plan
  type canonical_policy_conversion
  val prepare_canonical_admitted_with_policy :
    policy_request -> canonical_policy_plan
  val execute_canonical_with_policy :
    canonical_policy_plan -> canonical_policy_conversion
  val validate_canonical_with_policy_for :
    {graph:SmtReplayGraph.graph,caller:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     work:SmtReplayInvocationWork.portfolio} ->
    canonical_policy_conversion -> unit
  val endpoints_canonical_with_policy_for :
    {graph:SmtReplayGraph.graph,caller:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     work:SmtReplayInvocationWork.portfolio} -> canonical_policy_conversion ->
    {source:SmtReplayGraph.node,target:SmtReplayGraph.node,theorem:Thm.thm}

  (* Bounded conditional lift of the genuine closed body_fact
     E ==> (old_body = new_body). E is read from that same fact and needs
     an already exact graph free-variable inventory: opaque-condition
     opening requires a separate pre-effect bridge portfolio. Both actual
     graph binder identity and native binder freshness must exclude E.
     The existing fully realized input/output/template/type-work bounds
     apply before UNDISCH/ABS/DISCH. This does not admit an unbounded
     changed binder or alter the unchanged retained-binder path. The
     result is conditional; it is never an unconditional conversion. *)
  type conditional_policy_plan
  type conditional_policy_conversion
  val prepare_conditional_admitted_with_policy :
    policy_request -> conditional_policy_plan
  val execute_conditional_with_policy :
    conditional_policy_plan -> conditional_policy_conversion
  val validate_conditional_with_policy_for :
    {graph:SmtReplayGraph.graph,caller:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     work:SmtReplayInvocationWork.portfolio} ->
    conditional_policy_conversion -> unit
  val endpoints_conditional_with_policy_for :
    {graph:SmtReplayGraph.graph,caller:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     work:SmtReplayInvocationWork.portfolio} ->
    conditional_policy_conversion ->
    {condition:SmtReplayGraph.node,source:SmtReplayGraph.node,
     target:SmtReplayGraph.node,theorem:Thm.thm}

  (* Read-only original native contract, authenticated through the SAME
     conditional receipt validator before private request backing. *)
  val conditional_native_contract_with_policy_for :
    {graph:SmtReplayGraph.graph,caller:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     work:SmtReplayInvocationWork.portfolio} ->
    conditional_policy_conversion -> SmtReplayNativeContract.contract
end
