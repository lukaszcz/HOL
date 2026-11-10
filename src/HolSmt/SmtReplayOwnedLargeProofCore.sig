(* Nominal public-proof quote, not private/kernel/global work admission. *)
signature SmtReplayOwnedLargeProofCore =
sig
  type plan
  type result
  type summary =
    {leaves : int,steps : int,public_operations : int,
     assembly_work : IntInf.int,realization_work : IntInf.int,
     dictionary_work : IntInf.int,type_projection_work : IntInf.int,
     compact_context : IntInf.int * IntInf.int * IntInf.int,
     comparison_context : IntInf.int * IntInf.int * IntInf.int}
  val prepare : SmtReplayInvocationWork.portfolio ->
    {conversion : SmtReplayCanonGraph.graph_conversion,ordinal : int,
     check_type : Type.hol_type -> unit} -> plan
  (* SAME original-Work Root/body receipt; no caller Scope scalar. *)
  val prepare_in_scope : SmtReplayInvocationWork.portfolio ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     conversion : SmtReplayCanonGraph.graph_conversion,ordinal : int,
     check_type : Type.hol_type -> unit} -> plan
  val report : plan -> summary
  (* SAME original Work; one execution, no supplied theorem/Source leaves. *)
  val execute : SmtReplayInvocationWork.portfolio -> plan -> result
  val theorem_for : SmtReplayInvocationWork.portfolio -> result -> Thm.thm
  (* The SAME internal engine result, never an external theorem/node pair. *)
  val realization_for : SmtReplayInvocationWork.portfolio -> result ->
    SmtReplayProof.realization
  (* Semantic DATA from THIS opaque result. Expected Work is checked
     before activating its held owner. No past Work or raw Source grant. *)
  val conversion_description_for : SmtReplayInvocationWork.portfolio ->
    result -> {graph : SmtReplayGraph.graph,root : SmtReplayGraph.scope,
      scope : SmtReplayGraph.scope,
      sources : SmtReplaySource.sources,source : SmtReplayGraph.node,
      target : SmtReplayGraph.node}
  type policy_plan
  type policy_result
  val prepare_in_scope_with_policy : SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     conversion:SmtReplayCanonGraph.graph_conversion,ordinal:int,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> policy_plan
  val execute_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_plan -> policy_result
  val theorem_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_result -> Thm.thm
  val realization_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_result -> SmtReplayProof.policy_source_realization
  val conversion_description_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_result ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     source:SmtReplayGraph.node,target:SmtReplayGraph.node}
  val native_contract_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_result ->
    SmtReplayNativeContract.contract
  val conversion_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_result -> SmtReplayProof.closed_conversion

end
