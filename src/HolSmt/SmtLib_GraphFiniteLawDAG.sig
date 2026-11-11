(* Source-free conditional laws, with actual finite native realization. *)
signature SmtLib_GraphFiniteLawDAG =
sig
  type context
  type conditional
  (* Construction, schema, condition and description methods run inside the
     caller's action. The actual frame retains original Work/Sources/root;
     arbitrary graph/scope labels cannot substitute for that receipt. *)
  val create_with_policy : SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit} -> context
  (* Conditional body laws may retain evidence in their genuine ancestor
     frame. Statements and targets still use frame; only conjunctions of
     already-visible conditions are built in condition_frame. Neither
     scope labels nor semantic equality can move a private condition. *)
  val create_with_condition_frame_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     condition_frame:SmtReplayOwnedScopeReceipt.receipt,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit} -> context
  (* Same bounded declaration matcher used by the finite query producer.
     Returns a CLOSED curried schema, not a Source-dependent application. *)
  val schema_with_policy : SmtReplayInvocationWork.portfolio -> context ->
    {theorem:Thm.thm,premises:SmtReplayGraph.node list,
     target:SmtReplayGraph.node} -> SmtLib_GraphSourcePortfolio.fact
  val of_closed_with_policy : SmtReplayInvocationWork.portfolio -> context ->
    SmtLib_GraphSourcePortfolio.fact -> conditional
  (* Evidence E issues only the tautology E ==> E. It creates no assumption
     fact or Source. Ordered actual evidence endpoints remain DATA, to be
     discharged later by genuine current facts at the root proof boundary. *)
  val evidence_with_policy : SmtReplayInvocationWork.portfolio -> context ->
    SmtReplayGraph.node -> conditional
  val apply_with_policy : SmtReplayInvocationWork.portfolio -> context ->
    {law:SmtLib_GraphSourcePortfolio.fact,premises:conditional list,
     target:SmtReplayGraph.node} -> conditional
  val description_with_policy_for : SmtReplayInvocationWork.portfolio ->
    context -> conditional ->
    {fact:SmtLib_GraphSourcePortfolio.fact,
     condition:SmtReplayGraph.node option,evidence:SmtReplayGraph.node list,
     target:SmtReplayGraph.node}
  (* Outside an action. Native Context, closing implication, final law and
     repeated Type incidence must meet the actual caller's finite contract
     BEFORE freeze/realization. Returns an existing genuine closed fact;
     no equality-only receipt or Source-bearing theorem is accepted. *)
  val realize_with_policy : SmtReplayInvocationWork.portfolio -> context ->
    conditional -> SmtReplayProof.closed_fact
end
