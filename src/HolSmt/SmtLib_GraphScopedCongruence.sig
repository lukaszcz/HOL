(* Nodewise equality in one authentic proof frame. *)
signature SmtLib_GraphScopedCongruence =
sig
  type plan
  datatype preparation = DifferentShape | Prepared of plan
  (* Outside-action metadata preparation. Only identical owned leaves and
     ordinary applications are matched. A changed target application must
     actually belong to the supplied frame: no node is rehomed or relabeled.
     DifferentShape is unfinished DATA, never a proof or resource refusal.
     Preparation constructs no graph node and performs no native proof. *)
  val prepare_with_policy : SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     source:SmtReplayGraph.node,target:SmtReplayGraph.node,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit} -> preparation
  (* Outside-action execution, using the original Core/native bounds and
     genuine completed Source-free child cuts. No raw theorem is supplied.
     Plans retain exact owner, epochs, closure lifetimes and endpoints. *)
  val execute_with_policy : SmtReplayInvocationWork.portfolio -> plan ->
    SmtReplayProof.closed_fact
end
