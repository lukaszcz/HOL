(* A registered opening becomes proof only through the existing executor. *)
signature SmtLib_GraphCheckedOpening =
sig
  (* Call outside an owned action. The exact frame and native contract
     retain the original Work/Sources and existing native bounds. Ordinary
     application DAGs are closed nodewise on typed names and genuine child
     cuts. Only an already admitted opaque binder uses its actual bounded
     native bridge; this operation performs no new opening/admission.
     The result is the existing Source-free checked conversion, never a
     helper permission, caller theorem or semantic equality assertion. *)
  val bridge_with_policy : SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     original:SmtReplayGraph.node,opened:SmtReplayGraph.node,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit} -> SmtReplayProof.closed_conversion
  (* SAME authentic execution, additionally projecting its existing scoped
     Generated equality receipt. This is the actual proof boundary for an
     A.generated_scoped_with_policy focus descent in the same frame; it
     grants no opening, Source, native allowance or scope relabeling. *)
  val bridge_generated_with_policy : SmtReplayInvocationWork.portfolio ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     original:SmtReplayGraph.node,opened:SmtReplayGraph.node,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit} ->
    {conversion:SmtReplayProof.closed_conversion,
     generated:SmtReplayProof.scoped_generated_equality}
end
