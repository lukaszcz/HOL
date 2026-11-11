(* Additive exact fixed NUM context; old carrier/default APIs unchanged. *)
signature SmtLib_OwnedFixedNumSourceStage =
sig
  type owner
  val begin : SmtReplayInvocationWork.portfolio ->
    {import_limit:int,check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit} -> owner
  (* Carrier TOP_DEPTH, whole beta, then fixed SIMPLE, per original Source.
     Assertions first, positive Goal next, authentic fixed denial last. *)
  val build : owner -> SmtLib_GraphPreprocess.validation
  (* Complete needed-law batch uses the SAME fixed NUM producer and owner. *)
  val build_needed : owner -> SmtLib_GraphPreprocess.validation
  val close : owner -> unit
  (* One actual fixed-context Stage owner, including its shared traversal,
     catalogue and Simple callback transcript. No default is selected. *)
  type policy_needed_owner
  val begin_needed_with_policy : SmtReplayInvocationWork.portfolio ->
    {native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit} -> policy_needed_owner
  val traversal_needed_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_needed_owner ->
    SmtLib_CompactCarrierScheduler.policy_carrier_owner
  val numeric_needed_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_needed_owner ->
    SmtLib_FixedNumericSimple.policy_owner
  val finish_needed_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_needed_owner -> SmtLib_GraphSourcePortfolio.validation ->
    SmtLib_GraphPreprocess.validation

end
