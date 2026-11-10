(* Fixed-context PURE_ss numeric phase only; no default selector change. *)
signature SmtLib_FixedNumericSimple =
sig
  type owner
  type plan
  type result
  val begin : SmtReplayInvocationWork.portfolio ->
    {catalogue : SmtLib_GraphNumericCanonical.catalogue,
     traversal : SmtLib_CompactCarrierScheduler.owner,
     check_type : Type.hol_type -> unit} -> owner
  (* Metadata only; expected Work is checked before held-owner activation.
     No completed result or earlier policy invocation grants future work. *)
  val validate_for : SmtReplayInvocationWork.portfolio -> owner -> unit
  (* The same complete backing guards, memoized by the authentic graph
     revision/private retained-list generation; cheap owner/epochs run always. *)
  val validate_cached_for : SmtReplayInvocationWork.portfolio -> owner -> unit
  val prepare : owner ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     admission : SmtReplayFocusAdmission.focus} -> plan
  val execute : plan -> result
  (* NONE is a complete fixed-context no-change result, never unknown or
     resource failure. It does not mint a new whole-tree identity proof. *)
  val execute_changed : plan -> result option
  (* Genuine T target receipt. Normalize its target, then compose the
     retained original auxiliary prefix; no theorem/node/counter pairing. *)
  val normalize_aux : owner ->
    SmtLib_CompactCarrierScheduler.aux_target ->
    SmtReplayOwnedTransport.conversion
  (* One SAME-scoped genuine Core closure; no theorem/node constructor. *)
  val core_for : SmtReplayInvocationWork.portfolio -> result ->
    SmtReplayOwnedLargeProofCore.result
  type policy_owner
  type policy_plan
  type policy_result
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    {catalogue:SmtLib_GraphNumericCanonical.policy_catalogue,
     traversal:SmtLib_CompactCarrierScheduler.policy_carrier_owner,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type->unit} -> policy_owner
  val validate_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_owner -> unit
  val validate_cached_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_owner -> unit
  val prepare_with_policy : policy_owner ->
    {frame:SmtReplayOwnedScopeReceipt.receipt,
     admission:SmtReplayFocusAdmission.policy_focus} -> policy_plan
  val execute_with_policy : policy_plan -> policy_result
  (* Complete fixed-context no-change only. Resource/unknown is refusal. *)
  val execute_changed_with_policy : policy_plan -> policy_result option
  val core_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_result -> SmtReplayOwnedLargeProofCore.policy_result
  (* Actual selected auxiliary lease and original retained prefix. *)
  val normalize_aux_with_policy : policy_owner ->
    SmtLib_CompactCarrierScheduler.policy_carrier_aux_target ->
    SmtReplayOwnedTransport.policy_conversion

end
