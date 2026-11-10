(* Automatic trusted producers; compact recipes retain exact proof order. *)
signature SmtLib_CompactCarrierScheduler =
sig
  type owner
  type result
  (* The SAME execution retains genuine original/target D/Q/frame data.
     NONE input is original provenance, not a fabricated opened view. *)
  type source_target
  val run_assumption_target_owned : owner ->
    {occurrence : int,view : SmtReplayGraph.source option} -> source_target
  val run_goal_target_owned : owner ->
    {view : SmtReplayGraph.source option} -> source_target
  val source_target_for : SmtReplayInvocationWork.portfolio -> owner ->
    source_target ->
    {dynamic : SmtReplayOwnedTransport.focus,
     admission : SmtReplayFocusAdmission.focus,
     frame : SmtReplayOwnedScopeReceipt.receipt,
     raw : SmtReplayCanonGraph.graph_conversion option}
  type aux_target
  val begin : SmtReplayInvocationWork.portfolio ->
    {check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} -> owner
  val run_assumption_owned : owner ->
    {occurrence : int,view : SmtReplayGraph.source option} -> result option
  val run_goal_owned : owner ->
    {view : SmtReplayGraph.source option} -> result option
  (* Genuine selected closed auxiliary, never an ordinary Source ordinal.
     Both changed/identity routes return a SAME-owned checked D equality. *)
  val run_aux_owned : owner ->
    {law : SmtLib_GraphSelectedAuxiliary.receipt} ->
    SmtReplayOwnedTransport.conversion
  (* SAME completed execution retains its genuine lower target/frame.
     Unchanged keeps the captured original pair; changed keeps its actual
     generated pair. No metadata reconstruction or external theorem pair. *)
  val run_aux_target_owned : owner ->
    {law : SmtLib_GraphSelectedAuxiliary.receipt} -> aux_target
  val aux_target_for : SmtReplayInvocationWork.portfolio -> owner ->
    aux_target -> {dynamic : SmtReplayOwnedTransport.focus,
      admission : SmtReplayFocusAdmission.focus,
      frame : SmtReplayOwnedScopeReceipt.receipt,
      conversion : SmtReplayOwnedTransport.conversion}
  (* RAW original source -> final result. Positive goals stay positive
     here; the stage wraps the exact original fixed denial constructor. *)
  val graph_conversion_for : owner -> result ->
    SmtReplayCanonGraph.graph_conversion
  (* Pure backing metadata, expected Work checked before activation. *)
  val validate_for : SmtReplayInvocationWork.portfolio -> owner -> unit
  (* Same expected-owner guard, forcing a full backing pass at callbacks. *)
  val revalidate_for : SmtReplayInvocationWork.portfolio -> owner -> unit
  (* SAME authentic scheduler counter; not a past Work entitlement. *)
  val normalization_ordinal : owner -> int
  val close : owner -> unit
  (* Root-redex execution only; carrier/descent/Core are separate producers. *)
  type policy_owner
  type policy_result
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    {native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit} -> policy_owner
  val validate_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_owner -> unit
  val run_root_beta_assumption_with_policy : policy_owner ->
    {occurrence:IntInf.int,view:SmtReplayGraph.source option} ->
    policy_result option
  val run_root_beta_goal_with_policy : policy_owner ->
    {view:SmtReplayGraph.source option} -> policy_result option
  val source_conversion_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_owner -> policy_result ->
    SmtReplayProof.closed_conversion
  val denial_conversion_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_owner -> policy_result ->
    SmtReplayGraph.source -> SmtReplayProof.closed_conversion
  val target_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_owner -> policy_result -> SmtReplayGraph.node
  (* Genuine application descent and rebuilt-parent beta continuation.
     Standalone abstraction bodies/carrier recognition are separate. *)
  val run_recursive_application_beta_assumption_with_policy : policy_owner ->
    {occurrence:IntInf.int,view:SmtReplayGraph.source option} ->
    policy_result option
  val run_recursive_application_beta_goal_with_policy : policy_owner ->
    {view:SmtReplayGraph.source option} -> policy_result option
  (* Actual body Scope receipts and canonical Lambda equality lifting. *)
  val run_recursive_scope_beta_assumption_with_policy : policy_owner ->
    {occurrence:IntInf.int,view:SmtReplayGraph.source option} ->
    policy_result option
  val run_recursive_scope_beta_goal_with_policy : policy_owner ->
    {view:SmtReplayGraph.source option} -> policy_result option
  type policy_carrier_owner
  val begin_carrier_with_policy : SmtReplayInvocationWork.portfolio ->
    {native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit} -> policy_carrier_owner
  val validate_carrier_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner -> unit
  (* One action on the SAME authentic scheduler counter; no new credit. *)
  val carrier_normalization_ordinal_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner -> int
  val run_carrier_assumption_with_policy : policy_carrier_owner ->
    {occurrence:IntInf.int,view:SmtReplayGraph.source option} ->
    policy_result option
  val run_carrier_goal_with_policy : policy_carrier_owner ->
    {view:SmtReplayGraph.source option} -> policy_result option
  val carrier_source_conversion_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner ->
    policy_result ->
    SmtReplayProof.closed_conversion
  val carrier_denial_conversion_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner ->
    policy_result ->
    SmtReplayGraph.source -> SmtReplayProof.closed_conversion
  val carrier_target_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_carrier_owner -> policy_result -> SmtReplayGraph.node
  type policy_carrier_aux_target
  val run_carrier_aux_target_with_policy : policy_carrier_owner ->
    {law:SmtLib_GraphSelectedAuxiliary.policy_receipt} ->
    policy_carrier_aux_target
  val carrier_aux_target_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner ->
    policy_carrier_aux_target ->
    {dynamic:SmtReplayOwnedTransport.policy_focus,
     admission:SmtReplayFocusAdmission.policy_focus,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     conversion:SmtReplayOwnedTransport.policy_conversion}
  val native_contract_carrier_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner ->
    SmtReplayNativeContract.contract
  (* A suffix starts at the genuine discovery view. Raw Source alpha is
     retained separately; this is not a raw Source conversion claim. *)
  type policy_metadata_source_target
  val run_carrier_assumption_metadata_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner ->
    {occurrence:IntInf.int,
     partial:SmtReplayGraph.policy_partial_discovery} ->
    policy_metadata_source_target
  val run_carrier_goal_metadata_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner ->
    {partial:SmtReplayGraph.policy_partial_discovery} ->
    policy_metadata_source_target
  val carrier_metadata_source_target_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner ->
    policy_metadata_source_target ->
    {dynamic:SmtReplayOwnedTransport.policy_focus,
     admission:SmtReplayFocusAdmission.policy_focus,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     original:SmtReplayGraph.source,view:SmtReplayGraph.source option,
     partial:SmtReplayGraph.policy_partial_discovery,
     alpha:SmtReplayGraph.carrier_alpha option,
     suffix:SmtReplayCanonGraph.graph_conversion option,
     conversion:SmtReplayOwnedTransport.policy_conversion option}

  (* Whole raw Source -> actual current target grammar. Only genuine saved
     Alpha leaves mint native facts; application/sequence remain metadata
     until the actual Core assembler. No caller raw pair is accepted. *)
  type policy_complete_source_target
  val complete_carrier_metadata_source_target_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner ->
    policy_metadata_source_target -> policy_complete_source_target
  val carrier_complete_source_target_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_carrier_owner ->
    policy_complete_source_target ->
    {dynamic:SmtReplayOwnedTransport.policy_focus,
     admission:SmtReplayFocusAdmission.policy_focus,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     original:SmtReplayGraph.source,view:SmtReplayGraph.source option,
     source:SmtReplayGraph.node,target:SmtReplayGraph.node,
     recipe:SmtReplayCanonGraph.graph_conversion option}

end
