(* Semantic conversions with retained SAME original invocation ownership. *)
signature SmtReplayOwnedTransport =
sig
  type focus
  type conversion
  type application_plan
  datatype provenance = OriginalOccurrence | OriginalDescendant
                      | GeneratedResult | GeneratedDescendant
                      | OriginalPositiveGoal | PositiveGoalDescendant
                      | UnopenedPositiveGoal | UnopenedGoalDescendant
                      | UnopenedOriginalOccurrence
                      | UnopenedOriginalDescendant
                      | ClosedAuxiliaryRoot | ClosedAuxiliaryDescendant
  val start : SmtReplayInvocationWork.portfolio ->
    {occurrence : int,view : SmtReplayGraph.source} -> focus
  (* NONE retains raw positive Source DATA without issuing an opened view.
     Applicable local operations own admission, not the whole Goal DAG. *)
  val start_goal : SmtReplayInvocationWork.portfolio ->
    {view : SmtReplayGraph.source option} -> focus
  (* Genuine assumption index >=1; NONE has no opened recipe.
     Local producers retain their original operation admission. *)
  val start_assumption : SmtReplayInvocationWork.portfolio ->
    {occurrence : int,view : SmtReplayGraph.source option} -> focus
  (* Genuine exact selected closed-law receipt; public occurrence NONE. *)
  val start_auxiliary : SmtReplayInvocationWork.portfolio ->
    {law : SmtLib_GraphSelectedAuxiliary.receipt} -> focus
  val node : focus -> SmtReplayGraph.node
  val scope : focus -> SmtReplayGraph.scope
  val child : focus -> SmtReplayGraph.closure_child
  val provenance : focus -> provenance
  (* Expected ownership is checked before activating the held focus.
     Positive Goal roots/descendants have no public Source occurrence. *)
  val description_for :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio} -> focus ->
    {node : SmtReplayGraph.node,scope : SmtReplayGraph.scope,
     provenance : provenance,occurrence : int option}
  (* Index in denied-goal followed by original ordered assumptions. *)
  val original_occurrence : focus -> int
  (* The first original occurrence and opened canonical view stay separate.
     Descendants retain this root provenance, not invented raw incidence. *)
  val root_sources : focus ->
    {original : SmtReplayGraph.source,opened : SmtReplayGraph.source}
  val application_children : focus -> focus * focus
  val binder_body : focus -> focus
  val adopt_beta : focus -> SmtReplayRecordedBeta.conversion -> conversion
  val adopt_carrier : focus -> SmtLib_GraphCarrierRoot.conversion -> conversion
  (* Expected owner/frame checks precede conversion activation. ONE
     complete guard validates all retained backing paths and endpoints;
     only private immutable node/frame fields are then projected. No
     theorem, Work credit, callback or cross-call cache is returned. *)
  val conversion_description_for :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,work : SmtReplayInvocationWork.portfolio}
    -> conversion ->
    {source : SmtReplayGraph.node,target : SmtReplayGraph.node,
     scope : SmtReplayGraph.scope}
  (* Exact opaque compact result; genuine source/frame receipt required.
     The result itself authenticates BOTH endpoints and its theorem. *)
  val adopt_compact : focus -> SmtReplayOwnedLargeProofCore.result ->
    conversion
  (* Existing original caps; body definitions closed by the SAME Core. *)
  val adopt_realized_lambda : focus -> SmtReplayOwnedRealizedLambda.result ->
    conversion
  val target_focus : conversion -> focus
  val endpoints : conversion ->
    {source : SmtReplayGraph.node,target : SmtReplayGraph.node,
     theorem : Thm.thm}
  val compose :
    {first : conversion,second : conversion,ordinal : int,
     check_type : Type.hol_type -> unit} -> conversion
  val prepare_application :
    {parent : focus,left : conversion option,right : conversion option,
     ordinal : int,check_type : Type.hol_type -> unit} -> application_plan
  val execute_application : application_plan -> conversion
  (* Creates checked evidence internally, after validating its owned chain.
     The returned P fact alone carries no past Work or receipt authority. *)
  val closed_fact : conversion ->
    {ordinal : int,check_type : Type.hol_type -> unit} ->
    SmtReplayProof.closed_fact
  val closed_fact_for :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio} -> conversion ->
    {ordinal : int,check_type : Type.hol_type -> unit} ->
    SmtReplayProof.closed_fact
  val lift_lambda :
    {parent : focus,body : conversion,record_ordinal : int,
     lift_ordinal : int,check_type : Type.hol_type -> unit} -> conversion
  val lift_lambda_admitted :
    {parent : focus,admission : SmtReplayFocusAdmission.focus,
     body : conversion,record_ordinal : int,lift_ordinal : int,
     check_type : Type.hol_type -> unit} -> conversion
  val alpha_changed : conversion -> bool
  val alpha_changed_admitted :
    {conversion : conversion,admission : SmtReplayFocusAdmission.focus} -> bool
  (* ROOT occurrence only. Canonical RAW Source -> generated target for
     GP/F, preserving the original dependency node/index. SAME Work quotes
     the target identity view, bridge and P callbacks before execution. *)
  val source_conversion : conversion ->
    {ordinal : int,check_type : Type.hol_type -> unit} ->
    SmtReplayProof.closed_conversion
  (* Only an actually owned, opened POSITIVE Goal conversion. Fixed
     negation is wrapped AFTER traversal, under SAME template/Work. *)
  val denial_conversion : conversion ->
    {denial_view : SmtReplayGraph.source,ordinal : int,
     check_type : Type.hol_type -> unit} -> SmtReplayProof.closed_conversion
  (* ROOT occurrence only; restores its retained genuine whole raw bridge. *)
  val restore_original : conversion ->
    {ordinal : int,check_type : Type.hol_type -> unit} -> Thm.thm
  type policy_focus
  type policy_conversion
  val start_goal_with_policy : SmtReplayInvocationWork.portfolio ->
    {view:SmtReplayGraph.source option,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> policy_focus
  val start_assumption_with_policy : SmtReplayInvocationWork.portfolio ->
    {occurrence:IntInf.int,view:SmtReplayGraph.source option,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> policy_focus
  val description_with_policy_for :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio}
    -> policy_focus ->
    {node:SmtReplayGraph.node,scope:SmtReplayGraph.scope,
     provenance:provenance,occurrence:IntInf.int option}
  val child_with_policy : policy_focus -> SmtReplayGraph.closure_child
  val application_children_with_policy : policy_focus ->
    policy_focus * policy_focus
  val binder_body_with_policy : policy_focus -> policy_focus
  val adopt_beta_with_policy : policy_focus ->
    SmtReplayRecordedBeta.policy_conversion -> policy_conversion
  val target_focus_with_policy : policy_conversion -> policy_focus
  val endpoints_with_policy : policy_conversion ->
    {source:SmtReplayGraph.node,target:SmtReplayGraph.node,theorem:Thm.thm}
  val conversion_description_with_policy_for :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio}
    -> policy_conversion ->
    {source:SmtReplayGraph.node,target:SmtReplayGraph.node,
     scope:SmtReplayGraph.scope}
  val source_conversion_with_policy : policy_conversion ->
    {ordinal:int,check_type:Type.hol_type -> unit} ->
    SmtReplayProof.closed_conversion
  type policy_application_plan
  val compose_with_policy :
    {first:policy_conversion,second:policy_conversion,ordinal:int,
     check_type:Type.hol_type -> unit} -> policy_conversion
  val prepare_application_with_policy :
    {parent:policy_focus,left:policy_conversion option,
     right:policy_conversion option,ordinal:int,
     check_type:Type.hol_type -> unit} -> policy_application_plan
  val execute_application_with_policy : policy_application_plan ->
    policy_conversion
  val closed_fact_with_policy_for :
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,work:SmtReplayInvocationWork.portfolio}
    -> policy_conversion -> {ordinal:int,check_type:Type.hol_type -> unit} ->
    SmtReplayProof.closed_fact
  (* Whole import/opened association for the actual Lambda body producer. *)
  val denial_conversion_with_policy : policy_conversion ->
    {denial_view:SmtReplayGraph.source,ordinal:int,
     check_type:Type.hol_type -> unit} -> SmtReplayProof.closed_conversion
  val closed_generated_equality_with_policy_for :
    SmtReplayFocusAdmission.expected -> policy_conversion ->
    {ordinal:int,check_type:Type.hol_type -> unit} ->
    SmtReplayProof.scoped_generated_equality
  val lift_lambda_canonical_admitted_with_policy :
    {parent:policy_focus,admission:SmtReplayFocusAdmission.policy_focus,
     body:policy_conversion,record_ordinal:int,lift_ordinal:int,
     check_type:Type.hol_type -> unit} -> policy_conversion
  val adopt_profiled_carrier_with_policy : policy_focus ->
    SmtLib_GraphCarrierRoot.profiled_policy_conversion -> policy_conversion
  val original_lineage_with_policy_for :
    SmtReplayFocusAdmission.expected -> policy_focus -> IntInf.int
  val start_auxiliary_native_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {law:SmtLib_GraphSelectedAuxiliary.policy_receipt,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> policy_focus
  val identity_auxiliary_with_policy_for :
    SmtReplayFocusAdmission.expected -> policy_focus ->
    {ordinal:int,check_type:Type.hol_type -> unit} -> policy_conversion
  val adopt_core_with_policy_for : SmtReplayFocusAdmission.expected ->
    policy_focus -> SmtReplayOwnedLargeProofCore.policy_result ->
    policy_conversion
  val native_contract_conversion_with_policy_for :
    SmtReplayFocusAdmission.expected -> policy_conversion ->
    SmtReplayNativeContract.contract
  val root_sources_with_policy_for : SmtReplayFocusAdmission.expected ->
    policy_focus ->
    {original:SmtReplayGraph.source,view:SmtReplayGraph.source option}

end
