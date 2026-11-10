(* Checked finite-query transport. Planning DATA is not proof authority. *)
signature SmtLib_GraphFiniteQueryTransport =
sig
  type plan
  datatype requirement =
      CheckedBinderBody of SmtLib_GraphQueryAnalysis.scoped_node
    | CheckedAlphaEvidence of
        {subject:SmtLib_GraphQueryAnalysis.scoped_node,
         saved:SmtLib_GraphQueryAnalysis.scoped_node}
    | CheckedParsedLiteral of SmtLib_GraphQueryAnalysis.scoped_node
    | CheckedOpening of
        {original:SmtLib_GraphQueryAnalysis.scoped_node,
         opened:SmtLib_GraphQueryAnalysis.scoped_node}
  datatype preparation = Ready of plan | Needs of requirement list
  type backend =
    {set_backend:SmtLib.outbound_set_backend,
     bag_backend:SmtLib.outbound_bag_backend,sequence_emission:bool,
     has_set_terms:bool,has_bag_terms:bool}
  type markers =
    {sets:SmtLib_GraphQueryAnalysis.scoped_node list,
     bags:SmtLib_GraphQueryAnalysis.scoped_node list,
     raw_numbers:SmtLib_GraphQueryAnalysis.scoped_node list}
  datatype body_direction = FunctionChild | ArgumentChild | BinderBody
  type body_plan
  type body_description =
    {position:SmtReplayFocusAdmission.current_query_position,
     path:body_direction list,
     original:SmtLib_GraphQueryAnalysis.scoped_node,
     binder:SmtLib_GraphQueryAnalysis.scoped_node,
     body:SmtLib_GraphQueryAnalysis.scoped_node,
     requirements:requirement list,
     contract:SmtReplayNativeContract.contract,ordinal:int}
  datatype body_program = BodyNeeds of requirement list
    | BodyLaw of {fact:SmtReplayProof.closed_fact,
        condition:SmtReplayGraph.node option,
        evidence:SmtLib_GraphSourcePortfolio.fact list,
        target:SmtReplayGraph.node}
  type body_query_plan
  type body_binding =
    {plan:body_plan,fact:SmtReplayProof.closed_fact,
     condition:SmtReplayGraph.node,source:SmtReplayGraph.node,
     target:SmtReplayGraph.node,
     evidence:SmtLib_GraphSourcePortfolio.fact list}
  type nested_binding
  datatype body_query_result = QueryNeeds of requirement list
    | QueryRewritten of
        {validation:SmtLib_GraphSourcePortfolio.validation,
         preprocessing:SmtLib_GraphPreprocess.validation,
         backend:backend,markers:markers}

  (* Inside the SAME outbound borrow/action. Uses the shared backend and
     finite-decision programme. Only authentic scoped nodes, original fact
     occurrences and successful selected branch DATA survive this call.
     Goal remains syntax; no Source fact is created for it. Unchanged
     binders remain identical, including opaque or large retained bodies.
     Needs exposes genuine unfinished proof ports; it grants no erasure
     permission and is not wired to any default translation route. *)
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphQueryAnalysis.outbound_context ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     operations:SmtLib_GraphQueryAnalysis.carrier
       SmtLib.outbound_term_translation_operations,
     target:{solver:string,version:string option} option,
     emit_sequences:bool,
     native_contract:SmtReplayNativeContract.contract,ordinal:int,
     check_type:Type.hol_type -> unit} -> preparation

  (* Same preparation and SINGLE original finite-selection programme.
     finish runs at its end, while that actual selection and Q borrow are
     still live. Capture original backend transport here before erasure;
     selecting again after preparation would lose that association.
     The callback receives DATA, never proof or additional Work admission. *)
  val prepare_with_selection : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphQueryAnalysis.outbound_context ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     operations:SmtLib_GraphQueryAnalysis.carrier
       SmtLib.outbound_term_translation_operations,
     target:{solver:string,version:string option} option,
     emit_sequences:bool,
     native_contract:SmtReplayNativeContract.contract,ordinal:int,
     check_type:Type.hol_type -> unit} ->
    (SmtLib_GraphBackendSelection.selection -> preparation -> 'a) -> 'a

  (* The SAME traversal may additionally retain its actual changed body
     programmes. The old wrappers disable this observer: their Needs and
     decision/callback order stay unchanged. Plans contain genuine scoped
     nodes and selected proof traces, never Q closures or body admission.
     Existing alpha/literal/nested-binder needs remain explicit. *)
  val prepare_with_bodies : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphQueryAnalysis.outbound_context ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     operations:SmtLib_GraphQueryAnalysis.carrier
       SmtLib.outbound_term_translation_operations,
     target:{solver:string,version:string option} option,
     emit_sequences:bool,
     native_contract:SmtReplayNativeContract.contract,ordinal:int,
     check_type:Type.hol_type -> unit} ->
    (SmtLib_GraphBackendSelection.selection -> preparation ->
      body_plan list -> 'a) -> 'a
  (* Additionally retain the complete SAME root programme, including its
     exact body slots and unfinished ports. This DATA plan is not proof;
     execution needs the actual checked opening conversions and genuine
     closed body laws before it can rewrite any current Source fact. *)
  val prepare_with_body_query : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphQueryAnalysis.outbound_context ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     operations:SmtLib_GraphQueryAnalysis.carrier
       SmtLib.outbound_term_translation_operations,
     target:{solver:string,version:string option} option,
     emit_sequences:bool,
     native_contract:SmtReplayNativeContract.contract,ordinal:int,
     check_type:Type.hol_type -> unit} ->
    (SmtLib_GraphBackendSelection.selection -> preparation ->
      body_plan list -> body_query_plan -> 'a) -> 'a
  (* Description runs in the caller's action. Expected Work precedes held
     original validation, scoped nodes and declaration lifetime. *)
  val body_description_with_policy_for :
    SmtReplayInvocationWork.portfolio -> body_plan -> body_description
  (* The retained original policy callback, guarded before/after use and
     requiring the caller's SAME active action, including cached Type use. *)
  val body_check_type_with_policy_for :
    SmtReplayInvocationWork.portfolio -> body_plan -> Type.hol_type -> unit
  (* Outside an action. All frames and the actual A admission must match
     the retained path's genuine canonical binder/body. This single-use
     executor produces a CLOSED law; original evidence facts are returned
     separately for later checked Source application. Existing unfinished
     alpha/literal/nested-binder ports remain BodyNeeds, never a false proof
     or a new default refusal. Ordinary identical-operand finite evidence
     is related across frames by checked application congruence. *)
  val realize_body_with_policy : SmtReplayInvocationWork.portfolio ->
    body_plan ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     root_frame:SmtReplayOwnedScopeReceipt.receipt,
     parent_frame:SmtReplayOwnedScopeReceipt.receipt,
     body_frame:SmtReplayOwnedScopeReceipt.receipt,
     admission:SmtReplayFocusAdmission.policy_focus,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> body_program
  (* Retain ONLY an actual completed private body result plus its genuine
     scoped conditional lambda law/opening. The family of retained plans,
     exact body geometry, condition and evidence occurrences are checked;
     callers cannot turn a different law or scalar node into a body slot. *)
  (* Outside an action. The actual Law recording is tied privately to the
     already completed body programme; root consumers require that exact
     recorded fact and original contract, rather than a matching theorem. *)
  val retain_recorded_with_policy : SmtReplayInvocationWork.portfolio ->
    body_plan -> SmtLib_GraphConditionalLambdaLaw.recorded -> unit
  val seal_nested_with_policy : SmtReplayInvocationWork.portfolio ->
    body_plan ->
    {recording:SmtLib_GraphConditionalLambdaLaw.recorded,
     evidence:SmtLib_GraphSourcePortfolio.fact list,
     opening:SmtReplayProof.scoped_generated_equality option} ->
    nested_binding
  val realize_body_with_nested_with_policy :
    SmtReplayInvocationWork.portfolio -> body_plan ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     root_frame:SmtReplayOwnedScopeReceipt.receipt,
     parent_frame:SmtReplayOwnedScopeReceipt.receipt,
     body_frame:SmtReplayOwnedScopeReceipt.receipt,
     admission:SmtReplayFocusAdmission.policy_focus,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     bindings:nested_binding list} -> body_program
  (* Outside an action. The already checked opening ports must relate the
     exact saved/current ordered assumptions, positive goal and retained
     denial before any body fact is used. Conditional body laws are genuine
     CLOSED facts; their actual condition tree is discharged by V.Apply
     from the retained original ordered evidence, never by converting a
     conditional theorem into an unconditional conversion. Only root-frame
     body slots are completed here; remaining staged ports stay Needs. *)
  val execute_body_query_with_policy :
    SmtReplayInvocationWork.portfolio -> body_query_plan ->
    {opening:SmtLib_GraphCheckedQueryOpening.opened_query,
     bindings:body_binding list} -> body_query_result

  (* Single use, outside the borrow: owns one Work action. Actual closed
     branch schemas and graph congruence derive transformed assumption and
     denial facts through checked V.Apply, retaining the SAME Sources.
     Original backend/markers remain DATA for the subsequent checked query
     installer; recomputing selection after erasing evidence is not valid.
     No parser mapping, output selection or default tactic is installed. *)
  val execute : SmtReplayInvocationWork.portfolio -> plan ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     preprocessing:SmtLib_GraphPreprocess.validation,
     backend:backend,markers:markers}
end
