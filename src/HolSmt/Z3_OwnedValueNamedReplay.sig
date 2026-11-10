(* Actual packet receiver for named fragments; final transport is separate. *)
signature Z3_OwnedValueNamedReplay =
sig
  type invocation
  datatype requirement =
      CurrentSourceTransport of
        {index:int,node:SmtReplayGraph.node,
         value:SmtLib_GraphParserValue.value}
    | OriginalSourceProgramme of
        {index:int,node:SmtReplayGraph.node,
         value:SmtLib_GraphParserValue.value}
    | SourceOpening of SmtReplayGraph.scope * SmtReplayGraph.node
    | ScopedBinding of SmtLib_GraphFrontend.value_scoped_session
    | ResolutionProgramme of
        {target:SmtLib_GraphParserValue.value,
         premises:Z3_GraphProofParser.proof_id list,
         conclusion:SmtLib_GraphFrontend.value_term}
    | SpecializationProgramme of
        {source:SmtLib_GraphParserValue.proof_term,
         instance:SmtLib_GraphParserValue.proof_term,
         target:SmtLib_GraphParserValue.proof_term,
         arguments:SmtLib_GraphParserValue.proof_term list}
    | BinderAdmission of SmtReplayOwnedValueBinder.requirement
    | SpecializationAdmission of SmtReplayOwnedValueSpecialize.requirement
  datatype preparation = Prepared of invocation | Needs of requirement list
  (* Outside an action. Actual OriginalSlot indices refer to original
     Sources, NEVER to the current query assertion vector. All unfinished
     programmes are retained as DATA before any named kernel inference.
     Completed fragments use the SAME registry classifier and checked
     equality/Boolean workers as the original graph receiver. *)
  val prepare_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Same planner and fixed workers, with genuine demand-specific
     ORIGINAL Source ports. Their indices are authenticated by Work, kept
     distinct from current slots, and remain tagged through realization. *)
  val prepare_with_original_sources_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     check_type:Type.hol_type -> unit} -> preparation
  (* Actual parsed quant-inst programmes use genuine retained Source
     specialization receipts, reserved separately from Source occurrences.
     All unsupported programmes remain typed Needs before native assembly. *)
  val prepare_with_specialization_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* General retained arguments/results are admitted before any native
     freeze. Novel Value closures retain their typed producer requirement. *)
  val prepare_with_retained_specialization_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Explicit raw compatibility uses the SAME native dictionary/fallback
     discovery and recorded compact worker. Existing entries stay recorded.
     Genuine bounded quant-inst receipts are retained in the same pipeline. *)
  val prepare_with_raw_resolution_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* Explicit first scoped programme. Source-free atomic reflexivity
     under an authentic immediate proof-bind is proved through the shared
     bounded binder worker; all other child programmes remain typed Needs. *)
  val prepare_with_binders_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  (* The same genuine source-free Bind programme, additionally admitting
     matching forall/exists identity prefixes through BinderClose. *)
  val prepare_with_quantified_binders_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation

  (* These operations own one SAME Work action. Even empty/warmed reads
     check expected owner before actual packet/Value backing. The returned
     edge is a compact named theorem, not an expanded original Source
     theorem or a binder/Clause/specialization proof permission. *)
  (* Explicit composition of the SAME retained-specialization, scoped
     binder and native-raw clause programmes. Each unfinished programme
     still leaves the whole invocation as typed Needs before inference. *)
  val prepare_with_owned_programmes_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    Z3_GraphValueProofParser.proof SmtLib_GraphValueProof.packet ->
    {assertions:SmtLib_GraphParserValue.value list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit} -> preparation
  val replay_next_with_policy : SmtReplayInvocationWork.portfolio ->
    invocation -> {id:Z3_GraphProofParser.proof_id,
      node:SmtLib_GraphParserValue.value} option
  val step_with_policy_for : SmtReplayInvocationWork.portfolio -> invocation ->
    Z3_GraphProofParser.proof_id ->
    {block:SmtReplayOwnedValueProof.block,node:SmtLib_GraphParserValue.value,
     edge:SmtReplayOwnedValueProof.edge}
  val close : invocation -> unit
end
