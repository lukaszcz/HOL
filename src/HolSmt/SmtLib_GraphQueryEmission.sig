(* One genuine shared graph serialization, bound to its exact checked input. *)
signature SmtLib_GraphQueryEmission =
sig
  type receipt
  type description =
    {logic:string,logic_reason:string,regime:SmtLib.regime,
     regime_reason:string,features:SmtLib.logic_features,
     has_hol_strings:bool,metadata:SmtLib_GraphDeclarationMetadata.metadata,
     assertion_nodes:SmtLib_GraphQueryAnalysis.scoped_node list}

  (* Original solver-boundary order: availability, RegLan, then shared
     backend selection/capture. Call before finite erasure or its preparation.
     This is original-query DATA, not proof or Work admission. *)
  val prepare_backend : SmtReplayInvocationWork.portfolio ->
    {query:SmtLib_GraphPreprocess.graph_query,
     options:SmtLib_TranslationEmissions.options,
     open_opaque:SmtReplayGraph.scope -> SmtReplayGraph.node -> unit} ->
    SmtLib_GraphBackendSelection.transport

  (* Original preflight followed by ONE shared finite-selection programme.
     The actual original backend snapshot is captured at the end of that
     same live borrow, before checked erasure/opening. Needs remains an
     explicit unfinished proof port; it permits neither erasure nor emit. *)
  val prepare_finite : SmtReplayInvocationWork.portfolio ->
    {query:SmtLib_GraphPreprocess.graph_query,
     validation:SmtLib_GraphSourcePortfolio.validation,
     options:SmtLib_TranslationEmissions.options,
     open_opaque:SmtReplayGraph.scope -> SmtReplayGraph.node -> unit,
     native_contract:SmtReplayNativeContract.contract,ordinal:int,
     check_type:Type.hol_type -> unit} ->
    {preparation:SmtLib_GraphFiniteQueryTransport.preparation,
     backend:SmtLib_GraphBackendSelection.transport}

  (* Same original preflight and SINGLE finite selection. Retain its root
     programme and genuine body traces for checked opening/body execution;
     no second selection occurs after erasure. The partial plan is DATA,
     and residual proof ports remain explicit in preparation. Capture of
     the original backend still occurs inside this same live Q borrow. *)
  val prepare_finite_body_query : SmtReplayInvocationWork.portfolio ->
    {query:SmtLib_GraphPreprocess.graph_query,
     validation:SmtLib_GraphSourcePortfolio.validation,
     options:SmtLib_TranslationEmissions.options,
     open_opaque:SmtReplayGraph.scope -> SmtReplayGraph.node -> unit,
     native_contract:SmtReplayNativeContract.contract,ordinal:int,
     check_type:Type.hol_type -> unit} ->
    {preparation:SmtLib_GraphFiniteQueryTransport.preparation,
     bodies:SmtLib_GraphFiniteQueryTransport.body_plan list,
     plan:SmtLib_GraphFiniteQueryTransport.body_query_plan,
     backend:SmtLib_GraphBackendSelection.transport}

  (* Outside an owned action. The backend snapshot comes from the original
     authenticated query; checked preprocessing has already established the
     supplied current query. This calls the shared semantic dispatcher and
     freezes its actual declarations/encodings in the same borrow. No raw
     translation, full native query or Source fact is fabricated. *)
  val emit : SmtReplayInvocationWork.portfolio ->
    {query:SmtLib_GraphPreprocess.graph_query,
     backend:SmtLib_GraphBackendSelection.transport,
     options:SmtLib_TranslationEmissions.options,prefix:string,
     open_opaque:SmtReplayGraph.scope -> SmtReplayGraph.node -> unit} ->
    receipt
  (* Same bytes/dispatcher, with ordered assertion syntax retained in the
     emitted Mapping. No proof or Source allowance is added. *)
  val emit_with_assertions : SmtReplayInvocationWork.portfolio ->
    {query:SmtLib_GraphPreprocess.graph_query,
     backend:SmtLib_GraphBackendSelection.transport,
     options:SmtLib_TranslationEmissions.options,prefix:string,
     open_opaque:SmtReplayGraph.scope -> SmtReplayGraph.node -> unit} ->
    receipt
  val describe_for : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> receipt -> description

  (* Stream the immutable fragments without concatenating a whole script.
     Each sink callback is guarded on entry and return; callback Primary
     retires this same Work and escapes unchanged. The receipt binds input
     and bytes, not theorem/Source permission or a new work allowance. *)
  val write_for : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> receipt -> (string -> unit) -> unit
end
