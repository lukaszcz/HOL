(* Same invocation; each body scope comes from a genuine closure path. *)
signature SmtReplayOwnedScopeReceipt =
sig
  type receipt
  val root : SmtReplayInvocationWork.portfolio -> receipt
  val body : SmtReplayInvocationWork.portfolio -> receipt ->
    SmtReplayGraph.closure_child -> receipt
  (* Only an actual backend open_binders/open_bindings origin can issue
     this proof-binding frame. No caller G.scope or new Source is supplied. *)
  val binding : SmtReplayInvocationWork.portfolio -> receipt ->
    SmtReplayGraph.node SmtLib_GraphBackend.binding_origin -> receipt
  (* Read-only private lexical lifetime plus original owner/epochs/scopes.
     Graph-backed closure geometry still requires the ordinary descriptor
     on a changed G validation revision. No work/admission receipt. *)
  val validate_lifetime_for : SmtReplayInvocationWork.portfolio ->
    receipt -> unit
  val description_for : SmtReplayInvocationWork.portfolio -> receipt ->
    {graph : SmtReplayGraph.graph,root : SmtReplayGraph.scope,
     scope : SmtReplayGraph.scope,sources : SmtReplaySource.sources}
  (* The same opaque receipt can retain explicit policy metadata. Owner
     descriptions need no int projection; old finite bodies are unchanged.
     Legacy Work int getters still reject policy portfolios. *)
  val root_with_policy : SmtReplayInvocationWork.portfolio -> receipt
  val body_with_policy : SmtReplayInvocationWork.portfolio -> receipt ->
    SmtReplayGraph.closure_child -> receipt
  val binding_with_policy : SmtReplayInvocationWork.portfolio -> receipt ->
    SmtReplayGraph.node SmtLib_GraphBackend.binding_origin -> receipt
  (* Genuine typed parser binding, with the exact same original Work.
     Creation owns its action; retained descriptions need no nested action.
     This frame grants no Source fact or native binder admission. *)
  val binding_value_with_policy : SmtReplayInvocationWork.portfolio ->
    receipt -> SmtReplayOwnedParserValue.owner ->
    SmtLib_GraphParserValue.value SmtLib_GraphBackend.binding_origin -> receipt
  val description_with_policy_for : SmtReplayInvocationWork.portfolio ->
    receipt ->
    {graph:SmtReplayGraph.graph,root:SmtReplayGraph.scope,
     scope:SmtReplayGraph.scope,sources:SmtReplaySource.sources,
     limits:SmtReplayResourcePolicy.semantic_policy}
  val validate_lifetime_with_policy_for :
    SmtReplayInvocationWork.portfolio -> receipt -> unit

end
