(* The genuine parser factory's original Work association, not a proof. *)
signature SmtReplayOwnedParserValue =
sig
  type owner
  val create : SmtReplayInvocationWork.portfolio ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     validate_metadata:unit -> unit,
     import_limit:SmtReplayResourcePolicy.limit,
     literal_limit:SmtReplayResourcePolicy.limit,
     binder_limit:SmtReplayResourcePolicy.limit} -> owner
  val validate_for : SmtReplayInvocationWork.portfolio -> owner -> unit
  val factory_for : SmtReplayInvocationWork.portfolio -> owner ->
    SmtLib_GraphBackend.value_backend
  (* Caller owns the SAME action. Both actual backend and Value context
     come from this private factory; an arbitrary origin/guard is not
     adopted. The resulting Work guard grants only binding lifetime. *)
  val prepare_binding_for : SmtReplayInvocationWork.portfolio -> owner ->
    SmtReplayGraph.scope ->
    SmtLib_GraphParserValue.value SmtLib_GraphBackend.binding_origin ->
    SmtReplayInvocationWork.value_binding_guard
  val close : owner -> unit
end
