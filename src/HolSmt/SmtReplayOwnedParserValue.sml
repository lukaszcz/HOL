(* Below Scope/Proof/Mapping: genuine Work, graph and parser ownership only. *)
structure SmtReplayOwnedParserValue :> SmtReplayOwnedParserValue =
struct
  structure W = SmtReplayInvocationWork
  type owner = W.value_factory
  val create = SmtReplayInvocationWork.create_value_factory_with_policy
  val validate_for = W.validate_value_factory_for
  val factory_for = W.value_factory_data_for
  val close = W.close_value_factory
  val prepare_binding_for = W.prepare_value_backend_binding_guard
end
