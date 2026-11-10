(* General Mapping declarations with the shared real datatype grammar. *)
signature SmtLib_GraphValueTranslation =
sig
  type session =
    {session:SmtLib_GraphFrontend.value_session,
     context:SmtLib_GraphParserValue.context,
     owner:SmtReplayOwnedParserValue.owner,
     assertions:SmtLib_GraphParserValue.value list option,
     close:unit -> unit,
     admitted_branch:SmtReplayGraph.scope *
       SmtLib_GraphParserValue.value -> bool}
  (* Call outside an action. The initializer owns its Work action after the
     owning query getter returns. Subsequent parser callbacks run inside the
     caller's SAME expected Work action. Every declaration is interpreted by
     MappingBackend, including metadata closures. Datatype
     templates come from the actual emitted type dictionary; operand values
     never enter native template compilation. Call close on every outcome.
     The returned syntax grants no Source, graph-node or proof permission.
     Packets and their checked Value consumer remain separate integration. *)
  val create_session_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    SmtLib_GraphFrontend.value_options ->
    SmtLib_GraphDeclarationMetadata.metadata ->
    {solver:string,version:string,
     policy:SmtLib_GraphFrontend.lexical_policy,reserved_names:string list} ->
    (unit -> string) -> session
end
