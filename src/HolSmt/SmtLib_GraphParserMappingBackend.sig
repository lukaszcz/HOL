(* General Mapping syntax DATA, with the actual original Work owner. *)
signature SmtLib_GraphParserMappingBackend =
sig
  type value_backend =
    {backend:SmtLib_GraphParserValue.value SmtLib_GraphBackend.backend,
     owner:SmtReplayOwnedParserValue.owner,
     context:SmtLib_GraphParserValue.context,
     mapping_value:SmtLib_GraphParserValue.value SmtLib_GraphBackend.frame ->
       SmtLib_GraphParserMapping.node_id -> SmtLib_GraphParserValue.value,
     declarations:SmtLib_GraphParserValue.value SmtLib_GraphBackend.frame ->
       (SmtLib_GraphParserMapping.declaration *
        SmtLib_GraphParserValue.value) list,
     apply_declaration:
       SmtLib_GraphParserValue.value SmtLib_GraphBackend.frame ->
       SmtLib_GraphParserMapping.declaration ->
       SmtLib_GraphParserValue.value list -> SmtLib_GraphParserValue.value,
     binding_origin_data:SmtReplayGraph.scope ->
       SmtLib_GraphParserValue.value SmtLib_GraphBackend.binding_origin ->
       {scope:SmtReplayGraph.scope,
        variables:SmtLib_GraphParserValue.value list,
        descriptors:(string * string * Type.hol_type) list,binders:bool},
     close:unit -> unit}
  (* Creation captures DATA while Idle. Constructors, observations and
     declaration application require the SAME caller-owned Work action.
     Exact/AtMost rank and lexical variable shadowing retain the existing
     parser conventions. App(Abs,argument) remains explicit syntax.
     No value/origin can be cast to G.node or grant Source/proof authority. *)
  val create : SmtReplayInvocationWork.portfolio ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     mapping:SmtLib_GraphParserMapping.mapping,
     import_limit:SmtReplayResourcePolicy.limit,
     literal_limit:SmtReplayResourcePolicy.limit,
     binder_limit:SmtReplayResourcePolicy.limit} -> value_backend
end
