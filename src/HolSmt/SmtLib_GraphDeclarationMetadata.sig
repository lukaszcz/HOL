(* Durable declaration and committed encoding DATA for graph emission. *)
signature SmtLib_GraphDeclarationMetadata =
sig
  type metadata
  type term_declaration =
    {symbol:SmtLib_GraphParserMapping.declaration,
     domain_sorts:string list,range_sort:string,declaration:string}
  type encoding =
    {input:SmtLib_GraphParserMapping.node_id,
     head:SmtLib_GraphParserMapping.node_id,atomic_head:Term.term option,
     smt_symbol:string,arity:int}
  type definition =
    {encoding:encoding,replay_head:Term.term,unfolding:Thm.thm}

  (* Run inside the same authenticated borrow and fixed backend installation
     as Dispatcher.emit, using its actual committed result and complete
     shared operations. Declaration and encoding syntax share one Mapping
     typed DAG. No borrowed carrier or backend callback escapes. Native
     Terms retained here are atomic variable/constant/declaration metadata.

     Definitions attach the existing closed registry to actual atomic
     encoding observations. Neither an encoding nor an attached theorem
     grants parser, Source or original-assumption transport permission.
     General recipe interpretation and checked transport remain separate.
     Every accessor revalidates Mapping's graph/scope/epoch lifetime, even
     for empty metadata. No legacy raw-term translation is fabricated. *)
  val freeze : SmtLib_GraphQueryAnalysis.outbound_context ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     regime:SmtLib.regime,backend:SmtLib.outbound_backend_context,
     operations:SmtLib_GraphQueryAnalysis.carrier
       SmtLib.outbound_term_translation_operations,
     emission:SmtLib_GraphDispatcher.result} -> metadata
  type assertion =
    {scope:SmtReplayGraph.scope,node:SmtReplayGraph.node,
     syntax:SmtLib_GraphParserMapping.node_id}
  (* Opt-in syntax roots use the SAME Mapping DAG, after encoding inputs.
     Neither the roots nor their interpreted values are Source permissions. *)
  val freeze_with_assertions : SmtLib_GraphQueryAnalysis.outbound_context ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     regime:SmtLib.regime,backend:SmtLib.outbound_backend_context,
     operations:SmtLib_GraphQueryAnalysis.carrier
       SmtLib.outbound_term_translation_operations,
     emission:SmtLib_GraphDispatcher.result} -> metadata
  (* Passive expected-owner fence and private presence DATA only. No held
     Mapping/closure is activated and no Work admission is supplied. *)
  val has_assertions_for : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    metadata -> bool
  (* Authenticate actual ordered query roots BEFORE Mapping backing. The
     observer charges new metadata work; the caller guards its query around
     it and owns the SAME action. NONE traverses no roots. *)
  val assertions_for : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {assumptions:SmtReplayGraph.node list,denied:SmtReplayGraph.node,
     observe:unit -> unit} -> metadata -> assertion list option
  val validate : metadata -> unit
  val mapping : metadata -> SmtLib_GraphParserMapping.mapping
  (* Expected owner is checked before any held mapping backing is read. *)
  val mapping_for : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    metadata -> SmtLib_GraphParserMapping.mapping
  val type_records : metadata -> SmtLib.translation_record list
  val term_declarations : metadata -> term_declaration list
  val encodings : metadata -> encoding list
  val definitions : metadata -> definition list
end
