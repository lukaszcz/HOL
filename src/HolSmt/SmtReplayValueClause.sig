(* Recorded parser occurrences are typed DATA, never Source authority. *)
signature SmtReplayValueClause =
sig
  type factory
  datatype tree = False of SmtLib_GraphParserValue.proof_term
    | Literal of {node:SmtLib_GraphParserValue.proof_term,
        atom:SmtLib_GraphParserValue.proof_term,negative:bool}
    | Or of {node:SmtLib_GraphParserValue.proof_term,left:tree,right:tree}
  type occurrences
  (* Caller owns the actual original Work action for every operation. *)
  val create : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> 'proof SmtLib_GraphValueProof.packet
    -> factory
  (* SAME action; the opaque packet binding determines the actual child
     frame. The caller cannot choose a scope or substitute a descriptor.
     Recorded occurrence discovery remains the single existing worker. *)
  val create_scoped : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query -> 'proof SmtLib_GraphValueProof.packet
    -> SmtLib_GraphValueProof.binding_frame -> factory
  val validate_context_for : SmtReplayInvocationWork.portfolio -> factory ->
    SmtLib_GraphParserValue.context -> unit
  val discover_recorded : SmtReplayInvocationWork.portfolio -> factory ->
    SmtLib_GraphFrontend.value_term -> occurrences
  val discover_target : SmtReplayInvocationWork.portfolio -> factory ->
    SmtLib_GraphFrontend.value_term -> occurrences
  val data_for : SmtReplayInvocationWork.portfolio -> factory -> occurrences
    -> {root:SmtLib_GraphParserValue.value,tree:tree,expanded:tree option}
  type raw_occurrences
  (* Explicit raw compatibility, separate from recorded occurrences.
     Only actual head aliases receive selective checked OR fallbacks. *)
  val discover_raw : SmtReplayInvocationWork.portfolio -> factory ->
    {head:SmtLib_GraphFrontend.value_term,
     units:SmtLib_GraphFrontend.value_term list,
     target:SmtLib_GraphFrontend.value_term} -> raw_occurrences
  val raw_data_for : SmtReplayInvocationWork.portfolio -> factory ->
    raw_occurrences -> {head:occurrences,units:occurrences list,
      target:occurrences,fallbacks:tree list,
      atom_aliases:(SmtLib_GraphParserValue.proof_term *
        SmtLib_GraphParserValue.proof_term) list}
  val view : tree ->
    (SmtLib_GraphParserValue.proof_term,tree) SmtReplayNamedClause.tree_view
end
