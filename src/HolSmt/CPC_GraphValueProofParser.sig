(* Actual CPC policy commands over typed durable Mapping declarations. *)
signature CPC_GraphValueProofParser =
sig
  type proof = SmtLib_GraphParserValue.value
    CPC_ProofParser.constructed_graph_proof
  (* Outside an action. Initialization and parsing use the SAME original
     Work. The actual shared command grammar checks wrapper completion and
     real supplier EOF before publication. Index observations return only
     bounded scalars; metadata closures never become native abstractions.
     Neither a command nor this packet certifies inference or a Source. *)
  val create_packet_with_policy_from_input :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    SmtLib_GraphFrontend.value_options ->
    SmtLib_GraphDeclarationMetadata.metadata -> string ->
    (unit -> char option) -> proof SmtLib_GraphValueProof.packet
end
