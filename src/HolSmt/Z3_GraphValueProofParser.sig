(* The actual Z3 policy grammar, with typed Mapping values and strict EOF. *)
signature Z3_GraphValueProofParser =
sig
  type proof = SmtLib_GraphParserValue.value
    Z3_GraphProofParser.constructed_proof
  (* Outside an action. The same Work owns initialization and parsing.
     The supplier must return real EOF; malformed/trailing bytes or a forged
     parser EOF exception prevent packet publication. No replay/default
     path is selected and no parsed rule is certified by this packet. *)
  val create_packet_with_policy_from_input :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.graph_query ->
    SmtLib_GraphFrontend.value_options ->
    SmtLib_GraphDeclarationMetadata.metadata -> string ->
    (unit -> char option) -> proof SmtLib_GraphValueProof.packet
end
