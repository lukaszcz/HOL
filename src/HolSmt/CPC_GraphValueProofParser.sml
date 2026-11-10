(* One shared CPC grammar and recipe registry; only carrier access differs. *)
structure CPC_GraphValueProofParser :> CPC_GraphValueProofParser =
struct
  structure W = SmtReplayInvocationWork
  structure F = SmtLib_GraphFrontend
  structure P = SmtLib_Parser
  structure PV = SmtLib_GraphParserValue
  structure MD = SmtLib_GraphDeclarationMetadata
  structure M = SmtLib_GraphParserMapping
  structure C = CPC_ProofParser
  type proof = PV.value C.constructed_graph_proof
  val ERR = Feedback.mk_HOL_ERR "CPC_ProofParser"

  fun create_packet_with_policy_from_input expected query
      (options:F.value_options) metadata requested_version input =
    ((let
      val version = CPC_Proof.resolve_version requested_version
      val tokenizer = P.make_cpc_proof_tokenizer_from_input input
      val description = C.graph_policy_description version
      fun parse (factory:SmtLib_GraphValueTranslation.session) =
        let
          val context = #context factory val session = #session factory
          val width_limit = #index_limit (#recipe_limits options)
          fun value_index _ value =
            case PV.natural_index_with_policy context width_limit value of
                PV.NaturalIndex natural =>
                  if C.policy_reader_width width_limit natural then natural
                  else raise ERR "graph_index"
                    "private numeric index exceeds contract"
              | PV.ExpandedIndex => raise ERR "graph_index"
                  "expanded private index operand"
              | PV.OpaqueIndex => raise ERR "graph_index"
                  "opaque private index operand"
              | PV.NonNaturalIndex => raise ERR "graph private index"
                  "expected a CPC natural-number argument"
          fun install options terms =
            C.install_graph_recipes_with_policy_for_backend
              value_index options terms
          (* These native callbacks probe only bounded TypeBase metadata.
             No Mapping recipe or query operand is converted to a Term. *)
          val mapping = MD.mapping_for (#graph options) (#scope options)
            metadata
          val declarations =
            SmtLib.parser_datatype_term_dictionary_from_types
              (M.types mapping) (Redblackmap.mkDict String.compare)
          val dictionary = ((#sort_dictionary session) (),declarations)
          val reader =
            CPC_ProofParser.graph_command_reader_for_backend_with_policy
              install (fn _ => fn _ => fn _ => session) options dictionary
              requested_version (fn () => tokenizer)
          fun commands result = case (#next reader) () of
              NONE => List.rev result
            | SOME command =>
                (PV.spend context 1;commands (command::result))
          val proof:proof =
            {commands=commands [],cvc_version= #cvc_version reader}
          fun argument (current,terms) =
            (PV.spend context 1;case current of
                C.GraphTerm term => term::terms
              | C.GraphList entries => List.foldl argument terms entries
              | _ => terms)
          fun command (current,terms) =
            (PV.spend context 1;case current of
                C.GraphAssume (_,term) => term::terms
              | C.GraphAssumePush (_,term) => term::terms
              | C.GraphStep {step={conclusion,args,...},...} =>
                  List.foldl argument
                    (case conclusion of NONE => terms | SOME term =>
                       (PV.spend context 1;term::terms)) args)
          val terms = List.rev (List.foldl command [] (#commands proof))
          val _ = if Portable.pointer_eq
              (#backend (#reader (#terms reader)),#backend (#reader session))
            then () else raise ERR "graph_commands" "different Value reader"
        in {proof=proof,terms=terms,bindings=[],close=fn () => ()}
          : proof SmtLib_GraphValueProof.parsed end
    in SmtLib_GraphValueProof.create expected query
      {options=options,metadata=metadata,description=description,
       requested_version=requested_version,tokens=tokenizer} parse end)
     handle primary => (W.close expected;raise primary))
end
