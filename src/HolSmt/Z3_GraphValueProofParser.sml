(* Only carrier ownership differs; the proof grammar remains shared. *)
structure Z3_GraphValueProofParser :> Z3_GraphValueProofParser =
struct
  structure W = SmtReplayInvocationWork
  structure F = SmtLib_GraphFrontend
  structure PV = SmtLib_GraphParserValue
  structure P = SmtLib_Parser
  structure Z = Z3_GraphProofParser
  type proof = PV.value Z.constructed_proof

  fun create_packet_with_policy_from_input expected query options metadata
      requested_version input =
    ((let
      val version = Z3_Proof.resolve_version requested_version
      val tokenizer = P.make_proof_input_tokenizer input
      val description = Z.policy_description version
      fun parse (factory:SmtLib_GraphValueTranslation.session) =
        let
          val context = #context factory
          val observations:PV.value Z.policy_observations =
            {type_of=PV.type_of context,same_identity=op=,
             guard_alias_scope=fn (scope,value) =>
               PV.usable context scope value,
             alias_entry=fn (scope,value) =>
               {key=PV.key context value,visible=fn () =>
                 (PV.usable context scope value;true)}}
          fun complete tokens =
            case (SOME (tokens ()) handle P.ProofEOF => NONE) of
                NONE => ()
              | SOME _ => raise Z.ERR "parse" "trailing Z3 proof syntax"
          (* The immutable proof table is the inventory source. Every Rule
             contributes its conclusion/arguments; every Bind contributes
             its actual authenticated scoped session. This is ownership
             validation only, not inference or Source admission. *)
          fun publish
              {reader:F.value_reader,proof:proof,requested_version=_,close} =
            let
              fun add_terms [] terms = terms
                | add_terms (value::rest) terms =
                    (PV.spend context 1;add_terms rest (value::terms))
              fun step (_,entry,(terms,bindings)) =
                (PV.spend context 1;
                 case entry of Z.Rule {conclusion,arguments,...} =>
                     (add_terms (conclusion::arguments) terms,bindings)
                   | Z.Alias _ => (terms,bindings)
                   | Z.Bind {binding,...} =>
                       (terms,binding::bindings))
              val (terms,bindings) = Redblackmap.foldl step ([],[])
                (#steps proof)
              val _ = if Portable.pointer_eq
                  (#backend reader,#backend (#reader (#session factory)))
                then () else raise Z.ERR "parse" "different Value reader"
            in {proof=proof,terms=List.rev terms,bindings=List.rev bindings,
              close=close}:proof SmtLib_GraphValueProof.parsed end
        in Z.create_using_with_policy_token_factory_for_backend observations
          publish (fn _ => fn _ => fn _ => #session factory) options
          requested_version (fn () => tokenizer) complete end
    in SmtLib_GraphValueProof.create expected query
      {options=options,metadata=metadata,description=description,
       requested_version=requested_version,tokens=tokenizer} parse end)
     handle primary => (W.close expected;raise primary))
end
