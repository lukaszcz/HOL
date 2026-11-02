(* The shared dispatcher, actual committed metadata and streamed commands. *)
structure SmtLib_GraphQueryEmission :> SmtLib_GraphQueryEmission =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure S = SmtReplaySource
  structure GP = SmtLib_GraphPreprocess
  structure Q = SmtLib_GraphQueryAnalysis
  structure B = SmtLib_GraphBackendSelection
  structure R = SmtLib_GraphQueryRegime
  structure T = SmtLib_GraphTranslation
  structure Features = SmtLib_GraphQueryFeatures
  structure Availability = SmtLib_GraphQueryAvailability
  structure Dispatcher = SmtLib_GraphDispatcher
  structure Metadata = SmtLib_GraphDeclarationMetadata
  structure Fragments = SmtLib_OutputFragments
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphQueryEmission"
  type description =
    {logic:string,logic_reason:string,regime:SmtLib.regime,
     regime_reason:string,features:SmtLib.logic_features,
     has_hol_strings:bool,metadata:Metadata.metadata,
     assertion_nodes:Q.scoped_node list}
  type held = {scope:G.scope,node:G.node,child:G.closure_child}
  datatype receipt = Receipt of
    {work:W.portfolio,query:GP.graph_query,graph:G.graph,scope:G.scope,
     sources:S.sources,limits:SmtReplayResourcePolicy.semantic_policy,
     epoch:int,symbols:int,held:held list,description:description,
     document:Fragments.doc,validated_revision:IntInf.int ref}

  fun validate expected input (Receipt
      {work,query,graph,scope,sources,limits,epoch,symbols,held,description,
       validated_revision,...}) =
    ((if Portable.pointer_eq (expected,work) andalso
          Portable.pointer_eq (input,query) then () else
        raise ERR "validate" "different original Work or exact query";
      W.validate_policy expected graph scope sources limits;
      if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
        else raise ERR "validate" "query declaration lifetime changed";
      let val revision = G.validation_revision graph scope in
        if !validated_revision=revision then () else
          (GP.validate_query_with_policy expected query;
           ignore (Metadata.mapping_for graph scope (#metadata description));
           List.app (fn {scope=caller,node,child}:held =>
             if G.closure_child_node graph caller child=node then () else
               raise ERR "validate" "emitted assertion endpoint changed") held;
           W.validate_policy expected graph scope sources limits;
           if G.validation_revision graph scope=revision then
             validated_revision:=revision else
             raise ERR "validate" "graph publication during validation")
      end)
     handle primary => (W.close expected;raise primary))

  fun describe_for expected input
      (receipt as Receipt {description,...}) =
    (validate expected input receipt;description)

  fun write_for expected input (receipt as Receipt {document,...}) sink =
    ((validate expected input receipt;
      Fragments.render (fn text =>
        (validate expected input receipt;sink text;
         validate expected input receipt)) document;
      validate expected input receipt)
     handle primary => (W.close expected;raise primary))

  fun operations (context:Q.outbound_context) sequence_emission =
    let
      (* Diagnostic heads stay atomic; never force a compound native tree. *)
      fun diagnostic current = case (#view context) current of
          Q.ConstantView atom => Hol_pp.term_to_string atom
        | Q.VariableView (_,atom) => Hol_pp.term_to_string atom
        | _ => "<compound HOL term>"
    in SmtLib_GraphCarrierOperations.make_with_datatypes context
      {sequence_emission=sequence_emission}
      {term_to_string=diagnostic} end

  fun check_reglan (context:Q.outbound_context)
      (operations:Q.carrier SmtLib.outbound_term_translation_operations) =
    let
    val seen = ref (Redblackset.empty
      (Lib.pair_compare (Int.compare,Int.compare)))
    fun preflight [] = ()
      | preflight (current::pending) =
        let val key = (#key context) current in
          if Redblackset.member (!seen,key) then preflight pending
          else
            let val _ = (#step context) ()
                val _ = SmtLib.outbound_check_reglan_equality
                  {strip_comb= #strip_comb context,
                   known_const_matches=
                     #known_const_matches operations,
                   type_of= #type_of context} current
                val children = case (#view context) current of
                    Q.ApplicationView (left,right) => [left,right]
                  | Q.AbstractionView (_,body) => [body]
                  | _ => []
                val _ = ignore ((#key context) (#goal context))
                val _ = seen := Redblackset.add (!seen,key)
            in preflight (children @ pending) end
        end
    in preflight (#goal context :: #assumptions context) end

  fun original_preflight context sequence_emission target =
    (case target of NONE => () | SOME target =>
       ignore (Availability.check context
         {sequence_emission=sequence_emission,target=target});
     check_reglan context (operations context sequence_emission))

  fun prepare_backend work {query,options,open_opaque} =
    ((let val options:SmtLib_TranslationEmissions.options = options
      in T.with_outbound_query_analysis_with_policy work query open_opaque
        (fn context =>
          let val sequence_emission = Features.native_sequence_goal context
              val _ = original_preflight context sequence_emission
                (#target options)
              val selected = B.select context
                {operations=operations context sequence_emission,
                 target= #target options,emit_sequences=true}
          in B.capture_transport work query context selected end)
      end) handle primary => (W.close work;raise primary))

  fun with_finite_input work
      {query,validation,options,open_opaque,native_contract,ordinal,
       check_type} finish =
    ((let
      val options:SmtLib_TranslationEmissions.options = options
      val _ = W.with_step work (fn () => ignore
        (SmtLib_GraphSourcePortfolio.current_facts_with_policy_for
          work validation))
    in T.with_outbound_query_analysis_with_policy work query open_opaque
      (fn context =>
        let val sequence_emission = Features.native_sequence_goal context
            val _ = original_preflight context sequence_emission
              (#target options)
        in finish query context
          {validation=validation,
           operations=operations context sequence_emission,
           target= #target options,emit_sequences=true,
           native_contract=native_contract,ordinal=ordinal,
           check_type=check_type}
        end)
    end) handle primary => (W.close work;raise primary))

  fun prepare_finite work request =
    with_finite_input work request (fn query => fn context => fn input =>
      SmtLib_GraphFiniteQueryTransport.prepare_with_selection work
        context input (fn selection => fn preparation =>
          {preparation=preparation,
           backend=B.capture_transport work query context selection}))

  fun prepare_finite_body_query work request =
    with_finite_input work request (fn query => fn context => fn input =>
      SmtLib_GraphFiniteQueryTransport.prepare_with_body_query work
        context input (fn selection => fn preparation => fn bodies =>
          fn plan =>
            {preparation=preparation,bodies=bodies,plan=plan,
             backend=B.capture_transport work query context selection}))

  fun emit_using retain work {query,backend,options,prefix,open_opaque} =
    ((let
      val options:SmtLib_TranslationEmissions.options = options
      fun checkpoint label =
        if OS.Process.getEnv "HOL4_HOLSMT_REPLAY_DIAGNOSTICS" <>
            SOME "1" then () else
          let val audit = W.audit_policy work
          in TextIO.output (TextIO.stdErr,
            "QUERY_EMISSION_WORK phase=" ^ label ^ " charged=" ^
            IntInf.toString (#charged audit) ^ " retired=" ^
            Bool.toString (#retired audit) ^ "\n");
            TextIO.flushOut TextIO.stdErr end
      val _ = checkpoint "query.before"
      val input = GP.query_nodes_with_policy_for work query
      val _ = checkpoint "query.after"
      val graph = #graph input val scope = #scope input
      val sources = #sources input val limits = W.semantic_policy work
      val original_target = B.target_for_transport work backend
      val _ = if #target options=original_target then () else
        raise ERR "emit" "different original solver target"
      val _ = checkpoint "original.before"
      val _ = B.with_original_context_with_policy work backend open_opaque
        (fn {context,sequence_emission,target} =>
          original_preflight context sequence_emission target)
      val _ = checkpoint "original.after"
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val output:Fragments.doc SmtLib.outbound_output_operations =
        {text=Fragments.text,concat=Fragments.concat,join=Fragments.join}
      val _ = checkpoint "transport.before"
      val (description,document,held) =
        B.with_transported_context_with_policy work backend query open_opaque
          (fn (context,installed) =>
          let
            fun live () = ignore ((#key context) (#goal context))
            val state = #state installed
            val sequence_emission = (#sequence_emission state) ()
            val operations = operations context sequence_emission
            val roots = #assumptions context @ [#denied context]
            (* Original boundary checks have already run above. *)
            val selected = R.select context
              {operations=operations,
               request=SmtLib.AutomaticRegime (#dialect options)}
            val regime = #regime selected
            val _ = checkpoint "dispatcher.before"
            val numbered = Lib.mapi (fn index => fn current =>
              (index,current)) roots
            val emission = Dispatcher.emit context
              {operations=operations,regime=regime,
               apply_operator= #apply_operator options,prefix=prefix,
               roots=numbered}
            val _ = checkpoint "dispatcher.after"
            val freeze=if retain then Metadata.freeze_with_assertions
              else Metadata.freeze
            val metadata = freeze context
              {graph=graph,scope=scope,regime=regime,backend=installed,
               operations=operations,emission=emission}
            val _ = checkpoint "metadata.after"
            val declaration_inputs = List.map
              (fn (symbol:SmtLib_GraphCarrierStore.symbol) =>
                (#syntax symbol,#arity symbol)) (#symbols emission)
            val features = #features (Features.infer_features context
              {operations=operations,state=state,regime=regime,roots=roots,
               types= #types emission,declarations=declaration_inputs})
            val _ = checkpoint "features.after"
            val _ = live ()
            val logic = SmtLib.outbound_select_logic regime
              (#policy options) features
            val _ = live ()
            val presence = Features.string_presence context roots
            fun hold current = case (#graph_node context) current of
                NONE => raise ERR "emit"
                  "assertion root is not authentic graph syntax"
              | SOME {scope=caller,node} =>
                let val _ = (#step context) ()
                    val child = G.closure_root graph caller node
                in {scope=caller,node=node,child=child}:held end
            val held = List.map hold roots
            val description:description =
              {logic= #logic logic,logic_reason= #reason logic,
               regime=regime,regime_reason= #reason selected,
               features=features,has_hol_strings= #has_hol_strings presence,
               metadata=metadata,assertion_nodes=List.map
                 (fn {scope,node,...}:held => {scope=scope,node=node}) held}
            val assertions = List.map
              (fn (root:Dispatcher.root) =>
                (#declarations root,#expression root)) (#roots emission)
            val commands = SmtLib.outbound_query_script output
              {logic= #logic logic,assertions=assertions} @
              SmtLib.outbound_query_tail output (#get_proof options)
            val _ = live ()
          in (description,Fragments.concat commands,held) end)
      val _ = checkpoint "transport.after"
      val receipt = Receipt {work=work,query=query,graph=graph,scope=scope,
        sources=sources,limits=limits,epoch=epoch,symbols=symbols,held=held,
        description=description,document=document,
        validated_revision=ref (~1:IntInf.int)}
      val _ = checkpoint "receipt.before"
      val _ = validate work query receipt
      val _ = checkpoint "receipt.after"
    in receipt end)
     handle primary => (W.close work;raise primary))
  fun emit work options=emit_using false work options
  fun emit_with_assertions work options=emit_using true work options
end
