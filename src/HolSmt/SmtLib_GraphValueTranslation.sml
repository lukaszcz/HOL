(* Typed parser syntax over the actual durable emitted declaration DAG. *)
structure SmtLib_GraphValueTranslation :> SmtLib_GraphValueTranslation =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure GP = SmtLib_GraphPreprocess
  structure F = SmtLib_GraphFrontend
  structure PV = SmtLib_GraphParserValue
  structure M = SmtLib_GraphParserMapping
  structure MB = SmtLib_GraphParserMappingBackend
  structure MD = SmtLib_GraphDeclarationMetadata
  structure D = SmtLib_GraphDatatypeParser
  structure B = SmtLib_GraphBackend
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphValueTranslation"
  type session =
    {session:F.value_session,context:PV.context,close:unit -> unit,
     owner:SmtReplayOwnedParserValue.owner,
     assertions:PV.value list option,
     admitted_branch:G.scope * PV.value -> bool}

  fun create_session_with_policy expected query (base:F.value_options)
      metadata description tokens =
    ((let
      (* The expected original Work/query is inspected before held metadata
         or its owner, just as on the existing graph initializer route. *)
      val data = GP.query_nodes_with_policy_for expected query
      val graph = #graph base val scope = #scope base
      val _ = if Portable.pointer_eq (graph,#graph data) andalso
          scope= #scope data then () else
        raise ERR "create_session_with_policy" "different query owner"
      (* Compare exact authoritative query roots BEFORE any held Mapping
         alias is activated. Legacy metadata takes no extra owned action. *)
      val assertion_rows=if MD.has_assertions_for graph scope metadata then
          W.with_step expected(fn()=>
            let fun observe()=
                  (GP.validate_query_with_policy expected query;
                   W.spend_policy expected 1;
                   GP.validate_query_with_policy expected query)
                val rows=MD.assertions_for graph scope
                  {assumptions= #assumptions data,denied= #denied data,
                   observe=observe}metadata
                val _=GP.validate_query_with_policy expected query
            in rows end)
        else NONE
      val mapping = MD.mapping_for graph scope metadata
      val types = M.types mapping
      val factory = MB.create expected
        {graph=graph,scope=scope,mapping=mapping,
         import_limit= #import_limit base,literal_limit= #literal_limit base,
         binder_limit= #binder_limit base}
      val context = #context factory
      fun initialise () =
        let
          (* PV captures expected Work and the Mapping header. This guard
             rejects expiry even on tester mismatch or an empty registry. *)
          fun guard () = PV.protect context (fn () => ())
          val configured:F.value_options =
            {graph=graph,scope=scope,logic= #logic base,
             sources= #sources base,sorts=D.sort_dictionary_from_types types,
             binder_lists= #binder_lists base,
             import_limit= #import_limit base,
             literal_limit= #literal_limit base,
             binder_limit= #binder_limit base,
             recipe_limits= #recipe_limits base,special= #special base,
             ascribed= #ascribed base}
          val session = F.create_mapping_session_with_policy factory
            configured description tokens
          val branches = ref (Redblackset.empty Int.compare)
          fun record values = List.app (fn value =>
            (PV.spend context 1;
             branches := Redblackset.add (!branches,PV.key context value)))
            values
          val _ = D.install_with_policy
            {limits= #recipe_limits base,error=ERR} types
            (fn () => SmtLib.parser_datatype_declarations_from_types types)
            guard session record
          fun admitted_branch (caller,value) = PV.protect context (fn () =>
            (PV.usable context caller value;
             Redblackset.member (!branches,PV.key context value)))
          val assertions=case assertion_rows of NONE=>NONE|SOME rows=>
            let val _=guard()val _=PV.spend context 3
                val frame=B.root(#backend factory)
                fun values []=(guard();[])
                  | values(({scope=caller,syntax,...}:MD.assertion)::rest)=
                      let val _=guard()val _=PV.spend context 2
                          val _=if caller=scope then ()else
                            raise ERR "assertions" "assertion frame changed"
                          val value=(#mapping_value factory)frame syntax
                          val _=PV.usable context scope value
                          val _=PV.spend context 2
                      in value::values rest end
            in SOME(values rows)end
          val _=case assertions of NONE=>()|SOME _=>PV.spend context 1
          val _ = GP.validate_query_with_policy expected query
          val _ = guard ()
        in {session=session,context=context,owner= #owner factory,
          close= #close factory,assertions=assertions,
          admitted_branch=admitted_branch}:session end
      val outcome = Exn.capture (fn () => W.with_step expected
        (fn () => PV.protect context initialise)) ()
    in case outcome of
        Exn.Res result => result
      | Exn.Exn primary =>
          (ignore (Exn.capture (#close factory) ());raise primary)
    end) handle primary => (W.close expected;raise primary))
end
