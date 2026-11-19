(* Test support: a live owned-Value CPC fixture (graph, Source portfolio,
   query, declaration metadata, native contract) and the packet and
   assertion helpers that drive the owned receiver. Shared by selftest
   postlude 417 and CPC_OwnedClassificationTests. *)
structure CPC_OwnedValueTestFixture =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure V = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure T = SmtLib_GraphTranslation
  structure MD = SmtLib_GraphDeclarationMetadata
  structure F = SmtLib_GraphFrontend
  structure PV = SmtLib_GraphParserValue
  structure VP = SmtLib_GraphValueProof
  structure C = CPC_ProofParser
  structure CV = CPC_GraphValueProofParser
  structure NC = SmtReplayNativeContract
  structure RP = SmtReplayResourcePolicy
  type env = {graph:G.graph,scope:G.scope,sources:S.sources,work:W.portfolio,
    query:GP.graph_query,metadata:MD.metadata,contract:NC.contract}
  val cap = RP.AtMost 1000000000
  val native:NC.limits =
    {semantic_limits={input_limit=1000000,output_limit=1000000,
       template_limit=1000000},import_limit=1000000,
     type_work_limit=100000000}
  (* [budget] bounds the whole portfolio, setup included; [prefix] names
     the emitted declarations. *)
  fun fixture {budget,retain,prefix} assumptions goal action =
    let
      val graph=G.new () val scope=G.root_scope graph
      val sources=S.new graph scope 10000
        {assumptions=assumptions,goal=goal}
      val limit=case budget of NONE=>cap | SOME n=>RP.AtMost n
      val work=W.begin_with_policy graph scope sources
        {limits={input_limit=cap,output_limit=cap,template_limit=cap},
         work_limit=limit}
      fun run () =
        let
          val contract=NC.capture work native
          val {assumptions,denied}=V.originals_with_policy work
          val validation=V.validate_portfolio_with_policy work
            {assumptions=if retain then assumptions else [],
             goal= #node (S.goal_source sources),
             denied=denied}
          val query=GP.prepare_query_with_policy work
            (GP.from_portfolio_with_policy work validation)
          fun open_view caller node=ignore
            (G.record_opened_view_with_policy graph caller
              (RP.AtMost 10000) node)
          val metadata=T.with_outbound_query_analysis_with_policy work query
            open_view (fn context=>SmtLib.outbound_with_backend_context
              {sequence_emission=false,set_backend=SmtLib.Z3Set,
               bag_backend=SmtLib.Z3ArrayBag,
               has_set_terms=false,has_bag_terms=false} (fn backend=>
              let
                val operations=
                  SmtLib_GraphCarrierOperations.make_with_datatypes context
                    {sequence_emission=false}
                    {term_to_string=fn _=>raise Fail "unexpected formatter"}
                val emission=SmtLib_GraphDispatcher.emit context
                  {operations=operations,regime=SmtLib.FirstOrder,
                   apply_operator=SmtLib.ApplyUnderscore,prefix=prefix,
                   roots=ListPair.zip
                     (List.tabulate (length (#assumptions context)+2,Lib.I),
                      #goal context :: #assumptions context @
                        [#denied context])}
              in SmtLib_GraphDeclarationMetadata.freeze context
                {graph=graph,scope=scope,regime=SmtLib.FirstOrder,
                 backend=backend,operations=operations,emission=emission}
              end))
        in action ({graph=graph,scope=scope,sources=sources,work=work,
          query=query,metadata=metadata,contract=contract}:env) end
      val outcome=Exn.capture run ()
      val cleanup=Exn.capture (fn()=>
        (W.close work;G.close_scope graph scope)) ()
    in case outcome of Exn.Exn primary=>raise primary
      | Exn.Res result=>(Exn.release cleanup;result) end
  fun options bindings (e:env):F.value_options =
    {graph= #graph e,scope= #scope e,logic="ALL",sources=bindings,
     sorts=Redblackmap.mkDict String.compare,binder_lists=[],
     import_limit=cap,literal_limit=cap,binder_limit=RP.AtMost 1,
     recipe_limits={template_limit=cap,index_limit=cap,
       operand_limit=cap,token_limit=cap},
     special=fn _=>fn _=>NONE,ascribed=fn _=>fn _=>fn _=>NONE}
  fun input text =
    let val index=ref 0 in fn()=>
      if !index=String.size text then NONE else
        let val result=String.sub (text,!index)
        in index:= !index+1;SOME result end end
  fun packet bindings (e:env) text =
    CPC_GraphValueProofParser.create_packet_with_policy_from_input
      (#work e) (#query e) (options bindings e) (#metadata e) "1.3.4"
      (input text)
  fun graph_assertions (e:env) (data:CV.proof VP.contents) =
    let val current=GP.query_nodes_with_policy_for (#work e) (#query e)
    in W.with_step (#work e) (fn()=>
      let
        val context= #context data
        fun guard ()=(PV.validate context;
          G.validate_scope (#graph e) (#scope e))
        fun tick ()=(guard ();W.spend_policy (#work e) 1)
        fun compare (left,right)=(tick ();Int.compare (left,right))
        val memo=ref (Redblackmap.mkDict compare)
        (* The actual query supplies graph IDs. Copy App DATA with sharing;
           graph_leaf remains restricted to its genuine atomic contract.
           This fixture needs no native query term or binder conversion. *)
        fun copy node=
          let val _=tick () val syntax=G.view (#graph e) node
              val id=G.node_id node
          in case Redblackmap.peek (!memo,id) of
              SOME value=>(PV.usable context (#scope e) value;value)
            | NONE=>
                let val value=case syntax of
                        G.Variable _=>PV.graph_leaf context (#scope e) node
                      | G.Constant _=>PV.graph_leaf context (#scope e) node
                      | G.Application (left,right)=>
                          let val f=copy left val x=copy right
                          in PV.application context (#scope e) (f,x) end
                      | _=>raise Fail "fixture Source needs binder programme"
                    val _=PV.usable context (#scope e) value
                    val _=tick ()
                    val _=memo:=Redblackmap.insert (!memo,id,value)
                in value end
          end
        fun copies []=(guard ();[])
          | copies (node::rest)=(tick ();copy node::copies rest)
      in copies (#assumptions current @ [#denied current]) end)
    end
  fun asserted_values (e:env) (data:CV.proof VP.contents) =
    let val current=GP.query_nodes_with_policy_for(#work e)(#query e)
        val fallback=graph_assertions e data
    in W.with_step(#work e)(fn()=>
      let val context= #context data
          val asserted=List.mapPartial(fn C.GraphAssume(_,term)=>
              SOME(#node term)|_=>NONE)(#commands(#proof data))
          fun actual(node,copied)=case List.find(fn value=>
              case PV.corresponds_to_graph_with_policy context
                  (#graph e)(#scope e){value=value,node=node}of
                PV.Corresponding=>true|_=>false)asserted of
              SOME value=>value|NONE=>copied
      in ListPair.map actual
        (#assumptions current@[#denied current],fallback)end)
    end
end
