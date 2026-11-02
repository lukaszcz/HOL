(* Genuine graph emission and Value replay around the existing solver I/O. *)
structure Z3_OwnedValueSolver :> Z3_OwnedValueSolver =
struct
  structure G=SmtReplayGraph
  structure S=SmtReplaySource
  structure W=SmtReplayInvocationWork
  structure NC=SmtReplayNativeContract
  structure RP=SmtReplayResourcePolicy
  structure Checked=SmtCheckedGraph
  structure Session=SmtReplayWrapperSession
  structure V=SmtLib_GraphSourcePortfolio
  structure GP=SmtLib_GraphPreprocess
  structure E=SmtLib_GraphQueryEmission
  structure Finite=SmtLib_GraphFiniteQueryTransport
  structure Body=SmtLib_GraphFiniteBinderLaw
  structure Opening=SmtLib_GraphCheckedQueryOpening
  structure Backend=SmtLib_GraphBackendSelection
  structure VP=SmtLib_GraphValueProof
  structure PV=SmtLib_GraphParserValue
  structure Parser=Z3_GraphValueProofParser
  structure Final=Z3_OwnedValueProofReplay
  structure Solver=SolverSpec
  val ERR=Feedback.mk_HOL_ERR "Z3_OwnedValueSolver"
  type request={limits:Checked.policy_request,
    check_type:Type.hol_type -> unit}
  type finite_stage={preparation:Finite.preparation,
    bodies:Finite.body_plan list,plan:Finite.body_query_plan,
    backend:Backend.transport}
  datatype phase=Preparing | Ready | Running | Pending | Complete | Closed
  datatype invocation=Invocation of
    {work:W.portfolio,original:Abbrev.goal,owner:Checked.policy_invocation,
     graph:G.graph,scope:G.scope,sources:S.sources,contract:NC.contract,
     request:request,executable:string,version:string,phase:phase ref,
     query:GP.graph_query ref,profiles:G.policy_opaque_profile list ref,
     finite:finite_stage option ref,emission:E.receipt option ref,
     opening:Opening.opened_query option ref,
     bindings:Finite.body_binding list ref,
     nested:Finite.nested_binding list ref,
     packet:Parser.proof VP.packet option ref,
     final:Final.invocation option ref}
  datatype preparation=Prepared of invocation
    | FiniteNeeds of
        {invocation:invocation,requirements:Finite.requirement list}
  datatype result=Solved of SolverSpec.result
    | ReplayNeeds of
        {invocation:invocation,
         requirements:Z3_OwnedValueNamedReplay.requirement list}
    | RealizationNeeds of
        {invocation:invocation,
         requirements:SmtReplayValueRealization.requirement list}
  exception PendingReplay of Z3_OwnedValueNamedReplay.requirement list
  exception PendingRealization of SmtReplayValueRealization.requirement list
  fun work_of(Invocation{work,...})=work
  fun header expected(Invocation{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "owner" "different original Work"
  fun live expected(saved as Invocation{owner,query,phase,...})=
    (header expected saved;
     if !phase=Closed then raise ERR "owner" "solver invocation closed"
       else();
     Checked.validate_with_policy expected owner;
     GP.validate_query_with_policy expected(!query))
  fun close(Invocation{work,owner,packet,final,phase,...})=
    if !phase=Closed then ()else
      let val _=phase:=Closed
          val finish=Exn.capture(fn()=>Option.app Final.close(!final))()
          val parser=Exn.capture(fn()=>Option.app VP.close(!packet))()
          val source=Exn.capture(fn()=>
            Checked.close_original_with_policy work owner)()
          val meter=Exn.capture W.close work
      in Exn.release finish;Exn.release parser;
        Exn.release source;Exn.release meter end
  fun protected expected saved action=action()handle primary=>
    (W.close expected;ignore(Exn.capture close saved);raise primary)
  fun minimum maximum policy=case policy of RP.Uncapped=>RP.AtMost maximum
    | RP.AtMost n=>RP.AtMost(IntInf.min(maximum,n))

  fun prepare(request as {limits,check_type}:request)original=
    case Z3.configured_executable()of NONE=>
      raise ERR "prepare" Z3.error_msg
    | SOME executable=>
    let
      fun discover work _ sources=W.with_step work(fn()=>
        let val {assumptions,denied}=V.originals_with_policy work
            val validation=V.validate_portfolio_with_policy work
              {assumptions=assumptions,
               goal= #node(S.goal_source sources),denied=denied}
        in GP.from_portfolio_with_policy work validation end)
      val {work,invocation=owner}=
        Checked.prepare_original_with_policy limits discover original
      val _=(W.with_step work(fn()=>W.spend_policy work 2)
        handle primary=>
          (ignore(Exn.capture(fn()=>
             Checked.close_original_with_policy work owner)());
           W.close work;raise primary))
      val held=ref(NONE:invocation option)
      fun start()=
        let
          val sources=Checked.original_sources_with_policy_for work owner
          val graph=S.owning_graph sources val scope=S.owning_scope sources
          val preprocessing=Checked.preprocessing_with_policy_for work owner
          val validation=case GP.portfolio_validation preprocessing of
              SOME value=>value|NONE=>raise ERR "prepare"
                "actual original portfolio is missing"
          val query=GP.prepare_query_with_policy work preprocessing
          val contract=Checked.native_contract_with_policy_for work owner
          val version=Z3.version_string()
          (* Twenty captured fields, ten private refs, the constructor,
             held SOME/write and one prepaid retirement publication. *)
          val _=W.with_step work(fn()=>W.spend_policy work 34)
          fun checkpoint label =
            if OS.Process.getEnv "HOL4_HOLSMT_REPLAY_DIAGNOSTICS" <>
                SOME "1" then () else
              let val audit=W.audit_policy work
              in TextIO.output(TextIO.stdErr,"VALUE_SOLVER_WORK phase=" ^
                label ^ " charged=" ^ IntInf.toString(#charged audit) ^
                "\n");TextIO.flushOut TextIO.stdErr end
          val _=checkpoint "prepare.owner"
          val saved=Invocation{work=work,original=original,owner=owner,
            graph=graph,scope=scope,sources=sources,contract=contract,
            request=request,executable=executable,version=version,
            phase=ref Preparing,query=ref query,profiles=ref[],finite=ref NONE,
            emission=ref NONE,opening=ref NONE,bindings=ref[],nested=ref[],
            packet=ref NONE,final=ref NONE}
          val _=held:=SOME saved
          val Invocation{profiles,finite,query=current,emission,phase,
            opening=held_opening,bindings=held_bindings,nested=held_nested,
            ...}=saved
          val native=NC.for_work work contract
          val opening_limit=minimum
            (IntInf.fromInt(#input_limit(#semantic_limits native)))
            (#import_limit(#construction_limits limits))
          fun tick()=W.spend_policy work 1
          fun compare((a,b),(c,d))=
            (tick();case Int.compare(a,c)of EQUAL=>
              (tick();Int.compare(b,d))|answer=>answer)
          val options:SmtLib_TranslationEmissions.options=
            {policy=Z3.z3_414_logic_policy(SOME version),
             dialect=SmtLib.Z3LambdaArray,
             apply_operator=SmtLib.ApplyUnderscore,get_proof=true,
             target=SOME{solver="Z3",version=SOME version}}
          val(rows,opened)=W.with_step work(fn()=>
            (W.spend_policy work 4;
             (ref([]:Opening.opening list),
              ref(Redblackset.empty compare))))
          fun open_view caller node=
            let val result=G.record_opened_view_with_policy graph caller
                  opening_limit node
                val _=tick()
                val key=(G.scope_id caller,G.node_id node)
            in if caller=scope andalso #node result<>node andalso
                not(Redblackset.member(!opened,key))then
                (W.spend_policy work 4;
                 opened:=Redblackset.add(!opened,key);
                 rows:={scope=caller,original=node,
                   opened= #node result}:: !rows)else()end
          fun checked ty=
            (live work saved;check_type ty;live work saved)
          val _=checkpoint "finite.prepare.before"
          val prepared:finite_stage=E.prepare_finite_body_query work
            {query=query,validation=validation,options=options,
             open_opaque=open_view,native_contract=contract,ordinal=0,
             check_type=checked}
          val _=W.with_step work(fn()=>
            (W.spend_policy work 2;finite:=SOME prepared))
          val _=checkpoint "finite.prepare.after"
          val source_nodes=GP.query_nodes_with_policy_for work query
          (* Observe genuine retained opaque leaves directly. A completed
             no-op scan may supply an existing profile; no discovered view
             is adopted as an equality or Source transport. *)
          val _=W.with_step work(fn()=>
            let val _=W.spend_policy work 4
                val seen=ref(Redblackset.empty compare)
                fun append [] tail=(tick();tail)
                  | append(x::xs)tail=(W.spend_policy work 2;
                      x::append xs tail)
                fun keep []=tick()
                  | keep(profile::rest)=
                      (W.spend_policy work 2;
                       profiles:=profile:: !profiles;keep rest)
                fun walk []=tick()
                  | walk((caller,node)::rest)=
                    let val _=tick()
                        val _=ignore(G.closure_root graph caller node)
                        val key=(G.scope_id caller,G.node_id node)
                    in if Redblackset.member(!seen,key)then walk rest else
                      (tick();seen:=Redblackset.add(!seen,key);
                       case G.view graph node of
                         G.Application(f,x)=>
                           (W.spend_policy work 3;
                            walk((caller,f)::(caller,x)::rest))
                       | G.OpaqueRetained=>
                           let val found=G.discover_partial_with_policy
                                 graph caller
                                 {original=node,maximum=opening_limit,
                                  scan_limit=W.remaining_policy work,
                                  step=tick}
                               val actual=G.partial_profiles_with_policy
                                 graph caller found
                           in keep actual;walk rest end
                       | G.AdmittedBinder _=>
                           let val data=G.binder_closure_data graph caller
                                 (G.binder_closure graph caller node)
                           in W.spend_policy work 3;
                             walk((#body_frame data,#body data)::rest)end
                       | _=>walk rest)
                    end
                fun roots []=(tick();[])
                  | roots(node::rest)=(W.spend_policy work 2;
                      (scope,node)::roots rest)
                val _=W.spend_policy work 4
                val inputs=append(#assumptions source_nodes)
                  [#denied source_nodes,#goal source_nodes]
            in walk(roots inputs)end)
          val _=checkpoint "opening.before"
          val opening=Opening.transport_with_conversions_with_policy work
            {validation=validation,openings= !rows,
             native_contract=contract,profiles= !profiles,ordinal=0,
             check_type=checked}
          val _=W.with_step work(fn()=>
            (W.spend_policy work 2;held_opening:=SOME opening))
          fun bodies [] nested laws= (nested,laws)
            | bodies(plan::rest)nested laws=
                (case Body.execute_nested_conditioned_with_policy work plan
                    {validation= #validation opening,profiles= !profiles,
                     bindings=nested}of
                   Body.NestedLaw{binding,law}=>
                     let val(saved,nodes)=W.with_step work(fn()=>
                           (W.spend_policy work 4;
                            (binding::nested,law::laws)))
                     in bodies rest saved nodes end
                 | Body.NestedNeeds _=>bodies rest nested laws)
          val _=checkpoint "body.laws.before"
          val(nested,laws)=bodies(#bodies prepared)[][]
          val _=W.with_step work(fn()=>
            (W.spend_policy work 2;
             held_bindings:=laws;held_nested:=nested))
          (* This actual root programme reports ALL remaining requirements;
             private completed body laws discharge only their own ports. *)
          val _=checkpoint "body.query.before"
          val output=Finite.execute_body_query_with_policy work
            (#plan prepared){opening=opening,bindings=laws}
          val _=checkpoint "body.query.after"
        in case output of Finite.QueryNeeds requirements=>
            (W.with_step work(fn()=>
               (W.spend_policy work 1;phase:=Pending));
             FiniteNeeds{invocation=saved,requirements=requirements})
          | Finite.QueryRewritten{preprocessing,...}=>
            let val _=checkpoint "query.prepare.before"
                val actual=GP.prepare_query_with_policy work preprocessing
                val _=checkpoint "query.prepare.after"
                val _=W.with_step work(fn()=>
                  (W.spend_policy work 1;current:=actual))
                val _=checkpoint "emit.before"
                val receipt=E.emit_with_assertions work
                  {query=actual,backend= #backend prepared,options=options,
                   prefix="value_solver_",open_opaque=open_view}
                val _=checkpoint "emit.after"
                val _=W.with_step work(fn()=>
                  (W.spend_policy work 3;emission:=SOME receipt;
                   live work saved;phase:=Ready))
            in Prepared saved end
        end
    in start()handle primary=>
      (case !held of SOME saved=>ignore(Exn.capture close saved)
       | NONE=>ignore(Exn.capture(fn()=>
           Checked.close_original_with_policy work owner)());
       W.close work;raise primary)
    end

  fun run_using extra expected saved=
    ((header expected saved;
      protected expected saved(fn()=>
      let
        val Invocation{work,owner,original,graph,scope,sources,contract,
          request={limits,check_type},version,executable,query,profiles,
          emission,packet,final,phase,...}=saved
        val _=live expected saved
        val _=W.with_step expected(fn()=>
          (W.spend_policy expected 7;
           if !phase=Ready then phase:=Running else
             raise ERR "run" "solver invocation is not ready or was used"))
        val capture_primary=ref(NONE:exn option)
        val receipt=case !emission of SOME value=>value
          | NONE=>raise ERR "run" "actual emitted query is missing"
        fun guard()=live expected saved
        fun checked ty=(guard();check_type ty;guard())
        val description=E.describe_for expected(!query)receipt
        val SmtLib.LogicFeatures{quantifiers,...}= #features description
        val check_sat=if quantifiers then
            Z3.quantified_proof_check_sat_command
          else Z3.plain_check_sat_command
        fun select fragment=if not quantifiers then fragment else
          let val count=String.size fragment
              val size=String.size Z3.plain_check_sat_command
              val _=W.with_step expected(fn()=>
                (guard();W.spend_policy expected
                  (4+(if count=size then IntInf.fromInt count else 0))))
          in if count=size andalso fragment=Z3.plain_check_sat_command then
              check_sat else fragment end
        fun pre _=(guard();
          (saved,fn sink=>E.write_for expected(!query)receipt
            (fn fragment=>sink(select fragment))))
        fun command _=(guard();executable ^ Z3.current_proof_cmd_stem())
        val capture=Z3.z3_capture_for_invocation()
        fun call observer command key stage path=
          let val _=W.with_step expected(fn()=>
                (guard();W.spend_policy expected 8))
              val outcome=Exn.capture
                (fn()=>observer command key stage path)()
              val lifecycle=Exn.capture guard()
          in case outcome of Exn.Exn primary=>raise primary
            | Exn.Res()=>Exn.release lifecycle end
        fun observe command key stage path=
          (W.with_step expected(fn()=>
             (guard();W.spend_policy expected 2));
           Option.app(fn observer=>
             call observer command key stage path)capture;
           Option.app(fn observer=>
             call observer command key stage path)extra;guard())
          handle primary=>
            if Solver.terminal_capture_exception primary then raise primary
            else if #retired(W.audit_policy expected)then
              (* The existing best-effort observer swallows ordinary errors.
                 Carry this exact retired-owner Primary through its existing
                 terminal cancellation/cleanup boundary, then restore it. *)
              (capture_primary:=SOME primary;raise Interrupt)
            else raise primary
        fun parse input=
          let val description=E.describe_for expected(!query)receipt
              val construction= #construction_limits limits
              val options:SmtLib_GraphFrontend.value_options=
                {graph=graph,scope=scope,logic= #logic description,sources=[],
                 sorts=Redblackmap.mkDict String.compare,binder_lists=[],
                 import_limit= #import_limit construction,
                 literal_limit= #literal_limit construction,
                 binder_limit= #binder_limit construction,
                 recipe_limits= #recipe_limits construction,
                 special=fn _=>fn _=>NONE,
                 ascribed=fn _=>fn _=>fn _=>NONE}
              val _=W.with_step expected(fn()=>W.spend_policy expected 2)
              val parsed=Parser.create_packet_with_policy_from_input expected
                (!query)options(#metadata description)version
                (fn()=>TextIO.input1 input)
              val _=packet:=SOME parsed
              val assertions=W.with_step expected(fn()=>
                case VP.assertions_with_policy_for expected(!query)parsed of
                  SOME values=>values|NONE=>raise ERR "parse"
                    "actual emitted assertion Values are missing")
              val session=Checked.source_session_with_policy_for expected
                owner
              val _=Session.begin_replay session
              val _=W.with_step expected(fn()=>W.spend_policy expected 2)
              val preparation=
                Final.prepare_with_owned_programmes_with_policy
                expected(!query)parsed
                {assertions=assertions,native_contract=contract,
                 profiles= !profiles,check_type=checked}
          in case preparation of Final.ReplayNeeds requirements=>
              (phase:=Pending;raise PendingReplay requirements)
            | Final.Prepared actual=>
              (final:=SOME actual;
               W.with_step expected(fn()=>W.spend_policy expected 2);
               case Final.finish_with_policy expected actual of
                 Final.RealizationNeeds requirements=>
                   (phase:=Pending;raise PendingRealization requirements)
               | Final.Proved{theorem,...}=>
                   (guard();Session.accept session theorem;
                    phase:=Complete;theorem))
          end
        fun post _ path=
          let val input=TextIO.openIn path
              fun consume()=
                let val _=guard()
                    val(status,start)=Z3.is_sat_stream_with_consumed input
                    val _=guard()
                in case status of SolverSpec.UNSAT NONE=>
                    let val bytes=SmtResource.remaining_file_bytes path start
                        val _=SmtResource.check_proof_size
                          "z3-proof-text" bytes
                        val theorem=SolverSpec.quiet parse input
                    in SolverSpec.UNSAT(SOME theorem)end
                  | _=>status end
              val outcome=Exn.capture consume()
              val cleanup=Exn.capture TextIO.closeIn input
          in case outcome of Exn.Exn primary=>raise primary
            | Exn.Res value=>(Exn.release cleanup;value)end
        fun validate _ goal theorem=
          Checked.audit_original_with_policy expected owner goal theorem
        fun complete _=if !phase=Pending then ()else close saved
        val execute_solver=
          Solver.make_solver_with_capture_command_and_completion_writer_strict
        fun execute()=execute_solver validate complete(SOME observe)
          pre command post original
        val outcome=Exn.capture execute()
        val outcome=case !capture_primary of NONE=>outcome
          | SOME primary=>Exn.Exn primary
      in case outcome of
          Exn.Res value=>Solved value
        | Exn.Exn(PendingReplay requirements)=>
            ReplayNeeds{invocation=saved,requirements=requirements}
        | Exn.Exn(PendingRealization requirements)=>
            RealizationNeeds{invocation=saved,requirements=requirements}
        | Exn.Exn primary=>raise primary
      end))handle primary=>(W.close expected;raise primary))
  fun run expected saved=run_using NONE expected saved
  fun run_with_capture expected saved observe=
    run_using(SOME observe)expected saved
end
