(* Actual packet/Source/Work/NC ownership; no legacy proof callbacks. *)
structure Z3_PolicyGraphProofReplay :> Z3_PolicyGraphProofReplay =
struct
  structure W=SmtReplayInvocationWork
  structure NC=SmtReplayNativeContract
  structure G=SmtReplayGraph
  structure S=SmtReplaySource
  structure Scope=SmtReplayOwnedScopeReceipt
  structure GP=SmtLib_GraphPreprocess
  structure Packet=SmtLib_GraphProof
  structure Z=Z3_GraphProofParser
  structure Registry=Z3_Proof
  structure P=SmtReplayProof
  structure R=SmtReplayRules
  structure C=SmtReplayClause
  val _=SmtReplayClause.discover_recorded_with_policy
  val _=SmtReplayClause.prepare_resolution_with_policy
  val _=SmtReplayClause.discover_raw_resolution_with_policy
  val _=SmtReplayClause.prepare_raw_resolution_with_policy
  val _=SmtReplayClause.execute_resolution_with_policy
  val _=SmtReplayInvocationWork.validate_policy
  val _=SmtReplayNativeContract.validate_for
  val _=SmtReplayGraph.validate_scope
  val _=SmtReplaySource.owning_graph
  val _=SmtReplayOwnedScopeReceipt.description_with_policy_for
  val _=SmtLib_GraphProof.graph
  val _=Z3_Proof.lookup_rule
  val _=Z3_GraphProofParser.create_packet_with_policy
  val _=SmtLib_GraphPreprocess.assembler_with_policy
  val _=SmtReplayRules.boolean_graph_with_policy
  val _=SmtReplayRules.equality_rule_with_policy
  val _=SmtReplayProof.prepare_source_close_with_policy
  val _=SmtReplayProof.prepare_local_specialize_schema_with_policy
  val _=SmtReplayProof.retire_policy_block_for
  val ERR=Feedback.mk_HOL_ERR "Z3_PolicyGraphProofReplay"
  type request=
    {packet:Z.proof Packet.packet,preprocessing:GP.validation,
     profiles:G.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,ordinal:int}
  datatype phase=Preparing|Ready|Running|Completing|Complete|Retired
  open Z3_SharedReplayPlan
  type plan = (G.node,G.node) Z3_SharedReplayPlan.plan
  datatype task=Visit of Z.proof_id|Finish of Z.proof_id
  type entry={node:G.node,edge:P.edge}
  datatype invocation=Invocation of
    {work:W.portfolio,native:NC.contract,graph:G.graph,root:G.scope,
     sources:S.sources,frame:Scope.receipt,packet:Z.proof Packet.packet,
     preprocessing:GP.validation,profiles:G.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,phase:phase ref,
     block:P.block option ref,assemble:(G.node -> P.edge option)option ref,
     remaining:(Z.proof_id * plan)list ref,
     plans:(Z.proof_id,plan)Redblackmap.dict ref,
     published:(Z.proof_id,unit)Redblackmap.dict ref,
     laws:(Z.proof_id,P.closed_fact)Redblackmap.dict ref,
     facts:P.closed_fact list ref,roots:G.node list ref,ordinal:int ref,
     mode:resolution_mode,
     raw_batches:(Z.proof_id,C.policy_raw_occurrences)Redblackmap.dict ref,
     occurrences:(Z.proof_id,C.policy_occurrences)Redblackmap.dict ref,
     targets:(Z.proof_id,C.policy_occurrences)Redblackmap.dict ref,
     edges:(Z.proof_id,entry)Redblackmap.dict ref,
     frames:G.scope list ref,epoch:int,symbols:int}
  fun retire(Invocation{work,phase,...})=(phase:=Retired;W.close work)
  fun protect owner action=action()handle primary=>
    (retire owner;raise primary)
  fun header expected(Invocation{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "owner" "different original Work"
  fun active(Invocation{work,native,graph,root,sources,frame,packet,
      preprocessing,phase,block,frames,epoch,symbols,...})=
    (if !phase=Retired then raise ERR "owner" "invocation retired"else ();
     NC.validate_for work native;
     List.app(G.validate_scope graph)(!frames);
     let val data=Scope.description_with_policy_for work frame
         val _=if Portable.pointer_eq(#graph data,graph)andalso
             #scope data=root andalso
             Portable.pointer_eq(#sources data,sources)andalso
             Portable.pointer_eq(Packet.graph packet,graph)andalso
             Packet.scope packet=root andalso Packet.solver packet="Z3"
           then ()else raise ERR "owner"
             "actual packet/Source association changed"
         val proof=Packet.proof packet
         val version=Packet.versions packet
     in if #resolved version= #z3_version proof andalso
         Type.type_epoch()=epoch andalso Term.term_epoch()=symbols then ()
       else raise ERR "owner" "actual packet version/epochs changed"end;
     GP.validate_with_policy work preprocessing;
     if Portable.pointer_eq(GP.original_sources preprocessing,sources)andalso
         GP.source_nodes preprocessing=S.assumption_nodes sources @
           [S.denied_goal_node sources]then ()else
       raise ERR "owner" "actual original Source prefix changed";
     case !phase of Completing=>()|Complete=>()
       | _=>Option.app(P.validate_block_for work)(!block))
  fun expected_owner expected owner=
    ((header expected owner;active owner)
     handle primary=>(W.close expected;raise primary))
  fun policy owner ty=
    let val Invocation{check_type,...}=owner
    in active owner;check_type ty;active owner end
  fun action(owner as Invocation{work,...})operation=
    W.with_step work(fn()=>
      (active owner;let val value=operation()val _=active owner in value end))
  fun tick(owner as Invocation{work,...})=(active owner;W.spend_policy work 1)
  fun current(owner as Invocation{block,...})=
    (active owner;case !block of SOME held=>held
     | NONE=>raise ERR "block" "actual Block has not been frozen")
  fun lookup(owner as Invocation{edges,...})id=
    (tick owner;case Redblackmap.peek(!edges,id)of SOME value=>value
     | NONE=>raise ERR "registry" "premise is not a completed command")
  (* Normalization is part of the same shared registry classifier. *)
  fun plan_packet(owner as Invocation
      {graph,root,sources,packet,preprocessing,frames,mode,...})=
    let
      val proof=Packet.proof packet
      val marks=ref(Redblackmap.mkDict Z.compare_id)
      val ordered=ref([]:(Z.proof_id * plan)list)
      val endpoints=ref(Redblackmap.mkDict Z.compare_id)
      val roots=ref(Redblackset.empty Int.compare)
      val root_nodes=ref([]:G.node list)
      fun step id=(tick owner;case Redblackmap.peek(#steps proof,id)of
          SOME value=>value|NONE=>raise ERR "packet" "unknown proof ID")
      fun node id=(tick owner;case Redblackmap.peek(!endpoints,id)of
          SOME value=>value|NONE=>raise ERR "packet" "unplanned premise")
      fun located(value:SmtLib_GraphFrontend.term)=
        (tick owner;G.validate_scope graph(#scope value);
         if G.scope_visible graph(#scope value)root andalso
             G.scope_visible graph root(G.node_scope graph(#node value))
           then
             (if List.exists(fn held=>held= #scope value)(!frames)then ()
              else frames:= #scope value:: !frames;#node value)
           else raise ERR "packet"
             "actual local node needs scoped command programme")
      fun operands constant arity node=
            let fun walk current arguments=
                  (tick owner;case G.view graph current of
                      G.Application(operator,operand)=>
                        walk operator(operand::arguments)
                    | G.Constant _=>
                        if Term.same_const(G.representative graph current)
                            constant andalso List.length arguments=arity then
                          SOME arguments else NONE
                    | _=>NONE)
            in walk node []end
      (* Rule checks remain at the existing Finish event below. *)
      fun dependencies id=case step id of
          Z.Rule{premises,...}=>premises|Z.Alias other=>[other]
        | Z.Bind _=>raise ERR "packet" "proof-bind needs scoped programme"
      fun keep target=
        if Redblackset.member(!roots,G.node_id target)then ()else
          (roots:=Redblackset.add(!roots,G.node_id target);
           root_nodes:=target:: !root_nodes)
      fun finish id=
        let
          fun processed target=List.exists
            (fn held=>(tick owner;held=target))
            (GP.processed_assumptions preprocessing @
             [GP.processed_denied_goal preprocessing])
          fun original_slot target=
            let fun original index []=raise ERR "packet"
                      "hypothesis outside actual original Source prefix"
                  | original index (held::rest)=
                      (tick owner;if held=target then index
                       else original (index+1) rest)
            in original 0 (S.assumption_nodes sources @
              [S.denied_goal_node sources]) end
          val (target,plan)=Z3_SharedReplayPlan.classify
            {observer=Z3_SharedReplayPlan.silent_observer,
             prior=node,located=located,processed=processed,
             original_slot=original_slot,operands=operands,
             keep=keep,error=ERR}
            {version= #z3_version proof,mode=mode} (step id)
            val _=tick owner val _=keep target
            val _=endpoints:=Redblackmap.insert(!endpoints,id,target)
            val _=ordered:=(id,plan):: !ordered
        in marks:=Redblackmap.insert(!marks,id,2)end
      fun walk []=()
        | walk(Finish id::rest)=(finish id;walk rest)
        | walk(Visit id::rest)=
          (tick owner;case Redblackmap.peek(!marks,id)of SOME 2=>walk rest
           | SOME _=>raise ERR "packet" "cyclic actual proof commands"
           | NONE=>(marks:=Redblackmap.insert(!marks,id,1);
               walk(List.map Visit(dependencies id) @ Finish id::rest)))
      val _=walk[Visit(#root proof)]
    in(List.rev(!ordered),List.rev(!root_nodes))end
  (* Occurrence factories own actions, so packet planning finishes first.
     Only actual resolution premises/targets acquire these witnesses. *)
  fun prepare_resolution_occurrences(owner as Invocation
      {work,frame,packet,roots,occurrences,targets,raw_batches,...})ordered=
    let
      val proof=Packet.proof packet
      fun parsed id=
        case action owner(fn()=>
          (tick owner;case Redblackmap.peek(#steps proof,id)of
             SOME value=>value|NONE=>raise ERR "unit-resolution"
               "missing actual packet premise"))of
            Z.Rule{conclusion,...}=>conclusion
          | Z.Alias other=>parsed other
          | Z.Bind _=>raise ERR "unit-resolution"
              "proof-bind needs its actual scoped programme"
      fun retain saved=action owner(fn()=>
        let val required=C.roots_with_policy_for work saved
            fun add node=
              if List.exists(fn held=>(tick owner;held=node))(!roots)then ()
              else(tick owner;roots:=node:: !roots)
        in List.app add required end)
      fun source id=
        case action owner(fn()=>
          (tick owner;Redblackmap.peek(!occurrences,id)))of
            SOME saved=>saved
          | NONE=>
            let val value=parsed id
                val _=active owner
                val saved=C.discover_recorded_with_policy work frame value
                val _=active owner val _=retain saved
                val _=action owner(fn()=>
                  (tick owner;occurrences:=Redblackmap.insert
                    (!occurrences,id,saved)))
            in saved end
      fun prepare(id,Resolution(_,ids,parsed))=
            let val _=List.app(fn input=>ignore(source input))ids
                val _=active owner
                val target=C.discover_target_with_policy work frame parsed
                val _=active owner val _=retain target
            in action owner(fn()=>
              (tick owner;targets:=Redblackmap.insert(!targets,id,target)))end
        | prepare(id,RawResolution(_,ids,parsed_target))=
            let
              val(head,tail)=case ids of first::rest=>(first,rest)
                | []=>raise ERR "unit-resolution" "empty raw premises"
              val _=active owner
              val saved=C.discover_raw_resolution_with_policy work frame
                {head=parsed head,units=List.map parsed tail,
                 target=parsed_target}
              val _=active owner
            in action owner(fn()=>
              let val required=C.raw_roots_with_policy_for work saved
                  fun add node=if List.exists(fn held=>
                      (tick owner;held=node))(!roots)then ()else
                    (tick owner;roots:=node:: !roots)
                  val _=List.app add required val _=tick owner
              in raw_batches:=Redblackmap.insert(!raw_batches,id,saved)end)
            end
        | prepare _=()
    in List.app prepare ordered;active owner end

  (* This is a real replacement Context. Saved facts survive old Block
     retirement; no old edge crosses into the replacement. Publication
     and revocation are callback-free after the next freeze succeeds. *)
  fun rebuild(owner as Invocation{work,native,preprocessing,frame,roots,
      facts,ordinal,profiles,block,edges,assemble,...})=
    let
      val _=active owner
      val base_roots=GP.roots preprocessing
      (* Same actual root-list preparation/debit as the original GP
         frontier, now with the genuine accumulated native facts too. *)
      val combined=action owner(fn()=>
        let fun prepend []=base_roots
              | prepend(node::rest)=
                  (W.spend_policy work 2;node::prepend rest)
        in prepend(!roots)end)
      val frontier=P.prepare_scoped_original_realization_frontier_with_policy
        work{frame=frame,roots=combined,
          additional_sources=[],
          closed_facts= !facts @ GP.closed_facts preprocessing,
          conversions=GP.conversions preprocessing}
      val next=action owner(fn()=>
        let val tables=P.prepare_owned_realization_tables_with_policy
              work frontier
            val plan=P.prepare_native_realization_freeze_with_policy work
              {tables=tables,contract=native,profiles=profiles,
               ordinal= !ordinal,check_type=policy owner}
            val _=ordinal:= !ordinal+1
        in P.freeze_owned_realization_tables_with_policy work plan end)
      val _=action owner(fn()=>
        (Option.app(P.retire_policy_block_for work)(!block);
         block:=SOME next;edges:=Redblackmap.mkDict Z.compare_id;
         assemble:=NONE))
      (* Factory and query each own their separate Work actions. *)
      val build=GP.assembler_with_policy work preprocessing next
      val _=active owner val _=assemble:=SOME build
    in active owner end

  (* Immutable packet recipes are acyclic by the packet planner. Recursive
     premises are resolved BEFORE the caller-owned primitive rule action.
     The law branch never invokes NativeSPEC: only first publication does. *)
  fun evaluate(owner as Invocation
      {work,graph,plans,laws,edges,assemble,occurrences,targets,
       raw_batches,...})id=
    let
      val block=current owner
      val saved=action owner(fn()=>
        (tick owner;Redblackmap.peek(!edges,id)))
    in case saved of SOME entry=>entry | NONE=>
      let
        val plan=action owner(fn()=>
          (tick owner;case Redblackmap.peek(!plans,id)of SOME value=>value
           | NONE=>raise ERR "registry" "unknown planned command"))
        fun inputs ids=List.map(fn wanted=>
          let val entry=evaluate owner wanted
          in(#node entry,#edge entry)end)ids
        val(target,edge)=case plan of Original node=>
              (node,case !assemble of SOME build=>
                (case build node of SOME edge=>edge | NONE=>
                  raise ERR "source" "missing genuine Source derivation")
               | NONE=>raise ERR "source" "missing owned assembler")
          | OriginalSlot(index,node)=>action owner(fn()=>
              (node,P.source block index))
          | Alias other=>
              let val entry=evaluate owner other
              in(#node entry,#edge entry)end
          | Equality(rule,node,ids)=>
              let val premises=inputs ids
              in action owner(fn()=>
                (node,R.equality_rule_with_policy work graph block rule
                  node premises))end
          | Boolean(node,ids)=>
              let val premises=inputs ids
              in action owner(fn()=>
                (node,R.boolean_graph_with_policy work block
                  {root=node,premises=premises}))end
          | Resolution(target,ids,_)=>
              let
                (* Current-Block dependencies finish before any Clause
                   action. No old edge or native schema is replayed. *)
                val completed=List.map(fn input=>
                  (input,evaluate owner input))ids
                val(wanted,saved)=action owner(fn()=>
                  let val _=tick owner
                      val wanted=case Redblackmap.peek(!targets,id)of
                          SOME value=>value|NONE=>raise ERR "unit-resolution"
                            "actual target occurrences were not prepared"
                      fun source(input,entry:entry)=
                        (tick owner;case Redblackmap.peek(!occurrences,input)of
                           SOME value=>(value,#edge entry)
                         | NONE=>raise ERR "unit-resolution"
                             "actual premise occurrences were not prepared")
                  in(wanted,List.map source completed)end)
                fun clause(saved,edge)=
                  (active owner;
                   let val result=C.from_source_with_policy work block
                         saved edge
                   in active owner;result end)
                val premises=List.map clause saved
                val _=active owner
                val plan=C.prepare_resolution_with_policy work
                  {premises=premises,target=wanted,check_type=policy owner}
                val _=active owner
                val result=C.execute_resolution_with_policy work plan
                val _=active owner
              in(target,result)end
          | RawResolution(target,ids,_)=>
              let
                val completed=List.map(fn input=>evaluate owner input)ids
                val saved=action owner(fn()=>
                  (tick owner;case Redblackmap.peek(!raw_batches,id)of
                     SOME value=>value|NONE=>raise ERR "unit-resolution"
                       "actual raw occurrence batch was not prepared"))
                val _=active owner
                val prepared=C.prepare_raw_resolution_with_policy work block
                  saved{premises=List.map(fn value:entry=> #edge value)
                    completed,check_type=policy owner}
                val _=active owner
                val result=C.execute_resolution_with_policy work prepared
                val _=active owner
              in(target,result)end
          | Quantified{target,...}=>action owner(fn()=>
              let val _=tick owner
                  val law=case Redblackmap.peek(!laws,id)of SOME held=>held
                    | NONE=>raise ERR "quant-inst"
                        "native schema has not been published"
                  val law_node=P.closed_node law
                  val law_edge=P.closed block law
              in(target,R.boolean_graph_with_policy work block
                {root=target,premises=[(law_node,law_edge)]})end)
        val result={node=target,edge=edge}:entry
        val _=action owner(fn()=>
          let val _=P.validate_block_for work block val _=tick owner
              val _=if Portable.pointer_eq(Thm.concl(P.theorem block edge),
                  P.name block target)then ()else raise ERR "registry"
                    "actual named result differs"
          in edges:=Redblackmap.insert(!edges,id,result)end)
      in result end
    end

  fun publish_schema(owner as Invocation{work,profiles,laws,facts,...})
      id plan=
    case plan of Quantified{source,instance,arguments,...}=>
      let
        val _=action owner(fn()=>
          (tick owner;if Option.isSome(Redblackmap.peek(!laws,id))then
            raise ERR "quant-inst" "native schema already published"else()))
        val law=action owner(fn()=>
          let val prepared=P.prepare_local_specialize_schema_with_policy
                work(current owner){source=source,arguments=arguments,
                  target=instance,profiles=profiles,check_type=policy owner}
          in P.execute_local_specialize_with_policy work prepared end)
        val _=active owner
        val _=laws:=Redblackmap.insert(!laws,id,law)
        val _=facts:=law:: !facts
      in rebuild owner end
    | _=>()

  fun begin_resolution_with_policy mode work native
      ({packet,preprocessing,profiles,check_type,ordinal}:request)=
    ((let
        val _=NC.validate_for work native
        val _=if ordinal>=0 then ()else raise ERR "begin" "negative ordinal"
        val sources=W.original_sources work
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val frame=Scope.root_with_policy work
        val owner=Invocation{work=work,native=native,graph=graph,root=root,
          sources=sources,frame=frame,packet=packet,
          preprocessing=preprocessing,profiles=profiles,check_type=check_type,
          phase=ref Preparing,block=ref NONE,assemble=ref NONE,
          remaining=ref[],plans=ref(Redblackmap.mkDict Z.compare_id),
          published=ref(Redblackmap.mkDict Z.compare_id),
          laws=ref(Redblackmap.mkDict Z.compare_id),facts=ref[],roots=ref[],
          mode=mode,raw_batches=ref(Redblackmap.mkDict Z.compare_id),
          occurrences=ref(Redblackmap.mkDict Z.compare_id),
          targets=ref(Redblackmap.mkDict Z.compare_id),
          ordinal=ref ordinal,edges=ref(Redblackmap.mkDict Z.compare_id),
          frames=ref[root],epoch=Type.type_epoch(),symbols=Term.term_epoch()}
        val(ordered,needed)=action owner(fn()=>plan_packet owner)
        val Invocation{plans,remaining,roots,phase,...}=owner
        val _=plans:=List.foldl(fn((id,value),dict)=>
          Redblackmap.insert(dict,id,value))(Redblackmap.mkDict Z.compare_id)
            ordered
        val _=roots:=needed val _=remaining:=ordered
        val _=prepare_resolution_occurrences owner ordered
        val _=rebuild owner
        val _=active owner val _=phase:=Ready
      in owner end)handle primary=>(W.close work;raise primary))

  fun begin_with_policy work native request=
    begin_resolution_with_policy RecordedResolution work native request
  fun begin_raw_with_policy work native request=
    begin_resolution_with_policy LegacyRawResolution work native request

  fun replay_next_with_policy expected owner=
    ((expected_owner expected owner;protect owner(fn()=>
      let val Invocation{phase,remaining,published,...}=owner
          val _=if !phase=Ready then phase:=Running else
            raise ERR "next" "invocation consumed or reentrant"
      in case !remaining of []=>(phase:=Ready;NONE)
        |(id,plan)::tail=>
          let val _=publish_schema owner id plan
              val entry=evaluate owner id
              val _=active owner
              val _=published:=Redblackmap.insert(!published,id,())
              val _=remaining:=tail val _=phase:=Ready
          in SOME{id=id,node= #node entry}end
      end))handle primary=>(W.close expected;raise primary))

  fun step_with_policy_for expected owner id=
    ((expected_owner expected owner;protect owner(fn()=>
      let val Invocation{phase,published,...}=owner
          val _=if !phase=Ready then phase:=Running else
            raise ERR "step" "invocation consumed or reentrant"
          val _=action owner(fn()=>
            (tick owner;if Option.isSome(Redblackmap.peek(!published,id))then
               ()else raise ERR "registry" "command is not published"))
          val entry=evaluate owner id
          val value={block=current owner,node= #node entry,edge= #edge entry}
          val _=phase:=Ready
      in value end))handle primary=>(W.close expected;raise primary))
  fun finish_with_policy expected owner=
    ((expected_owner expected owner;protect owner(fn()=>
      let val Invocation{work,graph,packet,remaining,phase,profiles,...}=owner
          val _=if !phase=Ready andalso null(!remaining)then phase:=Running
            else raise ERR "finish" "unfinished or consumed invocation"
          val result=action owner(fn()=>
            let val final=lookup owner(#root(Packet.proof packet))
                val _=case G.view graph(#node final)of G.Constant _=>
                    if Term.same_const(G.representative graph(#node final))
                        boolSyntax.F then ()else
                      raise ERR "finish" "actual final node is not false"
                  | _=>raise ERR "finish" "actual final node is not false"
                val block=current owner
                val plan=P.prepare_realization_with_policy work block
                  (#node final)(#edge final)
                val receipt=P.execute_realization_with_policy work plan
                val _=phase:=Completing
                val closure=P.prepare_source_close_with_policy work receipt
                  {profiles=profiles,check_type=policy owner}
            in P.execute_source_close_with_policy work closure end)
          val _=active owner val _=phase:=Complete
      in result end))handle primary=>(W.close expected;raise primary))
  fun prove_with_policy work native request=
    let val owner=begin_with_policy work native request
        fun loop()=case replay_next_with_policy work owner of
            SOME _=>loop()|NONE=>finish_with_policy work owner
    in loop()end
  fun prove_raw_with_policy work native request=
    let val owner=begin_raw_with_policy work native request
        fun loop()=case replay_next_with_policy work owner of
            SOME _=>loop()|NONE=>finish_with_policy work owner
    in loop()end
end
