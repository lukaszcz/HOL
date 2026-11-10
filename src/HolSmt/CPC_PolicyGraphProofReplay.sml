(* Fixed policy programmes over genuine packet and Source owners. *)
structure CPC_PolicyGraphProofReplay :> CPC_PolicyGraphProofReplay =
struct
  structure W=SmtReplayInvocationWork
  structure NC=SmtReplayNativeContract
  structure G=SmtReplayGraph
  structure S=SmtReplaySource
  structure Scope=SmtReplayOwnedScopeReceipt
  structure P=SmtReplayProof
  structure GP=SmtLib_GraphPreprocess
  structure Packet=SmtLib_GraphProof
  structure Q=CPC_ProofParser
  structure R=SmtReplayRules
  val _=SmtReplayRules.boolean_graph_with_policy
  structure Native=CPC_ProofReplay.PolicyNative
  val _=CPC_ProofReplay.PolicyNative.prepare_specialize_with_policy
  val _=SmtReplayProof.constructor_with_policy
  val _=SmtReplayProof.initial_scope_layout_with_policy_for
  val _=SmtReplayProof.capture_scope_snapshot_with_policy
  val _=SmtReplayProof.prepare_scope_replay_batch_with_policy
  val _=SmtReplayProof.prepare_local_specialize_with_policy
  val _=SmtReplayProof.prepare_inferred_local_specialize_with_policy
  val _=SmtLib_GraphPreprocess.assembler_with_policy
  val ERR=Feedback.mk_HOL_ERR "CPC_PolicyGraphProofReplay"
  type request=
    {packet:Q.graph_proof Packet.packet,preprocessing:GP.validation,
     profiles:G.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,ordinal:int}
  datatype phase=Ready|Running|Completing|Complete|Retired
  datatype conjunction_boundary=MissingBoundary|RecoveredBoundary
    | ParsedBoundary of
        G.node SmtLib_Parser.construction_occurrence
    | IntroducedBoundary of (G.node*conjunction_boundary)list
  datatype recipe=Original of G.node|Local of int * G.node
    | Specialized of
        {source:recipe,target:G.node,law:P.closed_fact}
    | DoubleNegationEliminated of
        {source:G.node,premise:recipe,middle:G.node,target:G.node,
         boundary:conjunction_boundary}
    | AndEliminated of {source:G.node,premise:recipe,target:G.node,
        path:(G.node*bool)list,boundary:conjunction_boundary}
    | AndIntroduced of {premises:(G.node*recipe)list,
        joins:G.node list}
    | EqResolved of {first:recipe,second:recipe,
        first_node:G.node,second_node:G.node,target:G.node,
        equality_first:bool,reverse:bool}
    | Scoped of {snapshot:P.policy_scope_snapshot,
        selected:P.policy_scope_slot list,output:int}
  type entry={serial:int,id:string,node:G.node,recipe:recipe,
    boundary:conjunction_boundary}
  datatype invocation=Invocation of
    {work:W.portfolio,native:NC.contract,graph:G.graph,root:G.scope,
     sources:S.sources,frame:Scope.receipt,preprocessing:GP.validation,
     packet:Q.graph_proof Packet.packet,worker:Native.owner,
     profiles:G.policy_opaque_profile list,check_type:Type.hol_type -> unit,
     phase:phase ref,cursor:int ref,remaining:Q.graph_command list ref,
     known:entry list ref,stack:(entry list * int) list ref,
     extras:(int * G.node * P.policy_scope_slot)list ref,
     facts:P.closed_fact list ref,
     block:P.block option ref,layout:P.policy_scope_layout option ref,
     scoped_edges:(P.policy_scope_snapshot *
       (G.node * P.edge)list)list ref,
     roots:G.node list ref,ordinal:int ref,
     edges:(recipe * P.edge) list ref,last:entry option ref,
     epoch:int,symbols:int}
  fun retire(Invocation{phase,work,...})=(phase:=Retired;W.close work)
  fun protect owner action=action()handle primary=>
    (retire owner;raise primary)
  fun header expected(Invocation{work,...})=
    if Portable.pointer_eq(expected,work)then ()else
      raise ERR "owner" "different original Work"
  fun active(Invocation{work,native,graph,root,sources,frame,
      preprocessing,packet,phase,block,epoch,symbols,...})=
    (if !phase=Retired then raise ERR "owner" "invocation retired"else ();
     NC.validate_for work native;
     let val data=Scope.description_with_policy_for work frame
     in if Portable.pointer_eq(#graph data,graph)andalso #scope data=root
         andalso Portable.pointer_eq(#sources data,sources)andalso
         Portable.pointer_eq(Packet.graph packet,graph)andalso
         Packet.scope packet=root andalso Type.type_epoch()=epoch andalso
         Term.term_epoch()=symbols then ()else
       raise ERR "owner" "actual invocation association changed"end;
     GP.validate_with_policy work preprocessing;
     if Portable.pointer_eq(GP.original_sources preprocessing,sources)andalso
         GP.source_nodes preprocessing=S.assumption_nodes sources @
           [S.denied_goal_node sources]then ()else
       raise ERR "owner" "original Source prefix changed";
     case !phase of Completing=>()|Complete=>()
       | _=>Option.app(P.validate_block_for work)(!block))
  fun expected_owner expected owner=
    ((header expected owner;active owner)
     handle primary=>(W.close expected;raise primary))
  fun policy(owner as Invocation{check_type,...})ty=
    (active owner;check_type ty;active owner)
  fun action(owner as Invocation{work,...})operation=
    W.with_step work(fn()=>
      (active owner;let val answer=operation()val _=active owner
       in answer end))
  fun tick(owner as Invocation{work,...})=
    (active owner;W.spend_policy work 1)
  fun current(owner as Invocation{block,work,...})=
    (active owner;case !block of SOME saved=>
       (P.validate_block_for work saved;saved)
     | NONE=>raise ERR "block" "missing actual current Block")
  fun lookup owner wanted []=
        raise ERR "registry"("unknown visible command "^wanted)
    | lookup owner wanted((entry:entry)::rest)=
        (tick owner;if #id entry=wanted then entry
         else lookup owner wanted rest)
  fun add_root owner node roots=
    if List.exists(fn held=>(tick owner;held=node))roots then roots
    else node::roots
  (* These helpers belong only to the actual opaque E invocation. They
     never adopt a caller-supplied result, serial map or successor Block. *)
  fun current_layout(owner as Invocation{layout,...})=
    (active owner;case !layout of SOME value=>value
     | NONE=>raise ERR "layout" "missing actual current Source layout")
  fun scoped_result(owner as Invocation{scoped_edges,...})snapshot output=
    let val _=active owner
        fun find []=raise ERR "scope" "snapshot was not batched for this Block"
          | find((held,targets)::rest)=
              (tick owner;if Portable.pointer_eq(snapshot,held)then
                if output>=0 andalso output<List.length targets then
                  List.nth(targets,output)else
                    raise ERR "scope" "actual snapshot output absent"
               else find rest)
    in action owner(fn()=>find(!scoped_edges))end
  fun scope_recipes owner recipes=
    let val seen=ref([]:recipe list)
        val found=ref([]:recipe list)
        fun visit recipe=
          (tick owner;if List.exists(fn old=>
              (tick owner;Portable.pointer_eq(old,recipe)))(!seen)then ()else
            (case recipe of Specialized{source,...}=>visit source
              | DoubleNegationEliminated{premise,...}=>
                  visit premise
              | AndEliminated{premise,...}=>visit premise
              | AndIntroduced{premises,...}=>
                  List.app(fn(_,held)=>visit held)premises
              | EqResolved{first,second,...}=>
                  (visit first;visit second)
              | Scoped _=>found:=recipe:: !found|_=>();
             seen:=recipe:: !seen))
        val _=List.app visit recipes
    in List.rev(!found)end

  (* Recipes retain proof sharing without carrying stale Block edges into
     a new Context. All memo hits first validate the actual current Block. *)
  fun evaluate(owner as Invocation{work,graph,root,sources,preprocessing,
      extras,edges,...})recipe=
    let val block=current owner
        fun find []=NONE|find((held,edge)::rest)=
          (tick owner;if Portable.pointer_eq(held,recipe)then SOME edge
           else find rest)
        val saved=action owner(fn()=>(tick owner;find(!edges)))
        fun boolean opcode premises=P.execute_boolean_primitive_with_policy
          work(P.prepare_boolean_primitive_with_policy
            work block opcode premises)
        fun fixed opcode premises=P.execute_primitive_with_policy work
          (P.prepare_primitive_with_policy work block opcode premises)
        fun local_source serial node=
          let val prefix=S.assumption_nodes sources @
                [S.denied_goal_node sources]
              val rows= !extras
              val actual=P.scope_layout_sources_with_policy_for work
                (current_layout owner)
              val _=if P.sources block=prefix @
                  List.map(fn(_,node,_)=>node)rows then ()else
                raise ERR "registry" "actual local Source order differs"
              fun seek _ []=raise ERR "registry" "local occurrence absent"
                | seek index((held,current,token)::rest)=
                    (tick owner;if serial=held andalso node=current then
                      if P.same_scope_slot_with_policy_for work token
                          (#2(List.nth(actual,index)))then
                        P.source block index else
                          raise ERR "registry" "actual local origin differs"
                     else seek(index+1)rest)
          in seek(List.length prefix)rows end
    in case saved of SOME edge=>edge|NONE=>
      let
        val edge=case recipe of
            Original node=>
              (* The genuine GP factory and its returned query EACH own a
                 separate Work action. Neither is called inside action(). *)
              let val _=active owner
                  val assemble=GP.assembler_with_policy work
                    preprocessing block
                  val _=active owner
                  val answer=assemble node
                  val _=active owner
              in case answer of SOME edge=>edge
                | NONE=>raise ERR "registry"
                    "original/processed assertion has no genuine assembler"
              end
          | Local(serial,node)=>action owner(fn()=>local_source serial node)
          | Scoped{snapshot,output,...}=>
              #2(scoped_result owner snapshot output)
          | DoubleNegationEliminated{source,premise,target,...}=>
              let val incoming=evaluate owner premise
              in action owner(fn()=>
                let
                  val _=P.validate_block_for work block
                  fun endpoint node edge=
                    if Portable.pointer_eq(Thm.concl(P.theorem block edge),
                        P.name block node)then ()else
                      raise ERR "not_not_elim"
                        "incorrect actual named endpoint"
                  val _=endpoint source incoming
                  val result=R.boolean_graph_with_policy work block
                    {root=target,premises=[(source,incoming)]}
                  val _=endpoint target result
                in result end)end
          | AndEliminated{source,premise,target,path,...}=>
              let val incoming=evaluate owner premise
              in action owner(fn()=>
                let
                  val _=P.validate_block_for work block
                  fun endpoint node edge=
                    if Portable.pointer_eq(Thm.concl(P.theorem block edge),
                        P.name block node)then ()else
                      raise ERR "and_elim" "incorrect actual premise edge"
                  val _=endpoint source incoming
                  fun follow proof []=proof
                    | follow proof((node,take_left)::rest)=
                        let val _=endpoint node proof
                            val constructor=P.constructor_with_policy
                              work block node
                            val exposed=fixed P.EqualityMP[constructor,proof]
                            val selected=boolean
                              (if take_left then P.PolicyConjunctLeft
                               else P.PolicyConjunctRight)[exposed]
                        in follow selected rest end
                  val result=follow incoming path
                  val _=endpoint target result
                in result end)end
          | AndIntroduced{premises,joins}=>
              let
                (* Keep ordered command occurrences, including duplicates.
                   GP factories and queries own their separate actions. *)
                val inputs=List.map(fn(node,recipe)=>
                  (node,evaluate owner recipe))premises
              in action owner(fn()=>
                let
                  val _=P.validate_block_for work block
                  fun endpoint node edge=
                    if Portable.pointer_eq(Thm.concl(P.theorem block edge),
                        P.name block node)then ()else
                      raise ERR "and_intro" "incorrect actual premise edge"
                  val _=List.app(fn(node,edge)=>endpoint node edge)inputs
                  fun build [(_,edge)] []=edge
                    | build((_,left)::rest)(target::targets)=
                        let val right=build rest targets
                            val joined=boolean P.PolicyConjunction[left,right]
                            val constructor=P.constructor_with_policy
                              work block target
                            val reverse=fixed P.Symmetry[constructor]
                            val result=fixed P.EqualityMP[reverse,joined]
                            val _=endpoint target result
                        in result end
                    | build _ _=raise ERR "and_intro"
                        "private ordered conjunction shape changed"
                in build inputs joins end)end
          | EqResolved{first,second,first_node,second_node,target,
              equality_first,reverse}=>
              let
                (* Resolve immutable packet premises in recorded order.
                   GP factories/queries own their actions outside ours. *)
                val a=evaluate owner first val b=evaluate owner second
              in action owner(fn()=>
                let
                  val _=P.validate_block_for work block
                  fun endpoint node edge=
                    if Portable.pointer_eq(Thm.concl(P.theorem block edge),
                        P.name block node)then ()else
                      raise ERR "eq_resolve" "incorrect actual premise edge"
                  val _=endpoint first_node a val _=endpoint second_node b
                  val(equality_node,equality,proposition)=
                    if equality_first then(first_node,a,b)
                    else(second_node,b,a)
                  val constructor=P.constructor_with_policy
                    work block equality_node
                  val exposed=fixed P.EqualityMP[constructor,equality]
                  val oriented=if reverse then fixed P.Symmetry[exposed]
                    else exposed
                  val result=fixed P.EqualityMP[oriented,proposition]
                  val _=endpoint target result
                in result end)end
          | Specialized{source,target,law}=>
              let val premise=evaluate owner source
              in action owner(fn()=>
                let val _=P.validate_block_for work block
                    val law_edge=P.closed block law
                    val shell=P.constructor_with_policy work block
                      (P.closed_node law)
                    val implication=fixed P.EqualityMP[shell,law_edge]
                    val answer=boolean P.PolicyImplicationMP
                      [implication,premise]
                    val _=if Portable.pointer_eq
                        (Thm.concl(P.theorem block answer),P.name block target)
                      then ()else raise ERR "registry"
                        "fixed local law did not prove actual target name"
                in answer end)end
        val _=action owner(fn()=>
          (P.validate_block_for work block;edges:=(recipe,edge):: !edges))
      in edge end
    end
  (* Called outside receiver-owned actions. P prepare/execute each own
     their real Work action. They validate the old published Block through
     every callback/rule, and retire it only after genuine next outputs. *)
  fun replay_scopes(owner as Invocation{work,known,extras,block,layout,
      scoped_edges,edges,ordinal,...})additional=
    let
      val recipes=action owner(fn()=>scope_recipes owner
        (additional @ List.map(fn(entry:entry)=> #recipe entry)(!known)))
      fun data(Scoped value)=value
        | data _=raise ERR "scope" "not an actual scoped recipe"
    in if List.null recipes then ()else
      let
        val selected=List.concat(List.map(fn recipe=> #selected(data recipe))
          recipes)
        (* Compute this while the old owner is live. No origin getter,
           backing guard or callback lies in the final publish handoff. *)
        val continued=action owner(fn()=>List.filter
          (fn(_,_,slot)=>not(List.exists(fn selected=>
            (tick owner;P.same_scope_slot_with_policy_for work slot selected))
            selected))(!extras))
        val number=action owner(fn()=>
          let val value= !ordinal val _=ordinal:=value+1 in value end)
        val plan=P.prepare_scope_replay_batch_with_policy work
          (current_layout owner)
          {snapshots=List.map(fn recipe=> #snapshot(data recipe))recipes,
           ordinal=number,check_type=policy owner}
        val actual=P.execute_scope_replay_batch_with_policy work plan
        (* Real P has now consumed old. These are immediate DATA writes;
           active(), GP factories and all other actions follow publication. *)
        val _=block:=SOME(#block actual)
        val _=layout:=SOME(#layout actual)
        val _=extras:=continued
        val _=edges:=[]
        val _=scoped_edges:=List.map(fn{snapshot,targets}=>
          (snapshot,targets))(#outputs actual)
        val _=active owner
      in ()end
    end

  (* A metadata publication keeps exact producer-issued occurrence tokens.
     Only an actual parsed push supplies an append request here. *)
  fun rebuild(owner as Invocation{work,native,frame,preprocessing,extras,
      facts,block,layout,roots,ordinal,profiles,edges,scoped_edges,...})append=
    let
      val _=active owner
      val number=action owner(fn()=>
        let val value= !ordinal val _=ordinal:=value+1 in value end)
      val combined=action owner(fn()=>
        let fun prepend []=GP.roots preprocessing
              | prepend(node::rest)=
                  (W.spend_policy work 2;node::prepend rest)
        in prepend(!roots)end)
      val(next,next_layout,new_tokens)=case !layout of NONE=>
          let
            val _=if List.null(!extras)andalso List.null append then ()else
              raise ERR "layout" "initial owner cannot adopt local origins"
            val actual=
              P.prepare_scoped_original_realization_frontier_with_policy
                work{frame=frame,roots=combined,additional_sources=[],
                  closed_facts= !facts @ GP.closed_facts preprocessing,
                  conversions=GP.conversions preprocessing}
            val next=action owner(fn()=>
              let val tables=P.prepare_owned_realization_tables_with_policy
                    work actual
                  val plan=P.prepare_native_realization_freeze_with_policy
                    work{tables=tables,contract=native,profiles=profiles,
                      ordinal=number,check_type=policy owner}
              in P.freeze_owned_realization_tables_with_policy work plan end)
            val saved=P.initial_scope_layout_with_policy_for work next
          in(next,saved,[])end
        | SOME saved=>
          let val actual=P.rebuild_scope_layout_with_policy work saved
                {append=List.map #2 append,roots=combined,
                 closed_facts= !facts @ GP.closed_facts preprocessing,
                 conversions=GP.conversions preprocessing,ordinal=number,
                 check_type=policy owner}
          in(#block actual,#layout actual,#appended actual)end
      val _=if List.length append=List.length new_tokens then ()else
        raise ERR "layout" "actual append token count differs"
      val appended=ListPair.mapEq(fn((serial,node),token)=>
        (serial,node,token))(append,new_tokens)
      val _=action owner(fn()=>
        (Option.app(P.retire_policy_block_for work)(!block);
         block:=SOME next;layout:=SOME next_layout;
         extras:= !extras @ appended;edges:=[];scoped_edges:=[]))
      val _=replay_scopes owner []
    in active owner end
  fun begin_with_policy work native
      ({packet,preprocessing,profiles,check_type,ordinal}:request)=
    ((let
        val _=NC.validate_for work native
        val _=if ordinal>=0 then ()else
          raise ERR "begin" "negative first native ordinal"
        val sources=W.original_sources work
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val frame=Scope.root_with_policy work
        val worker=Native.begin_with_policy work native
          {packet=packet,preprocessing=preprocessing,
           profiles=profiles,check_type=check_type}
        val owner=Invocation{work=work,native=native,graph=graph,root=root,
          sources=sources,frame=frame,preprocessing=preprocessing,
          packet=packet,worker=worker,profiles=profiles,check_type=check_type,
          phase=ref Ready,cursor=ref 0,
          remaining=ref(#commands(Packet.proof packet)),known=ref[],
          stack=ref[],extras=ref[],facts=ref[],block=ref NONE,
          layout=ref NONE,scoped_edges=ref[],
          roots=ref[],ordinal=ref ordinal,edges=ref[],last=ref NONE,
          epoch=Type.type_epoch(),symbols=Term.term_epoch()}
        val _=active owner
        val _=rebuild owner []
      in owner end)handle primary=>(W.close work;raise primary))
  fun replay_next_with_policy expected owner=
    ((expected_owner expected owner;protect owner(fn()=>
      let
        val Invocation{work,graph,root,sources,preprocessing,worker,phase,
          cursor,remaining,known,stack,extras,facts,roots,last,
          profiles,...}=owner
        val _=if !phase=Ready then phase:=Running else
          raise ERR "next" "invocation consumed or reentrant"
      in case !remaining of []=>(phase:=Ready;NONE)|command::tail=>
        let
          val serial= !cursor
          fun located(value:SmtLib_GraphFrontend.term)=
            (G.validate_scope graph(#scope value);
             if #scope value=root andalso G.scope_visible graph root
                 (G.node_scope graph(#node value))then #node value else
               raise ERR "next" "non-root declaration needs scoped handler")
          fun save id node recipe=
            let val _=if List.exists(fn(entry:entry)=>
                  #id entry=id)(!known)then
                  raise ERR "next" "duplicate visible command ID"else ()
                (* Conjunction boundaries come from this actual producing
                   packet occurrence or the genuine ordered proof recipe.
                   A semantic node ID alone cannot invent n-ary arity. *)
                val boundary=action owner(fn()=>
                  case command of Q.GraphAssume(_,value)=>
                      ParsedBoundary(#occurrence value)
                    | Q.GraphAssumePush(_,value)=>
                        ParsedBoundary(#occurrence value)
                    | Q.GraphStep{step,...}=>(case recipe of
                        AndIntroduced{premises,...}=>
                          let
                            val actual=List.map(fn id=>
                              lookup owner id(!known))(#premises step)
                            fun joined((node,_),(held:entry))=
                              if node= #node held then(node,#boundary held)
                              else raise ERR "and_boundary"
                                "different ordered producing premise"
                            val children=ListPair.mapEq joined
                              (premises,actual)
                          in case children of [(_,child)]=>child
                            | _=>IntroducedBoundary children end
                      | DoubleNegationEliminated{boundary,...}=>
                          boundary
                      | AndEliminated{boundary,...}=>boundary
                      | _=>MissingBoundary))
                val result={serial=serial,id=id,node=node,recipe=recipe,
                  boundary=boundary}:entry
                val _=known:=result:: !known val _=last:=SOME result
            in {serial=serial,id=id,node=node}end
          val answer=case command of Q.GraphAssume(id,value)=>
              let val node=located value
                  val _=if List.exists(fn held=>held=node)
                      (GP.processed_assumptions preprocessing @
                        [GP.processed_denied_goal preprocessing] @
                        S.assumption_nodes sources @
                        [S.denied_goal_node sources])then ()else
                    raise ERR "next" "assertion outside actual Source prefix"
                  val _=action owner(fn()=>
                    roots:=add_root owner node(!roots))
                  val _=rebuild owner []
                  val recipe=Original node
                  val _=ignore(evaluate owner recipe)
              in save id node recipe end
            | Q.GraphAssumePush(id,value)=>
              let val node=located value
                  val _=stack:=(!known,List.length(!extras)):: !stack
                  val _=action owner(fn()=>
                    roots:=add_root owner node(!roots))
                  val _=rebuild owner[(serial,node)]
                  val recipe=Local(serial,node)
                  val _=ignore(evaluate owner recipe)
              in save id node recipe end
            | Q.GraphStep{step,pop=true}=>
              let
                val _=if #replay_handler(#rule step)="scope"then ()else
                  raise ERR "scope" "pop needs actual registered scope rule"
                val _=if List.null(#args step)then ()else
                  raise ERR "scope" "scope argument programme pending"
                val(outer,offset)=case !stack of saved::_=>saved
                  | []=>raise ERR "scope" "pop without actual push"
                val premise=case #premises step of [id]=>
                      action owner(fn()=>lookup owner id(!known))
                  | _=>raise ERR "scope" "pop needs one visible body premise"
                val rows= !extras
                val _=if List.length rows=offset+1 then ()else
                  raise ERR "scope" "actual nested local occurrence differs"
                val(_,hypothesis,slot)=List.nth(rows,offset)
                val declared=Option.map located(#conclusion step)
                (* Refuse a foreign/non-Boolean declared endpoint before
                   any capture callback or native DISCH. The derived G
                   shell is metadata only; P's real output remains the
                   authoritative inferred target and is checked below. *)
                val _=action owner(fn()=>
                  case declared of NONE=>()|SOME node=>
                    if Type.compare(G.type_of graph node,Type.bool)=EQUAL
                    then ()else raise ERR "scope"
                      "recorded pop target is not Boolean")
                val _=case declared of NONE=>()|SOME declared=>
                  action owner(fn()=>
                    let
                      val _=if Type.compare
                          (G.type_of graph hypothesis,Type.bool)=EQUAL andalso
                          Type.compare(G.type_of graph(#node premise),
                            Type.bool)=EQUAL then ()else
                        raise ERR "scope" "actual scope operands not Boolean"
                      val _=tick owner val _=W.spend_policy work 1
                      val head=G.constant graph root boolSyntax.implication
                      val _=tick owner val _=W.spend_policy work 1
                      val partial=G.application graph root(head,hypothesis)
                      val _=tick owner val _=W.spend_policy work 1
                      val actual=G.application graph root
                        (partial,#node premise)
                    in if actual=declared then ()else
                      raise ERR "scope" "recorded pop target differs"end)
                val index=action owner(fn()=>
                  let
                    val slots=P.scope_layout_sources_with_policy_for work
                      (current_layout owner)
                    fun seek [] _=raise ERR "scope" "push occurrence absent"
                      | seek((_,held)::rest)index=
                          (tick owner;
                           if P.same_scope_slot_with_policy_for work slot held
                           then index else seek rest(index+1))
                  in seek slots 0 end)
                val edge=evaluate owner(#recipe premise)
                val snapshot=P.capture_scope_snapshot_with_policy work
                  (current_layout owner){indices=[index],
                    outputs=[{body= #node premise,edge=edge}],
                    check_type=policy owner}
                val recipe=Scoped
                  {snapshot=snapshot,selected=[slot],output=0}
                (* Closed snapshot encapsulates the popped proof. Inner
                   IDs disappear before collecting outer visible recipes. *)
                val _=known:=outer val _=stack:=tl(!stack)
                val _=replay_scopes owner [recipe]
                val(target,_)=scoped_result owner snapshot 0
                val _=case declared of NONE=>()
                  | SOME node=>if node=target then ()else
                      raise ERR "scope" "recorded pop target differs"
                val _=action owner(fn()=>
                  roots:=add_root owner target(!roots))
                val _=ignore(evaluate owner recipe)
              in save(#id step)target recipe end
            | Q.GraphStep{step,pop=false}=>
              if #replay_handler(#rule step)="not_not_elim"then
              let
                (* The legacy rule ignores its argument list. Only the
                   actual single premise and optional result are semantic. *)
                val premise=case #premises step of [id]=>
                      action owner(fn()=>lookup owner id(!known))
                  | _=>raise ERR "not_not_elim"
                      "expected one visible premise"
                val declared=Option.map located(#conclusion step)
                val(target,middle,heads,boundary)=action owner(fn()=>
                  let
                    fun fail text=raise ERR "not_not_elim" text
                    fun boolean node=
                      (tick owner;
                       if G.scope_visible graph root(G.node_scope graph node)
                           andalso Type.compare(G.type_of graph node,
                             Type.bool)=EQUAL then ()else
                         fail "actual endpoint not visible Boolean")
                    fun negate node=
                      (boolean node;case G.view graph node of
                         G.Application(head,body)=>
                           (tick owner;
                            case G.view graph head of G.Constant _=>
                              if Term.same_const
                                  (G.representative graph head)
                                  boolSyntax.negation then
                                (boolean body;(head,body))else
                                  fail "expected actual double negation"
                            | _=>fail "expected actual double negation")
                       | _=>fail "expected actual double negation")
                    val(outer,middle)=negate(#node premise)
                    val(inner,target)=negate middle
                    val _=case declared of NONE=>()|SOME node=>
                      (boolean node;if node=target then ()else
                        fail "declared target differs from double negation")
                    (* Preserve only real parsed NOT children. A semantic
                       alias cannot invent a nested n-ary operand boundary. *)
                    fun peel node child(ParsedBoundary held)=
                          let
                            fun walk(held as
                                SmtLib_Parser.ConstructionOccurrence
                                  {role,token,children,...})=
                              (tick owner;
                               if SmtLib_Parser.construction_value held=node
                               then ()else fail
                                 "parsed negation names another node";
                               case role of
                                 SmtLib_Parser.ConstructionApplication=>
                                   (case children of [body]=>
                                      if token="not"andalso
                                          SmtLib_Parser.construction_value
                                            body=child then
                                        ParsedBoundary body
                                      else MissingBoundary
                                    | _=>MissingBoundary)
                               | SmtLib_Parser.ConstructionLet _=>
                                   (case List.rev children of body::_=>
                                      walk body|_=>MissingBoundary)
                               | SmtLib_Parser.ConstructionAnnotation=>
                                   (case children of [body]=>walk body
                                     | _=>MissingBoundary)
                               | _=>MissingBoundary)
                          in walk held end
                      | peel _ _ _=MissingBoundary
                    val inner_boundary=peel(#node premise)middle
                      (#boundary premise)
                    val boundary=peel middle target inner_boundary
                  in(target,middle,[outer,inner],boundary)end)
                val recipe=DoubleNegationEliminated
                  {source= #node premise,premise= #recipe premise,
                   middle=middle,target=target,boundary=boundary}
                (* R inspects these exact NOT definitions and their actual
                   operator ports. Demand them before any cold assembly;
                   semantic conversion cuts must not erase the obligation. *)
                val _=action owner(fn()=>
                  List.app(fn node=>roots:=add_root owner node(!roots))
                    (#node premise::middle::target::heads))
                val _=rebuild owner []
                val _=ignore(evaluate owner recipe)
              in save(#id step)target recipe end
              else
              if #replay_handler(#rule step)="and_elim"then
              let
                val target=case #conclusion step of SOME value=>located value
                  | NONE=>raise ERR "and_elim"
                      "inferred projection needs actual result producer"
                val index=case #args step of [Q.GraphIndex index]=>
                      if index>=0 then index else raise ERR "and_elim"
                        "negative actual conjunction index"
                  | _=>raise ERR "and_elim" "expected one recorded index"
                val premise=case #premises step of [id]=>
                      action owner(fn()=>lookup owner id(!known))
                  | _=>raise ERR "and_elim" "expected one visible premise"
                val(path,boundary)=action owner(fn()=>
                  let
                    fun fail text=raise ERR "and_elim" text
                    fun boolean node=
                      (tick owner;if Type.compare(G.type_of graph node,
                          Type.bool)=EQUAL then ()else
                        fail "actual endpoint not Boolean")
                    fun split node=
                      (boolean node;case G.view graph node of
                         G.Application(part,right)=>
                           (case G.view graph part of
                              G.Application(head,left)=>
                                (case G.view graph head of G.Constant _=>
                                   if Term.same_const
                                       (G.representative graph head)
                                       boolSyntax.conjunction then
                                     (boolean left;boolean right;
                                      SOME(left,right))else NONE
                                 | _=>NONE)
                            | _=>NONE)
                       | _=>NONE)
                    fun pair node=case split node of SOME value=>value
                      | NONE=>fail "actual conjunction spine missing"
                    fun parsed node(held as
                        SmtLib_Parser.ConstructionOccurrence
                          {role,token,children,...})=
                      (tick owner;
                       if SmtLib_Parser.construction_value held=node then ()
                       else fail "parsed boundary names another actual node";
                       case role of
                         SmtLib_Parser.ConstructionApplication=>
                           if token="and"andalso List.length children>=2
                           then SOME(List.map(fn child=>
                             (SmtLib_Parser.construction_value child,
                              ParsedBoundary child))children)else NONE
                       | SmtLib_Parser.ConstructionLet _=>
                           (case List.rev children of body::_=>
                              parsed node body|[]=>NONE)
                       | SmtLib_Parser.ConstructionAnnotation=>
                           (case children of [body]=>parsed node body
                             | _=>NONE)
                       | _=>NONE)
                    fun recovered node=
                      let val(left,right)=pair node
                          fun rest current=case split current of
                              SOME(a,b)=>(a,RecoveredBoundary)::rest b
                            | NONE=>[(current,RecoveredBoundary)]
                      in (left,RecoveredBoundary)::rest right end
                    val rows=case #boundary premise of
                        IntroducedBoundary rows=>rows
                      | ParsedBoundary held=>(case parsed(#node premise)held of
                          SOME rows=>rows|NONE=>recovered(#node premise))
                      | RecoveredBoundary=>recovered(#node premise)
                      | MissingBoundary=>fail
                          "premise conjunction boundary has not been retained"
                    (* Validate ALL recorded immediate boundaries. A nested
                       right AND stays one operand when arity says so. *)
                    fun validate node [(last,_)]=
                          (boolean last;if node=last then ()else
                            fail "recorded conjunction boundary changed")
                      | validate node((first,_)::rest)=
                          let val(left,right)=pair node
                          in if left=first then validate right rest else
                            fail "recorded conjunction boundary changed"end
                      | validate _ []=fail "empty conjunction boundary"
                    val _=if List.length rows>=2 then ()else
                      fail "recorded conjunction arity below two"
                    val _=validate(#node premise)rows
                    val _=if index<List.length rows then ()else
                      fail "conjunction index outside boundary"
                    fun select node [(last,boundary)] 0=
                          if node=last then(last,[],boundary)else
                            fail "selected boundary changed"
                      | select node((first,boundary)::rest) selected=
                          let val(left,right)=pair node
                          in if selected=0 then
                              (first,[(node,true)],boundary)
                            else let val(answer,path,held)=
                                  select right rest(selected-1)
                              in(answer,(node,false)::path,held)end end
                      | select _ _ _=fail "conjunction index outside boundary"
                    val _=boolean target
                    val(answer,path,boundary)=
                      select(#node premise)rows index
                    val _=if answer=target then ()else
                      fail "declared target differs from indexed boundary"
                  in(path,boundary)end)
                val recipe=AndEliminated{source= #node premise,
                  premise= #recipe premise,target=target,path=path,
                  boundary=boundary}
                val _=action owner(fn()=>
                  List.app(fn node=>roots:=add_root owner node(!roots))
                    (target::List.map #1 path))
                val _=rebuild owner []
                val _=ignore(evaluate owner recipe)
              in save(#id step)target recipe end
              else
              if #replay_handler(#rule step)="and_intro"then
              let
                val target=case #conclusion step of SOME value=>located value
                  | NONE=>raise ERR "and_intro"
                      "inferred conjunction needs actual result producer"
                val _=if null(#args step)then ()else
                  raise ERR "and_intro" "unexpected introduction arguments"
                val premises=action owner(fn()=>
                  List.map(fn id=>lookup owner id(!known))(#premises step))
                val _=if null premises then raise ERR "and_intro"
                  "expected nonempty ordered premises"else()
                (* The target's actual right-associated AND ports must
                   agree with every ordered premise before cold evaluation,
                   refreeze callbacks or any native proof programme. *)
                val joins=action owner(fn()=>
                  let
                    fun boolean node=
                      (tick owner;if Type.compare(G.type_of graph node,
                          Type.bool)=EQUAL then ()else
                        raise ERR "and_intro" "actual endpoint not Boolean")
                    fun mismatch()=raise ERR "and_intro"
                      "target is not the ordered conjunction of premises"
                    fun walk node [last:entry]=
                          (boolean node;if node= #node last then []else
                            mismatch())
                      | walk node((first:entry)::rest)=
                          let
                            val _=boolean node
                            val(part,right)=case G.view graph node of
                                G.Application pair=>pair|_=>mismatch()
                            val(head,left)=case G.view graph part of
                                G.Application pair=>pair|_=>mismatch()
                            val _=tick owner
                            val _=case G.view graph head of G.Constant _=>
                                if Term.same_const
                                    (G.representative graph head)
                                    boolSyntax.conjunction then ()else
                                  mismatch()
                              | _=>mismatch()
                            val _=if left= #node first then ()else mismatch()
                          in node::walk right rest end
                      | walk _ []=mismatch()
                    val _=List.app(fn(row:entry)=>boolean(#node row))premises
                  in walk target premises end)
                val recipe=AndIntroduced{premises=List.map(fn(row:entry)=>
                  (#node row,#recipe row))premises,joins=joins}
                val _=action owner(fn()=>
                  List.app(fn node=>roots:=add_root owner node(!roots))
                    (target::joins))
                val _=rebuild owner []
                val _=ignore(evaluate owner recipe)
              in save(#id step)target recipe end
              else
              if #replay_handler(#rule step)="eq_resolve"then
              let
                val target=case #conclusion step of SOME value=>located value
                  | NONE=>raise ERR "eq_resolve"
                      "inferred equality side needs actual result producer"
                val _=if List.null(#args step)then ()else
                  raise ERR "eq_resolve" "unexpected equality rule arguments"
                val(first,second)=case #premises step of [a,b]=>
                      action owner(fn()=>
                        (lookup owner a(!known),lookup owner b(!known)))
                  | _=>raise ERR "eq_resolve" "expected two ordered premises"
                (* Immutable real graph ports are checked before evaluating
                   either potentially cold premise, callbacks or refreeze.
                   No original Term equality/body opening is performed. *)
                val(equality_first,reverse)=action owner(fn()=>
                  let
                    fun boolean node=
                      (tick owner;if Type.compare(G.type_of graph node,
                          Type.bool)=EQUAL then ()else
                        raise ERR "eq_resolve"
                          "actual endpoint is not Boolean")
                    fun sides node=
                      (tick owner;case G.view graph node of
                         G.Application(part,right)=>
                           (case G.view graph part of
                              G.Application(operator,left)=>
                                (case G.view graph operator of G.Constant _=>
                                   if Term.same_const
                                       (G.representative graph operator)
                                       boolSyntax.equality then
                                     (boolean left;boolean right;
                                      SOME(left,right))else NONE
                                 | _=>NONE)
                            | _=>NONE)
                       | _=>NONE)
                    fun candidate equality proposition=
                      case sides(#node(equality:entry))of NONE=>NONE
                        | SOME(left,right)=>
                            if left= #node(proposition:entry)andalso
                                right=target then SOME false
                            else if right= #node proposition andalso
                                left=target then SOME true else NONE
                    val _=List.app boolean
                      [target,#node first,#node second]
                  in case candidate second first of SOME reverse=>
                       (false,reverse)
                     | NONE=>(case candidate first second of SOME reverse=>
                         (true,reverse)
                       | NONE=>raise ERR "eq_resolve"
                           "target is not the actual Boolean equality side")
                  end)
                val recipe=EqResolved{first= #recipe first,
                  second= #recipe second,first_node= #node first,
                  second_node= #node second,target=target,
                  equality_first=equality_first,reverse=reverse}
                val _=action owner(fn()=>
                  roots:=add_root owner target(!roots))
                val _=rebuild owner []
                val _=ignore(evaluate owner recipe)
              in save(#id step)target recipe end
              else
              let
                val _=if #replay_handler(#rule step)="instantiate"then ()else
                  raise ERR "next"
                    "native handler programme has not been migrated"
                val premise=case #premises step of [id]=>
                      action owner(fn()=>lookup owner id(!known))
                  | _=>raise ERR "next" "instantiate needs one premise"
                val declared=Option.map located(#conclusion step)
                fun argument(Q.GraphTerm value)=located value
                  | argument _=raise ERR "next"
                      "instantiate requires actual ordered term arguments"
                val arguments=List.map argument(#args step)
                val edge=evaluate owner(#recipe premise)
                val actual=current owner
                (* A missing declaration is resolved ONLY by the actual
                   admitted substitution producer, never a receiver map. *)
                val law=action owner(fn()=>
                  let
                    val input={node= #node premise,edge=edge}
                    val prepared=case declared of SOME target=>
                        P.prepare_local_specialize_with_policy
                          work actual{premise=input,arguments=arguments,
                            target=target,profiles=profiles,
                            check_type=policy owner}
                      | NONE=>P.prepare_inferred_local_specialize_with_policy
                          work actual{premise=input,arguments=arguments,
                            profiles=profiles,check_type=policy owner}
                  in P.execute_local_specialize_with_policy work prepared end)
                val target=action owner(fn()=>
                  let
                    val law_node=P.closed_node law
                    val(head,target)=case G.view graph law_node of
                        G.Application pair=>pair
                      | _=>raise ERR "next" "actual local law lacks target"
                    val(operator,source)=case G.view graph head of
                        G.Application pair=>pair
                      | _=>raise ERR "next" "actual local law lacks source"
                    val _=if source= #node premise andalso
                        Term.same_const(G.representative graph operator)
                          boolSyntax.implication then ()else
                      raise ERR "next" "actual local law premise differs"
                    val _=case declared of NONE=>()|SOME node=>
                      if node=target then ()else
                        raise ERR "next" "actual local law target differs"
                  in target end)
                val _=action owner(fn()=>
                  (facts:=law:: !facts;
                   roots:=add_root owner(P.closed_node law)
                     (add_root owner target(!roots))))
                val _=rebuild owner []
                val recipe=Specialized{source= #recipe premise,
                  target=target,law=law}
                val _=ignore(evaluate owner recipe)
              in save(#id step)target recipe end
          val _=remaining:=tail val _=cursor:=serial+1
          val _=active owner val _=phase:=Ready
        in SOME answer end
      end))handle primary=>(W.close expected;raise primary))
  fun step_with_policy_for expected owner id=
    ((expected_owner expected owner;protect owner(fn()=>
      let val Invocation{known,phase,...}=owner
          val _=if !phase=Ready then ()else
            raise ERR "step" "invocation consumed or reentrant"
          val _=phase:=Running
          val entry=action owner(fn()=>lookup owner id(!known))
          val edge=evaluate owner(#recipe entry)
          val answer={block=current owner,node= #node entry,edge=edge}
          val _=phase:=Ready
      in answer end))handle primary=>(W.close expected;raise primary))
  fun finish_with_policy expected owner=
    ((expected_owner expected owner;protect owner(fn()=>
      let val Invocation{work,graph,sources,phase,remaining,stack,last,
                profiles,...}=owner
          val _=if !phase=Ready andalso List.null(!remaining)andalso
              List.null(!stack)then phase:=Running else
            raise ERR "finish" "unfinished, scoped or consumed invocation"
          val final=case !last of SOME value=>value
            | NONE=>raise ERR "finish" "empty certificate"
          val _=case G.view graph(#node final)of G.Constant _=>
              if Term.same_const(G.representative graph(#node final))
                  boolSyntax.F then ()else
                raise ERR "finish" "last actual node is not false"
            | _=>raise ERR "finish" "last actual node is not false"
          val edge=evaluate owner(#recipe final)
          val theorem=action owner(fn()=>
            let val block=current owner
                val plan=P.prepare_realization_with_policy work block
                  (#node final)edge
                val receipt=P.execute_realization_with_policy work plan
                (* No waiver precedes the executor: current Block liveness
                   remains checked through preparation and native work.
                   The genuine receipt now retains the consumed owner;
                   final Source operations require their own native plan. *)
                val _=phase:=Completing
                val closure=P.prepare_source_close_with_policy work receipt
                  {profiles=profiles,check_type=policy owner}
            in P.execute_source_close_with_policy work closure end)
          val _=S.check_goal sources theorem val _=phase:=Complete
      in theorem end))handle primary=>(W.close expected;raise primary))
  fun prove_with_policy work native request=
    let val owner=begin_with_policy work native request
        fun loop()=case replay_next_with_policy work owner of
            NONE=>finish_with_policy work owner|SOME _=>loop()
    in loop()end
end
