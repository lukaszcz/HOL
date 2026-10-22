(* No rule registry or Source authority is reconstructed from Value shape. *)
structure Z3_OwnedValueNamedReplay :> Z3_OwnedValueNamedReplay =
struct
  structure W = SmtReplayInvocationWork
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure GP = SmtLib_GraphPreprocess
  structure PV = SmtLib_GraphParserValue
  structure VP = SmtLib_GraphValueProof
  structure Z = Z3_GraphProofParser
  structure R = Z3_Proof
  structure Plan = Z3_SharedReplayPlan
  structure P = SmtReplayOwnedValueProof
  structure NC = SmtReplayNativeContract
  structure RP = SmtReplayResourcePolicy
  structure Specialize = SmtReplayOwnedValueSpecialize
  structure Binder = SmtReplayOwnedValueBinder
  val ERR = Feedback.mk_HOL_ERR "Z3_OwnedValueNamedReplay"
  datatype requirement =
      CurrentSourceTransport of {index:int,node:G.node,value:PV.value}
    | OriginalSourceProgramme of {index:int,node:G.node,value:PV.value}
    | SourceOpening of G.scope * G.node
    | ScopedBinding of SmtLib_GraphFrontend.value_scoped_session
    | ResolutionProgramme of
        {target:PV.value,premises:Z.proof_id list,
         conclusion:SmtLib_GraphFrontend.value_term}
    | SpecializationProgramme of
        {source:PV.proof_term,instance:PV.proof_term,target:PV.proof_term,
         arguments:PV.proof_term list}
    | BinderAdmission of Binder.requirement
    | SpecializationAdmission of Specialize.requirement
  datatype operand = Operand of
    {term:PV.proof_term,endpoint:PV.value option}
  type entry = {node:PV.value,edge:P.edge}
  type current_source = {index:int,equality:PV.value option}
  type command =
    {id:Z.proof_id,target:PV.value,plan:(operand,PV.value) Plan.plan}
  datatype invocation = Invocation of
    {work:W.portfolio,active:bool ref,guard:unit -> unit,block:P.block,
     context:PV.context,remaining:command list ref,
     entries:(Z.proof_id,entry) Redblackmap.dict ref,
     sources:(int,current_source) Redblackmap.dict,
     clause_factory:SmtReplayValueClause.factory option,
     clause_sources:(Z.proof_id,SmtReplayValueClause.occurrences)
       Redblackmap.dict,
     clause_targets:(Z.proof_id,SmtReplayValueClause.occurrences)
       Redblackmap.dict,
     originals:(Z.proof_id,int) Redblackmap.dict option,
     original_ports:P.original_source_port vector option,
     raw_batches:(Z.proof_id,SmtReplayValueClause.raw_occurrences)
       Redblackmap.dict option,
     specializations:(Z.proof_id,PV.value * P.closed_law_port)
       Redblackmap.dict option,
     binder_laws:(Z.proof_id,P.binder_law_port) Redblackmap.dict option}
  datatype preparation = Prepared of invocation | Needs of requirement list
  datatype task = Visit of Z.proof_id | Finish of Z.proof_id
  fun protected work action=action ()
    handle primary=>(W.close work;raise primary)
  fun header expected (Invocation {work,...}) =
    if Portable.pointer_eq (expected,work) then () else
      raise ERR "owner" "different original Work"
  fun live expected (saved as Invocation {active,guard,block,...}) =
    (header expected saved;
     if !active then () else raise ERR "owner" "named receiver retired";
     guard ();P.validate_with_policy_for expected block)
  fun close (Invocation {active,block,...})=(active:=false;P.close block)
  fun compare_id pay (Z.Named a,Z.Named b)=
        (pay 1;Int.compare (a,b))
    | compare_id pay (Z.Anonymous a,Z.Anonymous b)=
        (pay 1;Int.compare (a,b))
    | compare_id pay (Z.Named _,Z.Anonymous _)=(pay 1;LESS)
    | compare_id pay (Z.Anonymous _,Z.Named _)=(pay 1;GREATER)
  fun actual_source work block sources node context =
    let
      val key=PV.key context node
      val {index,equality}=case Redblackmap.peek (sources,key) of
          SOME data=>data
        | NONE=>raise ERR "source" "missing genuine current Source port"
      val incoming=P.source work block (P.source_port_for work block index)
    in case equality of NONE=>incoming | SOME equation=>
      let
        (* The SAME checked congruence worker proves compact endpoint
           equality. Actual constructor exposure precedes Source EQ_MP;
           structural observation itself supplies no proof. *)
        val named=P.assemble_equality work block
          {rule="cong",target=equation,premises=[]}
        val endpoints=P.derive work block
          SmtReplayNamedContext.EqualityMP
          [P.constructor work block equation,named]
      in P.derive work block SmtReplayNamedContext.EqualityMP
        [endpoints,incoming] end
    end

  fun original_specializer retained=
    if retained then Specialize.prepare_retained else Specialize.prepare
  fun application_specializer _=Specialize.prepare_retained_application
  fun prepare_using_specializer specializer general
      quantified bindings retained allow_original
      specialization mode
      work query packet
      {assertions,native_contract,check_type} = protected work (fn()=>
    let
      val query_nodes=GP.query_nodes_with_policy_for work query
      val graph= #graph query_nodes val scope= #scope query_nodes
      val _=NC.validate_for work native_contract
      val planned=W.with_step work (fn()=>
        let
          (* Both Source modes fence the actual Work before packet
             activation; original indices never use current-query slots. *)
          val original_backing=if allow_original then
              SOME(W.original_sources work) else NONE
          val contents=VP.contents_with_policy_for work query packet
          val context= #context contents
          val proof= #proof contents
          val packet_guard=VP.prepare_scoped_guard_with_policy_for
            work query packet
          fun guard ()=
            (packet_guard ();NC.validate_for work native_contract)
          fun pay amount=(guard ();W.spend_policy work amount)
          fun tick ()=pay 1
          fun compare_int (a,b)=(tick ();Int.compare (a,b))
          fun copy_map action []=(guard ();[])
            | copy_map action (value::rest)=
                (tick ();action value::copy_map action rest)
          fun append [] tail=(guard ();tail)
            | append (value::rest) tail=(tick ();value::append rest tail)
          fun reverse values=
            let fun loop [] result=(guard ();result)
                  | loop (value::rest) result=
                      (tick ();loop rest (value::result))
            in loop values [] end
          fun string_work (left,right)=pay
            (1+IntInf.fromInt (String.size left)+
             IntInf.fromInt (String.size right))
          fun string_equal pair=(string_work pair;op = pair)
          val _=if string_equal (#solver contents,"Z3") andalso
              string_equal (#z3_version proof,#resolved (#versions contents))
            then () else raise ERR "owner" "actual packet/version differs"
          (* Copy by actual tree visitation, never call a payload-supplied
             dictionary comparator. The new dictionary has a private paid
             comparison and rejects duplicate actual command IDs. *)
          val steps=Redblackmap.foldl (fn (id,command,result)=>
            (pay 2;
             if Redblackmap.inDomain (result,id) then
               raise ERR "packet" "duplicate actual command ID"
             else Redblackmap.insert (result,id,command)))
            (Redblackmap.mkDict (compare_id pay)) (#steps proof)
          fun step id=(tick ();case Redblackmap.peek (steps,id) of
              SOME command=>command
            | NONE=>raise ERR "packet" "unknown proof ID")
          val pending=ref ([]:requirement list)
          fun need value=(tick ();pending:=value:: !pending)
          val marks=ref (Redblackmap.mkDict (compare_id pay))
          val order=ref ([]:Z.proof_id list)
          fun children (Z.Rule {rule,premises,accepts_bind,...})=
                if bindings andalso accepts_bind andalso
                    string_equal(#replay_handler rule,"quant_intro") then []
                else premises
            | children (Z.Alias id)=[id]
            | children (Z.Bind {binding,body,...})=
                (need (ScopedBinding binding);if bindings then []else[body])
          fun visits [] tail=(guard ();tail)
            | visits (id::rest) tail=(tick ();Visit id::visits rest tail)
          fun walk []=guard ()
            | walk (Finish id::rest)=
                (tick ();order:=id:: !order;
                 marks:=Redblackmap.insert (!marks,id,2);walk rest)
            | walk (Visit id::rest)=
                (tick ();case Redblackmap.peek (!marks,id) of
                    SOME 2=>walk rest
                  | SOME _=>raise ERR "packet" "cyclic proof commands"
                  | NONE=>
                      (marks:=Redblackmap.insert (!marks,id,1);
                       tick ();walk (visits (children (step id))
                         (Finish id::rest))))
          val _=tick ()
          val _=walk [Visit (#root proof)]
          val ordered=reverse (!order)
          val _=List.app (fn value=>
            (tick ();ignore (PV.key context value))) assertions
        in if not (null (!pending)) then
            (NONE,reverse (!pending),guard)
          else
          let
            val current=append (#assumptions query_nodes)
              [#denied query_nodes]
            val original=case original_backing of NONE=>
                append (S.assumption_nodes (W.original_sources work))
                  [S.denied_goal_node (W.original_sources work)]
              | SOME sources=>append (S.assumption_nodes sources)
                  [S.denied_goal_node sources]
            val endpoints=ref (Redblackmap.mkDict (compare_id pay))
            val binder_ids=if bindings then
                (pay 2;SOME(ref([]:Z.proof_id list)))else NONE
            val quantifiers=ref([]:(Z.proof_id *
              (PV.value * PV.value list * PV.value))list)
            val roots=ref ([]:operand list)
            val source_indices=ref (Redblackmap.mkDict compare_int)
            val original_state=if allow_original then
                (pay 4;SOME(ref ([]:(int * PV.value) list),ref 0,
                  ref(Redblackmap.mkDict (compare_id pay)))) else NONE
            fun reserve_original id index value=case original_state of
                NONE=>raise ERR "source" "original reservation disabled"
              | SOME(demands,count,indices)=>
                  (pay 5;demands:=(index,value):: !demands;
                   indices:=Redblackmap.insert (!indices,id,!count);
                   count:= !count+1)
            fun cursor (Operand {term,...})=term
            fun located (value:SmtLib_GraphFrontend.value_term)=
              let val _=tick () val node= #node value
                  val _=PV.usable context scope node
              in Operand {term=PV.proof_term context node,
                endpoint=SOME node} end
            val quant_endpoints=ref(Redblackmap.mkDict compare_int)
            fun recover value=
              let val _=tick()val key=PV.key context value
              in if Redblackmap.inDomain(!quant_endpoints,key)then()else
                (tick();quant_endpoints:=Redblackmap.insert
                  (!quant_endpoints,key,value);
                 case PV.view context value of
                   PV.Application(f,x)=>(pay 2;recover f;recover x)
                 | _=>())end
            fun origin (Operand {endpoint=SOME value,...})=
                  (tick ();PV.usable context scope value;value)
              | origin (Operand {term,...})=
                  (case specialization of NONE=>
                    (ignore(PV.proof_key context term);
                     raise ERR "packet" "not an actual parser endpoint")
                  | SOME _=>
                    let val wanted=PV.proof_key context term
                        fun seek []=raise ERR "packet"
                              "not an actual parser endpoint"
                          | seek((_,value)::rest)=
                              let val _=tick()
                                  val (a,b)=PV.proof_key context
                                    (PV.proof_term context value)
                                  val (c,d)=wanted
                              in if compare_int(a,c)=EQUAL andalso
                                  compare_int(b,d)=EQUAL then value
                                else seek rest end
                        (* Actual typed values only: no cursor-to-Value cast
                           or reconstruction of a retained binder. *)
                    in seek(Redblackmap.foldl(fn(k,v,rest)=>
                      (pay 2;(k,v)::rest))[](!quant_endpoints))end)
            fun prior id=(tick ();case Redblackmap.peek (!endpoints,id) of
                SOME node=>node
              | NONE=>raise ERR "packet" "unplanned premise")
            fun keep node=(tick ();roots:=node:: !roots)
            fun at values index=
              let fun find [] _=raise ERR "source" "Source slot disappeared"
                    | find (value::_) 0=(tick ();value)
                    | find (_::rest) n=(tick ();find rest (n-1))
              in find values index end
            fun compare_key ((a,b),(c,d))=
              (tick ();case Int.compare (a,c) of EQUAL=>
                 (tick ();Int.compare (b,d)) | order=>order)
            fun compare_pair ((a,b),(c,d))=
              case compare_key (a,c) of EQUAL=>compare_key (b,d)
                | order=>order
            (* Check only availability of this already supported App
               congruence programme, before any named native effect.
               Free/bound atoms need their exact authentic IDs. A new
               abstraction/opaque equality still needs its real binder
               programme and is retained as a requirement below. *)
            fun congruent_shape left right=
              let
                val seen=ref (Redblackset.empty compare_pair)
                fun walk []=(guard ();true)
                  | walk ((left,right)::rest)=
                    let
                      val _=tick ()
                      val keys=(PV.proof_key context left,
                        PV.proof_key context right)
                    in if compare_key keys=EQUAL then walk rest else
                      if Redblackset.member (!seen,keys) then walk rest else
                        (tick ();seen:=Redblackset.add (!seen,keys);
                         case (PV.proof_view context left,
                               PV.proof_view context right) of
                           (PV.ProofApplication (f,x),
                            PV.ProofApplication (g,y))=>
                              (pay 3;walk ((f,g)::(x,y)::rest))
                         | _=>false)
                    end
              in tick ();walk [(left,right)] end
            val equality_head=ref (NONE:PV.value option)
            fun boolean_equality ()=
              case !equality_head of SOME head=>
                  (tick ();ignore (PV.key context head);head)
              | NONE=>
                  let
                    (* One fixed declaration atom, never a query operand
                       or an expanded equality term. *)
                    val _=pay 6
                    val atom=Term.rator (Term.rator
                      (boolSyntax.mk_eq (boolSyntax.T,boolSyntax.T)))
                    val head=PV.literal context scope (RP.AtMost 1) atom
                    val _=tick () val _=equality_head:=SOME head
                  in head end
            fun equality_value source target=
              let val _=tick () val head=boolean_equality ()
                  val partial=PV.application context scope (head,source)
                  val result=PV.application context scope (partial,target)
                  val term=PV.proof_term context result
                  val _=keep (Operand {term=term,endpoint=SOME result})
              in result end
            fun supplied index operand=
              let val target=origin operand
                  fun assertion_at [] _=
                        raise ERR "source" "assertion count differs"
                    | assertion_at (value::rest) 0=(tick ();value)
                    | assertion_at (_::rest) n=
                        (tick ();assertion_at rest (n-1))
                  val value=assertion_at assertions index
                  val source=PV.proof_term context value
                  val same=compare_key
                    (PV.proof_key context source,
                     PV.proof_key context (cursor operand))=EQUAL
                  fun save equality=
                    (tick ();source_indices:=Redblackmap.insert
                      (!source_indices,PV.key context target,
                       {index=index,equality=equality}))
              in if same then save NONE else
                  if congruent_shape source (cursor operand) then
                    save (SOME (equality_value value target))
                  else need (CurrentSourceTransport
                    {index=index,node=at current index,value=target})
              end
            exception Opening of G.scope * G.node
            fun matching target candidates=
              let
                fun search [] _ missing=(case missing of
                    NONE=>NONE | SOME opening=>raise Opening opening)
                  | search (node::rest) index missing=
                      (tick ();case PV.corresponds_to_graph_with_policy
                          context graph scope
                            {value=origin target,node=node} of
                          PV.Corresponding=>SOME index
                        | PV.DifferentGraphSyntax=>
                            search rest (index+1) missing
                        | PV.NeedsGraphOpening opening=>
                            search rest (index+1) (SOME opening))
              in search candidates 0 NONE end
            fun processed target=case matching target current of
                NONE=>false | SOME index=>(supplied index target;true)
            fun original_slot target=case matching target original of
                NONE=>raise ERR "packet"
                  "hypothesis outside actual original Source prefix"
              | SOME index=>index
            fun operands constant arity node=
              let
                fun count [] total=(guard ();total)
                  | count (_::rest) total=(tick ();count rest (total+1))
                fun spine current arguments=
                  (tick ();case PV.proof_view context current of
                      PV.ProofApplication (operator,operand)=>
                        spine operator (operand::arguments)
                    | PV.ProofConstant atom=>
                        let val left=Term.dest_thy_const atom
                            val right=Term.dest_thy_const constant
                            val _=string_work (#Thy left,#Thy right)
                            val _=string_work (#Name left,#Name right)
                        in if Term.same_const atom constant andalso
                            count arguments 0=arity then
                              SOME (copy_map (fn term=>
                                Operand {term=term,endpoint=NONE}) arguments)
                          else NONE end
                    | _=>NONE)
              in spine (cursor node) [] end
            fun metadata_strings strings=
              List.app (fn text=>
                (tick ();pay (1+2*IntInf.fromInt (String.size text)))) strings
            fun metadata_rule (rule:R.proof_rule)=
              (pay 6;metadata_strings [#name rule,#replay_handler rule];
               metadata_strings (#aliases rule);
               case #version_support rule of R.AllZ3Versions=>tick ()
                 | R.Z3Versions values=>metadata_strings values
                 | R.Z3VersionPrefixes values=>metadata_strings values)
            val observer:Plan.observer =
              {registry={visit=tick,copy=tick,
                 string_comparison=string_work,prefix_comparison=string_work},
               rule_comparison=fn (a,b)=>(metadata_rule a;metadata_rule b),
               normalization_character=tick,
               premises=fn values=>List.app (fn _=>pay 2) values,
               argument_copy=tick,kept_item=tick,copied_roots=fn()=>pay 2}
            fun classify id=
              let val command=step id
                  val result=(SOME ((if bindings then
                      Plan.classify_with_bindings else Plan.classify)
                    {observer=observer,prior=prior,located=located,
                     processed=processed,original_slot=original_slot,
                     operands=operands,keep=keep,error=ERR}
                    {version= #z3_version proof,
                     mode=mode} command)
                    handle Opening opening=>
                      (need (SourceOpening opening);NONE))
                  val endpoint_operand=case result of
                      SOME (node,_)=>node
                    | NONE=>(case command of Z.Rule {conclusion,...}=>
                        located conclusion | Z.Alias other=>prior other
                      | Z.Bind _=>raise ERR "packet" "unexpected Bind")
                  val _=keep endpoint_operand
                  val target=origin endpoint_operand
                  val _=endpoints:=Redblackmap.insert
                    (!endpoints,id,endpoint_operand)
              in case result of NONE=>NONE | SOME (_,plan)=>
                (case plan of Plan.OriginalSlot (index,value)=>
                    ((if allow_original then
                        reserve_original id index (origin value)
                      else need (OriginalSourceProgramme
                        {index=index,node=at original index,
                         value=origin value}));
                     SOME {id=id,target=target,plan=plan})
                  | Plan.Resolution _=>
                      SOME {id=id,target=target,plan=plan}
                  | Plan.RawResolution (cursor,premises,conclusion)=>
                      ((case mode of Plan.RecordedResolution=>
                          need(ResolutionProgramme {target=origin cursor,
                            premises=premises,conclusion=conclusion})
                        | Plan.LegacyRawResolution=>());
                       SOME {id=id,target=target,plan=plan})
                  | Plan.ScopedEquality _=>
                      ((case binder_ids of SOME ids=>
                          (pay 2;ids:=id:: !ids)
                        | NONE=>raise ERR "quant_intro"
                            "scoped programme mode changed");
                       pay 4;SOME{id=id,target=target,plan=plan})
                  | Plan.Quantified {source,instance,target=quantified,
                                     arguments}=>
                      ((case specialization of NONE=>
                          need(SpecializationProgramme
                            {source=cursor source,instance=cursor instance,
                             target=cursor quantified,
                             arguments=copy_map cursor arguments})
                        | SOME _=>
                          (recover target;
                           List.app(fn Operand{endpoint,...}=>
                             (tick();case endpoint of
                               SOME value=>recover value|NONE=>()))arguments;
                           pay 3;quantifiers:=
                             (id,(origin source,copy_map origin arguments,
                               origin instance)):: !quantifiers));
                       SOME {id=id,target=target,plan=plan})
                  | _=>SOME {id=id,target=target,plan=plan}) end
            val commands=copy_map classify ordered
            fun present [] result=reverse result
              | present (NONE::rest) result=(tick ();present rest result)
              | present (SOME value::rest) result=
                  (tick ();present rest (value::result))
            val commands=present commands []
            (* Native receipts are produced only after all held Source
               prototypes have passed the SAME genuine correspondence.
               In particular an unused assertion cannot defer an opening
               until after SPEC has already run. *)
            fun preflight [] []=guard()
              | preflight(value::rest)(node::more)=
                  (tick();case PV.corresponds_to_graph_with_policy context
                      graph scope{value=value,node=node}of
                    PV.Corresponding=>preflight rest more
                  | PV.NeedsGraphOpening opening=>
                      (need(SourceOpening opening);preflight rest more)
                  | PV.DifferentGraphSyntax=>raise
                      Feedback.mk_HOL_ERR "SmtReplayOwnedValueProof"
                        "prepare"
                        "Value assertion differs from the actual query")
              | preflight _ _=raise
                  Feedback.mk_HOL_ERR "SmtReplayOwnedValueProof"
                    "prepare" "assertion count changed"
            fun original_preflight []=guard()
              | original_preflight((index,value)::rest)=
                  (tick();case PV.corresponds_to_graph_with_policy context
                      graph scope{value=value,node=at original index}of
                    PV.Corresponding=>original_preflight rest
                  | PV.NeedsGraphOpening opening=>
                      (need(SourceOpening opening);original_preflight rest)
                  | PV.DifferentGraphSyntax=>raise
                      Feedback.mk_HOL_ERR "SmtReplayOwnedValueProof"
                        "prepare"
                        "Value differs from the original Source occurrence")
            val _=case specialization of NONE=>()|SOME _=>
              (preflight assertions current;
               case original_state of NONE=>()|SOME(demands,_,_)=>
                 original_preflight(reverse(!demands)))
            val _=guard ()
            val clause_factory=ref(NONE:SmtReplayValueClause.factory option)
            val clause_sources=ref(Redblackmap.mkDict(compare_id pay))
            val clause_targets=ref(Redblackmap.mkDict(compare_id pay))
            val raw_batches=case mode of Plan.RecordedResolution=>NONE
              | Plan.LegacyRawResolution=>
                  (pay 3;SOME(ref(Redblackmap.mkDict(compare_id pay))))
            fun factory()=case !clause_factory of SOME saved=>
                  (tick();saved)
              | NONE=>let val saved=SmtReplayValueClause.create work query
                      packet
                    val _=tick()val _=clause_factory:=SOME saved
                  in saved end
            fun parsed id=
              (tick();case step id of Z.Rule{conclusion,...}=>conclusion
                | Z.Alias other=>parsed other
                | Z.Bind _=>raise ERR "unit_resolution"
                    "proof-bind requires its scoped programme")
            fun source_layout id=
              (tick();case Redblackmap.peek(!clause_sources,id)of
                  SOME saved=>saved
                | NONE=>let
                    val saved=SmtReplayValueClause.discover_recorded work
                      (factory())(parsed id)
                    val _=tick()
                    val _=clause_sources:=Redblackmap.insert
                      (!clause_sources,id,saved)
                  in saved end)
            fun clause_inputs []=guard()
              | clause_inputs(id::rest)=
                  (tick();ignore(source_layout id);clause_inputs rest)
            fun layouts []=guard()
              | layouts(({id,plan,...}:command)::rest)=
                  (tick();case plan of Plan.Resolution(_,ids,conclusion)=>
                    let val _=clause_inputs ids
                        val target=SmtReplayValueClause.discover_target work
                          (factory())conclusion
                        val _=tick()
                        val _=clause_targets:=Redblackmap.insert
                          (!clause_targets,id,target)
                    in layouts rest end
                  | Plan.RawResolution(_,ids,conclusion)=>
                    let val(head,units)=case ids of first::tail=>(first,tail)
                          | []=>raise ERR "unit_resolution"
                              "empty raw premises"
                        val batch=SmtReplayValueClause.discover_raw work
                          (factory()){head=parsed head,
                            units=copy_map parsed units,target=conclusion}
                        val _=pay 2
                        val _=case raw_batches of SOME batches=>
                            batches:=Redblackmap.insert(!batches,id,batch)
                          | NONE=>raise ERR "unit_resolution"
                              "raw discovery mode changed"
                    in layouts rest end
                  | _=>layouts rest)
          in if null (!pending) then
              let val _=layouts commands
              in
              (SOME (commands,copy_map origin (reverse (!roots)),
                 !source_indices,context,
                 (case original_state of NONE=>NONE
                   | SOME(demands,_,indices)=>
                       SOME(reverse(!demands),!indices)),
                 !clause_factory,!clause_sources,!clause_targets,
                 (case raw_batches of NONE=>NONE
                   | SOME held=>(pay 1;SOME(!held))),
                 (case specialization of NONE=>NONE
                   | SOME _=>SOME(reverse(!quantifiers))),
                 (case binder_ids of NONE=>NONE
                   | SOME ids=>(pay 1;SOME(reverse(!ids))))),
               [],guard)end
            else (NONE,reverse (!pending),guard) end
        end)
      val (data,pending,guard)=planned
    in if not (null pending) then Needs pending else
      case data of NONE=>raise ERR "prepare" "missing actual named plans"
      | SOME (commands,roots,sources,context,original_data,
              clause_factory,clause_sources,clause_targets,raw_batches,
              quantifiers,binder_ids)=>
        let
          fun paid action=W.with_step work(fn()=>
            (guard();W.spend_policy work 1;
             let val result=action()in guard();result end))
          fun prepare_quantifiers []=(paid(fn()=>());([],[]))
            | prepare_quantifiers((id,(source,arguments,target))::rest)=
              let val _=paid(fn()=>())
                  val profiles=case specialization of SOME held=>held
                    | NONE=>raise ERR "prepare" "missing actual profiles"
                  val current=(specializer retained)work query packet
                    {source=source,arguments=arguments,target=target,
                     profiles=profiles,native_contract=native_contract,
                     check_type=check_type}
                  val (ready,needs)=prepare_quantifiers rest
              in case current of Specialize.Prepared plan=>
                  (paid(fn()=>());((id,plan)::ready,needs))
                | Specialize.Needs missing=>
                    let fun copy []=needs
                          | copy(value::tail)=
                              (W.spend_policy work 2;
                               SpecializationAdmission value::copy tail)
                    in (ready,paid(fn()=>copy missing))end end
          val (quant_plans,quant_needs)=case quantifiers of NONE=>([],[])
            | SOME values=>prepare_quantifiers values
          fun prepare_binders []=(paid(fn()=>());([],[]))
            | prepare_binders(id::rest)=
                let val _=paid(fn()=>W.spend_policy work 4)
                    val current=(if quantified then Binder.prepare_quantified
                      else Binder.prepare)work query packet
                      {id=id,native_contract=native_contract,
                       check_type=check_type}
                    (* Only an ordinary metadata ChildProgramme decline
                       enters the general finite engine. Successful atomic
                       binders keep the identical plan/callback programme. *)
                    val current=case current of Binder.Prepared _=>current
                      | Binder.Needs missing=>if general then
                          let val eligible=paid(fn()=>
                                let val _=W.spend_policy work 2
                                    fun child []=false
                                      | child(Binder.ChildProgramme _::_)=
                                          (W.spend_policy work 1;true)
                                      | child(_::rest)=
                                          (W.spend_policy work 1;child rest)
                                in child missing end)
                          in if eligible then
                              Binder.prepare_general work query packet
                                {id=id,native_contract=native_contract,
                                 check_type=check_type}
                            else current end
                        else current
                    val (ready,needs)=prepare_binders rest
                in case current of Binder.Prepared plan=>
                    (paid(fn()=>W.spend_policy work 2);
                     ((id,plan)::ready,needs))
                  | Binder.Needs missing=>
                      let fun copy []=needs
                            | copy(value::tail)=
                                (W.spend_policy work 2;
                                 BinderAdmission value::copy tail)
                      in(ready,paid(fn()=>copy missing))end end
          val (binder_plans,binder_needs)=case binder_ids of NONE=>([],[])
            | SOME ids=>prepare_binders ids
          fun append_needs [] tail=tail
            | append_needs(value::rest)tail=
                (W.spend_policy work 2;value::append_needs rest tail)
          val all_needs=case binder_ids of NONE=>quant_needs
            | SOME _=>paid(fn()=>append_needs quant_needs binder_needs)
          fun execute []=(paid(fn()=>());[])
            | execute((id,plan)::rest)=
                let val _=paid(fn()=>())
                    val law=Specialize.execute work plan
                    val tail=execute rest
                    val _=paid(fn()=>())
                in (id,law)::tail end
          val closed=if null all_needs then
              (case quantifiers of NONE=>[]|SOME _=>execute quant_plans)
            else []
          fun execute_binders []=(paid(fn()=>());[])
            | execute_binders((id,plan)::rest)=
                let val _=paid(fn()=>())
                    val receipt=Binder.execute work plan
                    val tail=execute_binders rest
                    val _=paid(fn()=>W.spend_policy work 1)
                in(id,receipt)::tail end
          val closed_binders=if null all_needs then
              (case binder_ids of NONE=>[]
                | SOME _=>execute_binders binder_plans)else []
          fun binder_receipts []=[]
            | binder_receipts((_,receipt)::rest)=
                (W.spend_policy work 2;receipt::binder_receipts rest)
          fun closed_receipts []=[]
            | closed_receipts((_,receipt)::rest)=
                (W.spend_policy work 2;receipt::closed_receipts rest)
          fun original_demands()=case original_data of NONE=>[]
            | SOME(demands,_)=>demands
        in if not(null all_needs)then Needs all_needs else
          (case (if bindings then
              P.prepare_with_binder_laws work query packet
                {assertions=assertions,originals=original_demands(),
                 closed_laws=paid(fn()=>closed_receipts closed),
                 binder_laws=paid(fn()=>binder_receipts closed_binders),
                 roots=roots,native_contract=native_contract,
                 check_type=check_type}
            else case quantifiers of SOME _=>
              P.prepare_with_closed_laws work query packet
                {assertions=assertions,originals=original_demands(),
                 closed_laws=paid(fn()=>closed_receipts closed),roots=roots,
                 native_contract=native_contract,check_type=check_type}
            | NONE=>(case original_data of NONE=>P.prepare work query packet
                {assertions=assertions,roots=roots,
                 native_contract=native_contract,check_type=check_type}
              | SOME (demands,_)=>P.prepare_with_originals work query packet
                {assertions=assertions,originals=demands,roots=roots,
                 native_contract=native_contract,check_type=check_type})) of
              P.NeedsOpening openings=>Needs (W.with_step work (fn()=>
                let fun copy []=(guard ();[])
                      | copy (opening::rest)=
                          (guard ();W.spend_policy work 1;
                           SourceOpening opening::copy rest)
                in copy openings end))
            | P.Prepared block=>
                let
                  val held=case original_data of NONE=>NONE | SOME _=>
                    SOME(W.with_step work (fn()=>
                      let val ports=P.original_source_ports_for work block
                          fun quote []=P.validate_with_policy_for work block
                            | quote (_::rest)=
                                (P.validate_with_policy_for work block;
                                 W.spend_policy work 1;quote rest)
                          val _=quote ports
                      in Vector.fromList ports end))
                  val specialized=case quantifiers of NONE=>NONE|SOME _=>
                    SOME(paid(fn()=>
                      let val ports=P.closed_law_ports_for work block
                          fun join [] [] result=result
                            | join((id,receipt)::rest)(port::tail)result=
                              let val _=W.spend_policy work 3
                                  val data=Specialize.data_for work receipt
                              in join rest tail(Redblackmap.insert
                                (result,id,(#statement data,port)))end
                            | join _ _ _=raise ERR "prepare"
                                "closed specialization inventory changed"
                      in join closed ports(Redblackmap.mkDict(compare_id
                        (fn amount=>(guard();W.spend_policy work amount))))
                      end))
                  val bound=case binder_ids of NONE=>NONE | SOME _=>
                    SOME(paid(fn()=>
                      let val _=W.spend_policy work 4
                          val ports=P.binder_law_ports_for work block
                          fun join [] [] result=result
                            | join((id,_)::rest)(port::more)result=
                                (W.spend_policy work 3;
                                 join rest more(Redblackmap.insert
                                   (result,id,port)))
                            | join _ _ _=raise ERR "prepare"
                                "binder closed inventory changed"
                      in join closed_binders ports
                        (Redblackmap.mkDict(compare_id(fn amount=>
                          (guard ();W.spend_policy work amount))))end))
                in Prepared (Invocation
                  {work=work,active=ref true,guard=guard,
                   block=block,context=context,remaining=ref commands,
                   sources=sources,original_ports=held,
                   specializations=specialized,raw_batches=raw_batches,
                   binder_laws=bound,
                   clause_factory=clause_factory,
                   clause_sources=clause_sources,clause_targets=clause_targets,
                   originals=case original_data of NONE=>NONE
                     | SOME (_,indices)=>SOME indices,
                   entries=ref (Redblackmap.mkDict (compare_id
                     (fn amount=>(guard ();W.spend_policy work amount))))})
                end)
        end
    end)

  (* Existing callers keep pending original programmes. The new entry
     consumes only the privately validated ORIGINAL reservation vector. *)
  fun prepare_using quantified bindings retained allow_original
      specialization mode work query packet options=
    prepare_using_specializer original_specializer quantified
      quantified bindings retained allow_original specialization mode
      work query packet options

  fun prepare_with_policy work query packet options=
    prepare_using false false false false NONE Plan.RecordedResolution
      work query packet options
  fun prepare_with_original_sources_with_policy work query packet options=
    prepare_using false false false true NONE Plan.RecordedResolution
      work query packet options

  (* Owning phases: classify all rules; prepare every bounded programme;
     execute closed laws; then freeze the SAME named receiver. No native
     specialization prefix precedes a later pending programme. *)
  fun prepare_with_specialization_with_policy work query packet
      {assertions,native_contract,profiles,check_type}=
    prepare_using false false false true (SOME profiles)
      Plan.RecordedResolution
      work query packet
      {assertions=assertions,native_contract=native_contract,
       check_type=check_type}

  (* Raw compatibility opts into the SAME legacy registry mode and its
     selectively prepared fallbacks. It never changes recorded boundaries
     or supplies a new propositional solver. *)
  fun prepare_with_raw_resolution_with_policy work query packet
      {assertions,native_contract,profiles,check_type}=
    prepare_using false false false true (SOME profiles)
      Plan.LegacyRawResolution
      work query packet {assertions=assertions,
        native_contract=native_contract,check_type=check_type}

  (* Explicit general bounded retained inputs, SAME actual classifier,
     CLOSED reservation and shared specialization/Boolean programme. *)
  fun prepare_with_retained_specialization_with_policy work query packet
      {assertions,native_contract,profiles,check_type}=
    prepare_using false false true true (SOME profiles) Plan.RecordedResolution
      work query packet {assertions=assertions,
        native_contract=native_contract,check_type=check_type}

  fun prepare_with_binders_with_policy work query packet
      {assertions,native_contract,profiles,check_type}=
    prepare_using false true true true (SOME profiles) Plan.RecordedResolution
      work query packet {assertions=assertions,
        native_contract=native_contract,check_type=check_type}

  (* All three opt-in capabilities share the actual registry, whole
     invocation preflight and existing receipt/Source admission workers. *)
  fun prepare_with_owned_programmes_with_policy work query packet
      {assertions,native_contract,profiles,check_type}=
    prepare_using_specializer application_specializer true
      false true true true (SOME profiles) Plan.LegacyRawResolution
      work query packet {assertions=assertions,
        native_contract=native_contract,check_type=check_type}

  (* Explicit quantified identity prefixes, still the same canonical
     quant-intro classifier and whole-invocation metadata/Needs split. *)
  fun prepare_with_quantified_binders_with_policy work query packet
      {assertions,native_contract,profiles,check_type}=
    prepare_using true true true true (SOME profiles) Plan.RecordedResolution
      work query packet {assertions=assertions,
        native_contract=native_contract,check_type=check_type}

  fun step_pay expected (saved as Invocation{work,...}) amount=
    (live expected saved;W.spend_policy work amount)
  fun step_lookup expected (saved as Invocation{entries,...}) id=
    (step_pay expected saved 1;case Redblackmap.peek(!entries,id)of
       SOME entry=>entry
     | NONE=>raise ERR "registry" "premise not completed")
  fun step_inputs expected saved []=[]
    | step_inputs expected saved(id::rest)=
        let val _=step_pay expected saved 1
            val entry=step_lookup expected saved id
        in (#node entry,#edge entry)::step_inputs expected saved rest end
  (* Static specialization: all callbacks are module functions, not a
     fresh operations record or copied proof context on each command. *)
  structure StepInput =
  struct
    type expected=W.portfolio
    type context=invocation
    type command=command
    type node=operand
    type syntax=PV.value
    type edge=P.edge
    fun original expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) value=
      actual_source work block sources target context
    fun original_slot expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) _=
      (case (originals,original_ports) of
                    (SOME indices,SOME ports)=>
                      let val _=step_pay expected saved 1
                          val position=case Redblackmap.peek(indices,id) of
                              SOME slot=>slot | NONE=>raise ERR "source"
                                "missing original reservation"
                          val _=step_pay expected saved 1
                          val port=Vector.sub(ports,position)
                      in P.original_source work block port end
                  | _=>raise ERR "source" "original programme unfinished")
    fun alias expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) other=
      #edge (step_lookup expected saved other)
    fun equality expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) (rule,_,ids)=
      P.assemble_equality work block
                  {rule=rule,target=target,premises=
                    step_inputs expected saved ids}
    fun boolean expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) (_,ids)=
      P.assemble_boolean work block
                  {target=target,premises=
                    step_inputs expected saved ids}
    fun scoped_equality expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) _=
      (case binder_laws of NONE=>raise ERR "quant_intro"
                      "scoped programme unfinished"
                    | SOME laws=>
                        let val _=step_pay expected saved 1
                            val port=case Redblackmap.peek(laws,id)of
                                SOME actual=>actual
                              | NONE=>raise ERR "quant_intro"
                                  "missing genuine closed binder"
                        in P.binder_law_source work block port end)
    fun quantified expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) _=
      (case specializations of NONE=>raise ERR "quant-inst"
                      "specialization programme unfinished"
                    | SOME laws=>
                      let val _=step_pay expected saved 1
                          val (statement,port)=case Redblackmap.peek(laws,id)
                            of SOME held=>held|NONE=>raise ERR "quant-inst"
                              "missing genuine closed specialization"
                          val law=P.closed_law_source work block port
                      in P.assemble_boolean work block
                        {target=target,premises=[(statement,law)]}end)
    fun raw_resolution expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) (_,ids,_)=
      let val factory=case clause_factory of SOME held=>held
                        | NONE=>raise ERR "unit_resolution"
                            "missing actual raw clause factory"
                      val batch=case raw_batches of SOME batches=>
                          (step_pay expected saved 1;
                           case Redblackmap.peek(batches,id)of
                            SOME held=>held|NONE=>raise ERR "unit_resolution"
                              "missing actual raw occurrence batch")
                        | NONE=>raise ERR "unit_resolution"
                            "raw programme unfinished"
                      fun completed []=(live expected saved;[])
                        | completed(input::rest)=
                            (step_pay expected saved 2;
                             #edge(step_lookup expected saved input)::
                               completed rest)
                      val plan=P.prepare_raw_unit_resolution work block
                        {factory=factory,batch=batch,premises=completed ids}
                  in P.execute_raw_unit_resolution work plan end
    fun resolution expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) (_,ids,_)=
      let
                    val factory=case clause_factory of SOME saved=>saved
                      | NONE=>raise ERR "unit_resolution"
                          "missing actual clause factory"
                    val _=step_pay expected saved 1
                    val wanted=case Redblackmap.peek(clause_targets,id)of
                        SOME saved=>saved
                      | NONE=>raise ERR "unit_resolution"
                          "missing actual target occurrences"
                    fun completed []=(live expected saved;[])
                      | completed(input::rest)=
                          let val _=step_pay expected saved 1
                              val entry=step_lookup expected saved input
                              val layout=case Redblackmap.peek
                                  (clause_sources,input)of SOME value=>value
                                | NONE=>raise ERR "unit_resolution"
                                    "missing actual premise occurrences"
                          in (layout,#edge entry)::completed rest end
                    val prepared=P.prepare_unit_resolution work block
                      {factory=factory,premises=completed ids,target=wanted}
                  in P.execute_unit_resolution work prepared end
    fun unfinished expected (saved as Invocation
          {work,block,context,remaining,entries,sources,originals,
           original_ports,specializations,clause_factory,clause_sources,
           clause_targets,raw_batches,binder_laws,...})
        ({id,target,plan}:command) ()=
      raise ERR "registry" "unfinished programme in named queue"
  end
  structure Step=Z3_NamedReplayStepFn(StepInput)

  (* Passive opt-in observations only. Audit never activates an owner;
     printing failure must not replace the proof operation's Primary. *)
  fun command_phase expected label ({id,plan,...}:command) =
    ((if OS.Process.getEnv "HOL4_HOLSMT_REPLAY_DIAGNOSTICS"<>SOME "1"
      then ()else
      let val identity=case id of Z.Named n=>"named:"^Int.toString n
            | Z.Anonymous n=>"anonymous:"^Int.toString n
          val kind=case plan of
              Plan.Original _=>"original"
            | Plan.OriginalSlot _=>"original-slot"
            | Plan.Alias _=>"alias"
            | Plan.Equality(rule,_,_)=>"equality:"^rule
            | Plan.Boolean _=>"boolean"
            | Plan.ScopedEquality _=>"scoped-equality"
            | Plan.Quantified _=>"quantified"
            | Plan.RawResolution _=>"raw-resolution"
            | Plan.Resolution _=>"resolution"
          val audit=W.audit_policy expected
          val counts=Count.thm_count()
      in TextIO.output(TextIO.stdErr,
        "VALUE_REPLAY_COMMAND phase="^label^" id="^identity^
        " kind="^kind^" charged="^IntInf.toString(#charged audit)^
        " retired="^Bool.toString(#retired audit)^
        " ABS="^Int.toString(#ABS counts)^
        " AP_TERM="^Int.toString(#AP_TERM counts)^
        " INST="^Int.toString(#INST counts)^"\n");
        TextIO.flushOut TextIO.stdErr
      end)handle _=>())

  fun replay_next_with_policy expected saved = protected expected (fn()=>
    (header expected saved;W.with_step expected (fn()=>
      let val _=live expected saved
          val Invocation
            {work,block,context,remaining,entries,sources,
             originals,original_ports,specializations,clause_factory,
             clause_sources,clause_targets,raw_batches,binder_laws,...}=saved
      in case !remaining of []=>(live expected saved;NONE)
        | (current as {id,target,plan}:command)::rest=>
          let
            val _=command_phase expected "execute.before" current
            val edge=Step.execute expected saved current plan
              handle primary=>
                (command_phase expected "execute.failed" current;
                 raise primary)
            val _=command_phase expected "execute.after" current
            val theorem=P.compact_theorem_for work block edge
            val wanted=P.name work block target
            val _=step_pay expected saved 1
            val _=if Portable.pointer_eq (Thm.concl theorem,wanted) then ()
              else raise ERR "registry" "named endpoint differs"
            val _=entries:=Redblackmap.insert (!entries,id,
              {node=target,edge=edge})
            val _=step_pay expected saved 1 val _=remaining:=rest
            val _=command_phase expected "completion.before" current
            val _=live expected saved
            val _=command_phase expected "completion.after" current
          in SOME {id=id,node=target} end
      end)))
  fun step_with_policy_for expected saved id = protected expected (fn()=>
    (header expected saved;W.with_step expected (fn()=>
      let val _=live expected saved
          val Invocation {block,entries,...}=saved
          val _=W.spend_policy expected 1
          val entry=case Redblackmap.peek (!entries,id) of SOME entry=>entry
            | NONE=>raise ERR "registry" "command not completed"
          val _=ignore (P.compact_theorem_for expected block (#edge entry))
          val _=live expected saved
      in {block=block,node= #node entry,edge= #edge entry} end)))
end
