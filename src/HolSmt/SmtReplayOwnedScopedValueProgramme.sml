structure SmtReplayOwnedScopedValueProgramme :>
    SmtReplayOwnedScopedValueProgramme =
struct
  structure W=SmtReplayInvocationWork
  structure G=SmtReplayGraph
  structure C=SmtReplayOwnedScopedValueContext
  structure S=SmtReplayOwnedScopedValueSyntax
  structure PV=SmtLib_GraphParserValue
  structure VP=SmtLib_GraphValueProof
  structure NC=SmtReplayNativeContract
  structure Q=SmtReplayScopedNativeQueue
  structure N=SmtReplayNamedContext
  structure Z=Z3_GraphProofParser
  structure V=Z3_GraphValueProofParser
  structure Clause=SmtReplayValueClause
  structure O=SmtReplayRuleObservation
  structure RP=SmtReplayResourcePolicy
  val ERR=Feedback.mk_HOL_ERR "SmtReplayOwnedScopedValueProgramme"
  fun native_error message=ERR "native" message
  type node=PV.proof_term
  type state={work:W.portfolio,captured:C.context,syntax:S.plan,
    values:PV.context,key:node -> int,name:node -> Term.term,
    view:node -> node N.view,native:NC.limits,
    queue:Q.queue,definitions:(int,int)Redblackmap.dict,
    assumptions:Term.term list,seeds:Q.proof vector,
    proofs:(Z.proof_id,Q.proof)Redblackmap.dict ref,
    statements:(Z.proof_id,node)Redblackmap.dict ref,
    parsed:V.proof,factory:Clause.factory,
    occurrences:(Z.proof_id,Clause.occurrences)Redblackmap.dict ref}
  type closing={substitution:(Term.term,Term.term)Lib.subst,
    contexts:Term.term list,witnesses:Term.term list,
    type_ports:Type.hol_type list,all_type_ports:Type.hol_type list,
    body:SmtReplayGraph.node,
    target:Term.term}
  datatype plan=Plan of {state:state,proof:Q.proof,closing:closing,
    used:bool ref}
  datatype closed_child=ClosedChild of
    {state:state,closing:closing,theorem:Thm.thm}
  datatype requirement=NativeOpening of node
  datatype preparation=Prepared of plan | Needs of requirement list
  fun guard expected(state:state)=
    (if Portable.pointer_eq(expected,#work state)then ()else
       raise ERR "guard" "different original Work";
     ignore(C.data_for expected(#captured state)))
  fun pay expected state amount=
    (guard expected state;W.spend_policy expected amount)
  fun compare_id pay(Z.Named a,Z.Named b)=
        (pay 1;Int.compare(a,b))
    | compare_id pay(Z.Anonymous a,Z.Anonymous b)=
        (pay 1;Int.compare(a,b))
    | compare_id pay(Z.Named _,Z.Anonymous _)=(pay 1;LESS)
    | compare_id pay(Z.Anonymous _,Z.Named _)=(pay 1;GREATER)
  fun copy expected state action []=(guard expected state;[])
    | copy expected state action(x::rest)=
        (pay expected state 2;action x::copy expected state action rest)
  fun key expected state node=
    (guard expected state;(#key state)node)
  fun name expected state node=
    (guard expected state;(#name state)node)
  fun same expected state(a,b)=
    (pay expected state 1;Int.compare(key expected state a,
      key expected state b)=EQUAL)
  fun view expected state node=
    (pay expected state 2;(#view state)node)
  fun application expected state node=case view expected state node of
      N.Application pair=>SOME pair | _=>NONE
  fun constant expected state node=case view expected state node of
      N.Constant atom=>atom
    | _=>raise ERR "constant" "actual node is not a constant"
  fun type_of expected state node=
    (guard expected state;PV.proof_type_of(#values state)node)
  fun type_weight expected state ty=
    let val _=guard expected state
        val native= #native state
    in N.type_weight_using(pay expected state)native_error
      (IntInf.fromInt(#type_work_limit native))ty end
  fun definition expected(state:state)node=
    let val _=guard expected state
        val _=pay expected state 1
    in case Redblackmap.peek(#definitions state,key expected state node)of
        SOME slot=>Vector.sub(#seeds state,slot)
      | NONE=>raise ERR "definition" "missing actual constructor slot"end
  fun recipe expected state(N.ReflexiveName node)=
        N.ReflexiveName(name expected state node)
    | recipe _ _ N.Symmetry=N.Symmetry
    | recipe _ _ N.Transitivity=N.Transitivity
    | recipe _ _ N.Congruence=N.Congruence
    | recipe _ _ N.EqualityMP=N.EqualityMP
    | recipe expected state(N.ApplyNamedArgument node)=
        N.ApplyNamedArgument(name expected state node)
    | recipe _ _ N.ImplicationMP=N.ImplicationMP
  fun derive expected state opcode proofs=
    (guard expected state;
     Q.fixed(#queue state)(recipe expected state opcode)proofs)
  fun constructor expected state node=
    (pay expected state 4;
     N.constructor_using(guard expected)(view expected state)
       (definition expected)(derive expected)state node)
  fun edge expected(state:state)id=
    (pay expected state 1;case Redblackmap.peek(!(#proofs state),id)of
        SOME value=>value
      | NONE=>raise ERR "edge" "missing earlier genuine child proof")
  fun statement expected(state:state)id=
    (pay expected state 1;case Redblackmap.peek(!(#statements state),id)of
        SOME value=>value
      | NONE=>raise ERR "statement" "missing actual earlier endpoint")
  fun premises expected state ids=
    (pay expected state 1;
     copy expected state(fn id=>(pay expected state 1;
       (statement expected state id,edge expected state id)))ids)
  fun equality expected state _ (rule,target,ids)=
    let val _=pay expected state 22
    in Q.assemble_equality(#queue state)
      {key=key expected state,same=same expected state,
       name=name expected state,
       equality=N.equality(view expected state),
       application=application expected state,
       constructor=constructor expected state,
       definition=definition expected state,error=ERR "equality"}
      {rule=rule,target=target,premises=premises expected state ids}end
  fun boolean expected state _ (target,ids)=
    let val _=pay expected state 21
    in Q.assemble_boolean(#queue state)
      {native= #native state,type_weight=type_weight expected state,
       type_of=type_of expected state,view=view expected state,
       constant=constant expected state,same=same expected state,
       name=name expected state,constructor=constructor expected state,
       error=ERR "boolean"}
      {root=target,premises=premises expected state ids}end
  fun alias expected state _ id=edge expected state id
  fun no_source expected state _ _=
    (guard expected state;
     raise ERR "child" "a captured source-free queue gained a Source")
  fun no_nested expected state _ _=
    (guard expected state;
     raise ERR "child" "unadmitted nested child programme")
  fun parsed expected(state:state)wanted=
    let val _=pay expected state 1
        val found=Redblackmap.foldl(fn(id,value,result)=>
          (pay expected state 1;case result of SOME _=>result | NONE=>
            if compare_id(pay expected state)(wanted,id)=EQUAL then
              (pay expected state 1;SOME value)else NONE))
          NONE(#steps(#parsed state))
    in case found of SOME(Z.Rule{conclusion,...})=>conclusion
      | SOME(Z.Alias other)=>parsed expected state other
      | _=>raise ERR "recorded" "not an actual child Rule occurrence"end
  fun occurrence expected(state:state)id=
    (pay expected state 1;
     case Redblackmap.peek(!(#occurrences state),id)of
         SOME value=>value
       | NONE=>let val saved=Clause.discover_recorded expected
                     (#factory state)(parsed expected state id)
                   val _=pay expected state 1
                   val _= #occurrences state:=Redblackmap.insert
                     (!(#occurrences state),id,saved)
               in saved end)
  fun recorded expected state _ (_,ids,conclusion)=
    let
      val _=guard expected state
      val target=Clause.discover_target expected(#factory state)conclusion
      val target=Clause.data_for expected(#factory state)target
      val actual=copy expected state(fn id=>
        let val row=Clause.data_for expected(#factory state)
              (occurrence expected state id)
            val _=pay expected state 3
        in {tree= #tree row,edge=edge expected state id}end)ids
      val _=pay expected state 27
      fun constant_node node=case view expected state node of
          N.Constant _=>true | _=>false
      fun operator wanted arity node=
        case N.operands(view expected state)wanted arity node of
            SOME result=>result
          | NONE=>raise ERR "recorded" "actual operator arity changed"
      fun is_constant wanted node=case view expected state node of
          N.Constant atom=>
            (pay expected state 1;Term.same_const atom wanted)
        | _=>false
      (* Actual int-to-IntInf conversion; existing setup27 stays above. *)
      val _=pay expected state 1
    in Q.recorded(#queue state)
      {metadata_template=RP.AtMost(IntInf.fromInt(#template_limit
         (#semantic_limits(#native state)))),
       tree_view=Clause.view,node_view=application expected state,
       constant_node=constant_node,same_node=same expected state,
       named=name expected state,constant=is_constant,
       constant_term=constant expected state,operator=operator,
       definition=definition expected state,error=ERR "recorded"}
      {premises=actual,target= #tree target,
       target_expanded= #expanded target,fallbacks=[]}end
  structure Step=Z3_NamedReplayStepFn
    (struct
       type expected=W.portfolio
       type context=state
       type command=C.command
       type node=node
       type syntax=PV.value
       type edge=Q.proof
       val original=no_source
       val original_slot=no_source
       val alias=alias
       val equality=equality
       val boolean=boolean
       val scoped_equality=no_nested
       val quantified=no_nested
       val raw_resolution=no_nested
       val resolution=recorded
       val unfinished=no_nested
     end)
  (* The native closing programme is the SAME simultaneous realization
     worker used by the root consumer. This private admission is tied to
     the actual enclosing packet, not a caller native theorem/body map. *)
  fun prepare_closing expected(state:state) proof=
    let
      val _=guard expected state
      val data=S.data_for expected(#syntax state)
      val held=C.data_for expected(#captured state)
      val native= #native state
      val finite= #semantic_limits native
      val policy=W.semantic_policy expected
      val ceiling=IntInf.fromInt(#type_work_limit native)
      (* Thirty-five outer helpers, less the eight separately quoted
         below, plus the actual two refs and dictionary header. *)
      val _=pay expected state 30
      val _=pay expected state 1
      val closing_error=ERR "closing"
      fun spend amount=pay expected state amount
      fun tick()=spend 1
      fun weight ty=N.type_weight_using spend closing_error ceiling ty
      fun same_type left right=
        let val a=weight left val b=weight right
            val _=spend(1+a+b)
        in Type.compare(left,right)=EQUAL end
      fun compare_key((a,b),(c,d))=
        (tick();case Int.compare(a,c)of EQUAL=>
          (tick();Int.compare(b,d))|order=>order)
      val terms=ref(Redblackmap.mkDict compare_key)
      fun typed key=(tick();case Redblackmap.peek(!terms,key)of
          SOME actual=>actual
        | NONE=>raise ERR "closing" "missing authentic typed cell")
      val _=spend 3
      val substitution=SmtReplayValueInterpretation.interpret
        (fn()=>guard expected state)tick(#graph held)(#child held)
        typed same_type terms ERR(#cells data)[]
      fun term node= #1(typed(PV.proof_key(#values state)node))
      val _=spend 2
      val target=term(#body data)
      val body=(#semantic data)(#body data)
      val _=ignore(G.closure_root(#graph held)(#child held)body)
      (* These are actual admitted atomic native ports. A printed
         variable name alone cannot add a member to this inventory. *)
      val _=spend 1
      fun native_atoms []=[]
        | native_atoms(node::rest)=
            let val _=tick()
                val here=case PV.proof_view(#values state)node of
                    PV.ProofVariable _=>
                      (spend 1;[term node])|_=>[]
            in case here of []=>native_atoms rest
              | [value]=>(spend 1;value::native_atoms rest)
              | _=>raise ERR "closing" "invalid atomic inventory"end
      val atoms=native_atoms(#reachable data)
      val names=copy expected state(#name data)(#reachable data)
      val _=spend 1
      fun append [] tail=(guard expected state;tail)
        | append(x::rest)tail=(spend 2;x::append rest tail)
      val allowed=append names atoms
      fun member value=
        let val _=tick()
            fun loop []=false
              | loop(old::rest)=
                  (tick();Portable.pointer_eq(old,value)orelse loop rest)
        in loop allowed end
      (* Six fields/record plus actual guard/error adapters. *)
      val _=spend 9
      val admission:N.admission=
        {guard=fn()=>guard expected state,pay=spend,member=member,
         template_limit= #template_limit finite,
         type_work_limit= #type_work_limit native,error=ERR "closing"}
      val inspector=N.inspector admission
      val ports=ref([]:Type.hol_type list)
      fun profile current=(#profile inspector)current
      fun cost(p:N.profile)=1+ #raw p+ #inc p+ #ann p
      fun bound label limit(p:N.profile)=
        if #raw p<=IntInf.fromInt limit andalso
            #inc p<=IntInf.fromInt limit andalso #ann p<=ceiling then ()
        else raise ERR "closing" label
      fun policy_bound label limit(p:N.profile)=
        if RP.allows limit(#raw p)andalso RP.allows limit(#inc p)then ()
        else raise ERR "closing" label
      fun input p=
        (bound "actual closing input cap"(#input_limit finite)p;
         policy_bound "actual closing input policy"(#input_limit policy)p;
         bound "actual closing template"(#template_limit finite)p;
         policy_bound "actual closing policy"(#template_limit policy)p)
      fun output p=
        (bound "actual closing output cap"(#output_limit finite)p;
         policy_bound "actual closing output policy"(#output_limit policy)p;
         bound "actual closing template"(#template_limit finite)p;
         policy_bound "actual closing policy"(#template_limit policy)p)
      fun forest value=
        let val _=spend 2 val ty=Term.type_of value
            val _=ports:=ty:: !ports
        in if Term.is_comb value then
            let val _=spend 3 val(f,x)=Term.dest_comb value
            in forest f;forest x end
          else if Term.is_var value orelse Term.is_const value then ()else
            raise ERR "closing" "binder inside child interpretation"end
      fun spelling root=
        let val _=tick()
            fun walk current=
              (tick();if Term.is_var current then
                  let val _=tick()val(text,_)=Term.dest_var current
                  in IntInf.fromInt(String.size text)end
                else if Term.is_const current then
                  let val _=tick()val row=Term.dest_thy_const current
                  in IntInf.fromInt(String.size(#Thy row))+
                    IntInf.fromInt(String.size(#Name row))end
                else if Term.is_comb current then
                  let val _=spend 3 val(f,x)=Term.dest_comb current
                  in walk f+walk x end
                else raise ERR "closing" "binder in closing spelling")
        in walk root end
      fun inspect role value=
        let val p=profile value val _=role p val _=forest value
        in p end
      fun count [] total=(guard expected state;total)
        | count(_::rest)total=(tick();count rest(total+1))
      (* Every invocation is one genuine DISCH/INST/REFL/MP port list.
         Actual scan work is paid now; the native incidence is reserved
         once, independently of the extra forecast Term construction. *)
      fun quote inputs result incoming outgoing=
        let
          val _=spend 5
          fun total _ [] amount=(guard expected state;amount)
            | total role(value::rest)amount=
                (tick();total role rest(amount+cost(inspect role value)+
                  spelling value))
          val amount=total input inputs
            (cost(inspect output result)+spelling result+
              total input incoming
              (total output outgoing 0))
          val incidence=count incoming 0
          val tags=24+incidence*(incidence+2)
          val _=if amount<=ceiling then ()else
            raise ERR "closing" "native repeated closing portfolio"
        in spend(amount+tags)end
      fun equal left right=
        if Portable.pointer_eq(left,right)then (tick();true)else
          let val a=inspect input left val b=inspect input right
              val _=spend(cost a+cost b+spelling left+spelling right)
          in Term.aconv left right end
      val contexts=Q.hypotheses proof
      val named=Q.conclusion proof
      val _=if Portable.pointer_eq(named,(#name data)(#body data))then ()
        else raise ERR "closing" "different compiled child endpoint"
      val _=spend 1
      fun known []=guard expected state
        | known(context::rest)=
            let val _=tick()
                fun find []=false
                  | find(actual::more)=
                      (tick();Portable.pointer_eq(context,actual)orelse
                        find more)
            in if find(#assumptions state)then known rest else
              raise ERR "closing" "non-constructor child hypothesis"end
      val _=known contexts
      fun make_imp left right=
        let val _=spend 3
            val shape=N.PBImplication(N.PBHeld left,N.PBHeld right)
            val _=spend 1
            val described=N.boolean_syntax(fn _=>spend 3)shape
            val _=spend 3
            val(p,_)=N.describe_shape(fn _=>spend 4)profile weight
              same_type described
            val _=output p
            val _=spend(cost p)
        in boolSyntax.mk_imp(left,right)end
      (* Exactly the right-associated DISCH order in the shared worker. *)
      fun close []=(named,contexts)
        | close(context::rest)=
            let val(tail,incoming)=close rest
                val result=make_imp context tail
                val _=spend 1
                fun remove []=[]
                  | remove(value::more)=
                      (tick();if equal value context then remove more
                        else(spend 1;value::remove more))
                val outgoing=remove incoming
                val _=spend 2
                val _=quote[context,tail]result incoming outgoing
            in(result,outgoing)end
      val(compact,remaining)=close contexts
      val _=if null remaining then ()else
        raise ERR "closing" "constructor closure was not complete"
      fun replacement variable []=NONE
        | replacement variable({redex,residue}::rest)=
            (tick();if Portable.pointer_eq(variable,redex)then SOME residue
              else replacement variable rest)
      (* This is a bounded substitution image forecast, not a new proof
         rule. No compound output Term is made until its geometry fits. *)
      fun expanded current=
        if Term.is_var current then
          (tick();case replacement current substitution of
              SOME value=>profile value
            | NONE=>profile current)
        else if Term.is_comb current then
          let val _=spend 5 val(f,x)=Term.dest_comb current
              val a=expanded f val b=expanded x
              val own=weight(Term.type_of current)
          in {raw=1+ #raw a+ #raw b,inc=1+ #inc a+ #inc b,
            ann=own+ #ann a+ #ann b,ty=own}:N.profile end
        else if Term.is_const current then profile current else
          raise ERR "closing" "binder in compact substitution law"
      val _=spend 1
      fun substitution_bytes [] total=(guard expected state;total)
        | substitution_bytes({redex,...}::rest)total=
            (tick();substitution_bytes rest(total+spelling redex))
      val substitution_count=count substitution 0
      val substitution_spelling=substitution_bytes substitution 0
      fun substitute value=
        let val _=spend 1 val measured=expanded value
            val _=output measured
            (* Extra metadata substitution is a separate performed walk;
               the actual INST below still has its own full quotation. *)
            val input_profile=profile value
            val _=spend(cost measured+cost input_profile+
              (1+ #raw input_profile)*(1+substitution_count+
                substitution_spelling)+
              substitution_count*spelling value)
        in Term.subst substitution value end
      val expanded_law=substitute compact
      (* INST consumes the entire actual substitution, including unused
         entries. Every redex/residue is an input and Type port even when
         it disappears from the expanded conclusion. No Source or proof
         authority is obtained by this purely prospective input list. *)
      val _=spend 1
      fun inst_inputs []=(spend 1;[compact])
        | inst_inputs({redex,residue}::rest)=
            (spend 3;redex::residue::inst_inputs rest)
      val _=quote(inst_inputs substitution)expanded_law[][]
      fun witness context=
        let val _=spend 3 val(lhs,_)=boolSyntax.dest_eq context
            fun find []=raise ERR "closing" "missing constructor image"
              | find({redex,residue}::rest)=
                  (tick();if Portable.pointer_eq(lhs,redex)then residue
                    else find rest)
            val actual=find substitution
            val _=spend 3
            val shape=N.EqualitySyntax(N.HeldSyntax actual,
              N.HeldSyntax actual)
            val(p,_)=N.describe_shape(fn _=>spend 4)profile weight
              same_type shape
            val _=output p val _=spend(cost p)
            val reflexive=N.realize_shape(fn _=>spend 1)shape
            val interpreted=substitute context
            val _=if equal interpreted reflexive then ()else
              raise ERR "closing" "incorrect actual constructor image"
            val _=spend 1
            val _=quote[actual]reflexive[][]
        in(actual,reflexive)end
      val _=spend 1
      fun witnesses []=[]
        | witnesses(context::rest)=
            (spend 2;witness context::witnesses rest)
      val actual_witnesses=witnesses contexts
      val _=spend 1
      fun apply law []=law
        | apply law((_,fact)::rest)=
            let val _=spend 2 val(left,right)=boolSyntax.dest_imp_only law
                val _=if equal left fact then ()else
                  raise ERR "closing" "constructor witness order changed"
                val _=spend 2
                val _=quote[law,fact]right[][]
            in apply right rest end
      val result=apply expanded_law actual_witnesses
      val _=if equal result target then ()else
        raise ERR "closing" "actual interpreted child target changed"
      val _=spend 1
      fun just_terms []=[]
        | just_terms((actual,_)::rest)=
            (spend 2;actual::just_terms rest)
      val witness_terms=just_terms actual_witnesses
      val _=spend 1
      fun reverse [] result=(guard expected state;result)
        | reverse(x::rest)result=(spend 2;reverse rest(x::result))
      val closing_ports=reverse(!ports)[]
      val _=spend 2
      val type_ports=append(#type_ports data)closing_ports
      val all_ports=append(Q.type_ports(#queue state))type_ports
      val _=spend 5
      val _=SmtReplayLocalSpecialize.callback_forest
        {visit=tick,type_weight=weight,ceiling=ceiling,
         error=closing_error}all_ports
      (* Seven retained fields and their immutable record. *)
      val _=spend 8
    in {substitution=substitution,contexts=contexts,
      witnesses=witness_terms,type_ports=type_ports,
      all_type_ports=all_ports,body=body,
      target=target}:closing end
  fun prepare expected captured=((
    case SmtReplayOwnedScopedValueSyntax.prepare expected captured of
        S.Needs required=>
        W.with_step expected(fn()=>
          let val _=ignore(C.data_for expected captured)
              val _=W.spend_policy expected 3
              fun convert []=[]
                | convert(S.NativeOpening term::rest)=
                    (W.spend_policy expected 3;
                     NativeOpening term::convert rest)
          in Needs(convert required)end)
      | S.Prepared syntax=>W.with_step expected(fn()=>
        let
          val _=W.spend_policy expected 1
          val data=S.data_for expected syntax
          val held=C.data_for expected captured
          val native=NC.for_work expected(#native_contract held)
          val _=W.spend_policy expected 27
          fun guard()=ignore(C.data_for expected captured)
          fun pay amount=(guard();W.spend_policy expected amount)
          val nodes= #reachable data
          fun names []=(guard();[])
            | names(node::rest)=(pay 2;(#name data)node::names rest)
          val allowed=names nodes
          fun member term=
            let val _=pay 1
                fun loop []=false
                  | loop(old::rest)=
                      (pay 1;Portable.pointer_eq(old,term)orelse loop rest)
            in loop allowed end
          val _=pay 7
          val admission:N.admission={guard=guard,pay=pay,member=member,
            template_limit= #template_limit(#semantic_limits native),
            type_work_limit= #type_work_limit native,error=ERR "native"}
          val queue=SmtReplayScopedNativeQueue.create admission
          val layout=N.freeze_layout(#freeze data)
          val assumptions=N.materialize_freeze(#freeze data)
          fun seeds [] _=(guard();[])
            | seeds(term::rest)index=
                (pay 2;Q.seed queue index term::seeds rest(index+1))
          val _=pay 2
          val actual_seeds=Vector.fromList(seeds assumptions 0)
          val _=pay 3
          val compare=compare_id pay
          val proofs=ref(Redblackmap.mkDict compare)
          val statements=ref(Redblackmap.mkDict compare)
          val occurrences=ref(Redblackmap.mkDict compare)
          val factory=SmtReplayValueClause.create_scoped
            expected(#query held)
            (#packet held)(#binding held)
          (* Seventeen retained state fields, record and the actual
             emission visitor closure. Plan publication pays below. *)
          val _=pay 19
          val state:state={work=expected,captured=captured,syntax=syntax,
            values= #values held,key= #key data,name= #name data,
            view= #view data,native=native,queue=queue,
            definitions= #definitions layout,assumptions=assumptions,
            seeds=actual_seeds,proofs=proofs,statements=statements,
            parsed= #proof(VP.contents_with_policy_for expected
              (#query held)(#packet held)),factory=factory,
            occurrences=occurrences}
          fun compile []=(guard();())
            | compile((command as {id,target,plan}:C.command)::rest)=
                let val _=pay 1
                    val result=Step.execute expected state command plan
                    val _=pay 2
                    val _=if Portable.pointer_eq(Q.conclusion result,
                        (#name data)target)then ()else
                      raise ERR "prepare" "actual child endpoint changed"
                    val _=pay 2
                    val _=proofs:=Redblackmap.insert(!proofs,id,result)
                    val _=statements:=Redblackmap.insert
                      (!statements,id,target)
                in compile rest end
          val _=compile(#commands held)
          val actual=edge expected state(#body held)
          val _=Q.seal queue
          val closing=prepare_closing expected state actual
          val _=guard()
          val _=pay 7
        in Prepared(Plan{state=state,proof=actual,closing=closing,
          used=ref false})end))
    handle primary=>(W.close expected;raise primary))
  fun execute_in_action expected(Plan{state,proof,closing,used})
      {check_type}=
    ((
      (if Portable.pointer_eq(expected,#work state)then ()else
         raise ERR "execute" "different original Work";
        let
          val _=guard expected state
          val _=pay expected state 2
          val _=if !used then raise ERR "execute" "used scoped child plan"
            else used:=true
          val data=S.data_for expected(#syntax state)
          val held=C.data_for expected(#captured state)
          val _=pay expected state 2
          fun checked ty=(guard expected state;check_type ty;
            guard expected state)
          fun callbacks []=guard expected state
            | callbacks(ty::rest)=
                (pay expected state 1;checked ty;callbacks rest)
          (* Every queue/interpretation/closing Type and Hyp portfolio
             settled in preparation. No later logical Needs is possible. *)
          val _=Q.check_types(#queue state)checked
          val _=callbacks(#type_ports closing)
          val block=N.execute_freeze(#freeze data)
          (* The plan is now consumed. Use its exact privately retained
             definition map, never re-open the one-use layout afterwards. *)
          val _=pay expected state 1
          fun seed slot=
            let val _=pay expected state 1
                fun seek []=raise ERR "execute" "missing constructor row"
                  | seek(node::rest)=
                      (pay expected state 1;
                       case Redblackmap.peek(#definitions state,
                           (#key data)node)of
                           SOME actual=>if actual=slot then
                             N.theorem block(N.definition block node)
                             else seek rest
                         | NONE=>seek rest)
            in seek(#reachable data)end
          val _=Q.execute(#queue state)seed
          val native=Q.theorem(#queue state)proof
          val _=guard expected state
          (* The six-field/record, guard and error adapters are actual
             native-call setup, independently of the retained quota. *)
          val _=pay expected state 10
          val law=SmtReplaySimultaneousRealization.instantiate
            {guard=fn()=>guard expected state,error=ERR "execute",
             contexts= #contexts closing,proof=native,
             substitution= #substitution closing}
          val _=pay expected state 1
          fun witnesses []=(guard expected state;[])
            | witnesses(term::rest)=
                let val _=guard expected state
                    val actual=O.REFL term
                    val _=guard expected state
                    val _=pay expected state 2
                in actual::witnesses rest end
          val genuine=witnesses(#witnesses closing)
          val _=pay expected state 6
          val result=SmtReplaySimultaneousRealization.apply
            {guard=fn()=>guard expected state,law=law,witnesses=genuine}
          val _=guard expected state
          val _=pay expected state 3
          val _=if null(Thm.hyp result)andalso N.clean result andalso
              Portable.pointer_eq(Thm.concl result,#target closing)then ()
            else raise ERR "execute" "closed interpreted child changed"
          val _=ignore(G.closure_root(#graph held)(#child held)
            (#body closing))
          val _=pay expected state 4
        in ClosedChild{state=state,closing=closing,theorem=result}end))
    handle primary=>(W.close expected;raise primary))
  fun execute expected plan options=((
    W.with_step expected(fn()=>
      (W.spend_policy expected 1;
       execute_in_action expected plan options)))
    handle primary=>(W.close expected;raise primary))
  fun closed_child_data_for expected
      (ClosedChild{state,closing,theorem})=((
    let val _=guard expected state
        val held=C.data_for expected(#captured state)
        val _=pay expected state 6
        val _=if null(Thm.hyp theorem)andalso N.clean theorem andalso
            Portable.pointer_eq(Thm.concl theorem,#target closing)then ()
          else raise ERR "closed_child" "actual closed child changed"
        val _=ignore(G.closure_root(#graph held)(#child held)
          (#body closing))
        (* Closed child Scope/body only. Parent generalization and final
           closed-law quota still belong to the actual BinderClose owner. *)
        val _=pay expected state 10
    in {context= #captured state,binding= #binding held,
      frame= #frame held,native_contract= #native_contract held,
      body= #body closing,theorem=theorem}end)
    handle primary=>(W.close expected;raise primary))
  fun data_for expected(Plan{state,proof,closing,...})=
    ((
    (guard expected state;pay expected state 9;
     {context= #captured state,syntax= #syntax state,
      conclusion=Q.conclusion proof,hypotheses=Q.hypotheses proof,
      assumptions= #assumptions state,native_body= #body closing,
      native_term= #target closing,type_ports= #all_type_ports closing}))
    handle primary=>(W.close expected;raise primary))
end
