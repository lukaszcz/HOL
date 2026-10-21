structure SmtReplayOwnedScopedValueLift :> SmtReplayOwnedScopedValueLift =
struct
  structure W=SmtReplayInvocationWork
  structure C=SmtReplayOwnedScopedValueContext
  structure Programme=SmtReplayOwnedScopedValueProgramme
  structure Syntax=SmtReplayOwnedScopedValueSyntax
  structure G=SmtReplayGraph
  structure PV=SmtLib_GraphParserValue
  structure VP=SmtLib_GraphValueProof
  structure GP=SmtLib_GraphPreprocess
  structure NC=SmtReplayNativeContract
  structure Scope=SmtReplayOwnedScopeReceipt
  structure N=SmtReplayNamedContext
  structure P=SmtReplayProof
  structure Close=SmtReplayBinderClose
  structure RP=SmtReplayResourcePolicy
  val ERR=Feedback.mk_HOL_ERR "SmtReplayOwnedScopedValueLift"
  datatype requirement=Enclosing of C.requirement
    | ChildOpening of PV.proof_term | BindingShape
    | TargetProgramme of PV.value | TargetOpening of G.scope * G.node
  exception Pending of requirement
  type ports={query:GP.graph_query,context:PV.context,frame:Scope.receipt,
    binding:VP.binding_frame,native_contract:NC.contract,
    statement:PV.value,law_node:G.node,
    aliases:(PV.proof_term * G.node)list}
  datatype plan=Plan of {work:W.portfolio,captured:C.context,
    child:Programme.plan,guard:unit -> unit,ports:ports,
    variable:Term.term,kind:Close.kind,body:G.node,
    type_ports:Type.hol_type list,check_type:Type.hol_type -> unit,
    used:bool ref}
  datatype preparation=Prepared of plan | Needs of requirement list
  fun prepare expected query packet {id,native_contract,check_type}=
    ((
      case SmtReplayOwnedScopedValueContext.capture
          expected query packet
          {id=id,native_contract=native_contract}of
          C.Needs requirements=>W.with_step expected(fn()=>
            let val _=W.spend_policy expected 3
                fun convert []=[]
                  | convert(value::rest)=(W.spend_policy expected 3;
                      Enclosing value::convert rest)
            in Needs(convert requirements)end)
        | C.Captured captured=>
          case SmtReplayOwnedScopedValueProgramme.prepare
              expected captured of
              Programme.Needs requirements=>W.with_step expected(fn()=>
                let val _=ignore(C.data_for expected captured)
                    val _=W.spend_policy expected 3
                    fun convert []=[]
                      | convert(Programme.NativeOpening value::rest)=
                          (W.spend_policy expected 3;
                           ChildOpening value::convert rest)
                in Needs(convert requirements)end)
            | Programme.Prepared child=>W.with_step expected(fn()=>
              ((let
                val _=W.spend_policy expected 1
                val held=C.data_for expected captured
                val compiled=Programme.data_for expected child
                val syntax=SmtReplayOwnedScopedValueSyntax.data_for
                  expected(#syntax compiled)
                val binding=VP.binding_frame_data_for expected query
                  (#binding held)
                val context= #values held val graph= #graph held
                val root= #root held val inner= #child held
                val frame= #parent binding val target= #target held
                val native=NC.for_work expected native_contract
                val finite= #semantic_limits native
                val policy=W.semantic_policy expected
                val ceiling=IntInf.fromInt(#type_work_limit native)
                val _=W.spend_policy expected 43
                val _=W.spend_policy expected 2
                val type_error=ERR "type"
                val native_error=ERR "native"
                fun guard()=
                  (ignore(C.data_for expected captured);
                   NC.validate_for expected native_contract;
                   ignore(VP.binding_frame_data_for expected query
                     (#binding held));
                   ignore(Scope.description_with_policy_for expected frame))
                fun pay amount=(guard();W.spend_policy expected amount)
                fun tick()=pay 1
                fun weight ty=N.type_weight_using pay type_error ceiling ty
                fun same_type left right=
                  let val a=weight left val b=weight right
                      val _=pay(1+a+b)
                  in Type.compare(left,right)=EQUAL end
                fun need value=(pay 2;raise Pending value)
                val variable=case (#binders binding,#variables binding,
                    #lambda_blocks held)of (true,[value],[1])=>value
                  | _=>need BindingShape
                val cursor=PV.proof_term context variable
                val variable_node=case PV.proof_graph_reference context
                    cursor of SOME reference=>
                      let val _=pay 3
                          val _=if Portable.pointer_eq
                              (#graph reference,graph)then ()else
                            raise ERR "prepare" "different binder graph"
                      in G.closure_child_node graph(#scope reference)
                        (#child reference)end
                  | NONE=>raise ERR "prepare" "missing actual binder ID"
                val atom=case G.view graph variable_node of
                    G.Variable(G.Bound,_)=>
                      G.representative graph variable_node
                  | _=>raise ERR "prepare" "annotation is not Bound"
                val domain=Term.type_of atom
                val own=weight domain
                fun view term=(tick();PV.proof_view context term)
                fun operands constant arity term=
                  let val _=tick()
                      fun spine current args left=
                        (tick();case view current of
                            PV.ProofApplication(f,x)=>if left>0 then
                              (pay 2;spine f(x::args)(left-1))else NONE
                          | PV.ProofConstant actual=>
                              let val _=pay 3
                                  val a=Term.dest_thy_const actual
                                  val b=Term.dest_thy_const constant
                                  val _=pay(1+
                                    IntInf.fromInt(String.size(#Thy a))+
                                    IntInf.fromInt(String.size(#Name a))+
                                    IntInf.fromInt(String.size(#Thy b))+
                                    IntInf.fromInt(String.size(#Name b)))
                              in if left=0 andalso
                                  Term.same_const actual constant then
                                  SOME args else NONE end
                          | _=>NONE)
                  in spine term [] arity end
                fun abstraction term=case view term of
                    PV.ProofAbstraction{binder,body,body_frame}=>
                      (G.validate_scope graph body_frame;
                       if same_type domain(PV.proof_type_of context binder)
                         then SOME(body,term)else NONE)
                  | _=>NONE
                fun prefix term=case abstraction term of SOME pair=>
                      (pay 3;SOME(Close.Lambda,pair,NONE))
                  | NONE=>
                    let val _=pay 2
                        fun quantified constant kind=
                          case operands constant 1 term of
                              SOME[lambda]=>
                                (case abstraction lambda of SOME pair=>
                                  let val head=case view term of
                                          PV.ProofApplication(h,_)=>h
                                        | _=>raise ERR "prepare"
                                            "quantifier spine changed"
                                      val _=pay 4
                                  in SOME(kind,pair,SOME head)end
                                | NONE=>NONE)
                            | _=>NONE
                    in case quantified boolSyntax.universal Close.Forall of
                        SOME found=>SOME found
                      | NONE=>quantified boolSyntax.existential Close.Exists
                    end
                val target_cursor=PV.proof_term context target
                val(left,right)=case operands boolSyntax.equality 2
                    target_cursor of SOME[a,b]=>(pay 1;(a,b))
                  | _=>need(TargetProgramme target)
                val(kind,left_lambda,right_lambda,operator)=
                  case(prefix left,prefix right)of
                      (SOME(ka,(_,la),ha),SOME(kb,(_,lb),hb))=>
                        if ka=kb then
                          let val _=pay 6
                              val heads=case(ha,hb)of
                                  (NONE,NONE)=>NONE
                                | (SOME a,SOME b)=>SOME(a,b)
                                | _=>raise ERR "prepare"
                                    "different target prefix kinds"
                          in(ka,la,lb,heads)end else
                          need(TargetProgramme target)
                    | _=>need(TargetProgramme target)
                val(body_left,body_right)=case N.equality(#view syntax)
                    (#body syntax)of SOME pair=>pair
                  | NONE=>need(TargetProgramme target)
                val left_node=(#semantic syntax)body_left
                val right_node=(#semantic syntax)body_right
                val lhs=G.representative graph left_node
                val rhs=G.representative graph right_node
                val range=G.type_of graph left_node
                val _=if same_type range(G.type_of graph right_node)then ()
                  else raise ERR "prepare" "different child equation Types"
                val _=case kind of Close.Lambda=>()|_=>
                  if same_type range Type.bool then ()else
                    need(TargetProgramme target)
                (* All used native free IDs must already be visible to
                   the parent or be this exact annotated Bound identity. *)
                val _=pay 2
                val seen=ref(Redblackset.empty
                  (fn(a,b)=>(tick();Int.compare(a,b))))
                fun free term=
                  let val _=tick()val key=(#key syntax)term
                  in if Redblackset.member(!seen,key)then ()else
                    let val _=pay 1 val _=seen:=Redblackset.add(!seen,key)
                    in case view term of
                        PV.ProofApplication(f,x)=>(free f;free x)
                      | PV.ProofVariable _=>
                          let val node=(#semantic syntax)term val _=pay 2
                          in if node=variable_node orelse
                              G.scope_visible graph root
                                (G.node_scope graph node) then ()else
                              need(TargetProgramme target)end
                      | PV.ProofConstant _=>()
                      | _=>raise ERR "prepare" "unadmitted child image"end
                  end
                val _=free(#body syntax)
                fun arrow left right=
                  let val a=weight left val b=weight right
                      val _=if 1+a+b<=ceiling then ()else
                        raise ERR "prepare" "generated arrow Type cap"
                      val _=pay(4+a+b)
                  in Type.mk_type("fun",[left,right])end
                val abstraction_type=arrow domain range
                val abstraction_weight=weight abstraction_type
                val _=pay 3
                fun atoms []=[]
                  | atoms(term::rest)=
                      let val _=tick()
                      in case view term of PV.ProofVariable _=>
                          (pay 2;G.representative graph
                            ((#semantic syntax)term)::atoms rest)
                        | _=>atoms rest end
                val actual_atoms=atom::atoms(#reachable syntax)
                fun member term=
                  let val _=tick()
                      fun loop []=false|loop(old::rest)=
                        (tick();Portable.pointer_eq(term,old)orelse
                          loop rest)
                  in loop actual_atoms end
                val _=pay 7
                val inspect=N.inspector
                  {guard=guard,pay=pay,member=member,
                   template_limit= #template_limit finite,
                   type_work_limit= #type_work_limit native,
                   error=native_error}
                fun profile term=(#profile inspect)term
                val a=profile lhs val b=profile rhs
                val body_profile=profile(#native_term compiled)
                fun bound label metadata limit(p:N.profile)=
                  (pay 5;if #raw p<=IntInf.fromInt limit andalso
                      #inc p<=IntInf.fromInt limit andalso
                      RP.allows metadata(#raw p)andalso
                      RP.allows metadata(#inc p)andalso #ann p<=ceiling
                    then ()else raise ERR "prepare" label)
                fun input p=bound "actual lifted input quota"
                  (#input_limit policy)(#input_limit finite)p
                fun output p=
                  (bound "actual lifted output quota"(#output_limit policy)
                    (#output_limit finite)p;
                   bound "actual lifted template quota"
                    (#template_limit policy)(#template_limit finite)p)
                val _=pay 2
                fun lambda(p:N.profile):N.profile=
                  (pay 8;{raw=1+ #raw p,inc=2+ #inc p,
                    ann=abstraction_weight+own+ #ann p,
                    ty=abstraction_weight})
                val la=lambda a val lb=lambda b
                fun equation(p:N.profile)(q:N.profile):N.profile=
                  (pay 8;{raw=3+ #raw p+ #raw q,
                    inc=3+ #inc p+ #inc q,
                    ann=6+3* #ty p+ #ann p+ #ann q,ty=1})
                val lambda_law=equation la lb
                val quantifier=case operator of NONE=>NONE
                  | SOME(head,_)=>
                      let val actual=case view head of
                              PV.ProofConstant atom=>atom
                            | _=>raise ERR "prepare" "quantifier changed"
                          val expected=arrow abstraction_type Type.bool
                          val _=if same_type(Term.type_of actual)expected
                            then ()else need(TargetProgramme target)
                          val _=pay 4
                      in SOME(actual,weight expected)end
                fun quantified(p:N.profile)operator_weight:N.profile=
                  (pay 8;{raw=2+ #raw p,inc=2+ #inc p,
                    ann=1+operator_weight+ #ann p,ty=1})
                val law=case quantifier of NONE=>lambda_law
                  | SOME(_,amount)=>equation(quantified la amount)
                      (quantified lb amount)
                val bridge=equation law law
                val _=input body_profile val _=output lambda_law
                val _=output law val _=output bridge
                fun cost(p:N.profile)=1+ #raw p+ #inc p+ #ann p
                val _=pay 8
                (* ABS input/output; ALPHA two operands/bridge; EQ_MP
                   bridge/input/result, empty-Hyp/tag validation. *)
                val amount=own+cost body_profile+5*cost law+
                  2*cost bridge+32
                val extra=case quantifier of NONE=>0|SOME(_,n)=>
                  let val _=pay 5
                      val op_profile:N.profile={raw=1,inc=1,ann=n,ty=n}
                      val _=input op_profile
                  in 2*cost lambda_law+cost op_profile+17 end
                val _=if amount+extra<=ceiling then ()else
                  raise ERR "prepare" "lifted repeated native Type portfolio"
                val _=pay(amount+extra)
                val _=pay 2
                val(spelling,_)=Term.dest_var atom
                fun body_spelling term=
                  (tick();if Term.is_var term then
                      let val _=tick()val(name,_)=Term.dest_var term
                      in IntInf.fromInt(String.size name)end
                    else if Term.is_const term then
                      let val _=tick()val row=Term.dest_thy_const term
                      in IntInf.fromInt(String.size(#Thy row))+
                        IntInf.fromInt(String.size(#Name row))end
                    else if Term.is_comb term then
                      let val _=pay 3 val(f,x)=Term.dest_comb term
                      in body_spelling f+body_spelling x end
                    else raise ERR "prepare" "binder in child body")
                val _=pay(1+32*IntInf.fromInt(String.size spelling)+
                  16*(body_spelling lhs+body_spelling rhs))
                val _=pay 2
                fun compare_pair((a,b),(c,d))=
                  (tick();case Int.compare(a,c)of EQUAL=>
                    (tick();Int.compare(b,d))|order=>order)
                val ty_memo=ref(Redblackmap.mkDict compare_pair)
                fun types term=
                  let val _=tick()val key=PV.proof_key context term
                  in case Redblackmap.peek(!ty_memo,key)of SOME all=>all
                    | NONE=>let val ty=PV.proof_type_of context term
                        val _=pay 2
                        val all=case view term of
                            PV.ProofApplication(f,x)=>
                              ty::append(types f)(types x)
                          | _=>[ty]
                        val _=tick()
                        val _=ty_memo:=Redblackmap.insert(!ty_memo,key,all)
                      in all end end
                and append [] tail=(guard();tail)
                  | append(x::rest)tail=(pay 2;x::append rest tail)
                val _=pay 2
                val left_types=types body_left
                val right_types=types body_right
                val eq_partial=arrow range Type.bool
                val eq_head=arrow range eq_partial
                val lambda_partial=arrow abstraction_type Type.bool
                val lambda_head=arrow abstraction_type lambda_partial
                val bool_partial=arrow Type.bool Type.bool
                val bool_head=arrow Type.bool bool_partial
                val _=pay 9
                val lambda_left_types=abstraction_type::domain::left_types
                val lambda_right_types=abstraction_type::domain::right_types
                val lambda_types=append
                  [Type.bool,lambda_partial,lambda_head]
                  (append lambda_left_types lambda_right_types)
                val law_types=case quantifier of NONE=>lambda_types
                  | SOME(operator,_)=>
                      let val _=pay 7 val ty=Term.type_of operator
                      in append[Type.bool,bool_partial,bool_head]
                        (append[Type.bool,ty]
                          (append lambda_left_types(append[Type.bool,ty]
                            lambda_right_types)))end
                val _=pay 3
                val bridge_types=append[Type.bool,bool_partial,bool_head]
                  (append law_types law_types)
                fun copies 0 _ tail=(guard();tail)
                  | copies n all tail=(tick();append all(copies(n-1)all tail))
                val _=pay 2
                val ordinary_types=domain::append
                  [Type.bool,eq_partial,eq_head]
                  (append left_types(append right_types
                    (copies 5 law_types(copies 2 bridge_types[]))))
                val type_ports=case quantifier of NONE=>ordinary_types
                  | SOME(operator,_)=>
                      let val schema=case kind of Close.Forall=>
                              boolSyntax.universal|_=>boolSyntax.existential
                          val _=pay 3
                      in append[Term.type_of schema,Term.type_of operator]
                        (copies 2 lambda_types ordinary_types)end
                val all_ports=append(#type_ports compiled)type_ports
                val _=pay 6
                val _=SmtReplayLocalSpecialize.callback_forest
                  {visit=tick,type_weight=weight,ceiling=ceiling,
                   error=ERR "prepare"}all_ports
                (* All parent input/output/Type/ALPHA portfolios are fixed
                   before the first actual native abstraction is built. *)
                val _=pay 8
                val left_abs=G.recorded_abstraction_with_policy graph root
                  (RP.AtMost(IntInf.fromInt(#template_limit finite)))
                  {binder=variable_node,body=left_node,body_frame=inner}
                val right_abs=G.recorded_abstraction_with_policy graph root
                  (RP.AtMost(IntInf.fromInt(#template_limit finite)))
                  {binder=variable_node,body=right_node,body_frame=inner}
                val quantifier_node=case quantifier of NONE=>NONE
                  | SOME(operator,_)=>
                      (pay 3;SOME(G.constant graph root operator))
                val(left_endpoint,right_endpoint)=case quantifier_node of
                    NONE=>(pay 1;(left_abs,right_abs))
                  | SOME operator=>(pay 7;
                      (G.application graph root(operator,left_abs),
                       G.application graph root(operator,right_abs)))
                val _=pay(cost law)
                val eq_atom=Term.rator(Term.rator(boolSyntax.mk_eq
                  (G.representative graph left_endpoint,
                   G.representative graph right_endpoint)))
                val _=pay 10
                val head=G.constant graph root eq_atom
                val partial=G.application graph root(head,left_endpoint)
                val node=G.application graph root(partial,right_endpoint)
                val _=case PV.corresponds_to_graph_with_policy context graph
                    root {value=target,node=node}of PV.Corresponding=>()
                  | PV.NeedsGraphOpening opening=>
                      need(TargetOpening opening)
                  | PV.DifferentGraphSyntax=>raise ERR "prepare"
                      "quant-intro target differs from actual child closure"
                val(partial_cursor,head_cursor)=case view target_cursor of
                    PV.ProofApplication(partial,_)=>
                      (case view partial of PV.ProofApplication(head,_)=>
                         (pay 1;(partial,head))
                       | _=>raise ERR "prepare" "equality spine changed")
                  | _=>raise ERR "prepare" "equality spine changed"
                val _=pay 14
                val base=[(target_cursor,node),(partial_cursor,partial),
                  (head_cursor,head),(left,left_endpoint),
                  (right,right_endpoint),(left_lambda,left_abs),
                  (right_lambda,right_abs)]
                val aliases=case(operator,quantifier_node)of
                    (SOME(a,b),SOME node)=>
                      (pay 4;(a,node)::(b,node)::base)|_=>base
                val _=pay 9
                val ports:ports={query=query,context=context,frame=frame,
                  binding= #binding held,native_contract=native_contract,
                  statement=target,law_node=node,aliases=aliases}
                val _=pay 14
              in Prepared(Plan{work=expected,captured=captured,child=child,
                guard=guard,ports=ports,variable=atom,kind=kind,
                body= #native_body compiled,type_ports=type_ports,
                check_type=check_type,used=ref false})end)
              handle Pending missing=>
                (W.spend_policy expected 3;Needs[missing]))))
    handle primary=>(W.close expected;raise primary))
  fun data_for expected(Plan{work,guard,ports,...})=((
    (if Portable.pointer_eq(expected,work)then ()else
       raise ERR "data_for" "different original Work";
     guard();ports))
    handle primary=>(W.close expected;raise primary))
  fun execute_in_action expected
      (Plan{work,captured,child,guard,ports,variable,kind,body,
        type_ports,check_type,used})=((
    let
      val _=if Portable.pointer_eq(expected,work)then ()else
        raise ERR "execute" "different original Work"
      val _=guard()val _=W.spend_policy expected 2
      val _=if !used then raise ERR "execute" "used scoped lift"
        else used:=true
      fun checked ty=(guard();check_type ty;guard())
      fun callbacks []=guard()
        | callbacks(ty::rest)=
            (W.spend_policy expected 1;checked ty;callbacks rest)
      val _=callbacks type_ports
      val closed=Programme.execute_in_action expected child
        {check_type=checked}
      val actual=Programme.closed_child_data_for expected closed
      val _=W.spend_policy expected 3
      val _=if Portable.pointer_eq(#context actual,captured)andalso
          #body actual=body then ()else
        raise ERR "execute" "different authentic closed child"
      val held=C.data_for expected captured
      val _=W.spend_policy expected 9
      val proof=Close.run(fn value=>value)
        {entries=[(kind,variable)],theorem= #theorem actual,
         target=fn()=>(guard();G.representative(#graph held)(#law_node ports))}
      val _=guard()val _=W.spend_policy expected 6
    in P.record_closed_with_policy_scoped_profiles(#graph held)(#root held)
      {node= #law_node ports,theorem=proof,
       template_limit= #template_limit(W.semantic_policy expected),
       profiles=[],check_type=checked}end)
    handle primary=>(W.close expected;raise primary))
end
