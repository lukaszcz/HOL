structure SmtReplayOwnedValueBinder :> SmtReplayOwnedValueBinder =
struct
  structure W=SmtReplayInvocationWork
  structure G=SmtReplayGraph
  structure GP=SmtLib_GraphPreprocess
  structure VP=SmtLib_GraphValueProof
  structure PV=SmtLib_GraphParserValue
  structure F=SmtLib_GraphFrontend
  structure Scope=SmtReplayOwnedScopeReceipt
  structure NC=SmtReplayNativeContract
  structure N=SmtReplayNamedContext
  structure P=SmtReplayProof
  structure Z=Z3_GraphProofParser
  structure Shared=Z3_SharedReplayPlan
  structure RP=SmtReplayResourcePolicy
  val ERR=Feedback.mk_HOL_ERR "SmtReplayOwnedValueBinder"
  datatype requirement = ChildProgramme of Z.proof_id
    | BindingProgramme of F.value_scoped_session
    | TargetProgramme of PV.value
    | GeneralProgramme of SmtReplayOwnedScopedValueLift.requirement
  type ports={query:GP.graph_query,context:PV.context,frame:Scope.receipt,
    binding:VP.binding_frame,native_contract:NC.contract,
    statement:PV.value,law_node:G.node,
    aliases:(PV.proof_term * G.node) list}
  datatype plan=Plan of {work:W.portfolio,guard:unit -> unit,ports:ports,
    produce:unit -> P.closed_fact,used:bool ref}
  datatype closed_law=ClosedLaw of {work:W.portfolio,guard:unit -> unit,
    ports:ports,graph:G.graph,scope:G.scope,fact:P.closed_fact,
    checked_aliases:(IntInf.int * IntInf.int)option ref}
  datatype preparation=Prepared of plan | Needs of requirement list
  exception Pending of requirement
  datatype 'a metadata = Complete of 'a | Missing of requirement
  (* Only ordinary syntax requirements leave an action successfully. Work,
     ownership and callback Primary exceptions retain the existing bracket. *)
  fun metadata expected action =
    case W.with_step expected (fn()=>
        ((let val value=action ()
              val _=W.spend_policy expected 1
          in Complete value end)
          handle Pending needed=>
            (W.spend_policy expected 4;Missing needed))) of
        Complete value=>value | Missing needed=>raise Pending needed
  fun pending expected make=
    (W.spend_policy expected 3;raise Pending(make ()))
  fun protected expected action=action ()
    handle primary=>(W.close expected;raise primary)

  fun prepare_using quantified expected query
      (packet:Z3_GraphValueProofParser.proof VP.packet)
      {id,native_contract,check_type} = protected expected (fn()=>
    let
      val original=GP.query_nodes_with_policy_for expected query
      val _=NC.validate_for expected native_contract
      (* These are authentic packet syntax observations only. No native
         worker or copied proof payload is admitted by the lookup. *)
      val parsed=metadata expected (fn()=>
        let
          val contents=VP.contents_with_policy_for expected query packet
          val proof= #proof contents
          (* Nine lookup/observer helper closures, seven observer fields
             plus its record, four registry fields plus its record, and
             the two observer adapter closures. *)
          val _=W.spend_policy expected 24
          fun valid ()=ignore(VP.contents_with_policy_for
            expected query packet)
          fun pay amount=(valid ();W.spend_policy expected amount)
          fun tick ()=pay 1
          fun compare_id (Z.Named a,Z.Named b)=
                (tick ();Int.compare(a,b))
            | compare_id (Z.Anonymous a,Z.Anonymous b)=
                (tick ();Int.compare(a,b))
            | compare_id (Z.Named _,Z.Anonymous _)=(tick ();LESS)
            | compare_id (Z.Anonymous _,Z.Named _)=(tick ();GREATER)
          fun find wanted=(tick ();case Redblackmap.foldl
              (fn(key,value,found)=>
                (tick ();case found of SOME _=>found | NONE=>
                   if compare_id(wanted,key)=EQUAL then (tick ();SOME value)
                   else NONE)) NONE (#steps proof) of
              SOME command=>command
            | NONE=>raise ERR "prepare" "unknown actual proof ID")
          fun strings (a,b)=pay(1+IntInf.fromInt(String.size a)+
            IntInf.fromInt(String.size b))
          fun metadata_strings values=
            List.app(fn text=>
              (tick ();pay(1+2*IntInf.fromInt(String.size text)))) values
          fun metadata_rule (rule:Z3_Proof.proof_rule)=
            (pay 6;metadata_strings[#name rule,#replay_handler rule];
             metadata_strings(#aliases rule);
             case #version_support rule of Z3_Proof.AllZ3Versions=>tick ()
               | Z3_Proof.Z3Versions values=>metadata_strings values
               | Z3_Proof.Z3VersionPrefixes values=>metadata_strings values)
          val observer:Shared.observer=
            {registry={visit=tick,copy=tick,string_comparison=strings,
               prefix_comparison=strings},
             rule_comparison=fn(a,b)=>(metadata_rule a;metadata_rule b),
             normalization_character=tick,premises=fn entries=>
               List.app(fn _=>tick ())entries,
             argument_copy=tick,kept_item=tick,copied_roots=tick}
          fun canonical rule=Shared.canonical_name observer ERR
            (#z3_version proof) rule
          val (target,bound)=case find id of
              Z.Rule{rule,premises=[bound],arguments=[],metadata=NONE,
                     conclusion,accepts_bind=true}=>
                if canonical rule="quant-intro" then
                  (tick ();(#node conclusion,bound))
                else pending expected(fn()=>ChildProgramme id)
            | _=>pending expected(fn()=>ChildProgramme id)
          val (saved,body)=case find bound of
              Z.Bind{binding,body,lambda_blocks=[1]}=>
                (tick ();(binding,body))
            | Z.Bind{binding,...}=>
                pending expected(fn()=>BindingProgramme binding)
            | _=>pending expected(fn()=>ChildProgramme bound)
          val child=case find body of
              Z.Rule{rule,premises=[],arguments=[],metadata=NONE,
                     conclusion,...}=>
                if canonical rule="refl" then #node conclusion
                else pending expected(fn()=>ChildProgramme body)
            | _=>pending expected(fn()=>ChildProgramme body)
          val _=pay 5
        in {target=target,saved=saved,child=child,body=body} end)
      val binding=VP.prepare_root_binding_frame_with_policy expected query
        packet (#saved parsed)
    in metadata expected (fn()=>
      let
        val contents=VP.contents_with_policy_for expected query packet
        val context= #context contents
        val graph= #graph original val root= #scope original
        val actual=VP.binding_frame_data_for expected query binding
        val frame= #parent actual
        val inner= #scope actual
        val target= #target parsed val child= #child parsed
        val epoch=Type.type_epoch () val symbols=Term.term_epoch ()
        (* Seventeen local guarded observation/forecast helper closures.
           They are new producer setup, separate from native quotation. *)
        val _=W.spend_policy expected 17
        val packet_guard=VP.prepare_scoped_guard_with_policy_for
          expected query packet
        fun guard ()=
          (packet_guard ();
           NC.validate_for expected native_contract;
           let val held=VP.binding_frame_data_for expected query binding
               val parent=Scope.description_with_policy_for expected frame
           in if Portable.pointer_eq(#context held,context) andalso
               Portable.pointer_eq(#graph held,graph) andalso
               #root held=root andalso #scope held=inner andalso
               #scope parent=root andalso Type.type_epoch ()=epoch andalso
               Term.term_epoch ()=symbols then () else
             raise ERR "guard" "different actual binder lifetime" end;
           PV.usable context root target;PV.usable context inner child)
        fun pay amount=(guard ();W.spend_policy expected amount)
        fun tick ()=pay 1
        val _=guard ()
        val variable=case (#binders actual,#variables actual) of
            (true,[value])=>value
          | _=>pending expected(fn()=>BindingProgramme (#saved parsed))
        val cursor=PV.proof_term context variable
        val variable_node=case PV.proof_graph_reference context cursor of
            SOME held=>
              (tick ();if Portable.pointer_eq(#graph held,graph) andalso
                  G.closure_child_node graph (#scope held)(#child held)=
                    #node held then #node held else
                raise ERR "prepare" "different bound graph identity")
          | NONE=>raise ERR "prepare" "annotation has no genuine Bound ID"
        val atom=case G.view graph variable_node of
            G.Variable(G.Bound,_)=>G.representative graph variable_node
          | _=>raise ERR "prepare" "annotation is not an authentic Bound"
        fun compare_key ((a,b),(c,d))=
          (tick ();case Int.compare(a,c) of EQUAL=>
             (tick ();Int.compare(b,d)) | order=>order)
        fun same a b=compare_key(PV.proof_key context a,
          PV.proof_key context b)=EQUAL
        fun operands constant count value=
          let val _=tick ()
              fun loop current arguments remaining=
                (tick ();case PV.proof_view context current of
                    PV.ProofApplication(f,x)=>
                      if remaining>0 then
                        (pay 2;loop f (x::arguments)(remaining-1)) else NONE
                  | PV.ProofConstant head=>
                      let val a=Term.dest_thy_const head
                          val b=Term.dest_thy_const constant
                          val _=pay(2+IntInf.fromInt(String.size(#Thy a))+
                            IntInf.fromInt(String.size(#Name a))+
                            IntInf.fromInt(String.size(#Thy b))+
                            IntInf.fromInt(String.size(#Name b)))
                      in if remaining=0 andalso
                          Term.same_const head constant then SOME arguments
                        else NONE end
                  | _=>NONE)
          in loop value [] count end
        val child_cursor=PV.proof_term context child
        val _=case operands boolSyntax.equality 2 child_cursor of
            SOME[a,b]=>if same a cursor andalso same b cursor then ()
              else pending expected(fn()=>ChildProgramme (#body parsed))
          | _=>pending expected(fn()=>ChildProgramme (#body parsed))
        fun identity value=
          (tick ();case PV.proof_view context value of
              PV.ProofAbstraction{binder,body,body_frame}=>
                (G.validate_scope graph body_frame;
                 if same binder body then SOME binder else NONE)
            | _=>NONE)
        (* Only the new entry allocates this additional grammar DATA.
           The old Lambda entry retains its original tuple/aliases path. *)
        val prefixes=if quantified then
            (pay 2;SOME(ref NONE))else NONE
        val target_cursor=PV.proof_term context target
        val (left,right,left_binder,right_binder)=
          case operands boolSyntax.equality 2 target_cursor of
              SOME[a,b]=>if quantified then
                  let val _=pay 2
                    fun quantifier value=
                      let val _=pay 2
                          fun identified constant kind=
                            case operands constant 1 value of
                              SOME[abstraction]=>
                                (case identity abstraction of SOME binder=>
                                   let val head=case
                                       PV.proof_view context value of
                                           PV.ProofApplication(head,_)=>head
                                         | _=>raise ERR "prepare"
                                             "quantifier changed"
                                       val _=pay 5
                                   in SOME(kind,binder,abstraction,head)end
                                 | NONE=>NONE)
                              | _=>NONE
                      in case identified boolSyntax.universal
                          SmtReplayBinderClose.Forall of SOME data=>
                          (tick ();SOME data)
                        | NONE=>identified boolSyntax.existential
                            SmtReplayBinderClose.Exists end
                    fun target_binders left right=
                      let val _=pay 2 in
                      case(identity left,identity right)of
                          (SOME a,SOME b)=>(pay 2;(a,b))
                        | _=>(pay 2;
                          case(quantifier left,quantifier right)of
                            (SOME(ka,a,la,ha),SOME(kb,b,lb,hb))=>
                              if ka=kb then
                                (case prefixes of SOME held=>
                                   (pay 9;held:=SOME(ka,la,lb,ha,hb);(a,b))
                                 | NONE=>raise ERR "prepare"
                                     "prefix mode changed")
                              else pending expected
                                (fn()=>TargetProgramme target)
                          | _=>pending expected(fn()=>TargetProgramme target))
                      end
                    val (left,right)=target_binders a b val _=pay 4
                  in(a,b,left,right)end
                else(case(identity a,identity b)of
                  (SOME left,SOME right)=>(tick ();(a,b,left,right))
                | _=>pending expected(fn()=>TargetProgramme target))
            | _=>pending expected(fn()=>TargetProgramme target)
        val (partial_cursor,head_cursor)=case
            PV.proof_view context target_cursor of
              PV.ProofApplication(partial,_)=>
                (case PV.proof_view context partial of
                    PV.ProofApplication(head,_) =>
                      (tick ();(partial,head))
                  | _=>raise ERR "prepare" "equality spine changed")
            | _=>raise ERR "prepare" "equality spine changed"
        val prefix=case prefixes of NONE=>NONE
          | SOME held=>(tick ();!held)
        val kind=case prefix of NONE=>SmtReplayBinderClose.Lambda
          | SOME(kind,_,_,_,_)=>(tick ();kind)
        val native=NC.for_work expected native_contract
        val finite= #semantic_limits native
        val policy=W.semantic_policy expected
        val ceiling=IntInf.fromInt(#type_work_limit native)
        fun weight ty=N.type_weight_using pay (ERR "type") ceiling ty
        val ty=PV.type_of context variable
        val own=weight ty
        fun same_type other=
          let val n=weight other val _=pay(1+own+n)
          in Type.compare(ty,other)=EQUAL end
        val _=if same_type(PV.proof_type_of context left_binder) andalso
            same_type(PV.proof_type_of context right_binder) then () else
          pending expected(fn()=>TargetProgramme target)
        val _=case prefix of NONE=>() | SOME _=>
          if same_type Type.bool then () else
            pending expected(fn()=>TargetProgramme target)
        (* Exact fully unfolded constructor profiles of this actual
           atomic-body programme. Binder-inclusive counts include both
           admitted binder atoms. No unknown body or caller size enters. *)
        (* Three four-field profiles plus record constructors; the 32
           arithmetic operations in these profiles and the invoice below. *)
        val _=pay 47
        val lambda_ty=1+2*own
        val lambda_ann=1+4*own
        val body:N.profile={raw=5,inc=5,ann=6+5*own,ty=1}
        val lambda_law:N.profile={raw=7,inc=9,
          ann=6+3*lambda_ty+2*lambda_ann,ty=1}
        val law:N.profile=case prefix of NONE=>lambda_law | SOME _=>
          (pay 11;{raw=11,inc=13,ann=31,ty=1})
        val bridge:N.profile={raw=3+2* #raw law,inc=3+2* #inc law,
          ann=9+2* #ann law,ty=1}
        fun bound label metadata cap(p:N.profile)=
          (pay 5;if #raw p<=IntInf.fromInt cap andalso
              #inc p<=IntInf.fromInt cap andalso
              RP.allows metadata(#raw p) andalso
              RP.allows metadata(#inc p) andalso #ann p<=ceiling then ()
            else raise ERR "prepare" (label^" exceeds native quota"))
        val _=bound "body input" (#input_limit policy)
          (#input_limit finite) body
        val _=bound "lifted output" (#output_limit policy)
          (#output_limit finite) law
        val _=bound "ALPHA output" (#output_limit policy)
          (#output_limit finite) bridge
        val _=bound "ALPHA template" (#template_limit policy)
          (#template_limit finite) bridge
        fun cost(p:N.profile)=1+ #raw p+ #inc p+ #ann p
        (* REFL input/result; ABS input/result; ALPHA operands/result;
           EQ_MP equation/input/result and empty-Hyp/tag checks. Every
           prospective native input/output is bounded above before debit. *)
        val amount=own+2*cost body+6*cost law+2*cost bridge+32
        val _=if amount<=ceiling then () else
          raise ERR "prepare" "binder Type portfolio exceeds allowance"
        (* AP_TERM's actual operator and ABS input/output are additional
           bounded ports. This path never interprets a general body. *)
        val _=case prefix of NONE=>() | SOME _=>
          let val _=pay 5
              val operator:N.profile={raw=1,inc=1,ann=5,ty=5}
              val _=bound "quantifier operator" (#input_limit policy)
                (#input_limit finite)operator
              val _=bound "quantifier intermediate" (#output_limit policy)
                (#output_limit finite)lambda_law
              val _=bound "quantifier intermediate template"
                (#template_limit policy)(#template_limit finite)lambda_law
              val _=pay 13
              val extra=2*cost lambda_law+cost operator+17
              val _=if amount+extra<=ceiling then () else
                raise ERR "prepare"
                  "quantifier Type portfolio exceeds allowance"
          in pay extra end
        val _=pay amount
        val (spelling,_)=Term.dest_var atom
        val _=pay(1+32*IntInf.fromInt(String.size spelling))
        val _=pay(16+own*own)
        fun arrow left right=
          let val a=weight left val b=weight right
              val _=pay(4+a+b)
          in Type.mk_type("fun",[left,right])end
        val abstraction_type=arrow ty ty
        val body_partial=arrow ty Type.bool
        val body_head=arrow ty body_partial
        val old_law_partial=arrow abstraction_type Type.bool
        val old_law_head=arrow abstraction_type old_law_partial
        val law_partial=case prefix of NONE=>old_law_partial
          | SOME _=>arrow Type.bool Type.bool
        val law_head=case prefix of NONE=>old_law_head
          | SOME _=>arrow Type.bool law_partial
        val bridge_partial=arrow Type.bool Type.bool
        val bridge_head=arrow Type.bool bridge_partial
        (* Each actual syntax occurrence is retained, including repeated
           input/result/Hyp Type ports. This is not a distinct-Type set. *)
        val _=pay 5
        val body_types=[Type.bool,body_partial,body_head,ty,ty]
        val _=pay 9
        val lambda_law_types=[Type.bool,old_law_partial,old_law_head,
          abstraction_type,ty,ty,abstraction_type,ty,ty]
        val law_types=case prefix of NONE=>lambda_law_types | SOME _=>
          let val operator=arrow abstraction_type Type.bool val _=pay 13
          in[Type.bool,law_partial,law_head,
            Type.bool,operator,abstraction_type,ty,ty,
            Type.bool,operator,abstraction_type,ty,ty]end
        fun append [] tail=(guard ();tail)
          | append(value::rest)tail=(pay 2;value::append rest tail)
        val _=pay 3
        val bridge_types=append [Type.bool,bridge_partial,bridge_head]
          (append law_types law_types)
        fun repeats 0 _ tail=(guard ();tail)
          | repeats count values tail=
              (tick ();append values(repeats(count-1)values tail))
        val _=pay 1
        val ordinary_type_ports=ty::repeats 2 body_types
          (repeats 6 law_types(repeats 2 bridge_types []))
        val type_ports=case prefix of NONE=>ordinary_type_ports | SOME _=>
          let val schema=case kind of SmtReplayBinderClose.Forall=>
                  boolSyntax.universal | _=>boolSyntax.existential
              val _=pay 4
              val operator_type=arrow abstraction_type Type.bool
          in append[Term.type_of schema,operator_type]
            (repeats 2 lambda_law_types ordinary_type_ports)end
        val _=pay 6
        val _=ignore(SmtReplayLocalSpecialize.callback_forest
          {visit=tick,type_weight=weight,ceiling=ceiling,
           error=ERR "prepare"}type_ports)
        fun checked other=(guard ();check_type other;guard ())
        fun callbacks []=guard ()
          | callbacks(other::rest)=(tick ();checked other;callbacks rest)
        val _=pay 4
        val abstraction=G.recorded_abstraction_with_policy graph root
          (#template_limit policy)
          {binder=variable_node,body=variable_node,body_frame=inner}
        val quantifier_node=case prefix of NONE=>NONE
          | SOME(_,_,_,head,_)=>
              let val atom=case PV.proof_view context head of
                      PV.ProofConstant atom=>atom
                    | _=>raise ERR "prepare" "quantifier head changed"
                  val _=pay 4
              in SOME(G.constant graph root atom)end
        val closed_endpoint=case quantifier_node of NONE=>abstraction
          | SOME operator=>
              (pay 3;G.application graph root(operator,abstraction))
        val equality_atom=Term.rator(Term.rator(boolSyntax.mk_eq
          (G.representative graph closed_endpoint,
           G.representative graph closed_endpoint)))
        val _=pay(16+ #ann law)
        val head=G.constant graph root equality_atom
        val partial=G.application graph root(head,closed_endpoint)
        val node=G.application graph root(partial,closed_endpoint)
        val _=pay 3
        val _=case PV.corresponds_to_graph_with_policy context graph root
            {value=target,node=node} of PV.Corresponding=>()
          | _=>raise ERR "prepare" "admitted target geometry changed"
        val aliases=case prefix of NONE=>
            (pay 10;
             [(target_cursor,node),(partial_cursor,partial),
              (head_cursor,head),(left,abstraction),(right,abstraction)])
          | SOME(_,la,lb,ha,hb)=>
              let val operator=case quantifier_node of SOME node=>node
                    | NONE=>raise ERR "prepare" "missing quantifier node"
                  val _=pay 18
              in[(target_cursor,node),(partial_cursor,partial),
                (head_cursor,head),(left,closed_endpoint),
                (right,closed_endpoint),(ha,operator),(hb,operator),
                (la,abstraction),(lb,abstraction)]end
        val _=pay 9
        val ports:ports={query=query,context=context,frame=frame,
          binding=binding,native_contract=native_contract,
          statement=target,law_node=node,aliases=aliases}
        fun produce ()=
          let
            val _=guard ()
            (* Fixed native-call argument records/adapters: REFL three;
               BinderClose eight; closed-record programme six. *)
            val _=pay 17
            val _=callbacks type_ports
            val proof=N.primitive_using
              (fn()=>ERR "execute" "wrong fixed reflexivity arity")
              (fn value=>value) (N.ReflexiveName atom) []
            val _=guard ()
            val closed=SmtReplayBinderClose.run (fn value=>value)
              {entries=[(kind,atom)],theorem=proof,
               target=fn()=>(guard ();G.representative graph node)}
            val _=guard ()
          in P.record_closed_with_policy_scoped_profiles graph root
            {node=node,theorem=closed,template_limit= #template_limit policy,
             profiles=[],check_type=checked} end
        (* Five retained fields, the Plan constructor and its once ref. *)
        val _=pay 7
        val result=Plan{work=expected,guard=guard,ports=ports,
          produce=produce,used=ref false}
        val _=guard ()
        val _=pay 1
      in Prepared result end)
    end handle Pending needed=>Needs[needed])

  fun prepare expected query packet options=
    prepare_using false expected query packet options
  fun prepare_quantified expected query packet options=
    prepare_using true expected query packet options

  fun prepare_general expected query packet options=
    ((
      case SmtReplayOwnedScopedValueLift.prepare expected query packet
          options of
          SmtReplayOwnedScopedValueLift.Needs requirements=>
            W.with_step expected(fn()=>
              let val _=GP.validate_query_with_policy expected query
                  val _=ignore(VP.contents_with_policy_for
                    expected query packet)
                  val _=W.spend_policy expected 3
                  fun convert []=[]
                    | convert(missing::rest)=
                        (W.spend_policy expected 3;
                         GeneralProgramme missing::convert rest)
              in Needs(convert requirements)end)
        | SmtReplayOwnedScopedValueLift.Prepared lower=>
            W.with_step expected(fn()=>
              let val _=W.spend_policy expected 1
                  val ports=SmtReplayOwnedScopedValueLift.data_for
                    expected lower
                  val _=W.spend_policy expected 10
                  fun guard()=ignore
                    (SmtReplayOwnedScopedValueLift.data_for expected lower)
                  fun produce()=
                    SmtReplayOwnedScopedValueLift.execute_in_action
                      expected lower
              in Prepared(Plan{work=expected,guard=guard,ports=ports,
                produce=produce,used=ref false})end))
    handle primary=>(W.close expected;raise primary))

  fun execute expected (Plan{work,guard,ports,produce,used}) =
    protected expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "execute" "different original Work";
       W.with_step expected(fn()=>
         let val _=guard ()
             val _=if !used then raise ERR "execute" "used binder plan"
               else(W.spend_policy expected 1;used:=true)
             val fact=produce ()
             val data=Scope.description_with_policy_for expected(#frame ports)
             val _=guard () val _=W.spend_policy expected 9
         in ClosedLaw{work=expected,guard=guard,ports=ports,
           graph= #graph data,scope= #scope data,fact=fact,
           checked_aliases=ref NONE} end)))

  fun validate_lifetime_for expected
      (ClosedLaw{work,guard,ports,graph,scope,checked_aliases,...}) =
    protected expected(fn()=>
      let val _=if Portable.pointer_eq(expected,work)then ()else
            raise ERR "validate_lifetime_for" "different original Work"
          val _=guard ()
          val _=W.spend_policy expected 9
          val stamp=(G.validation_revision graph scope,
            G.scope_retirement_epoch graph scope)
          (* The aliases belong to this packet's private Mapping context.
             Its guard still checks closure/private lexical flags on every
             call. The immutable alias portfolio needs no repeated walk
             until graph publication or retirement changes its backing. *)
          fun aliases []=()
            | aliases((cursor,node)::rest)=
                (W.spend_policy expected 2;
                 ignore(PV.proof_key(#context ports)cursor);
                 ignore(G.closure_root graph scope node);aliases rest)
          val _=if !checked_aliases=SOME stamp then ()else
            aliases(#aliases ports)
          val _=W.spend_policy expected 6
          val after=(G.validation_revision graph scope,
            G.scope_retirement_epoch graph scope)
          val _=checked_aliases:=if after=stamp then SOME stamp else NONE
      in ignore(G.closure_root graph scope(#law_node ports))end)

  fun data_for expected (ClosedLaw{work,guard,ports,graph,scope,fact,...}) =
    protected expected(fn()=>
      let val _=if Portable.pointer_eq(expected,work)then ()else
            raise ERR "data_for" "different original Work"
          val _=guard ()
          val _=NC.for_work expected(#native_contract ports)
          (* The fact retains its authentic Scope policy cap. Native input,
             output/template and Type quotas were checked by this receipt's
             actual producer under the same retained NC above. *)
          (* Frame projection, two argument fields and their record. *)
          val _=W.spend_policy expected 4
          val _=P.validate_closed_fact_in_scope_with_policy_for expected
            {frame= #frame ports,fact=fact}
          fun aliases []=guard ()
            | aliases((cursor,node)::rest)=
                (guard ();W.spend_policy expected 2;
                 ignore(PV.proof_key(#context ports)cursor);
                 ignore(G.closure_root graph scope node);aliases rest)
          val _=aliases(#aliases ports)
          val _=W.spend_policy expected 10
      in {query= #query ports,context= #context ports,frame= #frame ports,
        binding= #binding ports,native_contract= #native_contract ports,
        statement= #statement ports,law_node= #law_node ports,fact=fact,
        aliases= #aliases ports}end)
end
