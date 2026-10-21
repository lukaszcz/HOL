(* Retained specialization and an explicit bounded App syntax image. *)
structure SmtReplayOwnedValueSpecialize :> SmtReplayOwnedValueSpecialize =
struct
  structure W=SmtReplayInvocationWork
  structure G=SmtReplayGraph
  structure S=SmtReplaySource
  structure GP=SmtLib_GraphPreprocess
  structure VP=SmtLib_GraphValueProof
  structure PV=SmtLib_GraphParserValue
  structure Scope=SmtReplayOwnedScopeReceipt
  structure NC=SmtReplayNativeContract
  structure N=SmtReplayNamedContext
  structure P=SmtReplayProof
  structure RP=SmtReplayResourcePolicy
  val ERR=Feedback.mk_HOL_ERR "SmtReplayOwnedValueSpecialize"
  datatype requirement = RetainedOriginalSource of PV.value
    | AtomicFalseOperand of PV.value
    | SourceInstance of PV.value
    | ArgumentProgramme of PV.value list
    | SourceProfile of G.scope * G.node
    | RetainedOperand of PV.value
  type ports={query:GP.graph_query,context:PV.context,frame:Scope.receipt,
    native_contract:NC.contract,source:PV.proof_term,
    arguments:PV.proof_term list,target:PV.proof_term,statement:PV.value,
    source_node:G.node,target_node:G.node,original_occurrences:int list}
  datatype plan=Plan of {work:W.portfolio,guard:unit -> unit,ports:ports,
    produce:unit -> P.closed_fact,used:bool ref}
  datatype closed_law=ClosedLaw of {work:W.portfolio,guard:unit -> unit,
    ports:ports,graph:G.graph,scope:G.scope,fact:P.closed_fact}
  datatype preparation=Prepared of plan | Needs of requirement list
  exception MissingProfile of G.scope * G.node
  fun protected expected action=action()
    handle primary=>(W.close expected;raise primary)
  exception UnsupportedInstance
  (* Private syntax image, never a Source or a theorem. Only the bounded
     actual Value constructor compiler below can mint this token. *)
  datatype target_image=TargetImage of
    {work:W.portfolio,query:GP.graph_query,context:PV.context,
     target:PV.value,native_contract:NC.contract,graph:G.graph,
     scope:G.scope,node:G.node,guard:unit -> unit}
  fun validate_target_image expected query context contract target
      (TargetImage{work,query=owner,context=held,target=actual,
        native_contract,graph,scope,node,guard})=
    protected expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "target_image" "different original Work";
       W.spend_policy expected 10;
       if Portable.pointer_eq(query,owner)andalso
           Portable.pointer_eq(context,held)andalso
           Portable.pointer_eq(contract,native_contract)andalso
           target=actual then ()else
         raise ERR "target_image" "different actual target owner";
       guard()))
  fun target_image_node expected query context contract target
      (image as TargetImage{graph,scope,node,...})=
    (validate_target_image expected query context contract target image;
     W.spend_policy expected 3;
     case PV.corresponds_to_graph_with_policy context graph scope
         {value=target,node=node}of
         PV.Corresponding=>node
       | _=>raise ERR "target_image" "actual target image changed")

  fun prepare_using_image image retained expected query packet
      {source,arguments,target,profiles,native_contract,check_type}=
    protected expected(fn()=>
    let
      (* Owning query getter runs before the action and before the held
         packet. No arbitrary frame or replacement counter is accepted. *)
      val current=GP.query_nodes_with_policy_for expected query
      val original=W.original_sources expected
      val graph=S.owning_graph original val scope=S.owning_scope original
      val _=if Portable.pointer_eq(#graph current,graph)andalso
          #scope current=scope andalso
          Portable.pointer_eq(#sources current,original)then ()else
        raise ERR "prepare" "different actual original Source frame"
      val _=NC.validate_for expected native_contract
      val frame=Scope.root_with_policy expected
    in W.with_step expected(fn()=>
      let
        val contents=VP.contents_with_policy_for expected query packet
        val context= #context contents
        val epoch=Type.type_epoch()val symbols=Term.term_epoch()
        fun guard()=
          (ignore(VP.contents_with_policy_for expected query packet);
           NC.validate_for expected native_contract;
           let val held=Scope.description_with_policy_for expected frame
           in if Portable.pointer_eq(#graph held,graph)andalso
               #scope held=scope andalso
               Portable.pointer_eq(#sources held,original)andalso
               Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
             then ()else raise ERR "guard" "original owner changed"end;
           PV.validate_for context graph scope;
           PV.usable context scope source;PV.usable context scope target;
           List.app(fn value=>
             (PV.spend context 1;PV.usable context scope value))arguments;
           case image of NONE=>()|SOME held=>
             validate_target_image expected query context native_contract
               target held)
        fun pay amount=(guard();W.spend_policy expected amount)
        fun tick()=pay 1
        fun map action []=(guard();[])
          | map action(value::rest)=
              (pay 2;action value::map action rest)
        fun reverse values=
          let fun loop [] result=(guard();result)
                | loop(value::rest)result=
                    (pay 2;loop rest(value::result))
          in loop values []end
        val _=map(PV.usable context scope)arguments
        val pending=ref([]:requirement list)
        fun need row=(pay 2;pending:=row:: !pending)
        fun backing value=PV.proof_graph_reference context
          (PV.proof_term context value)
        fun actual value=case backing value of NONE=>NONE|SOME held=>
          (tick();if Portable.pointer_eq(#graph held,graph)andalso
              G.closure_child_node graph (#scope held)(#child held)= #node held
              andalso G.scope_visible graph scope
                (G.node_scope graph(#node held))then SOME(#node held)else
            raise ERR "prepare" "foreign retained graph backing")
        fun atomic_false value=
          (tick();case PV.proof_view context(PV.proof_term context value)of
              PV.ProofConstant atom=>
                if Term.same_const atom boolSyntax.F then
                  (case actual value of SOME node=>
                     (case G.view graph node of G.Constant _=>SOME node
                       | _=>raise ERR "prepare" "constant backing changed")
                   | NONE=>(need(AtomicFalseOperand value);NONE))
                else(need(AtomicFalseOperand value);NONE)
            | _=>(need(AtomicFalseOperand value);NONE))
        val source_node=actual source
        val occurrences=ref([]:int list)
        fun originals [] _=guard()
          | originals(node::rest)index=
              (tick();case source_node of SOME actual=>
                 (if node=actual then
                    (pay 2;occurrences:=index:: !occurrences)else();
                  originals rest(index+1))
               | NONE=>originals rest(index+1))
        val _=originals(S.assumption_nodes original)0
        val _=if null(!occurrences)then need(RetainedOriginalSource source)
          else()
        fun retained_operand value=case actual value of SOME node=>SOME node
          | NONE=>(need(RetainedOperand value);NONE)
        fun retained_arguments []=(guard();[])
          | retained_arguments(value::rest)=
              let val _=pay 2 val held=retained_operand value
                  val tail=retained_arguments rest
              in case held of NONE=>tail|SOME node=>node::tail end
        val arg_nodes=if retained then
            (if null arguments then need(ArgumentProgramme arguments)else();
             retained_arguments arguments)
          else case arguments of [one]=>
              (case atomic_false one of SOME node=>[node]|NONE=>[])
          | _=>(need(ArgumentProgramme arguments);[])
        val target_node=if retained then
            (case image of NONE=>retained_operand target
             | SOME held=>(W.spend_policy expected 1;
                 SOME(target_image_node expected query context
                   native_contract target held)))
          else atomic_false target
        fun universal node=(tick();case G.view graph node of
            G.Application(head,_)=>
              (case G.view graph head of G.Constant _=>
                 Term.same_const(G.representative graph head)
                   boolSyntax.universal | _=>false)
          | _=>false)
        val _=case source_node of SOME node=>
              if universal node then()else need(RetainedOriginalSource source)
          | NONE=>()
        val native=NC.for_work expected native_contract
        val ceiling=IntInf.fromInt(#type_work_limit native)
        val limits= #semantic_limits native
        val policy=W.semantic_policy expected
        val captures=ref([]:G.profiled_metric list)
        fun valid()=
          (guard();List.app(fn capture=>
            (tick();ignore(G.profiled_metric_data graph scope capture)))
              (!captures))
        fun profile_for requester node=
          let fun seek []=raise MissingProfile(requester,node)
                | seek(profile::rest)=
                    (tick();case G.opaque_profile_for_node_with_policy
                        graph requester node profile of
                       SOME data=>data|NONE=>seek rest)
          in seek profiles end
        val memo=ref([]:((G.scope * G.node) * N.profile)list)
        fun find _ []=NONE
          | find(requester,node)(((held,actual),p)::rest)=
              (pay 2;if requester=held andalso node=actual then SOME p
               else find(requester,node)rest)
        fun shape requester node=case find(requester,node)(!memo)of
            SOME p=>p|NONE=>
              let
                val _=tick()
                val own=N.type_weight_using pay(ERR "type")ceiling
                  (G.type_of graph node)
                val p:N.profile=case G.view graph node of
                    G.OpaqueRetained=>
                      let val data=profile_for requester node
                      in if #ty data=own then
                        {raw= #raw data,inc= #inc data,
                         ann= #ann data,ty=own}else
                        raise ERR "prepare" "opaque Type annotation changed"
                      end
                  | G.Application(f,x)=>
                      let val a=shape requester f val b=shape requester x
                      in {raw=1+ #raw a+ #raw b,inc=1+ #inc a+ #inc b,
                        ann=own+ #ann a+ #ann b,ty=own}end
                  | G.AdmittedBinder _=>
                      let val data=G.binder_closure_data graph requester
                            (G.binder_closure graph requester node)
                          val body=shape(#body_frame data)(#body data)
                          val binder=N.type_weight_using pay(ERR "type")
                            ceiling(G.type_of graph(#binder data))
                      in {raw=1+ #raw body,inc=2+ #inc body,
                        ann=own+binder+ #ann body,ty=own}end
                  | _=>{raw=1,inc=1,ann=own,ty=own}
                val _=pay 2 val _=memo:=((requester,node),p):: !memo
              in p end
        fun bounded label maximum cap(p:N.profile)=
          if #raw p<=IntInf.fromInt cap andalso
              #inc p<=IntInf.fromInt cap andalso
              RP.allows maximum(#raw p)andalso RP.allows maximum(#inc p)
              andalso #ann p<=ceiling then ()else
            raise ERR "prepare" label
        fun geometry node maximum cap=
          let val p=shape scope node
              val _=bounded "actual retained operand exceeds native cap"
                maximum cap p
              val captured=G.prepare_scoped_profiled_metric_observed graph
                scope{node=node,profiles=profiles,observe=tick}
              val measured=G.profiled_metric_data graph scope captured
              val _=if #raw measured= #raw p andalso
                  #inc measured= #inc p then ()else
                raise ERR "prepare" "actual retained geometry changed"
              val _=pay 2 val _=captures:=captured:: !captures
          in p end
        fun preflight source_node target_node arg_node=
          let
            val a=geometry source_node(#input_limit policy)
              (#input_limit limits)
            val b=geometry target_node(#output_limit policy)
              (#output_limit limits)
            val _=ignore(geometry arg_node(#input_limit policy)
              (#input_limit limits))
            val law:N.profile={raw=3+ #raw a+ #raw b,
              inc=3+ #inc a+ #inc b,ann=9+ #ann a+ #ann b,ty=1}
            val _=bounded "actual local law exceeds output cap"
              (#output_limit policy)(#output_limit limits)law
            val _=bounded "actual local law exceeds template cap"
              (#template_limit policy)(#template_limit limits)law
          in ()end
        (* General retained inputs are bounded as genuine graph operands
           BEFORE public native syntax is opened. Substitution and its
           repeated Type/Hyp portfolios use the SAME local SPEC predictor. *)
        fun retained_preflight source_node target_node arg_nodes=
          let
            val first_graph=geometry source_node(#input_limit policy)
              (#input_limit limits)
            val target_graph=geometry target_node(#output_limit policy)
              (#output_limit limits)
            val arguments_graph=map(fn node=>geometry node
              (#input_limit policy)(#input_limit limits))arg_nodes
            val law:N.profile={raw=3+ #raw first_graph+ #raw target_graph,
              inc=3+ #inc first_graph+ #inc target_graph,
              ann=9+ #ann first_graph+ #ann target_graph,ty=1}
            val _=bounded "actual local law exceeds output cap"
              (#output_limit policy)(#output_limit limits)law
            val _=bounded "actual local law exceeds template cap"
              (#template_limit policy)(#template_limit limits)law
            val original=G.representative graph source_node
            val target=G.representative graph target_node
            val arguments=map(G.representative graph)arg_nodes
            val _=pay 2
            val type_ports=ref([]:Type.hol_type list)
            val profile=SmtReplayLocalSpecialize.native_profile
              {tick=fn()=>pay 4,type_weight=N.type_weight_using pay(ERR "type")
                 ceiling,type_seen=fn ty=>
                   (pay 3;type_ports:=ty:: !type_ports),
               input=IntInf.fromInt(#input_limit limits),
               output=IntInf.fromInt(#output_limit limits),
               template=IntInf.fromInt(#template_limit limits),
               ceiling=ceiling,error=ERR "native_profile"}
            fun same_profile(a:N.profile,b:N.profile)=
              (pay 4;#raw a= #raw b andalso #inc a= #inc b andalso
               #ann a= #ann b andalso #ty a= #ty b)
            fun weight(p:N.profile)= #raw p+ #inc p+ #ann p
            (* Opening every admitted Abs during a complete native pass can
               rebuild each nested body. The squared whole annotation/
               structure weight bounds that metadata reconstruction. *)
            fun quote_reconstruction(p:N.profile)=
              let val n=weight p in pay(1+n*n)end
            fun measured term expected=
              let val _=quote_reconstruction expected
                  val actual=profile term
              in if same_profile(actual,expected)then actual else
                raise ERR "prepare" "retained native profile changed"end
            val first=measured original first_graph
            val _=measured target target_graph
            fun argument_profiles [] []=(guard();[])
              | argument_profiles(term::rest)(shape::more)=
                  (pay 2;measured term shape::argument_profiles rest more)
              | argument_profiles _ _=raise ERR "prepare"
                  "retained argument inventory changed"
            val profiles=argument_profiles arguments arguments_graph
            fun sum [] total=(guard();total)
              | sum(p::rest)total=(tick();sum rest(total+weight p))
            fun charge result inputs hypotheses=
              let val amount=sum hypotheses(sum inputs(1+weight result))
              in if amount<=ceiling then
                  (quote_reconstruction result;pay(amount+20))else
                raise ERR "prepare" "local native Type portfolio exceeded"
              end
            fun in_bound p=bounded "local input exceeds native cap"
              (#input_limit policy)(#input_limit limits)p
            fun out_bound p=bounded "local output exceeds native cap"
              (#output_limit policy)(#output_limit limits)p
            fun variable_compare(a,b)=
              let val _=pay 2
                  val (left,_)=Term.dest_var a
                  val (right,_)=Term.dest_var b
                  val _=pay(1+IntInf.fromInt(String.size left)+
                    IntInf.fromInt(String.size right))
              in Term.var_compare(a,b)end
            fun forall term=
              let val _=tick()
                  (* forecast just cached this exact current term before
                     its forall destructor. Pay the fresh body pass too. *)
                  val _=quote_reconstruction(profile term)
              in boolSyntax.dest_forall term
                handle Feedback.HOL_ERR _=>raise UnsupportedInstance end
            (* Native alpha comparison is bounded above already. Charge
               repeated atom spelling as well as structural/Type work;
               equal printed names alone never authenticate a Value port. *)
            val _=tick()
            val spellings=ref([]:(Term.term * IntInf.int)list)
            fun find_spelling _ []=NONE
              | find_spelling term((held,n)::rest)=
                  (tick();if Portable.pointer_eq(term,held)then SOME n
                   else find_spelling term rest)
            fun spelling term=case find_spelling term(!spellings)of
                SOME n=>n|NONE=>
                let
                  val _=tick()
                  val n=if Term.is_comb term then
                      let val(a,b)=Term.dest_comb term
                      in spelling a+spelling b end
                    else if Term.is_abs term then
                      let val(a,b)=Term.dest_abs term
                      in spelling a+spelling b end
                    else if Term.is_var term then
                      let val(name,_)=Term.dest_var term
                      in IntInf.fromInt(String.size name)end
                    else if Term.is_const term then
                      let val data=Term.dest_thy_const term
                      in IntInf.fromInt(String.size(#Thy data))+
                        IntInf.fromInt(String.size(#Name data))end
                    else raise ERR "prepare" "unknown admitted syntax"
                  val _=pay(2+n)val _=spellings:=(term,n):: !spellings
                in n end
            fun quoted_spelling term=
              let val _=quote_reconstruction(profile term)
              in spelling term end
            fun substitute(variable,arg,body)=
              let
                val bp=profile body val ap=profile arg
                val bytes=quoted_spelling body+quoted_spelling arg
                (* Quote the bounded native substitution and its variable
                   comparisons before the SAME public substitution call. *)
                val amount=(1+ #raw bp)*(1+ #raw ap)*
                  (1+bytes+ #ann bp+ #ann ap)
                val _=pay amount
              in Term.subst[{redex=variable,residue=arg}]body end
            val _=charge first[][first]
            fun quote_occurrence_setup []=guard()
              | quote_occurrence_setup(_::rest)=
                  (pay 2;quote_occurrence_setup rest)
            val _=quote_occurrence_setup profiles
            val (predicted,_)=SmtReplayLocalSpecialize.forecast_using
              {dest_forall=forall,substitute=substitute}
              {profile=profile,tick=fn()=>pay 4,pay=pay,in_bound=in_bound,
               out_bound=out_bound,charge=charge,first=first,
               variable_compare=variable_compare,
               error=fn _=>UnsupportedInstance}original arguments profiles
            val predicted_profile=profile predicted
            val target_profile=profile target
            val amount=1+weight predicted_profile+weight target_profile+
              quoted_spelling predicted+quoted_spelling target
            val _=pay amount
            val _=if Term.aconv predicted target then()else
              raise UnsupportedInstance
            fun law_bound p=
              (out_bound p;bounded "local law exceeds native template cap"
                (#template_limit policy)(#template_limit limits)p)
            val {law=law_profile,...}=
              SmtReplayLocalSpecialize.close_forecast
                {out_bound=out_bound,law_bound=law_bound,charge=charge}
                {first=first,final=target_profile}
            (* Only this prospectively admitted binder-free implication is
               constructed as metadata. It grants no closed proof. Retain
               its actual Types in the SAME native callback forest. *)
            val _=pay(3+weight law_profile)
            val implication=G.constant graph scope boolSyntax.implication
            val law_node=G.application graph scope
              (G.application graph scope(implication,source_node),target_node)
            val actual_law=G.representative graph law_node
            val _=quote_reconstruction law_profile
            val measured_law=profile actual_law
            val _=if same_profile(measured_law,law_profile)then()else
              raise ERR "prepare" "actual local law profile changed"
            val types=reverse(!type_ports)
            val _=SmtReplayLocalSpecialize.callback_forest
              {visit=tick,type_weight=N.type_weight_using pay(ERR "type")
                 ceiling,ceiling=ceiling,error=ERR "prepare"}types
          in ()end
        val _=if null(!pending)then
            ((if retained then
                (case(source_node,target_node)of
                   (SOME a,SOME b)=>retained_preflight a b arg_nodes
                 | _=>raise ERR "prepare" "private retained inventory changed")
              else case(source_node,target_node,arg_nodes)of
              (SOME a,SOME b,[c])=>
                ((preflight a b c;
                  (* First genuine programme: after actual unfolded and
                     annotated native admission, inspect only the retained
                     bounded original. No substitution or binder is built.
                     Other universal bodies keep their typed requirement
                     before any authorizing native block is created. *)
                  let val measured=shape scope a
                  in if #raw measured<>4 orelse #inc measured<>5 then
                      need(SourceInstance source)else
                    let val _=pay 3
                        val original=G.representative graph a
                        val abstraction=Term.rand original
                    in if Term.is_abs abstraction then
                        let val _=pay 4
                            val (binder,body)=Term.dest_abs abstraction
                        in if Type.compare(Term.type_of binder,Type.bool)
                            =EQUAL andalso Term.is_var body then
                            let val _=pay 2
                                val (left,_)=Term.dest_var binder
                                val (right,_)=Term.dest_var body
                                val _=pay(1+IntInf.fromInt(String.size left)+
                                  IntInf.fromInt(String.size right))
                            in if Term.aconv binder body then()else
                              need(SourceInstance source)end
                          else need(SourceInstance source)end
                      else need(SourceInstance source)end
                  end)
                    handle MissingProfile missing=>
                      need(SourceProfile missing))
            | _=>raise ERR "prepare" "private operand inventory changed")
              handle MissingProfile missing=>need(SourceProfile missing)
                | UnsupportedInstance=>need(SourceInstance source))
          else()
      in if not(null(!pending))then Needs(reverse(!pending))else
        let
          val source_node=valOf source_node val target_node=valOf target_node
          fun checked ty=(valid();check_type ty;valid())
          fun produce()=
            let
              val frontier=P.prepare_realization_frontier_with_policy
                expected
                {frame=frame,roots=[source_node,target_node],
                 closed_facts=[],conversions=[]}
              val tables=P.prepare_owned_realization_tables_with_policy
                expected frontier
              val ordinal=W.unused_policy_ordinal expected
                {role=W.FinalFreeze,minimum=0}
              val frozen=P.prepare_native_realization_freeze_with_policy
                expected
                {tables=tables,contract=native_contract,profiles=profiles,
                 ordinal=ordinal,check_type=checked}
              val block=P.freeze_owned_realization_tables_with_policy expected
                frozen
              val specialized=P.prepare_local_specialize_schema_with_policy
                expected block{source=source_node,arguments=arg_nodes,
                  target=target_node,profiles=profiles,check_type=checked}
              val fact=P.execute_local_specialize_with_policy expected
                specialized
              val _=valid()
              val _=P.retire_policy_block_for expected block
            in fact end
          val implication=PV.literal context scope(RP.AtMost 1)
            boolSyntax.implication
          val statement=PV.application context scope
            (PV.application context scope(implication,source),target)
          val ports:ports={query=query,context=context,frame=frame,
            native_contract=native_contract,
            source=PV.proof_term context source,
            arguments=map(PV.proof_term context)arguments,
            target=PV.proof_term context target,statement=statement,
            source_node=source_node,target_node=target_node,
            original_occurrences=reverse(!occurrences)}
          val _=valid()val _=pay 3
        in Prepared(Plan{work=expected,guard=valid,ports=ports,
          produce=produce,used=ref false})end
      end)
    end)
  fun prepare_using retained expected query packet options=
    prepare_using_image NONE retained expected query packet options
  fun prepare expected query packet options=
    prepare_using false expected query packet options
  fun prepare_retained expected query packet options=
    prepare_using true expected query packet options
  (* Explicit ordinary-App compatibility boundary. No native import,
     abstraction, free-variable reconstruction or theorem is produced.
     Source/argument admission and SPEC prediction remain the old worker. *)
  exception UnsupportedTargetImage
  fun prepare_retained_application expected query packet
      (options as {source,arguments,target,profiles,native_contract,
        check_type})=
    protected expected(fn()=>
    let
      val first=prepare_retained expected query packet options
      val _=W.with_step expected(fn()=>W.spend_policy expected 2)
    in case first of Needs[RetainedOperand actual]=>
      if actual<>target then first else
      let
        val current=GP.query_nodes_with_policy_for expected query
        val graph= #graph current val scope= #scope current
        val _=NC.validate_for expected native_contract
        val frame=Scope.root_with_policy expected
        val image=W.with_step expected(fn()=>
          let
            val contents=VP.contents_with_policy_for expected query packet
            val context= #context contents
            val _=W.spend_policy expected 58
            val type_error=ERR "target_type"
            val epoch=Type.type_epoch()val symbols=Term.term_epoch()
            val native=NC.for_work expected native_contract
            val limits= #semantic_limits native
            val policy=W.semantic_policy expected
            val ceiling=IntInf.fromInt(#type_work_limit native)
            fun restrict RP.Uncapped bound=bound
              | restrict(RP.AtMost actual)bound=IntInf.min(actual,bound)
            val maximum=restrict(#output_limit policy)
              (restrict(#template_limit policy)
                (IntInf.fromInt(Int.min(#output_limit limits,
                  #template_limit limits))))
            fun guard()=
              (ignore(VP.contents_with_policy_for expected query packet);
               NC.validate_for expected native_contract;
               let val held=Scope.description_with_policy_for expected frame
               in if Portable.pointer_eq(#graph held,graph)andalso
                   #scope held=scope andalso
                   Portable.pointer_eq(#sources held,#sources current)
                   andalso Type.type_epoch()=epoch andalso
                   Term.term_epoch()=symbols then ()else
                 raise ERR "target_image" "actual target frame changed"end;
               PV.validate_for context graph scope;
               PV.usable context scope target)
            fun pay amount=(guard();W.spend_policy expected amount)
            fun tick()=pay 1
            fun fail message=raise ERR "target_image" message
            fun type_work ty=N.type_weight_using pay type_error
              ceiling ty
            fun same_type a b=
              let val x=type_work a val y=type_work b
                  val _=pay(1+x+y)
              in Type.compare(a,b)=EQUAL end
            fun weight(p:N.profile)= #raw p+ #inc p+ #ann p
            fun bound(p:N.profile)=
              if #raw p<=maximum andalso #inc p<=maximum andalso
                  #ann p<=ceiling andalso
                  RP.allows(#output_limit policy)(#raw p)andalso
                  RP.allows(#output_limit policy)(#inc p)andalso
                  RP.allows(#template_limit policy)(#raw p)andalso
                  RP.allows(#template_limit policy)(#inc p)then ()else
                fail "ordinary target image exceeds actual native cap"
            fun plus maximum a b=IntInf.min(maximum+1,a+b)
            fun compare((a,b),(c,d))=
              (pay 2;case Int.compare(a,c)of EQUAL=>Int.compare(b,d)
                | order=>order)
            datatype tree=Tree of
              {id:int,shape:N.shape,profile:N.profile,
               ty:Type.hol_type,syntax:syntax}
            and syntax=Existing of G.node | Constant of Term.term
              | App of tree * tree
            val memo=ref(Redblackmap.mkDict compare)
            val ordered=ref([]:tree list)val next=ref 0
            val observations=ref(0:IntInf.int)
            val atoms=ref([]:(Term.term * N.profile)list)
            fun parts(Tree data)=data
            fun profile tree= #profile(parts tree)
            fun publish key shape ty p syntax=
              let val _=bound p val _=pay 15 val id= !next
                  val tree=Tree{id=id,shape=shape,profile=p,
                    ty=ty,syntax=syntax}
                  val _=next:=id+1 val _=ordered:=tree:: !ordered
                  val _=memo:=Redblackmap.insert(!memo,key,tree)
              in tree end
            fun leaf key ty atom syntax=
              let val own=type_work ty
                  val _=if same_type(Term.type_of atom)ty then ()else
                    fail "actual atom Type differs"
                  val _=pay 5
                  val p:N.profile={raw=1,inc=1,ann=own,ty=own}
                  val _=bound p val _=pay 4
                  val _=atoms:=(atom,p):: !atoms
                  val _=tick()
              in publish key(N.HeldSyntax atom)ty p syntax end
            fun build cursor=
              let
                val _=tick()
                val key=PV.proof_key context cursor
              in case Redblackmap.peek(!memo,key)of SOME tree=>tree
                | NONE=>
                  let
                    (* Distinct syntax is itself a genuine lower bound on
                       unfolded raw size. Admit every new visit before its
                       children as well as every saturated result below. *)
                    val _=pay 4
                    val _=observations:= !observations+1
                    val _=if !observations<=maximum then ()else
                      fail "ordinary target image exceeds actual native cap"
                    val ty=PV.proof_type_of context cursor
                    val own=type_work ty
                  in case PV.proof_view context cursor of
                      PV.ProofVariable(G.Bound,_)=>
                        raise UnsupportedTargetImage
                    | PV.ProofVariable _=>
                        (case PV.proof_graph_reference context cursor of
                           NONE=>raise UnsupportedTargetImage
                         | SOME held=>
                             let val _=pay 6
                                 val _=if Portable.pointer_eq
                                     (#graph held,graph)then ()else
                                   fail "foreign actual variable owner"
                                 val node=G.closure_child_node graph
                                   (#scope held)(#child held)
                                 val _=if node= #node held andalso
                                     G.scope_visible graph scope
                                       (G.node_scope graph node)then ()else
                                   fail "foreign actual variable backing"
                                 val _=case G.view graph node of
                                     G.Variable(G.Bound,_)=>
                                       raise UnsupportedTargetImage
                                   | G.Variable _=>()
                                   | _=>fail "actual variable backing differs"
                                 val atom=G.representative graph node
                                 val _=tick()
                             in leaf key ty atom(Existing node)end)
                    | PV.ProofConstant atom=>
                        if Term.is_const atom then
                          (tick();leaf key ty atom(Constant atom))
                        else raise UnsupportedTargetImage
                    | PV.ProofApplication(f,x)=>
                        let val a=build f val b=build x
                            val ap=profile a val bp=profile b
                            val _=pay 5
                            val p:N.profile=
                              {raw=plus maximum 1
                                 (plus maximum(#raw ap)(#raw bp)),
                               inc=plus maximum 1
                                 (plus maximum(#inc ap)(#inc bp)),
                               ann=plus ceiling own
                                 (plus ceiling(#ann ap)(#ann bp)),ty=own}
                            val _=bound p val _=pay 5
                        in publish key(N.ApplicationSyntax
                          (#shape(parts a),#shape(parts b)))ty p(App(a,b))end
                    | _=>raise UnsupportedTargetImage
                  end
              end
            val original=PV.proof_term context target
            val _=case PV.proof_view context original of
                PV.ProofApplication _=>()|_=>raise UnsupportedTargetImage
            val root=build original
            fun atom_profile term=
              (tick();let fun find []=fail "unregistered actual target atom"
                    | find((held,p)::rest)=
                        (tick();if Portable.pointer_eq(term,held)then p
                         else find rest)
              in find(!atoms)end)
            fun observe shape=pay(case shape of N.HeldSyntax _=>2
              | N.ApplicationSyntax _=>7|N.EqualitySyntax _=>8)
            (* The first shared scalar pass is saturated and DAG-memoized.
               Only after its real cap admission does the SAME shared
               exact expression walker visit unfolded incidences. *)
            val(p,ty)=N.describe_shape observe atom_profile
              type_work same_type(#shape(parts root))
            val measured=profile root val _=pay 5
            val _=if #raw p= #raw measured andalso
                #inc p= #inc measured andalso #ann p= #ann measured andalso
                #ty p= #ty measured andalso same_type ty(#ty(parts root))
              then ()else fail "actual target shape changed"
            val _=bound p
            fun quote [] total=(tick();total)
              | quote(tree::rest)total=
                  let val _=tick()
                      val amount=case #syntax(parts tree)of Existing _=>1
                        | Constant _=>2+weight(profile tree)
                        | App(a,b)=>3+weight(profile tree)+
                            weight(profile a)+weight(profile b)
                  in quote rest(total+amount)end
            val amount=quote(!ordered)0
            val _=pay amount
            val _=pay(4+IntInf.fromInt(!next))
            val nodes=Array.array(!next,NONE:G.node option)
            fun get tree=
              (pay 3;case Array.sub(nodes,#id(parts tree))of
                 SOME node=>node|NONE=>fail "forward target image reference")
            fun realize []=(guard();())
              | realize(tree::rest)=
                  let val _=guard()val _=pay 4
                      val node=case #syntax(parts tree)of
                          Existing node=>node
                        | Constant atom=>G.constant graph scope atom
                        | App(a,b)=>(tick();
                            G.application graph scope(get a,get b))
                      val _=ignore(G.closure_root graph scope node)
                      val _=pay 2
                      val _=Array.update(nodes,#id(parts tree),SOME node)
                  in realize rest end
            fun reverse [] result=(tick();result)
              | reverse(x::rest)result=(pay 2;reverse rest(x::result))
            val _=realize(reverse(!ordered)[])
            val node=get root
            val _=pay 3
            val _=case PV.corresponds_to_graph_with_policy context graph
                scope{value=target,node=node}of PV.Corresponding=>()
              | _=>fail "constructed target changed actual free identities"
            val _=pay 6
            val lifetime=PV.prepare_lifetime_guard context
              {remaining_work=fn()=>W.remaining_policy expected,
               scopes=[scope],values=[target]}
            val lifetime_work=PV.lifetime_guard_work lifetime
            val child=G.closure_root graph scope node
            fun held_guard()=
              (guard();W.spend_policy expected lifetime_work;
               PV.validate_lifetime_guard lifetime;
               ignore(G.closure_child_node graph scope child))
            val _=held_guard()val _=pay 12
          in SOME(TargetImage{work=expected,query=query,context=context,
            target=target,native_contract=native_contract,graph=graph,
            scope=scope,node=node,guard=held_guard})end
          handle UnsupportedTargetImage=>NONE)
      in case image of NONE=>first|SOME held=>
        prepare_using_image(SOME held)true expected query packet options
      end
    | _=>first end)

  fun execute expected(saved as Plan{work,...})=protected expected(fn()=>
    (if Portable.pointer_eq(expected,work)then ()else
       raise ERR "execute" "different original Work";
     W.with_step expected(fn()=>
      let val Plan{guard,ports,produce,used,...}=saved
          val _=guard()val _=W.spend_policy expected 2
          val _=if !used then raise ERR "execute" "used specialization"
            else used:=true
          val fact=produce()
          val _=guard()
          val data=Scope.description_with_policy_for expected(#frame ports)
          val graph= #graph data val scope= #scope data
          val law=P.closed_node fact
          val _=case PV.corresponds_to_graph_with_policy(#context ports)
              graph scope{value= #statement ports,node=law}of
                PV.Corresponding=>()|_=>raise ERR "execute"
                  "actual closed law cursor differs"
          val _=guard()val _=W.spend_policy expected 3
      in ClosedLaw{work=expected,guard=guard,ports=ports,
        graph=graph,scope=scope,fact=fact}end)))
  fun data_for expected(saved as ClosedLaw{work,...})=protected expected
    (fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "data" "different original Work";
       let val ClosedLaw{guard,ports,graph,scope,fact,...}=saved
           val _=guard()val _=W.spend_policy expected 2
           val _=P.validate_closed_fact_in_scope_with_policy_for expected
             {frame= #frame ports,fact=fact}
           val law=P.closed_node fact
           val _=ignore(G.closure_root graph scope law)
           val _=guard()
       in {query= #query ports,context= #context ports,frame= #frame ports,
         native_contract= #native_contract ports,source= #source ports,
         arguments= #arguments ports,target= #target ports,
         statement= #statement ports,source_node= #source_node ports,
         target_node= #target_node ports,law_node=law,fact=fact,
         original_occurrences= #original_occurrences ports}end))
end
