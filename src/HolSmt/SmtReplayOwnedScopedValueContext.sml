structure SmtReplayOwnedScopedValueContext :>
    SmtReplayOwnedScopedValueContext =
struct
  structure W=SmtReplayInvocationWork
  structure G=SmtReplayGraph
  structure GP=SmtLib_GraphPreprocess
  structure VP=SmtLib_GraphValueProof
  structure PV=SmtLib_GraphParserValue
  structure F=SmtLib_GraphFrontend
  structure NC=SmtReplayNativeContract
  structure Scope=SmtReplayOwnedScopeReceipt
  structure Z=Z3_GraphProofParser
  structure Shared=Z3_SharedReplayPlan
  structure R=Z3_Proof
  val ERR=Feedback.mk_HOL_ERR "SmtReplayOwnedScopedValueContext"
  type syntax=PV.proof_term
  type command={id:Z.proof_id,target:syntax,
    plan:(syntax,PV.value) Shared.plan}
  datatype requirement=EnclosingProgramme of Z.proof_id
    | BindingProgramme of F.value_scoped_session
    | LocalSourceClosure of Z.proof_id * syntax
    | NestedProgramme of Z.proof_id | RawProgramme of Z.proof_id
  type data={query:GP.graph_query,
    packet:Z3_GraphValueProofParser.proof VP.packet,values:PV.context,
    graph:G.graph,root:G.scope,child:G.scope,frame:Scope.receipt,
    binding:VP.binding_frame,target:PV.value,body:Z.proof_id,
    lambda_blocks:int list,
    commands:command list,roots:PV.value list,native_contract:NC.contract}
  datatype context=Context of
    {work:W.portfolio,guard:unit -> unit,data:data}
  datatype capture=Captured of context | Needs of requirement list
  exception Pending of requirement
  datatype 'a observed=Complete of 'a | Missing of requirement
  fun metadata expected action=
    case W.with_step expected (fn()=>
        ((let val _=W.spend_policy expected 2
              val value=action () val _=W.spend_policy expected 1
          in Complete value end)
          handle Pending needed=>
            (W.spend_policy expected 4;Missing needed))) of
        Complete value=>value | Missing needed=>raise Pending needed
  fun capture expected query
      (packet:Z3_GraphValueProofParser.proof VP.packet)
      {id,native_contract}=((
    ((let
      val original=GP.query_nodes_with_policy_for expected query
      val _=NC.validate_for expected native_contract
      val initial=metadata expected (fn()=>
        let
          val contents=VP.contents_with_policy_for expected query packet
          val proof= #proof contents
          (* Eight captured visitors, two observer lambdas and thirteen
             observer/registry fields and record constructors. *)
          val _=W.spend_policy expected 23
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
              (fn(key,value,found)=>(tick ();case found of SOME _=>found
                | NONE=>if compare_id(wanted,key)=EQUAL then
                    (tick ();SOME value)else NONE)) NONE (#steps proof) of
                SOME command=>command
              | NONE=>raise ERR "capture" "unknown actual proof ID")
          fun strings(a,b)=pay(1+IntInf.fromInt(String.size a)+
            IntInf.fromInt(String.size b))
          fun metadata_strings values=(tick ();List.app(fn text=>
            (tick ();pay(1+2*IntInf.fromInt(String.size text))))values)
          fun metadata_rule(rule:R.proof_rule)=
            (* Four rule fields, the two name-list cells and case setup. *)
            (pay 7;metadata_strings[#name rule,#replay_handler rule];
             metadata_strings(#aliases rule);
             case #version_support rule of R.AllZ3Versions=>tick ()
               | R.Z3Versions rows=>metadata_strings rows
               | R.Z3VersionPrefixes rows=>metadata_strings rows)
          val observer:Shared.observer=
            {registry={visit=tick,copy=tick,string_comparison=strings,
               prefix_comparison=strings},
             rule_comparison=fn(a,b)=>(metadata_rule a;metadata_rule b),
             normalization_character=tick,
             premises=fn rows=>(tick ();List.app(fn _=>pay 2)rows),
             argument_copy=tick,kept_item=tick,copied_roots=tick}
          val (target,bound)=case find id of
              Z.Rule{rule,premises=[bound],arguments=[],metadata=NONE,
                  conclusion,accepts_bind=true}=>
                if Shared.canonical_name observer ERR
                    (#z3_version proof)rule="quant-intro" then
                  (pay 2;(#node conclusion,bound))
                else (pay 2;raise Pending(EnclosingProgramme id))
            | _=>(pay 2;raise Pending(EnclosingProgramme id))
          val (saved,body,blocks)=case find bound of
              Z.Bind{binding,body,lambda_blocks}=>
                (pay 2;(binding,body,lambda_blocks))
            | _=>(pay 2;raise Pending(EnclosingProgramme bound))
          (* Data fields/record and the once-only saved-Bind projection
             used by the outside-action authentic frame constructor. *)
          val _=pay 6
        in {target=target,saved=saved,body=body,blocks=blocks} end)
      val binding=VP.prepare_root_binding_frame_with_policy expected query
        packet (#saved initial)
    in metadata expected (fn()=>
      let
        val contents=VP.contents_with_policy_for expected query packet
        val actual=VP.binding_frame_data_for expected query binding
        val parent= #parent actual
        (* Six header projections and two immutable declaration stamps. *)
        val _=W.spend_policy expected 8
        val values= #context contents
        val graph= #graph original val root= #scope original
        val child= #scope actual val frame= #frame actual
        val epoch=Type.type_epoch () val symbols=Term.term_epoch ()
        (* Seventeen captured visitors, five private refs, two initial
           containers and fifteen observer fields/records/lambdas. Every
           later container/copy event pays separately. *)
        val _=W.spend_policy expected 39
        val packet_guard=VP.prepare_scoped_guard_with_policy_for
          expected query packet
        fun guard ()=
          (packet_guard ();
           NC.validate_for expected native_contract;
           let val held=VP.binding_frame_data_for expected query binding
               val owner=Scope.description_with_policy_for expected parent
               (* Actual retained header fields, seven comparisons, two
                  epoch reads, branch and target projection. *)
               val _=W.spend_policy expected 16
           in if Portable.pointer_eq(#context held,values) andalso
               Portable.pointer_eq(#graph held,graph) andalso
               #root held=root andalso #scope held=child andalso
               #scope owner=root andalso Type.type_epoch ()=epoch andalso
               Term.term_epoch ()=symbols then ()else
             raise ERR "guard" "different actual scoped lifetime" end;
           PV.usable values root (#target initial))
        fun pay amount=(guard ();W.spend_policy expected amount)
        fun tick ()=pay 1
        fun compare_id (Z.Named a,Z.Named b)=
              (tick ();Int.compare(a,b))
          | compare_id (Z.Anonymous a,Z.Anonymous b)=
              (tick ();Int.compare(a,b))
          | compare_id (Z.Named _,Z.Anonymous _)=(tick ();LESS)
          | compare_id (Z.Anonymous _,Z.Named _)=(tick ();GREATER)
        fun reverse rows=
          let val _=pay 1
              fun visit [] result=(guard ();result)
                | visit(value::rest)result=
                    (pay 2;visit rest(value::result))
          in visit rows [] end
        val proof= #proof contents
        fun step wanted=(tick ();case Redblackmap.foldl
            (fn(key,value,found)=>(tick ();case found of SOME _=>found
              | NONE=>if compare_id(wanted,key)=EQUAL then
                  (tick ();SOME value)else NONE)) NONE (#steps proof) of
              SOME command=>command
            | NONE=>raise ERR "capture" "missing child proof ID")
        val seen=ref(Redblackset.empty compare_id)
        val endpoints=ref(Redblackmap.mkDict compare_id)
        val commands=ref([]:command list)
        val roots=ref([]:PV.value list)
        val requirements=ref([]:requirement list)
        fun need value=(pay 2;requirements:=value:: !requirements)
        fun located(value:F.value_term)=
          (pay 2;PV.usable values child (#node value);
           roots:= #node value:: !roots;
           PV.proof_term values (#node value))
        fun prior wanted=(tick ();case Redblackmap.peek(!endpoints,wanted)
            of SOME value=>value | NONE=>
              (pay 2;raise Pending(NestedProgramme wanted)))
        fun keep value=(tick ();ignore(PV.proof_key values value))
        fun string_work(a,b)=pay(1+IntInf.fromInt(String.size a)+
          IntInf.fromInt(String.size b))
        fun metadata_strings texts=(tick ();List.app(fn text=>
          (tick ();pay(1+2*IntInf.fromInt(String.size text))))texts)
        fun metadata_rule(rule:R.proof_rule)=
          (* Four rule fields, the two name-list cells and case setup. *)
          (pay 7;metadata_strings[#name rule,#replay_handler rule];
           metadata_strings(#aliases rule);
           case #version_support rule of R.AllZ3Versions=>tick ()
             | R.Z3Versions rows=>metadata_strings rows
             | R.Z3VersionPrefixes rows=>metadata_strings rows)
        val observer:Shared.observer=
          {registry={visit=tick,copy=tick,string_comparison=string_work,
             prefix_comparison=string_work},
           rule_comparison=fn(a,b)=>(metadata_rule a;metadata_rule b),
           normalization_character=tick,
           premises=fn rows=>(tick ();List.app(fn _=>pay 2)rows),
           argument_copy=tick,kept_item=tick,copied_roots=tick}
        fun operands constant arity value=
          let
            val _=pay 2
            fun count [] total=(guard ();total)
              | count(_::rest)total=(tick ();count rest(total+1))
            fun spine cursor arguments=
              (tick ();case PV.proof_view values cursor of
                  PV.ProofApplication(f,x)=>(pay 2;spine f(x::arguments))
                | PV.ProofConstant atom=>
                    let val _=pay 2
                        val a=Term.dest_thy_const atom
                        val b=Term.dest_thy_const constant
                        val _=string_work(#Thy a,#Thy b)
                        val _=string_work(#Name a,#Name b)
                    in if Term.same_const atom constant andalso
                        count arguments 0=arity then SOME arguments
                      else NONE end
                | _=>NONE)
          in spine value [] end
        fun local_source wanted value=
          (pay 3;raise Pending(LocalSourceClosure(wanted,value)))
        fun classify wanted command=
          let
            (* Eight fields+record, two source observer closures, the
               private decline observer, mode record and SOME. *)
            val _=pay 16
            fun plan_error stage message=
              let
                val _=tick ()
                fun equals left right=
                  (string_work(left,right);left=right)
                val pending=equals stage "packet" andalso
                  (equals message
                     "actual rule programme has not been migrated" orelse
                   equals message "native argument programme pending" orelse
                   equals message
                     "indexed native argument programme pending" orelse
                   equals message
                     "actual native/theory arguments need owned programme")
              in if pending then
                  (pay 2;Pending(NestedProgramme wanted))
                else ERR stage message end
            val result=(SOME(Shared.classify_with_bindings
              {observer=observer,prior=prior,located=located,
               processed=local_source wanted,
               original_slot=local_source wanted,operands=operands,
               keep=keep,error=plan_error}
              {version= #z3_version proof,mode=Shared.RecordedResolution}
              command)handle Pending value=>(need value;NONE))
            val _=tick ()
            val target=case result of SOME(value,_)=>SOME value
              | NONE=>(case command of Z.Rule{conclusion,...}=>
                    (tick ();SOME(located conclusion))
                  | Z.Alias other=>
                      (tick ();Redblackmap.peek(!endpoints,other))
                  | Z.Bind _=>NONE)
            val _=case target of NONE=>() | SOME value=>
              (pay 2;endpoints:=Redblackmap.insert
                (!endpoints,wanted,value))
          in case result of NONE=>() | SOME(actual_target,plan)=>
              (case plan of
                  Shared.ScopedEquality _=>
                    (tick ();need(NestedProgramme wanted))
                | Shared.Quantified _=>
                    (tick ();need(NestedProgramme wanted))
                | Shared.RawResolution _=>
                    (tick ();need(RawProgramme wanted))
                | _=>(pay 6;commands:={id=wanted,target=actual_target,
                    plan=plan}::
                    !commands))
          end
        fun walk wanted ancestors=
          (tick ();if Redblackset.member(!seen,wanted)then ()else
            if Redblackset.member(ancestors,wanted)then
              raise ERR "capture" "cyclic actual child programme"else
            let
              (* One actual ancestor insertion; its private comparator
                 separately meters every actual tree comparison. *)
              val _=tick ()
              val path=Redblackset.add(ancestors,wanted)
              val command=step wanted
              val _=case command of
                  (* One fresh List.app visitor on this actual Rule. *)
                  Z.Rule{premises,...}=>(tick ();List.app
                    (fn prior=>(tick ();walk prior path))premises)
                | Z.Alias prior=>(tick ();walk prior path)
                | Z.Bind _=>(tick ();need(NestedProgramme wanted))
              val _=case command of Z.Bind _=>()
                | _=>classify wanted command
              val _=tick ()val _=seen:=Redblackset.add(!seen,wanted)
            in ()end)
        val _=if #binders actual then ()else
          (pay 2;raise Pending(BindingProgramme(#saved initial)))
        (* The initial ancestors container is not the seen/endpoints
           setup already charged above. *)
        val _=pay 2
        val ancestors=Redblackset.empty compare_id
        val _=walk (#body initial)ancestors
        val missing=reverse(!requirements)
      in if not(null missing)then (tick ();Needs missing)else
        let
          val ordered=reverse(!commands)
          val actual_roots=reverse(!roots)
          (* Fourteen data fields+record, three owner fields+constructor
             and Captured. The guard is retained, not re-created. *)
          val _=pay 20
          val data:data={query=query,packet=packet,values=values,graph=graph,
            root=root,child=child,frame=frame,binding=binding,
            target= #target initial,body= #body initial,
            lambda_blocks= #blocks initial,commands=ordered,
            roots=actual_roots,native_contract=native_contract}
          val _=guard ()
        in Captured(Context{work=expected,guard=guard,data=data})end
      end)end)handle Pending value=>Needs[value]))
    handle primary=>(W.close expected;raise primary))
  fun data_for expected(Context{work,guard,data})=((
    let
      val _=if Portable.pointer_eq(expected,work)then ()else
        raise ERR "data_for" "different original Work"
      val _=guard ()
      (* Existing immutable data is returned without copying fields/list. *)
      val _=W.spend_policy expected 1
    in data end)
    handle primary=>(W.close expected;raise primary))
end
