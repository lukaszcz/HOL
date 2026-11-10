(* Exact stock variant name selection from authentic per-proof Hyp origins.
   This module issues DATA only, not a variable/closure/proof entitlement. *)
structure SmtLib_OwnedContextFreshChoice :> SmtLib_OwnedContextFreshChoice =
struct
  structure G=SmtReplayGraph
  structure W=SmtReplayInvocationWork
  structure P=SmtReplayProof
  structure C=SmtLib_OwnedNamedContextSeeds
  structure Scope=SmtReplayOwnedScopeReceipt
  val _=SmtReplayProof.prepare_source_condition_freshness_origins
  val _=SmtReplayProof.prepare_source_condition_binder_origins
  val _=SmtLib_OwnedNamedContextSeeds.prepare_context_origin_metadata
  val ERR=Feedback.mk_HOL_ERR "SmtLib_OwnedContextFreshChoice"
  datatype choice=Choice of
    {work:W.portfolio,evidence:P.source_condition_evidence,
     proof:P.source_freshness_origins,
     binders:P.source_condition_binder_origins,
     context:C.context_metadata,origins:C.context_origin_metadata list,
     frame:Scope.receipt,name:string,ty:Type.hol_type}
  fun protect work operation=operation()handle primary=>
    (W.close work;raise primary)
  fun guard expected(Choice {work,proof,binders,context,origins,frame,...})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "guard" "foreign expected Work";
       ignore(P.source_condition_freshness_origins_for expected proof);
       ignore(P.source_condition_binder_origins_for expected binders);
       ignore(C.context_metadata_for expected context);
       List.app(fn origin=>ignore
         (C.context_origin_metadata_for expected origin))origins;
       Scope.validate_lifetime_for expected frame))
  fun prepare_existential work {evidence,context}=
    protect work(fn()=>
    let
      val proof=P.prepare_source_condition_freshness_origins work evidence
      val pd=P.source_condition_freshness_origins_for work proof
      val binders=P.prepare_source_condition_binder_origins work evidence
      val bd=P.source_condition_binder_origins_for work binders
      val _=if Portable.pointer_eq(#statement pd,#statement bd)then ()else
        raise ERR "prepare_existential" "different retained proof syntax"
      val cd=C.context_metadata_for work context
      val actual=Scope.description_for work (#frame pd)
      val source=Scope.description_for work (#frame cd)
      val graph= #graph actual
      val _=if Portable.pointer_eq(graph,#graph source) andalso
          #root actual= #root source andalso
          Portable.pointer_eq(#sources actual,#sources source) andalso
          G.scope_visible graph (#scope actual)(#scope source)then ()else
        raise ERR "prepare_existential" "different authentic context frame"
      (* Each exact unknown proof origin must be resolved by the genuine
         matching origin slice, never the aggregate whole-Gamma variables. *)
      val origins=List.map
        (C.prepare_context_origin_metadata work context)(#unknown pd)
      fun live()=
        (ignore(P.source_condition_freshness_origins_for work proof);
         ignore(P.source_condition_binder_origins_for work binders);
         ignore(C.context_metadata_for work context);
         List.app(fn origin=>ignore
           (C.context_origin_metadata_for work origin))origins;
         Scope.validate_lifetime_for work (#frame pd))
      val result=W.with_step work(fn()=>
      let
        fun tick n=(live();W.spend work n)
        fun guarded operation=
          (live();let val value=operation()in live();value end)
        fun append [] all=all
          | append(v::rest)all=(tick 1;v::append rest all)
        val variables=List.foldl(fn(origin,all)=>
          let val d=C.context_origin_metadata_for work origin
              val values=case #variables d of SOME values=>values | NONE=>
                raise ERR "prepare_existential"
                  "actual proof origin FV remains unknown"
          in append values all end)(#variables pd)origins
        fun first_exists path term=
          (tick 1;if boolSyntax.is_imp_only term then
             let val(ant,body)=guarded(fn()=>boolSyntax.dest_imp_only term)
             in if boolSyntax.is_exists ant then
                  (path@[0,1,1],
                   #1(guarded(fn()=>boolSyntax.dest_exists ant)))
                else first_exists(path@[1])body end
           else raise ERR "prepare_existential"
             "actual implication spine has no existential antecedent")
        val statement= #statement pd
        val(statement,path)=if boolSyntax.is_eq statement then
              let val(a,b)=guarded(fn()=>boolSyntax.dest_eq statement)
              in if Term.is_const b andalso Term.same_const b boolSyntax.T
                   then (a,[0,1])else (statement,[])end
            else (statement,[])
        val(route,emitted)=first_exists path statement
        val original=case List.find(fn(path,_,actual)=>
            (tick(length path+length route+1);
             path=route andalso Term.term_eq actual emitted))
            (#binders bd)of
            SOME(_,variable,_)=>variable
          | NONE=>raise ERR "prepare_existential"
              "missing actual lexical binder origin"
        val(base,_)=guarded(fn()=>Term.dest_var original)
        val ty=guarded(fn()=>Term.type_of emitted)
        (* Public Term.variant owns the exact signature-name test. The
           restored kernel does not export its private signature table.
           Pay both temporary native VARIABLE construction footprints and
           repeated actual type annotations before these native effects. *)
        fun type_weight current=
          (tick 1;if Type.is_vartype current then
             (tick(String.size(Type.dest_vartype current));1)
           else let val {Thy,Tyop,Args}=guarded(fn()=>
                      Type.dest_thy_type current)
                val _=tick(String.size Thy+String.size Tyop)
             in 1+List.foldl(fn(arg,all)=>all+type_weight arg)0 Args end)
        val weight=type_weight ty
        val _=List.app(fn variable=>
          let val(name,_)=guarded(fn()=>Term.dest_var variable)
          in tick(String.size name+1)end)variables
        val _=tick(String.size base+1)
        val _=tick(4+2*weight+2)
        val native=guarded(fn()=>Term.mk_var(base,ty))
        val selected=guarded(fn()=>Term.variant variables native)
        val(name,actual_type)=guarded(fn()=>Term.dest_var selected)
        val _=if Portable.pointer_eq(actual_type,ty)then ()else
          raise ERR "prepare_existential" "public variant changed type"
        val choice=Choice {work=work,evidence=evidence,
          proof=proof,binders=binders,
          context=context,
          origins=origins,frame= #frame pd,name=name,ty=ty}
        val _=guard work choice
      in choice end)
    in result end)
  fun describe_for expected(value as Choice {frame,name,ty,...})=
    (guard expected value;{frame=frame,name=name,ty=ty})
  datatype antecedent_plan=AntecedentPlan of
    {work:W.portfolio,choice:choice,
     argument:P.source_condition_argument_plan,available:bool ref}
  fun antecedent_guard expected
      (AntecedentPlan {work,choice,available,...})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "antecedent_guard" "foreign expected Work";
       if !available then ()else raise ERR "antecedent_guard"
         "antecedent plan already consumed";
       guard expected choice))
  fun prepare_antecedent expected
      (choice as Choice {evidence,frame,name,ty,...}) {check_type}=
    protect expected(fn()=>
      (guard expected choice;
       let val d=Scope.description_for expected frame
           val argument=P.prepare_source_condition_exists_argument expected
             {evidence=evidence,frame=frame,caller= #scope d,name=name,
              ty=ty,check_type=check_type}
           val result=AntecedentPlan {work=expected,choice=choice,
             argument=argument,available=ref true}
           val _=antecedent_guard expected result
       in result end))
  fun execute_antecedent expected
      (value as AntecedentPlan {choice,argument,available,...})=
    protect expected(fn()=>
      (antecedent_guard expected value;
       available:=false;
       let
         val ready=P.admit_source_condition_exists_argument expected
           argument
         val _=guard expected choice
         val quoted=P.source_condition_argument_ready_for expected ready
         val child=W.with_step expected(fn()=>
           let
             fun live()=(guard expected choice;
               ignore(P.source_condition_argument_ready_for expected ready))
             fun guarded operation=
               (live();let val result=operation()in live();result end)
             val d=Scope.description_for expected (#frame quoted)
             val graph= #graph d val scope= #scope d
             (* Whole prospective P grammar and all type policies have
                completed BEFORE either native/graph VARIABLE effect. *)
             val _=live()
             val _=W.spend expected 2
             val variable=guarded(fn()=>
               Term.mk_var(#name quoted,#ty quoted))
             val node=guarded(fn()=>G.variable graph scope
               G.Generated variable)
             val actual=guarded(fn()=>G.closure_root graph scope node)
           in actual end)
         val result=P.execute_source_condition_exists_argument expected
           {ready=ready,argument=child}
         val _=guard expected choice
       in result end))

  datatype canonical_choice=CanonicalExistsChoice of choice
    | CanonicalUniversalChoice of
        {work:W.portfolio,state:P.source_canonical_state,
         proof:P.source_freshness_origins,
         binders:P.source_condition_binder_origins,
         context:C.context_metadata,origins:C.context_origin_metadata list,
         frame:Scope.receipt,arguments:(string*Type.hol_type) list}
  datatype canonical_plan=CanonicalPlan of
    {work:W.portfolio,state:P.source_canonical_state,choice:canonical_choice,
     raw:P.source_canonical_plan,available:bool ref}
  fun canonical_choice_guard expected(CanonicalExistsChoice choice)=
        guard expected choice
    | canonical_choice_guard expected(CanonicalUniversalChoice
        {work,state,proof,binders,context,origins,frame,...})=
        protect expected(fn()=>
          (if Portable.pointer_eq(expected,work)then ()else
             raise ERR "canonical_choice" "foreign expected Work";
           ignore(P.source_canonical_current_for expected state);
           ignore(P.source_condition_freshness_origins_for expected proof);
           ignore(P.source_condition_binder_origins_for expected binders);
           ignore(C.context_metadata_for expected context);
           List.app(fn origin=>ignore
             (C.context_origin_metadata_for expected origin))origins;
           Scope.validate_lifetime_for expected frame))
  fun canonical_guard expected(CanonicalPlan {work,state,choice,...})=
    protect expected(fn()=>
      (if Portable.pointer_eq(expected,work)then ()else
         raise ERR "canonical_plan" "foreign expected Work";
       ignore(P.source_canonical_current_for expected state);
       canonical_choice_guard expected choice))
  fun prepare_canonical_exists expected {state,context,check_type}=
    protect expected(fn()=>
      let val evidence=P.source_canonical_current_for expected state
          (* Retain all original proof/row/lexical provenance. The current
             DATA shadow additionally supplies the stock destructor stem. *)
          val prior as Choice {proof,binders,origins,frame,...}=
            prepare_existential expected{evidence=evidence,context=context}
          fun live()=(guard expected prior;
            ignore(P.source_canonical_current_for expected state))
          val syntax=P.source_canonical_syntax_for expected state
          val(name,ty)=W.with_step expected(fn()=>
            let fun tick n=(live();W.spend expected n)
                fun guarded operation=
                  (live();let val value=operation()in live();value end)
                val pd=P.source_condition_freshness_origins_for expected proof
                fun append [] all=all
                  | append(v::rest)all=(tick 1;v::append rest all)
                val variables=List.foldl(fn(origin,all)=>
                  let val d=C.context_origin_metadata_for expected origin
                      val values=case #variables d of SOME values=>values
                        | NONE=>raise ERR "canonical_exists"
                            "actual Hyp FV remains unknown"
                  in append values all end)(#variables pd)origins
                val(ant,_)=guarded(fn()=>boolSyntax.dest_imp_only
                  (#statement syntax))
                val(v,_)=guarded(fn()=>boolSyntax.dest_exists ant)
                val(base,ty)=guarded(fn()=>Term.dest_var v)
                fun type_weight current=
                  (tick 1;if Type.is_vartype current then
                     (tick(String.size(Type.dest_vartype current));1)
                   else let val {Thy,Tyop,Args}=guarded(fn()=>
                              Type.dest_thy_type current)
                            val _=tick(String.size Thy+String.size Tyop)
                        in 1+List.foldl(fn(t,n)=>n+type_weight t)0 Args end)
                val weight=type_weight ty
                val _=List.app(fn variable=>
                  let val(old,_)=guarded(fn()=>Term.dest_var variable)
                  in tick(String.size old+1)end)variables
                val _=tick(String.size base+1)
                val _=tick(4+2*weight+2)
                val native=guarded(fn()=>Term.mk_var(base,ty))
                val selected=guarded(fn()=>Term.variant variables native)
                val(name,actual)=guarded(fn()=>Term.dest_var selected)
                val _=if Portable.pointer_eq(actual,ty)then ()else
                  raise ERR "canonical_exists" "actual type changed"
            in(name,ty)end)
          val choice=Choice {work=expected,evidence=evidence,proof=proof,
            binders=binders,context=context,origins=origins,
            frame=frame,name=name,ty=ty}
          val _=guard expected choice
          val raw=P.prepare_source_canonical_future expected
            {state=state,operation=P.CanonicalExists,
             quotations=[(name,ty)],check_type=check_type}
          val result=CanonicalPlan {work=expected,state=state,
            choice=CanonicalExistsChoice choice,raw=raw,available=ref true}
          val _=canonical_guard expected result
      in result end)
  fun prepare_canonical_universals expected {state,context,check_type}=
    protect expected(fn()=>
    let
      val evidence=P.source_canonical_current_for expected state
      val proof=P.prepare_source_condition_freshness_origins expected evidence
      val pd=P.source_condition_freshness_origins_for expected proof
      val binders=P.prepare_source_condition_binder_origins expected evidence
      val bd=P.source_condition_binder_origins_for expected binders
      val _=if Portable.pointer_eq(#statement pd,#statement bd)then ()else
        raise ERR "canonical_universals" "retained statement changed"
      val cd=C.context_metadata_for expected context
      val actual=Scope.description_for expected (#frame pd)
      val source=Scope.description_for expected (#frame cd)
      val graph= #graph actual
      val _=if Portable.pointer_eq(graph,#graph source) andalso
          #root actual= #root source andalso
          Portable.pointer_eq(#sources actual,#sources source) andalso
          G.scope_visible graph (#scope actual)(#scope source)then ()else
        raise ERR "canonical_universals" "different authentic Source frame"
      val origins=List.map
        (C.prepare_context_origin_metadata expected context)(#unknown pd)
      fun live()=
        (ignore(P.source_canonical_current_for expected state);
         ignore(P.source_condition_freshness_origins_for expected proof);
         ignore(P.source_condition_binder_origins_for expected binders);
         ignore(C.context_metadata_for expected context);
         List.app(fn origin=>ignore
           (C.context_origin_metadata_for expected origin))origins;
         Scope.validate_lifetime_for expected (#frame pd))
      val arguments=W.with_step expected(fn()=>
      let
        fun tick n=(live();W.spend expected n)
        fun guarded operation=
          (live();let val value=operation()in live();value end)
        fun append [] all=all
          | append(v::rest)all=(tick 1;v::append rest all)
        val variables=List.foldl(fn(origin,all)=>
          let val d=C.context_origin_metadata_for expected origin
              val values=case #variables d of SOME values=>values | NONE=>
                raise ERR "canonical_universals" "actual Hyp FV is unknown"
          in append values all end)(#variables pd)origins
        val syntax=P.source_canonical_syntax_for expected state
        (* Public strip_forall performs the stock simultaneous prefix
           unclashing. Repeated dest_forall has different mixed-name rules. *)
        val(vars,_)=guarded(fn()=>
          boolSyntax.strip_forall(#statement syntax))
        val originals=List.map(fn variable=>guarded(fn()=>
          Term.dest_var variable))vars
        val _=if null originals then raise ERR "canonical_universals"
          "actual universal block is empty"else ()
        fun type_weight current=
          (tick 1;if Type.is_vartype current then
             (tick(String.size(Type.dest_vartype current));1)
           else let val {Thy,Tyop,Args}=guarded(fn()=>
                      Type.dest_thy_type current)
                val _=tick(String.size Thy+String.size Tyop)
             in 1+List.foldl(fn(arg,all)=>all+type_weight arg)0 Args end)
        (* SPEC_ALL varies the entire binder list from RIGHT to LEFT and
           uses prim_variant: signature-name avoidance belongs to EXISTS. *)
        fun choose [] avoid=(avoid,[])
          | choose((base,ty)::rest)avoid=
            let val(used,selected)=choose rest avoid
                val weight=type_weight ty
                val _=List.app(fn variable=>
                  let val(name,_)=guarded(fn()=>Term.dest_var variable)
                  in tick(String.size name+1)end)used
                val _=tick(String.size base+1)
                val _=tick(4+2*weight+2)
                val native=guarded(fn()=>Term.mk_var(base,ty))
                val varied=guarded(fn()=>Term.prim_variant used native)
                val(name,actual)=guarded(fn()=>Term.dest_var varied)
                val _=if Portable.pointer_eq(actual,ty)then ()else
                  raise ERR "canonical_universals" "actual type changed"
            in(varied::used,(name,ty)::selected)end
        val(_,result)=choose originals variables
        val _=live()
      in result end)
      val choice=CanonicalUniversalChoice {work=expected,state=state,
        proof=proof,binders=binders,context=context,origins=origins,
        frame= #frame pd,arguments=arguments}
      val _=canonical_choice_guard expected choice
      val raw=P.prepare_source_canonical_future expected
        {state=state,operation=P.CanonicalUniversals,quotations=arguments,
         check_type=check_type}
      val result=CanonicalPlan {work=expected,state=state,choice=choice,
        raw=raw,available=ref true}
      val _=canonical_guard expected result
    in result end)
  fun execute_canonical expected
      (value as CanonicalPlan {raw,available,...})=
    protect expected(fn()=>
      (canonical_guard expected value;
       if !available then ()else raise ERR "canonical_execute"
         "canonical argument plan consumed";
       available:=false;
       let val ready=P.admit_source_canonical_plan expected raw
           val quoted=P.source_canonical_arguments_for expected ready
           val children=W.with_step expected(fn()=>
             let fun live()=(canonical_guard expected value;
                   ignore(P.source_canonical_arguments_for expected ready))
                 fun guarded operation=
                   (live();let val result=operation()in live();result end)
                 val d=Scope.description_for expected (#frame quoted)
                 val graph= #graph d val scope= #scope d
                 val _=live()
                 val _=W.spend expected(2*length(#arguments quoted))
                 fun mint []=[]
                   | mint((name,ty)::rest)=
                     let val variable=guarded(fn()=>Term.mk_var(name,ty))
                         val node=guarded(fn()=>G.variable graph scope
                           G.Generated variable)
                         val child=guarded(fn()=>G.closure_root graph scope
                           node)
                     in child::mint rest end
                 val result=mint(#arguments quoted)
                 val _=live()
             in result end)
           val result=P.execute_source_canonical_plan expected
             {ready=ready,arguments=children}
           val _=canonical_guard expected value
       in result end))

end
