structure SmtReplayRecordedBeta :> SmtReplayRecordedBeta =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure F = SmtReplayFocusAdmission
  val _ = SmtReplayFocusAdmission.describe_for
  fun ERR message = Feedback.mk_HOL_ERR "SmtReplayRecordedBeta" "beta" message
  type request =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,ordinal : int,redex : G.closure_child,
     check_type : Type.hol_type -> unit,scope_opened : G.scope -> unit}
  type admitted_request =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,ordinal : int,admission : F.focus,
     check_type : Type.hol_type -> unit,scope_opened : G.scope -> unit}
  type size = {raw : int,binder : int,types : int}
  datatype recipe =
      Retain of G.node
    | Insert
    | Apply of G.node * bool * recipe * recipe
    | Lambda of G.node * bool * G.binder_closure * recipe
  type guard_cache = (IntInf.int * G.scope list * G.closure_child list *
    (G.scope * G.closure_child) list * (G.node * Term.term) list) option ref
  type common =
    {request : request,root_scope : G.scope,limits : W.limits,
     admission : F.focus option,source_limit : int,
     handles : G.closure_child list ref,frames : G.scope list ref,
     minted : (G.scope * G.closure_child) list ref,
     originals : (G.node * Term.term) list ref,validated : guard_cache}
  datatype plan = Plan of
    {common : common,source : G.node,operand : G.node,recipe : recipe,
     annotations : Type.hol_type list,output_size : size,
     entitlement : W.entitlement,
     footprint : int,used : bool ref}
  datatype conversion = Conversion of
    {common : common,source : G.node,target : G.node,theorem : Thm.thm}

  (* Genuine graph closure geometry is immutable; only G retirement can
     invalidate an already checked handle. Retain the successfully checked
     list suffix, not a caller guard or a lifetime grant. New links are
     still checked before use, even without a graph mutation. Every probe
     (including a hit) debits the SAME Work, in Idle as well as Busy. *)
  fun guard_app work held action rows =
    let fun visit rows =
          (W.spend_guard_policy work 1;
           if Portable.pointer_eq (rows,held) then () else
             case rows of []=>() | row::rest=>(action row;visit rest))
    in visit rows end
  fun retained work graph scope validated frames handles minted originals =
    let
      val _=W.spend_guard_policy work 1
      val revision=G.scope_retirement_epoch graph scope
      val (fs,hs,ms,os)=case !validated of SOME (old,f,h,m,o')=>
          if old=revision then (f,h,m,o') else ([],[],[],[])
        | NONE=>([],[],[],[])
      val _=guard_app work fs (G.validate_scope graph) (!frames)
      val _=guard_app work hs (fn h=>ignore
        (G.closure_child_node graph scope h)) (!handles)
      val _=guard_app work ms (fn (frame,h)=>ignore
        (G.closure_child_node graph frame h)) (!minted)
      val _=guard_app work os (fn (node,original)=>
        if Portable.pointer_eq (G.representative graph node,original) then ()
        else raise ERR "retained original term changed") (!originals)
    in validated:=SOME (revision,!frames,!handles,!minted,!originals) end

  fun active ({request={graph,scope,sources,work,redex,...},root_scope,
               limits,admission,source_limit,handles,frames,minted,originals,
               validated}
      : common) =
    (W.validate work graph root_scope sources limits;
     G.validate_scope graph scope;
     (case admission of NONE => () | SOME held =>
       let val d = F.describe_for
             {graph = graph,scope = scope,sources = sources,work = work} held
       in if #source_limit d = source_limit andalso #node d =
           G.closure_child_node graph scope redex then () else
          raise ERR "different admitted beta source profile" end);
     retained work graph scope validated frames handles minted originals)
    handle primary=>(W.close work;raise primary)

  fun invoke common operation =
    (active common;
     let val result=operation () in active common;result end)

  fun charge (common as {request={work,...},...} : common) amount =
    (W.spend work amount;active common)

  fun plus limit (a,b) =
    if a > limit orelse b > limit orelse a > limit-b then
      raise ERR "prospective syntax/type budget exhausted"
    else a+b
  fun sum limit values = List.foldl (fn (n,a)=>plus limit (n,a)) 0 values
  fun check maximum type_maximum ({raw,binder,types} : size) =
    if raw<=maximum andalso binder<=maximum andalso types<=type_maximum
    then ()
    else raise ERR "prospective syntax/type budget exhausted"

  (* The type getter is discovery, not a policy or proof callback. Each child
     and association is charged before descent. Getter allocation is not
     thereby a whole private-kernel cost bound. *)
  fun weight common limit ty =
    (charge common 1;
     if invoke common (fn()=>Type.is_vartype ty) then 1
     else
       let val {Args,...}=invoke common (fn()=>Type.dest_thy_type ty)
           fun next [] total = total
             | next (x::xs) total =
                 (charge common 1;
                  next xs (plus limit (total,weight common limit x)))
       in next Args 1 end)

  fun copied common size lists =
    (charge common (#types (size : size));List.concat lists)

  fun type_at common node =
    let val {request={graph,...},...}=common
    in invoke common (fn()=>G.type_of graph node) end

  fun inspect common maximum annotation_maximum handle_root =
    let
      val {request={graph,scope,...},handles,...}=common
      val memo=ref (Redblackmap.mkDict Int.compare)
      val visiting=ref (Redblackset.empty Int.compare)
      fun walk child =
        let
          val _=charge common 1
          val node=invoke common
            (fn()=>G.closure_child_node graph scope child)
          val _=handles:=child :: !handles
          val id=G.node_id node
        in
          case Redblackmap.peek (!memo,id) of
            SOME answer=>answer
          | NONE=>
              let
                val _=if Redblackset.member (!visiting,id) then
                    raise ERR "cyclic recorded closure" else ()
                val _=visiting:=Redblackset.add (!visiting,id)
                val ty=type_at common node
                val t=weight common annotation_maximum ty
                val result=case invoke common (fn()=>G.view graph node) of
                    G.Variable _=>({raw=1,binder=1,types=t},[ty])
                  | G.Constant _=>({raw=1,binder=1,types=t},[ty])
                  | G.Application _=>
                      let val (f,x)=invoke common (fn()=>
                            G.closure_application_children graph scope child)
                          val (fs,ft)=walk f val (xs,xt)=walk x
                      val size : size=
                            {raw=sum maximum [1,#raw fs,#raw xs],
                             binder=sum maximum [1,#binder fs,#binder xs],
                             types=sum annotation_maximum
                               [t,#types fs,#types xs]}
                      in (size,copied common size [[ty],ft,xt]) end
                  | G.AdmittedBinder _=>
                      let val closure=invoke common (fn()=>
                            G.closure_child_binder graph scope child)
                          val data=invoke common (fn()=>
                            G.binder_closure_data graph scope closure)
                          val binder_ty=type_at common (#binder data)
                          val bt=weight common annotation_maximum binder_ty
                          val body=invoke common (fn()=>
                            G.binder_closure_body graph scope closure)
                          val (bs,ts)=walk body
                      val size : size=
                            {raw=plus maximum (1,#raw bs),
                             binder=plus maximum (2,#binder bs),
                             types=sum annotation_maximum [t,bt,#types bs]}
                      in (size,copied common size [[ty,binder_ty],ts]) end
                  | G.OpaqueRetained=>
                      raise ERR "unrecorded opaque beta syntax"
                val value : size = #1 result
                val _=if #raw value <= maximum andalso
                    #binder value <= maximum andalso
                    #types value <= annotation_maximum then () else
                  raise ERR "prospective syntax/type budget exhausted"
                val _=visiting:=Redblackset.delete (!visiting,id)
                val _=memo:=Redblackmap.insert (!memo,id,result)
              in result end
        end
    in walk handle_root end

  fun prepare_internal admission
      (request as {graph,scope,sources,work,ordinal,redex,...} : request) =
    let
      val root_scope=S.owning_scope sources
      val limits=W.semantic_limits work
      val source_limit = case admission of NONE => #input_limit limits
        | SOME held => #source_limit (F.describe_for
            {graph = graph,scope = scope,sources = sources,work = work} held)
      val common : common=
        {request = request,root_scope = root_scope,limits = limits,
         admission = admission,source_limit = source_limit,
         handles = ref [],frames = ref [],minted = ref [],originals = ref [],
         validated = ref NONE}
      fun attempt () =
        let
          val _=active common
          (* Absolute saturation ceiling only. Actual discovery debits and
             upfront reservations use SAME monotonically remaining Work. *)
          val allowance=W.work_limit work
          val _=charge common 1
          val _=if ordinal>=0 then () else raise ERR "negative stage ordinal"
          val source=invoke common
            (fn()=>G.closure_child_node graph scope redex)
          fun admitted metric =
            case invoke common (fn()=>G.unfolded_nodes graph metric
                source_limit source) of
                SOME size=>
                  if size<=source_limit then ()
                  else raise ERR "cached input syntax exceeds original cap"
              | NONE=>raise ERR "cached input syntax is unknown"
          val _=admitted G.RawNodes
          val _=admitted G.BinderInclusiveNodes
          val (lambda,arg)=invoke common
            (fn()=>G.closure_application_children graph scope redex)
          val closure=invoke common
            (fn()=>G.closure_child_binder graph scope lambda)
          val data=invoke common
            (fn()=>G.binder_closure_data graph scope closure)
          val operand=invoke common
            (fn()=>G.closure_child_node graph scope arg)
          val source_term=invoke common
            (fn()=>G.representative graph source)
          val operand_term=invoke common
            (fn()=>G.representative graph operand)
          val _= #originals common:=
            [(source,source_term),(operand,operand_term)]
          val _=if invoke common (fn()=>G.type_id graph operand)=
              invoke common (fn()=>G.type_id graph (#binder data)) then ()
              else raise ERR "beta operand type differs"
          val (input_size,input_types)=
            inspect common source_limit allowance redex
          val _=if invoke common (fn()=>G.unfolded_nodes graph G.RawNodes
              source_limit source)=SOME (#raw input_size) andalso
              invoke common (fn()=>G.unfolded_nodes graph
                G.BinderInclusiveNodes source_limit source)=
                SOME (#binder input_size) then ()
            else raise ERR "recorded input metrics differ"
          val (arg_size,arg_types)=inspect common source_limit allowance arg
          val body=invoke common
            (fn()=>G.binder_closure_body graph scope closure)
          val maximum= #output_limit limits
          val memo=ref (Redblackmap.mkDict
            (fn ((a,b),(c,d))=>case Int.compare (a,c) of
                EQUAL=>if b=d then EQUAL else if b then GREATER else LESS
              | answer=>answer))
          fun plan child enabled =
            let
              val _=charge common 1
              val node=invoke common
                (fn()=>G.closure_child_node graph scope child)
              val _= #handles common:=child :: !(#handles common)
              val key=(G.node_id node,enabled)
            in case Redblackmap.peek (!memo,key) of
                SOME answer=>answer
              | NONE=>
                let
                  val ty=type_at common node
                  val t=weight common allowance ty
                  val answer=
                    if enabled andalso node= #binder data then
                      (Insert,arg_size,arg_types)
                    else case invoke common (fn()=>G.view graph node) of
                      G.Variable _=>(Retain node,{raw=1,binder=1,types=t},[ty])
                    | G.Constant _=>(Retain node,{raw=1,binder=1,types=t},[ty])
                    | G.Application _=>
                        let val (f,x)=invoke common (fn()=>
                              G.closure_application_children graph scope child)
                            val (fr,fs,ft)=plan f enabled
                            val (xr,xs,xt)=plan x enabled
                        val size : size=
                              {raw=sum maximum [1,#raw fs,#raw xs],
                               binder=sum maximum [1,#binder fs,#binder xs],
                               types=sum allowance [t,#types fs,#types xs]}
                        in (Apply (node,enabled,fr,xr),size,
                            copied common size [[ty],ft,xt]) end
                    | G.AdmittedBinder _=>
                        let val inner=invoke common (fn()=>
                              G.closure_child_binder graph scope child)
                            val inner_data=invoke common (fn()=>
                              G.binder_closure_data graph scope inner)
                            val binder_ty=type_at common (#binder inner_data)
                            val bt=weight common allowance binder_ty
                            val nested=invoke common (fn()=>
                              G.binder_closure_body graph scope inner)
                            val child_enabled=enabled andalso
                              #binder inner_data<> #binder data
                            val (br,bs,ts)=plan nested child_enabled
                        val size : size=
                              {raw=plus maximum (1,#raw bs),
                               binder=plus maximum (2,#binder bs),
                               types=sum allowance [t,bt,#types bs]}
                        in (Lambda (node,enabled,inner,br),size,
                            copied common size [[ty,binder_ty],ts]) end
                    | G.OpaqueRetained=>raise ERR "unrecorded beta body"
                  val (_,size,_)=answer
                  val _=check maximum allowance size
                  val _=charge common 1
                  val _=memo:=Redblackmap.insert (!memo,key,answer)
                in answer end
            end
          val (recipe,output_size,output_types)=plan body true
          val result_ty=type_at common source
          val t=weight common allowance result_ty
          val equality_size : size=
            {raw=sum (#template_limit limits)
                 [3,#raw input_size,#raw output_size],
             binder=sum (#template_limit limits)
                 [3,#binder input_size,#binder output_size],
             types=sum allowance
                 [6,t,t,t,#types input_size,#types output_size]}
          val _=check (#template_limit limits) allowance equality_size
          val alignment_size : size=
            {raw=sum (#template_limit limits)
                 [3,#raw output_size,#raw output_size],
             binder=sum (#template_limit limits)
                 [3,#binder output_size,#binder output_size],
             types=sum allowance
                 [6,t,t,t,#types output_size,#types output_size]}
          val _=check (#template_limit limits) allowance alignment_size
          fun extent ({raw,binder,types} : size)=
            sum allowance [raw,binder,types]
          (* The named reservation is charged ONCE and consumed ONCE.
             Build/control debits below are separate retained-step visits. *)
          val footprint=sum allowance
            [extent output_size,extent equality_size,extent alignment_size,
             extent equality_size]
          val entitlement=W.reserve work
            {role=W.LocalCarrier,ordinal=ordinal,amount=footprint}
          (* Admit the entire repeated annotation/list portfolio BEFORE
             future type constructors, policies or public beta/ALPHA. *)
          val annotation_weight=sum allowance
            [#types input_size,#types output_size,#types equality_size,
             #types alignment_size,#types equality_size]
          val _=charge common annotation_weight
          val bool_ty=Type.bool
          val partial=invoke common
            (fn()=>Type.mk_type ("fun",[result_ty,bool_ty]))
          val equality=invoke common
            (fn()=>Type.mk_type ("fun",[result_ty,partial]))
          val header=[bool_ty,partial,equality]
          val annotations=List.concat
            [input_types,output_types,header,input_types,output_types,
             header,output_types,output_types,header,input_types,output_types]
          val _=active common
        in Plan {common=common,source=source,operand=operand,recipe=recipe,
          annotations=annotations,output_size=output_size,
          entitlement=entitlement,
          footprint=footprint,used=ref false} end
    in W.with_step work attempt end
    handle primary=>(W.close work;raise primary)

  fun prepare request = prepare_internal NONE request
  fun prepare_admitted
      ({graph,scope,sources,work,ordinal,admission,check_type,scope_opened}
       : admitted_request) =
    let val d = F.describe_for
          {graph = graph,scope = scope,sources = sources,work = work} admission
    in prepare_internal (SOME admission)
      {graph = graph,scope = scope,sources = sources,work = work,
       ordinal = ordinal,redex = #child d,check_type = check_type,
       scope_opened = scope_opened} end
    handle primary => (W.close work;raise primary)

  fun execute (Plan {common,source,operand,recipe,annotations,output_size,
                     entitlement,
                     footprint,used}) =
    let
      val {request={graph,scope,work,check_type,scope_opened,...},limits,
           frames,...}=common
      fun opened parent bindings =
        let val frame=invoke common (fn()=>G.new_scope graph parent bindings)
            val _=frames:=frame :: !frames
            val _=invoke common (fn()=>scope_opened frame)
        in frame end
      fun mapped [] node = NONE
        | mapped ((old,new)::rest) node =
            (charge common 1;
             if old=node then SOME new else mapped rest node)
      val next_env=ref 0
      val built=ref (Redblackmap.mkDict
        (fn ((a,b,c,d),(e,f,h,i))=>
          case Int.compare (a,e) of EQUAL=>
            (case Int.compare (b,f) of EQUAL=>
              (case Int.compare (c,h) of EQUAL=>Int.compare (d,i)
                | answer=>answer) | answer=>answer) | answer=>answer))
      fun build current env_id env retained =
        let
          val _=charge common 1
          val (node_id,mode)=case retained of
              Retain node=>(G.node_id node,0)
            | Insert=>(~1,1)
            | Apply (node,enabled,_,_)=>(G.node_id node,
                if enabled then 2 else 3)
            | Lambda (node,enabled,_,_)=>(G.node_id node,
                if enabled then 2 else 3)
          val key=(node_id,mode,G.scope_id current,env_id)
        in case Redblackmap.peek (!built,key) of
            SOME (node,held)=>
              (ignore (invoke common
                (fn()=>G.closure_child_node graph current held));node)
          | NONE=>
              let
                val node=case retained of
                    Retain node=>(case mapped env node of SOME new=>new
                      | NONE=>node)
                  | Insert=>operand
                  | Apply (_,_,f,x)=>
                      let val f=build current env_id env f
                          val x=build current env_id env x
                      in invoke common
                        (fn()=>G.application graph current (f,x)) end
                  | Lambda (_,_,closure,body)=>
                      let val data=invoke common (fn()=>
                                G.binder_closure_data graph scope closure)
                          val frame=opened current []
                          val binder=invoke common (fn()=>
                            G.fresh_bound_variable graph frame
                              (#binder_term data))
                          (* Subsequent checked rules re-import the NEW
                             body syntax. Bind its canonical spelling, not
                             the old binder alias (which may now be free in
                             an inserted operand). Graph-ID substitution
                             below still maps the original bound node. *)
                          val canonical=invoke common
                            (fn()=>G.representative graph binder)
                          val body_frame=opened frame [(canonical,binder)]
                          val _=charge common 1
                          val token=plus (W.work_limit work) (!next_env,1)
                          val _=next_env:=token
                          val body=build body_frame token
                            ((#binder data,binder)::env) body
                      in invoke common (fn()=>G.recorded_abstraction
                          graph current (#output_limit limits)
                          {binder=binder,body=body,body_frame=body_frame}) end
                val held=invoke common
                  (fn()=>G.closure_root graph current node)
                val _=charge common 1
                val _= #minted common:=(current,held):: !(#minted common)
                val _=built:=Redblackmap.insert (!built,key,(node,held))
              in node end
        end
      fun attempt () =
        let
          val _=active common
          val _=if !used then raise ERR "beta plan already consumed" else ()
          val _=used:=true
          val _=W.consume work entitlement footprint
          val _=List.app (fn ty=>
            invoke common (fn()=>check_type ty)) annotations
          val target=build scope 0 [] recipe
          val _=if invoke common (fn()=>G.unfolded_nodes graph G.RawNodes
              (#output_limit limits) target)=SOME (#raw output_size) andalso
              invoke common (fn()=>G.unfolded_nodes graph
                G.BinderInclusiveNodes (#output_limit limits) target)=
                SOME (#binder output_size) then ()
            else raise ERR "constructed beta output metrics differ"
          val original=invoke common (fn()=>G.representative graph source)
          val expected=invoke common (fn()=>G.representative graph target)
          val primitive=invoke common (fn()=>Thm.BETA_CONV original)
          val (_,actual)=invoke common
            (fn()=>boolSyntax.dest_eq (Thm.concl primitive))
          val align=invoke common (fn()=>Thm.ALPHA actual expected)
          val theorem=invoke common (fn()=>Thm.TRANS primitive align)
          val (left,right)=invoke common
            (fn()=>boolSyntax.dest_eq (Thm.concl theorem))
          val _=if Portable.pointer_eq (left,original) andalso
                   Portable.pointer_eq (right,expected) andalso
                   null (Thm.hyp theorem) andalso
                   Tag.dest_tag (Thm.tag theorem)=([],[]) then ()
                else raise ERR "beta endpoint/Hyp/tag mismatch"
        in Conversion {common=common,source=source,target=target,
                       theorem=theorem} end
    in W.with_step work attempt
       handle primary =>
         (List.app (fn frame=>G.close_scope graph frame handle _=>())
            (!frames);
          raise primary)
    end

  fun validate (Conversion {common,...}) = active common
  fun validate_for {graph,scope,sources,work}
      (Conversion {common as {request=held,...},...}) =
    let
      val root=S.owning_scope sources
      val limits=W.semantic_limits work
      val _=W.validate work graph root sources limits
      val _=G.validate_scope graph scope
      val _=if Portable.pointer_eq (graph,#graph held) andalso
               scope= #scope held andalso
               Portable.pointer_eq (sources,#sources held) andalso
               Portable.pointer_eq (work,#work held) then ()
            else raise ERR "foreign beta owner or work receipt"
    in active common end
    handle primary=>(W.close work;raise primary)
  fun endpoints (conversion as Conversion {source,target,theorem,...}) =
    (validate conversion;{source=source,target=target,theorem=theorem})
  structure RP = SmtReplayResourcePolicy
  structure NativeContract = SmtReplayNativeContract
  type native_budget = NativeContract.contract
  val native_budget_for = NativeContract.for_work
  val validate_native_budget_for = NativeContract.validate_for

  fun native_source_limit
      (budget:NativeContract.limits) category =
    let val {semantic_limits,...} = budget
    in case category of
        F.Original => #input_limit semantic_limits
      | F.Generated => #output_limit semantic_limits
      | F.Auxiliary => #template_limit semantic_limits
    end

  type policy_request =
    {graph:G.graph,scope:G.scope,sources:S.sources,work:W.portfolio,
     ordinal:int,redex:G.closure_child,native_budget:native_budget,
     check_type:Type.hol_type -> unit,scope_opened:G.scope -> unit}
  type policy_admitted_request =
    {graph:G.graph,scope:G.scope,sources:S.sources,work:W.portfolio,
     ordinal:int,admission:F.policy_focus,native_budget:native_budget,
     check_type:Type.hol_type -> unit,scope_opened:G.scope -> unit}
  type policy_common =
    {request:policy_request,root_scope:G.scope,limits:W.limits,
     policy_limits:RP.semantic_policy,native_budget:native_budget,
     admission:F.policy_focus option,source_limit:int,source_policy:RP.limit,
     handles:G.closure_child list ref,frames:G.scope list ref,
     minted:(G.scope * G.closure_child) list ref,
     originals:(G.node * Term.term) list ref,validated:guard_cache}
  datatype policy_plan = PolicyPlan of
    {common:policy_common,source:G.node,operand:G.node,recipe:recipe,
     annotations:Type.hol_type list,output_size:size,
     entitlement:W.entitlement,footprint:int,used:bool ref}
  datatype policy_conversion = PolicyConversion of
    {common:policy_common,source:G.node,target:G.node,theorem:Thm.thm}

  fun pb_active ({request={graph,scope,sources,work,redex,...},root_scope,
               limits,policy_limits,native_budget,admission,source_limit,
               source_policy,handles,frames,minted,originals,validated}
      : policy_common) =
    (W.validate_policy work graph root_scope sources policy_limits;
     ignore (native_budget_for work native_budget);
     G.validate_scope graph scope;
     (case admission of NONE => () | SOME held =>
       let val d = F.describe_with_policy_for
             {graph = graph,scope = scope,sources = sources,work = work} held
       in if #source_limit d = source_policy andalso
           native_source_limit (native_budget_for work native_budget)
             (#category d) = source_limit andalso #node d =
           G.closure_child_node graph scope redex then () else
          raise ERR "different admitted beta source profile" end);
     retained work graph scope validated frames handles minted originals)
    handle primary=>(W.close work;raise primary)

  fun pb_invoke common operation =
    (pb_active common;
     let val result=operation () in pb_active common;result end)

  fun pb_charge (common as {request={work,...},...} : policy_common) amount =
    (W.spend_policy work (IntInf.fromInt amount);pb_active common)

  fun pb_plus limit (a,b) =
    if a > limit orelse b > limit orelse a > limit-b then
      raise ERR "prospective syntax/type budget exhausted"
    else a+b
  fun pb_sum limit values = List.foldl (fn (n,a)=>pb_plus limit (n,a)) 0 values
  fun pb_check maximum type_maximum ({raw,binder,types} : size) =
    if raw<=maximum andalso binder<=maximum andalso types<=type_maximum
    then ()
    else raise ERR "prospective syntax/type budget exhausted"

  (* The type getter is discovery, not a policy or proof callback. Each child
     and association is charged before descent. Getter allocation is not
     thereby a whole private-kernel cost bound. *)
  fun pb_weight common limit ty =
    (pb_charge common 1;
     if pb_invoke common (fn()=>Type.is_vartype ty) then 1
     else
       let val {Args,...}=pb_invoke common (fn()=>Type.dest_thy_type ty)
           fun next [] total = total
             | next (x::xs) total =
                 (pb_charge common 1;
                  next xs (pb_plus limit (total,pb_weight common limit x)))
       in next Args 1 end)

  fun pb_copied common size lists =
    (pb_charge common (#types (size : size));List.concat lists)

  fun pb_type_at common node =
    let val {request={graph,...},...}=common
    in pb_invoke common (fn()=>G.type_of graph node) end

  fun pb_inspect common maximum annotation_maximum handle_root =
    let
      val {request={graph,scope,...},handles,...}=common
      val memo=ref (Redblackmap.mkDict Int.compare)
      val visiting=ref (Redblackset.empty Int.compare)
      fun walk child =
        let
          val _=pb_charge common 1
          val node=pb_invoke common
            (fn()=>G.closure_child_node graph scope child)
          val _=handles:=child :: !handles
          val id=G.node_id node
        in
          case Redblackmap.peek (!memo,id) of
            SOME answer=>answer
          | NONE=>
              let
                val _=if Redblackset.member (!visiting,id) then
                    raise ERR "cyclic recorded closure" else ()
                val _=visiting:=Redblackset.add (!visiting,id)
                val ty=pb_type_at common node
                val t=pb_weight common annotation_maximum ty
                val result=case pb_invoke common (fn()=>G.view graph node) of
                    G.Variable _=>({raw=1,binder=1,types=t},[ty])
                  | G.Constant _=>({raw=1,binder=1,types=t},[ty])
                  | G.Application _=>
                      let val (f,x)=pb_invoke common (fn()=>
                            G.closure_application_children graph scope child)
                          val (fs,ft)=walk f val (xs,xt)=walk x
                      val size : size=
                            {raw=pb_sum maximum [1,#raw fs,#raw xs],
                             binder=pb_sum maximum [1,#binder fs,#binder xs],
                             types=pb_sum annotation_maximum
                               [t,#types fs,#types xs]}
                      in (size,pb_copied common size [[ty],ft,xt]) end
                  | G.AdmittedBinder _=>
                      let val closure=pb_invoke common (fn()=>
                            G.closure_child_binder graph scope child)
                          val data=pb_invoke common (fn()=>
                            G.binder_closure_data graph scope closure)
                          val binder_ty=pb_type_at common (#binder data)
                          val bt=pb_weight common annotation_maximum binder_ty
                          val body=pb_invoke common (fn()=>
                            G.binder_closure_body graph scope closure)
                          val (bs,ts)=walk body
                      val size : size=
                            {raw=pb_plus maximum (1,#raw bs),
                             binder=pb_plus maximum (2,#binder bs),
                             types=pb_sum annotation_maximum [t,bt,#types bs]}
                      in (size,pb_copied common size [[ty,binder_ty],ts]) end
                  | G.OpaqueRetained=>
                      raise ERR "unrecorded opaque beta syntax"
                val value : size = #1 result
                val _=if #raw value <= maximum andalso
                    #binder value <= maximum andalso
                    #types value <= annotation_maximum then () else
                  raise ERR "prospective syntax/type budget exhausted"
                val _=visiting:=Redblackset.delete (!visiting,id)
                val _=memo:=Redblackmap.insert (!memo,id,result)
              in result end
        end
    in walk handle_root end

  fun pb_prepare_internal admission
      (request as {graph,scope,sources,work,ordinal,redex,...}
        : policy_request) =
    let
      val actual_sources=W.original_sources work
      val _=if Portable.pointer_eq (sources,actual_sources) andalso
          Portable.pointer_eq (graph,S.owning_graph actual_sources) then ()
        else raise ERR "different original policy beta Source owner"
      val root_scope=S.owning_scope actual_sources
      val native_budget= #native_budget request
      val native=native_budget_for work native_budget
      val limits= #semantic_limits native
      val policy_limits=W.semantic_policy work
      val selected=Option.map (F.describe_with_policy_for
        {graph=graph,scope=scope,sources=sources,work=work}) admission
      val source_limit=case selected of NONE=> #input_limit limits
        | SOME data=>native_source_limit native (#category data)
      val source_policy=case selected of NONE=> #input_limit policy_limits
        | SOME data=> #source_limit data
      val common : policy_common=
        {request=request,root_scope=root_scope,limits=limits,
         policy_limits=policy_limits,native_budget=native_budget,
         admission=admission,source_limit=source_limit,
         source_policy=source_policy,
         handles = ref [],frames = ref [],minted = ref [],originals = ref [],
         validated = ref NONE}
      fun attempt () =
        let
          val _=pb_active common
          (* Absolute saturation ceiling only. Actual discovery debits and
             upfront reservations use SAME monotonically remaining Work. *)
          val allowance= #type_work_limit native
          val _=pb_charge common 1
          val _=if ordinal>=0 then () else raise ERR "negative stage ordinal"
          val source=pb_invoke common
            (fn()=>G.closure_child_node graph scope redex)
          fun admitted metric =
            case pb_invoke common (fn()=>G.unfolded_nodes graph metric
                source_limit source) of
                SOME size=>
                  if size<=source_limit andalso
                      RP.allows source_policy (IntInf.fromInt size)
                    then ()
                  else raise ERR "cached input syntax exceeds original cap"
              | NONE=>raise ERR "cached input syntax is unknown"
          val _=admitted G.RawNodes
          val _=admitted G.BinderInclusiveNodes
          val (lambda,arg)=pb_invoke common
            (fn()=>G.closure_application_children graph scope redex)
          val closure=pb_invoke common
            (fn()=>G.closure_child_binder graph scope lambda)
          val data=pb_invoke common
            (fn()=>G.binder_closure_data graph scope closure)
          val operand=pb_invoke common
            (fn()=>G.closure_child_node graph scope arg)
          val source_term=pb_invoke common
            (fn()=>G.representative graph source)
          val operand_term=pb_invoke common
            (fn()=>G.representative graph operand)
          val _= #originals common:=
            [(source,source_term),(operand,operand_term)]
          val _=if pb_invoke common (fn()=>G.type_id graph operand)=
              pb_invoke common (fn()=>G.type_id graph (#binder data)) then ()
              else raise ERR "beta operand type differs"
          val (input_size,input_types)=
            pb_inspect common source_limit allowance redex
          val _=if pb_invoke common (fn()=>G.unfolded_nodes graph G.RawNodes
              source_limit source)=SOME (#raw input_size) andalso
              pb_invoke common (fn()=>G.unfolded_nodes graph
                G.BinderInclusiveNodes source_limit source)=
                SOME (#binder input_size) then ()
            else raise ERR "recorded input metrics differ"
          val (arg_size,arg_types)=pb_inspect common source_limit allowance arg
          val body=pb_invoke common
            (fn()=>G.binder_closure_body graph scope closure)
          val maximum= #output_limit limits
          val memo=ref (Redblackmap.mkDict
            (fn ((a,b),(c,d))=>case Int.compare (a,c) of
                EQUAL=>if b=d then EQUAL else if b then GREATER else LESS
              | answer=>answer))
          fun plan child enabled =
            let
              val _=pb_charge common 1
              val node=pb_invoke common
                (fn()=>G.closure_child_node graph scope child)
              val _= #handles common:=child :: !(#handles common)
              val key=(G.node_id node,enabled)
            in case Redblackmap.peek (!memo,key) of
                SOME answer=>answer
              | NONE=>
                let
                  val ty=pb_type_at common node
                  val t=pb_weight common allowance ty
                  val answer=
                    if enabled andalso node= #binder data then
                      (Insert,arg_size,arg_types)
                    else case pb_invoke common (fn()=>G.view graph node) of
                      G.Variable _=>(Retain node,{raw=1,binder=1,types=t},[ty])
                    | G.Constant _=>(Retain node,{raw=1,binder=1,types=t},[ty])
                    | G.Application _=>
                        let val (f,x)=pb_invoke common (fn()=>
                              G.closure_application_children graph scope child)
                            val (fr,fs,ft)=plan f enabled
                            val (xr,xs,xt)=plan x enabled
                        val size : size=
                              {raw=pb_sum maximum [1,#raw fs,#raw xs],
                               binder=pb_sum maximum [1,#binder fs,#binder xs],
                               types=pb_sum allowance [t,#types fs,#types xs]}
                        in (Apply (node,enabled,fr,xr),size,
                            pb_copied common size [[ty],ft,xt]) end
                    | G.AdmittedBinder _=>
                        let val inner=pb_invoke common (fn()=>
                              G.closure_child_binder graph scope child)
                            val inner_data=pb_invoke common (fn()=>
                              G.binder_closure_data graph scope inner)
                            val binder_ty=pb_type_at common
                              (#binder inner_data)
                            val bt=pb_weight common allowance binder_ty
                            val nested=pb_invoke common (fn()=>
                              G.binder_closure_body graph scope inner)
                            val child_enabled=enabled andalso
                              #binder inner_data<> #binder data
                            val (br,bs,ts)=plan nested child_enabled
                        val size : size=
                              {raw=pb_plus maximum (1,#raw bs),
                               binder=pb_plus maximum (2,#binder bs),
                               types=pb_sum allowance [t,bt,#types bs]}
                        in (Lambda (node,enabled,inner,br),size,
                            pb_copied common size [[ty,binder_ty],ts]) end
                    | G.OpaqueRetained=>raise ERR "unrecorded beta body"
                  val (_,size,_)=answer
                  val _=pb_check maximum allowance size
                  val _=pb_charge common 1
                  val _=memo:=Redblackmap.insert (!memo,key,answer)
                in answer end
            end
          val (recipe,output_size,output_types)=plan body true
          val _=if RP.allows (#output_limit policy_limits)
                (IntInf.fromInt (#raw output_size)) andalso
              RP.allows (#output_limit policy_limits)
                (IntInf.fromInt (#binder output_size)) then () else
            raise ERR "prospective syntax/type budget exhausted"
          val result_ty=pb_type_at common source
          val t=pb_weight common allowance result_ty
          val equality_size : size=
            {raw=pb_sum (#template_limit limits)
                 [3,#raw input_size,#raw output_size],
             binder=pb_sum (#template_limit limits)
                 [3,#binder input_size,#binder output_size],
             types=pb_sum allowance
                 [6,t,t,t,#types input_size,#types output_size]}
          val _=pb_check (#template_limit limits) allowance equality_size
          val alignment_size : size=
            {raw=pb_sum (#template_limit limits)
                 [3,#raw output_size,#raw output_size],
             binder=pb_sum (#template_limit limits)
                 [3,#binder output_size,#binder output_size],
             types=pb_sum allowance
                 [6,t,t,t,#types output_size,#types output_size]}
          val _=pb_check (#template_limit limits) allowance alignment_size
          val _=List.app (fn ({raw,binder,...}:size)=>
            if RP.allows (#template_limit policy_limits) (IntInf.fromInt raw)
                andalso RP.allows (#template_limit policy_limits)
                  (IntInf.fromInt binder) then () else
              raise ERR "prospective syntax/type budget exhausted")
            [equality_size,alignment_size]
          fun extent ({raw,binder,types} : size)=
            pb_sum allowance [raw,binder,types]
          (* The named reservation is charged ONCE and consumed ONCE.
             Build/control debits below are separate retained-step visits. *)
          val footprint=pb_sum allowance
            [extent output_size,extent equality_size,extent alignment_size,
             extent equality_size]
          val entitlement=W.reserve_policy work
            {role=W.LocalCarrier,ordinal=ordinal,
             amount=IntInf.fromInt footprint}
          (* Admit the entire repeated annotation/list portfolio BEFORE
             future type constructors, policies or public beta/ALPHA. *)
          val annotation_weight=pb_sum allowance
            [#types input_size,#types output_size,#types equality_size,
             #types alignment_size,#types equality_size]
          val _=pb_charge common annotation_weight
          val bool_ty=Type.bool
          val partial=pb_invoke common
            (fn()=>Type.mk_type ("fun",[result_ty,bool_ty]))
          val equality=pb_invoke common
            (fn()=>Type.mk_type ("fun",[result_ty,partial]))
          val header=[bool_ty,partial,equality]
          val annotations=List.concat
            [input_types,output_types,header,input_types,output_types,
             header,output_types,output_types,header,input_types,output_types]
          val _=pb_active common
        in PolicyPlan {common=common,source=source,operand=operand,
          recipe=recipe,
          annotations=annotations,output_size=output_size,
          entitlement=entitlement,
          footprint=footprint,used=ref false} end
    in W.with_step work attempt end
    handle primary=>(W.close work;raise primary)

  fun prepare_with_policy request = pb_prepare_internal NONE request
  fun prepare_admitted_with_policy
      ({graph,scope,sources,work,ordinal,admission,native_budget,
        check_type,scope_opened}
       : policy_admitted_request) =
    let val _=ignore (native_budget_for work native_budget)
        val d = F.describe_with_policy_for
          {graph = graph,scope = scope,sources = sources,work = work} admission
    in pb_prepare_internal (SOME admission)
      {graph = graph,scope = scope,sources = sources,work = work,
       ordinal=ordinal,redex= #child d,native_budget=native_budget,
       check_type=check_type,
       scope_opened = scope_opened} end
    handle primary => (W.close work;raise primary)

  fun execute_with_policy (PolicyPlan {common,source,operand,recipe,
                     annotations,output_size,
                     entitlement,
                     footprint,used}) =
    let
      val {request={graph,scope,work,check_type,scope_opened,...},limits,
           frames,...}=common
      fun opened parent bindings =
        let val frame=pb_invoke common
              (fn()=>G.new_scope graph parent bindings)
            val _=frames:=frame :: !frames
            val _=pb_invoke common (fn()=>scope_opened frame)
        in frame end
      fun mapped [] node = NONE
        | mapped ((old,new)::rest) node =
            (pb_charge common 1;
             if old=node then SOME new else mapped rest node)
      val next_env=ref 0
      val built=ref (Redblackmap.mkDict
        (fn ((a,b,c,d),(e,f,h,i))=>
          case Int.compare (a,e) of EQUAL=>
            (case Int.compare (b,f) of EQUAL=>
              (case Int.compare (c,h) of EQUAL=>Int.compare (d,i)
                | answer=>answer) | answer=>answer) | answer=>answer))
      fun build current env_id env retained =
        let
          val _=pb_charge common 1
          val (node_id,mode)=case retained of
              Retain node=>(G.node_id node,0)
            | Insert=>(~1,1)
            | Apply (node,enabled,_,_)=>(G.node_id node,
                if enabled then 2 else 3)
            | Lambda (node,enabled,_,_)=>(G.node_id node,
                if enabled then 2 else 3)
          val key=(node_id,mode,G.scope_id current,env_id)
        in case Redblackmap.peek (!built,key) of
            SOME (node,held)=>
              (ignore (pb_invoke common
                (fn()=>G.closure_child_node graph current held));node)
          | NONE=>
              let
                val node=case retained of
                    Retain node=>(case mapped env node of SOME new=>new
                      | NONE=>node)
                  | Insert=>operand
                  | Apply (_,_,f,x)=>
                      let val f=build current env_id env f
                          val x=build current env_id env x
                      in pb_invoke common
                        (fn()=>G.application graph current (f,x)) end
                  | Lambda (_,_,closure,body)=>
                      let val data=pb_invoke common (fn()=>
                                G.binder_closure_data graph scope closure)
                          val frame=opened current []
                          val binder=pb_invoke common (fn()=>
                            G.fresh_bound_variable graph frame
                              (#binder_term data))
                          (* Match the finite builder's canonical lexical
                             binding; never rebind the old source spelling. *)
                          val canonical=pb_invoke common
                            (fn()=>G.representative graph binder)
                          val body_frame=opened frame [(canonical,binder)]
                          val _=pb_charge common 1
                          val native=native_budget_for work
                            (#native_budget common)
                          val token=pb_plus (#type_work_limit native)
                            (!next_env,1)
                          val _=next_env:=token
                          val body=build body_frame token
                            ((#binder data,binder)::env) body
                      in pb_invoke common (fn()=>G.recorded_abstraction
                          graph current (#output_limit limits)
                          {binder=binder,body=body,body_frame=body_frame}) end
                val held=pb_invoke common
                  (fn()=>G.closure_root graph current node)
                val _=pb_charge common 1
                val _= #minted common:=(current,held):: !(#minted common)
                val _=built:=Redblackmap.insert (!built,key,(node,held))
              in node end
        end
      fun attempt () =
        let
          val _=pb_active common
          val _=if !used then raise ERR "beta plan already consumed" else ()
          val _=used:=true
          val _=W.consume_policy work entitlement
            (IntInf.fromInt footprint)
          val _=List.app (fn ty=>
            pb_invoke common (fn()=>check_type ty)) annotations
          val target=build scope 0 [] recipe
          val _=if pb_invoke common (fn()=>G.unfolded_nodes graph G.RawNodes
              (#output_limit limits) target)=SOME (#raw output_size) andalso
              pb_invoke common (fn()=>G.unfolded_nodes graph
                G.BinderInclusiveNodes (#output_limit limits) target)=
                SOME (#binder output_size) then ()
            else raise ERR "constructed beta output metrics differ"
          val original=pb_invoke common (fn()=>G.representative graph source)
          val expected=pb_invoke common (fn()=>G.representative graph target)
          val primitive=pb_invoke common (fn()=>Thm.BETA_CONV original)
          val (_,actual)=pb_invoke common
            (fn()=>boolSyntax.dest_eq (Thm.concl primitive))
          val align=pb_invoke common (fn()=>Thm.ALPHA actual expected)
          val theorem=pb_invoke common (fn()=>Thm.TRANS primitive align)
          val (left,right)=pb_invoke common
            (fn()=>boolSyntax.dest_eq (Thm.concl theorem))
          val _=if Portable.pointer_eq (left,original) andalso
                   Portable.pointer_eq (right,expected) andalso
                   null (Thm.hyp theorem) andalso
                   Tag.dest_tag (Thm.tag theorem)=([],[]) then ()
                else raise ERR "beta endpoint/Hyp/tag mismatch"
        in PolicyConversion {common=common,source=source,target=target,
                       theorem=theorem} end
    in W.with_step work attempt
       handle primary =>
         (List.app (fn frame=>G.close_scope graph frame handle _=>())
            (!frames);
          raise primary)
    end

  fun validate_with_policy (PolicyConversion {common,...}) = pb_active common
  fun validate_with_policy_for {graph,scope,sources,work}
      (PolicyConversion {common as {request=held,...},...}) =
    let
      val _=if Portable.pointer_eq (graph,#graph held) andalso
               scope= #scope held andalso
               Portable.pointer_eq (sources,#sources held) andalso
               Portable.pointer_eq (work,#work held) then ()
            else raise ERR "foreign beta owner or work receipt"
      val actual_sources=W.original_sources work
      val root=S.owning_scope actual_sources
      val limits=W.semantic_policy work
      val _=W.validate_policy work graph root sources limits
      val _=G.validate_scope graph scope
    in pb_active common end
    handle primary=>(W.close work;raise primary)
  fun endpoints_with_policy
      (conversion as PolicyConversion {source,target,theorem,...}) =
    (validate_with_policy conversion;
     {source=source,target=target,theorem=theorem})

end
