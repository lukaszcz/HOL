(* Genuine closure metadata plus an opaque checked equality, no raw pairing. *)
structure SmtReplayOwnedLambda :> SmtReplayOwnedLambda =
struct
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure F = SmtReplayLambdaPreflight
  structure A = SmtReplayFocusAdmission
  val _ = SmtReplayFocusAdmission.describe_for
  val _ = SmtReplayLambdaPreflight.prepare
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedLambda"
  type request =
    {graph : G.graph,caller : G.scope,scope : G.scope,sources : S.sources,
     work : W.portfolio,ordinal : int,binder : G.binder_closure,
     body_fact : P.closed_fact,check_type : Type.hol_type -> unit}
  type admitted_request =
    {graph : G.graph,scope : G.scope,sources : S.sources,
     work : W.portfolio,ordinal : int,admission : A.focus,
     body_fact : P.closed_fact,check_type : Type.hol_type -> unit}
  type captured =
    {node : G.node,node_frame : G.scope,creation_node : G.node,
     declaring_scope : G.scope,binder : G.node,binder_term : Term.term,
     binder_frame : G.scope,body : G.node,body_frame : G.scope,rehomed : bool}
  datatype held = Child of G.closure_child | Binder of G.binder_closure
  datatype phase = Preparing | Ready | Running | Complete | Retired
  type size = {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int,
               ty : IntInf.int}
  type common =
    {request : request,owner : G.scope,limits : W.limits,epoch : int,
     captured : captured,held : (G.scope * held) list ref,
     phase : phase ref,admission : A.focus option}
  datatype plan = Plan of
    {common : common,pre_request : F.request,preflight : F.plan,
     equality : G.node,right : G.node,target : G.node,block : P.block}
  datatype conversion = Conversion of
    {plan : plan,source : G.node,target : G.node,theorem : Thm.thm}

  fun same (a : captured) (b : captured) =
    #node a = #node b andalso #node_frame a = #node_frame b andalso
    #creation_node a = #creation_node b andalso
    #declaring_scope a = #declaring_scope b andalso
    #binder a = #binder b andalso #binder_frame a = #binder_frame b andalso
    #body a = #body b andalso #body_frame a = #body_frame b andalso
    #rehomed a = #rehomed b andalso
    Portable.pointer_eq (#binder_term a,#binder_term b)
  fun retire ({request = {work,...},phase,...} : common) =
    (phase := Retired;W.close work)
  fun active (common as {request = {graph,caller,scope,sources,work,
                          binder,...},owner,limits,epoch,captured,held,
                        phase,admission,...} : common) =
    ((case !phase of Retired => raise ERR "active" "lambda retired"
       | _ => ());
     W.validate work graph owner sources limits;
     (case admission of NONE => () | SOME focus =>
        let val d = A.describe_for
              {graph = graph,scope = scope,sources = sources,work = work} focus
        in if #node d = #node captured then () else
          raise ERR "active" "different admitted lambda" end);
     G.validate_scope graph caller;G.validate_scope graph scope;
     if Type.type_epoch () = epoch andalso
         same captured (G.binder_closure_data graph caller binder) then ()
       else raise ERR "active" "closure or Type epoch changed";
     List.app (fn (fixed,handle_value) => case handle_value of
         Child child => ignore (G.closure_child_node graph fixed child)
       | Binder closure =>
           ignore (G.binder_closure_data graph fixed closure)) (!held))
    handle primary => (retire common;raise primary)
  fun invoke common operation =
    (active common;let val result = operation () val _ = active common
                   in result end)
    handle primary => (retire common;raise primary)
  fun charge (common as {request = {work,...},...} : common) amount =
    (active common;W.spend work amount;active common)

  fun prepare_internal admission
      (request as {graph,caller,scope,sources,work,ordinal,binder,
                   body_fact,check_type}) =
    W.with_step work (fn () =>
    let
      val owner = S.owning_scope sources
      val limits = W.semantic_limits work
      val _ = W.validate work graph owner sources limits
      val _ = if ordinal >= 0 then () else
        raise ERR "prepare" "negative lambda ordinal"
      val source_cap = case admission of NONE => #input_limit limits
        | SOME focus => #source_limit (A.describe_for
            {graph = graph,scope = scope,sources = sources,work = work} focus)
      val captured = G.binder_closure_data graph caller binder
      val common : common =
        {request = request,owner = owner,limits = limits,
         epoch = Type.type_epoch (),captured = captured,held = ref [],
         phase = ref Preparing,admission = admission}
      fun run operation = invoke common operation
      val body_scope = #body_frame captured
      val _ = active common
      (* Private frame walks are genuine guards, not certified unit-cost IO.
         No original-Source DAG membership restriction excludes generated
         binders. This is exact visibility, not raw-origin evidence. *)
      val _ = if run (fn () => G.scope_visible graph scope
          (#node_frame captured)) andalso
          run (fn () => G.scope_visible graph body_scope owner) then () else
        raise ERR "prepare" "closure outside the original owning scope"
      val equality = run (fn () => P.closed_node body_fact)
      fun cached label cap node =
        List.app (fn metric =>
          (charge common 1;
           case run (fn () => G.unfolded_nodes graph metric cap node) of
               SOME n => if n <= cap then () else
                 raise ERR "prepare" (label ^ " exceeds original cap")
             | NONE => raise ERR "prepare" (label ^ " unknown metric")))
          [G.RawNodes,G.BinderInclusiveNodes]
      val _ = cached "source lambda" source_cap (#node captured)
      val _ = cached "body equality" (#template_limit limits) equality
      val (partial,right) = case run (fn () => G.view graph equality) of
          G.Application pair => pair
        | _ => raise ERR "prepare" "body evidence is not equality"
      val (head,left) = case run (fn () => G.view graph partial) of
          G.Application pair => pair
        | _ => raise ERR "prepare" "body equality has no operator"
      val _ = if left = #body captured andalso
          run (fn () => G.type_id graph left) =
          run (fn () => G.type_id graph right) then () else
        raise ERR "prepare" "body endpoints or type differ"
      val _ = case run (fn () => G.view graph head) of G.Constant id =>
          if KernelSig.id_compare (id,#Name (Term.dest_thy_constid
              boolSyntax.equality)) = EQUAL then () else
            raise ERR "prepare" "different equality declaration"
        | _ => raise ERR "prepare" "nonconstant equality head"
      (* F inventories the whole fixed local P context, closed law, sole
         final INST and lifted lambda equality BEFORE policies and freeze.
         Its owner scope is original S, not a renewed body-frame owner. *)
      val pre_request : F.request =
        {graph = graph,scope = owner,sources = sources,work = work,
         ordinal = ordinal,body_scope = body_scope,
         declaring_scope = #node_frame captured,old_lambda = #node captured,
         binder = #binder captured,equality = equality,left = left,
         right = right,body_fact = body_fact}
      val preflight = run (fn () => case admission of
          NONE => F.prepare pre_request
        | SOME focus => F.prepare_admitted
            {request = pre_request,source_scope = scope,admission = focus})
      val ceiling = IntInf.fromInt (W.work_limit work)
      fun plus a b = IntInf.min (ceiling+1,a+b)
      fun times a b = IntInf.min (ceiling+1,a*b)
      val memo = ref ([] : (G.node * size) list)
      fun lookup node [] = NONE
        | lookup node ((old,value)::rest) =
            (charge common 1;if node = old then SOME value
             else lookup node rest)
      fun type_weight ty =
        let
          fun walk [] total = total
            | walk (pending::more) total =
              (charge common 1;case pending of [] => walk more total
               | current::rest =>
                 let val next = plus total 1
                     val _ = if next <= ceiling then () else
                       raise ERR "prepare" "type annotation exceeds Work"
                 in if run (fn () => Type.is_vartype current) then
                      walk (rest::more) next
                    else walk
                      ((run (fn () => #2 (Type.dest_type current)))::
                       rest::more) next end)
        in walk [[ty]] 0 end
      fun visit fixed child =
        let
          val _ = charge common 1
          val node = run (fn () => G.closure_child_node graph fixed child)
          val _ = #held common := (fixed,Child child) :: !(#held common)
        in case lookup node (!memo) of SOME value => value
         | NONE =>
          let
            val ty = type_weight (run (fn () => G.type_of graph node))
            val value = case run (fn () => G.view graph node) of
                G.Application _ =>
                  let val (f,x) = run (fn () =>
                        G.closure_application_children graph fixed child)
                      val a = visit fixed f val b = visit fixed x
                  in {raw = plus 1 (plus (#raw a) (#raw b)),
                      inc = plus 1 (plus (#inc a) (#inc b)),
                      ann = plus ty (plus (#ann a) (#ann b)),ty = ty}
                  end
              | G.AdmittedBinder _ =>
                  let val nested = run (fn () =>
                        G.closure_child_binder graph fixed child)
                      val _ = charge common 1
                      val _ = #held common :=
                        (fixed,Binder nested) :: !(#held common)
                      val d = run (fn () =>
                        G.binder_closure_data graph fixed nested)
                      val bt = type_weight
                        (run (fn () => G.type_of graph (#binder d)))
                      val b = visit fixed (run (fn () =>
                        G.binder_closure_body graph fixed nested))
                  in {raw = plus 1 (#raw b),inc = plus 2 (#inc b),
                      ann = plus ty (plus bt (#ann b)),ty = ty} end
              | G.OpaqueRetained => raise ERR "prepare"
                  "unrecorded opaque body annotations"
              | _ => {raw = 1,inc = 1,ann = ty,ty = ty}
            val _ = charge common 1
            val _ = memo := (node,value) :: !memo
          in value end
        end
      val old = visit (#node_frame captured) (run (fn () =>
        G.closure_root graph (#node_frame captured) (#node captured)))
      val rhs = visit body_scope
        (run (fn () => G.closure_root graph body_scope right))
      val bt = type_weight
        (run (fn () => G.type_of graph (#binder captured)))
      val new : size =
        {raw = plus 1 (#raw rhs),inc = plus 2 (#inc rhs),
         ann = plus (#ty old) (plus bt (#ann rhs)),ty = #ty old}
      (* ALPHA(old,ABS-left) may be LARGER than the final equation when the
         body shrinks. Likewise ALPHA(ABS-right,target) uses two outputs.
         Repeated raw/binder/type incidences are admitted separately. *)
      fun equation (a : size) (b : size) =
        {raw = plus 3 (plus (#raw a) (#raw b)),
         inc = plus 3 (plus (#inc a) (#inc b)),
         ann = plus 6 (plus (times 3 (#ty a))
           (plus (#ann a) (#ann b))),ty = 1} : size
      val equations = [equation old old,equation new new,
                       equation old new,equation old new]
      fun check (value : size) =
        if #raw value <= IntInf.fromInt (#template_limit limits) andalso
            #inc value <= IntInf.fromInt (#template_limit limits) then () else
          raise ERR "prepare" "ALPHA/TRANS footprint exceeds template cap"
      val _ = List.app check equations
      val amount = List.foldl (fn (value : size,total) =>
        plus total (plus (#raw value)
          (plus (#inc value) (#ann value)))) 0 equations
      val _ = if amount > 0 andalso amount <= ceiling then () else
        raise ERR "prepare" "lift footprint exceeds original Work"
      val token = W.reserve work
        {role = W.ClosedRecord,ordinal = ordinal,amount = IntInf.toInt amount}
      val _ = W.consume work token (IntInf.toInt amount)
      fun policy ty =
        (active common;F.validate pre_request preflight;
         check_type ty;active common;F.validate pre_request preflight)
      val types = run (fn () => F.policy_types pre_request preflight)
      val _ = List.app policy types
      (* Construct ONLY from the actual retained binder/body frames. A
         rehomed closure creates its result in the genuine declaring frame
         and uses G's checked rehome, never a fabricated Raw origin. *)
      val first = run (fn () => G.recorded_abstraction graph
        (#declaring_scope captured) (#output_limit limits)
        {binder = #binder captured,body = right,body_frame = body_scope})
      val target = if #node_frame captured = #declaring_scope captured
        then first else #node (run (fn () =>
          G.rehome graph (#node_frame captured) first))
      val _ = charge common 1
      val target_child = run (fn () => G.closure_root graph scope target)
      val _ = #held common := (scope,Child target_child) :: !(#held common)
      val block = run (fn () => P.freeze_with_closed graph
        {scope = body_scope,roots = [equality],sources = [],
         closed_facts = [body_fact],template_limit = #template_limit limits})
      val _ = #phase common := Ready
      val _ = active common
    in Plan {common = common,pre_request = pre_request,
       preflight = preflight,equality = equality,right = right,
       target = target,block = block} end)

  fun prepare request = prepare_internal NONE request
  fun prepare_admitted {graph,scope,sources,work,ordinal,admission,
                         body_fact,check_type} =
    let val d = A.describe_for
          {graph = graph,scope = scope,sources = sources,work = work} admission
        val binder = G.closure_child_binder graph scope (#child d)
    in prepare_internal (SOME admission)
      {graph = graph,caller = scope,scope = scope,sources = sources,
       work = work,ordinal = ordinal,binder = binder,body_fact = body_fact,
       check_type = check_type} end
    handle primary => (W.close work;raise primary)

  fun execute (plan as Plan {common,pre_request,preflight,equality,right,
                             target,block}) =
    let
      val {request = {graph,work,body_fact,...},captured,phase,...} = common
      fun run operation = invoke common operation
      fun guard () = (active common;F.validate pre_request preflight)
      fun clean theorem =
        if List.null (Thm.hyp theorem) andalso
            List.all (fn oracle => oracle = "DISK_THM")
              (#1 (Tag.dest_tag (Thm.tag theorem))) andalso
            List.null (Tag.axioms_of (Thm.tag theorem)) then () else
          raise ERR "execute" "local lambda theorem is not clean closed"
    in W.with_step work (fn () =>
      ((guard ();
        (case !phase of Ready => phase := Running
         | _ => raise ERR "execute" "lambda plan is one shot");
        let
          val edge = run (fn () => P.closed block body_fact)
          (* Exactly one local final INST outside the captured binder.
             The actual body equality has NO Source assumptions. *)
          val body = run (fn () => P.realize block equality edge)
          val _ = guard ()
          val _ = clean body
          val (lhs,rhs) = Term.dest_eq (Thm.concl body)
          val _ = if Portable.pointer_eq
              (lhs,run (fn () => G.representative graph (#body captured)))
              andalso Portable.pointer_eq
              (rhs,run (fn () => G.representative graph right)) then () else
            raise ERR "execute" "realized body endpoints changed"
          val abstraction = run (fn () => Thm.ABS (#binder_term captured) body)
          val (a,b) = Term.dest_eq (Thm.concl abstraction)
          val left = run (fn () => Thm.ALPHA
            (G.representative graph (#node captured)) a)
          val right = run
            (fn () => Thm.ALPHA b (G.representative graph target))
          val tail = run (fn () => Thm.TRANS abstraction right)
          val theorem = run (fn () => Thm.TRANS left tail)
          val _ = clean theorem
          val (actual_source,actual_target) = Term.dest_eq (Thm.concl theorem)
          val _ = if Portable.pointer_eq (actual_source,
              run (fn () => G.representative graph (#node captured))) andalso
              Portable.pointer_eq (actual_target,
              run (fn () => G.representative graph target)) then () else
            raise ERR "execute" "final canonical endpoints changed"
          val _ = guard ()
          val _ = phase := Complete
        in Conversion {plan = plan,source = #node captured,target = target,
          theorem = theorem} end)
       handle primary => (retire common;raise primary))) end

  fun validate_for {graph,caller,scope,sources,work}
      (Conversion {plan = Plan {common,...},...}) =
    let val {request = original,phase,...} = common
    in
      if Portable.pointer_eq (graph,#graph original) andalso
          caller = #caller original andalso scope = #scope original andalso
          Portable.pointer_eq (sources,#sources original) andalso
          Portable.pointer_eq (work,#work original) then
        (active common;case !phase of Complete => ()
         | _ => raise ERR "validate_for" "incomplete conversion")
      else raise ERR "validate_for" "different expected original receipt"
    end handle primary => (W.close work;raise primary)
  fun endpoints (Conversion {plan = Plan {common,...},source,target,theorem}) =
    (active common;
     case !(#phase common) of Complete =>
       {source = source,target = target,theorem = theorem}
     | _ => raise ERR "endpoints" "incomplete conversion")
  structure RP=SmtReplayResourcePolicy
  structure NC=SmtReplayNativeContract
  structure I=SmtReplayImport
  type policy_request=
    {graph:G.graph,scope:G.scope,sources:S.sources,work:W.portfolio,
     ordinal:int,admission:A.policy_focus,body_fact:P.closed_fact,
     native_contract:NC.contract,profiles:G.policy_opaque_profile list,
     check_type:Type.hol_type->unit}
  type policy_common=
    {request:policy_request,root:G.scope,binder:G.binder_closure,
     captured:captured,epoch:int,symbols:int,limits:RP.semantic_policy,
     phase:phase ref,held:(G.scope*G.closure_child) list ref}
  datatype policy_plan=PolicyPlan of
    {common:policy_common,original:Thm.thm,imported:G.source,
     opened:G.source,right:G.node,target:G.node}
  datatype policy_conversion=PolicyConversion of
    {plan:policy_plan,theorem:Thm.thm}
  fun pl_retire ({request={work,...},phase,...}:policy_common)=
    (phase:=Retired;W.close work)
  fun pl_active (common as {request={graph,scope,sources,work,admission,
        body_fact,native_contract,profiles,...},root,binder,captured,
        epoch,symbols,limits,phase,held}:policy_common)=
    ((NC.validate_for work native_contract;
      W.validate_policy work graph root sources limits;
      if !phase<>Retired andalso Type.type_epoch ()=epoch andalso
          Term.term_epoch ()=symbols then () else
        raise ERR "policy_active" "lambda lifetime changed";
      let val d=A.describe_with_policy_for
            {graph=graph,scope=scope,sources=sources,work=work} admission
      in if #node d= #node captured andalso
          same captured (G.binder_closure_data graph scope binder) then ()
        else raise ERR "policy_active" "different admitted binder" end;
      P.validate_closed_fact_with_policy graph (#body_frame captured)
        (#template_limit limits) body_fact;
      List.app (fn (fixed,child)=>
        ignore (G.closure_child_node graph fixed child)) (!held);
      List.app (fn profile=>ignore
        (G.opaque_profile_data_with_policy graph scope profile)) profiles)
     handle primary=>(pl_retire common;raise primary))
  fun pl_invoke common action=
    (pl_active common;
     let val value=action () in pl_active common;value end)
    handle primary=>(pl_retire common;raise primary)
  fun prepare_admitted_with_policy (request as
      {graph,scope,sources,work,ordinal,admission,body_fact,native_contract,
       profiles,check_type}:policy_request)=
    ((NC.validate_for work native_contract;
      W.with_step work (fn()=>
      let
        val actual=W.original_sources work
        val _=if Portable.pointer_eq (sources,actual) andalso
            Portable.pointer_eq (graph,S.owning_graph actual) then () else
          raise ERR "policy_prepare" "different original Source owner"
        val root=S.owning_scope actual
        val limits=W.semantic_policy work
        val native=NC.for_work work native_contract
        val finite= #semantic_limits native
        val type_cap=IntInf.fromInt (#type_work_limit native)
        val used=ref (0:IntInf.int)
        fun debit amount=
          if amount>=0 andalso !used+amount<=type_cap then
            (W.spend_policy work amount;used:= !used+amount)
          else raise ERR "policy_prepare" "native planning allowance exhausted"
        val _=if ordinal>=0 then () else
          raise ERR "policy_prepare" "negative lambda ordinal"
        val d=A.describe_with_policy_for
          {graph=graph,scope=scope,sources=sources,work=work} admission
        val source_cap=case #category d of A.Original=> #input_limit finite
          | A.Generated=> #output_limit finite
          | A.Auxiliary=> #template_limit finite
        val binder=G.closure_child_binder graph scope (#child d)
        val captured=G.binder_closure_data graph scope binder
        val common:policy_common=
          {request=request,root=root,binder=binder,captured=captured,
           epoch=Type.type_epoch (),symbols=Term.term_epoch (),limits=limits,
           phase=ref Preparing,held=ref []}
        fun run action=pl_invoke common action
        fun tick ()=(pl_active common;debit 1;pl_active common)
        val body_scope= #body_frame captured
        val _=pl_active common
        val _=if run (fn()=>G.scope_visible graph scope (#node_frame captured))
            andalso run (fn()=>G.scope_visible graph body_scope root) then ()
          else raise ERR "policy_prepare" "binder outside original owner"
        val equality=run (fn()=>P.closed_node body_fact)
        val original=run (fn()=>P.closed_original body_fact)
        val (partial,right)=case run (fn()=>G.view graph equality) of
            G.Application p=>p
          | _=>raise ERR "policy_prepare" "body fact is not equality"
        val (head,left)=case run (fn()=>G.view graph partial) of
            G.Application p=>p
          | _=>raise ERR "policy_prepare" "body equality has no head"
        val _=if left= #body captured andalso
            run (fn()=>G.type_id graph left)=run (fn()=>G.type_id graph right)
          then () else raise ERR "policy_prepare" "body endpoints/types differ"
        val _=case run (fn()=>G.view graph head) of G.Constant id=>
            if KernelSig.id_compare (id,#Name (Term.dest_thy_constid
                boolSyntax.equality))=EQUAL then () else
              raise ERR "policy_prepare" "different equality declaration"
          | _=>raise ERR "policy_prepare" "nonconstant equality head"
        val (imported,opened)=run (fn()=>G.imported_opened_source graph
          body_scope (Thm.concl original) equality)
        fun plus a b=
          if a>=0 andalso b>=0 andalso a+b<=type_cap then a+b else
            raise ERR "policy_prepare" "native repeated Type/portfolio ceiling"
        val types=ref ([]:Type.hol_type list)
        val type_memo=ref ([]:(Type.hol_type*IntInf.int) list)
        fun lookup same key []=NONE
          | lookup same key ((old,value)::rest)=
              (tick ();if same (key,old) then SOME value
               else lookup same key rest)
        fun weight ty=case lookup Portable.pointer_eq ty (!type_memo) of
            SOME n=>n
          | NONE=>
              let fun walk [] total=total
                    | walk (pending::more) total=
                        (tick ();case pending of []=>walk more total
                         | current::rest=>
                             let val next=plus total 1
                             in if run (fn()=>Type.is_vartype current)
                               then walk (rest::more) next else
                               walk ((run (fn()=> #2
                                 (Type.dest_type current)))::rest::more) next
                             end)
                  val n=walk [[ty]] 0
                  val _=types:=ty:: !types
                  val _=type_memo:=(ty,n):: !type_memo
              in n end
        val memo=ref ([]:(G.node*size) list)
        fun inspect fixed child=
          let val _=tick ()
              val node=run (fn()=>G.closure_child_node graph fixed child)
              val _= #held common:=(fixed,child):: !(#held common)
          in case lookup (op =) node (!memo) of SOME value=>value
           | NONE=>
              let val ty=weight (run (fn()=>G.type_of graph node))
                  fun opaque []=raise ERR "policy_prepare"
                        "opaque syntax lacks a genuine policy profile"
                    | opaque (profile::rest)=
                        let val _=tick ()
                            val p=run (fn()=>
                              G.opaque_profile_data_with_policy graph fixed
                                profile)
                        in if #node p=node then
                          (List.app (fn t=>ignore (weight t)) (#types p);
                           {raw= #raw p,inc= #inc p,ann= #ann p,ty= #ty p})
                          else opaque rest end
                  val value:size=case run (fn()=>G.view graph node) of
                      G.Application _=>
                        let val (f,x)=run (fn()=>
                              G.closure_application_children graph fixed child)
                            val a=inspect fixed f val b=inspect fixed x
                        in {raw=1+ #raw a+ #raw b,inc=1+ #inc a+ #inc b,
                            ann=plus ty (plus (#ann a) (#ann b)),ty=ty} end
                    | G.AdmittedBinder _=>
                        let val closure=run (fn()=>
                              G.closure_child_binder graph fixed child)
                            val b=run (fn()=>
                              G.binder_closure_data graph fixed closure)
                            val bt=weight (run (fn()=>
                              G.type_of graph (#binder b)))
                            val subtree=inspect fixed (run (fn()=>
                              G.binder_closure_body graph fixed closure))
                        in {raw=1+ #raw subtree,inc=2+ #inc subtree,
                            ann=plus ty (plus bt (#ann subtree)),ty=ty} end
                    | G.OpaqueRetained=>opaque profiles
                    | _=>{raw=1,inc=1,ann=ty,ty=ty}
                  val _=if #ann value<=type_cap then () else
                    raise ERR "policy_prepare" "annotation ceiling exceeded"
                  val _=memo:=(node,value):: !memo
              in value end
          end
        fun metric fixed node=inspect fixed
          (run (fn()=>G.closure_root graph fixed node))
        fun check label native_cap metadata (value:size)=
          if #raw value<=IntInf.fromInt native_cap andalso
              #inc value<=IntInf.fromInt native_cap andalso
              RP.allows metadata (#raw value) andalso
              RP.allows metadata (#inc value) then () else
            raise ERR "policy_prepare" (label^" exceeds native/metadata cap")
        val old=metric (#node_frame captured) (#node captured)
        val lhs=metric body_scope left val rhs=metric body_scope right
        val eq=metric body_scope equality
        val _=check "source lambda" source_cap (#source_limit d) old
        val _=check "source body" source_cap (#source_limit d) lhs
        val _=check "body right" (#output_limit finite)
          (#output_limit limits) rhs
        val _=check "body equality" (#template_limit finite)
          (#template_limit limits) eq
        val bt=weight (run (fn()=>G.type_of graph (#binder captured)))
        val result:size={raw=1+ #raw rhs,inc=2+ #inc rhs,
          ann=plus (#ty old) (plus bt (#ann rhs)),ty= #ty old}
        val _=check "lifted lambda" (#output_limit finite)
          (#output_limit limits) result
        fun equation (a:size) (b:size):size=
          {raw=3+ #raw a+ #raw b,inc=3+ #inc a+ #inc b,
           ann=plus 6 (plus (3* #ty a) (plus (#ann a) (#ann b))),ty=1}
        val lifted=[equation old old,equation result result,
                    equation old result,equation old result]
        val _=List.app (check "lift equation" (#template_limit finite)
          (#template_limit limits)) lifted
        (* Actual retained proof operands are admitted too. These public
           count-only traversals grant no binding or endpoint authority. *)
        fun original_input theorem=
          let val _=tick () val term=run (fn()=>Thm.concl theorem)
              val cap=IntInf.fromInt (#template_limit finite)
              val _=if null (run (fn()=>Thm.hyp theorem)) then () else
                raise ERR "policy_prepare" "surviving local hypotheses"
              fun walk [] raw inc ann=
                    {raw=raw,inc=inc,ann=ann,ty=1}:size
                | walk (current::rest) raw inc ann=
                    let val _=tick ()
                        val raw=raw+1 val inc=inc+1
                        val _=if raw<=cap andalso inc<=cap then () else
                          raise ERR "policy_prepare"
                            "actual proof input syntax ceiling"
                        val ty=run (fn()=>Term.type_of current)
                        val annotation=weight ty
                        val ann=plus ann annotation
                    in if run (fn()=>Term.is_comb current) then
                        let val (f,x)=run (fn()=>Term.dest_comb current)
                        in walk (f::x::rest) raw inc ann end
                      else if run (fn()=>Term.is_abs current) then
                        let val (domain,_)=run (fn()=>Type.dom_rng ty)
                            val bt=weight domain
                            val _=if inc+1<=cap then () else
                              raise ERR "policy_prepare"
                                "actual proof binder slot ceiling"
                            val body=run (fn()=>I.count_body current)
                        in walk (body::rest) raw (inc+1) (plus ann bt) end
                      else walk rest raw inc ann end
          in walk [term] 0 0 0 end
        val actual_inputs=List.map original_input
          [original,#bridge imported,#bridge opened]
        val bridges=[equation eq eq,equation eq eq,equation eq eq,eq]
        val _=List.app (check "body bridge" (#template_limit finite)
          (#template_limit limits)) bridges
        val portfolio=old::lhs::rhs::eq::result::lifted@bridges@actual_inputs
        val amount=List.foldl (fn (v:size,n)=>
          plus n (plus (#raw v) (plus (#inc v) (#ann v)))) 0 portfolio
        val _=if amount>0 andalso !used+amount<=type_cap then () else
          raise ERR "policy_prepare" "native lift portfolio exceeds allowance"
        val token=W.reserve_policy work
          {role=W.ClosedRecord,ordinal=ordinal,amount=amount}
        val _=W.consume_policy work token amount
        val _=used:= !used+amount
        val _=List.app (fn ty=>run (fn()=>check_type ty)) (List.rev (!types))
        val first=run (fn()=>G.recorded_abstraction_with_policy graph
          (#declaring_scope captured)
          (RP.AtMost (IntInf.fromInt (#output_limit finite)))
          {binder= #binder captured,body=right,body_frame=body_scope})
        val target=if #node_frame captured= #declaring_scope captured then
            first else #node (run (fn()=>G.rehome graph
              (#node_frame captured) first))
        val _=ignore (metric scope target)
        val _= #phase common:=Ready
        val _=pl_active common
      in PolicyPlan {common=common,original=original,imported=imported,
        opened=opened,right=right,target=target} end))
     handle primary=>(W.close work;raise primary))
  fun execute_with_policy (plan as PolicyPlan
      {common,original,imported,opened,right,target})=
    let val
      {request={graph,scope,work,body_fact,...},captured,phase,...}=common
        fun run action=pl_invoke common action
        fun guard ()=
          (pl_active common;
           let val (actual_import,actual_open)=G.imported_opened_source graph
                 (#body_frame captured) (Thm.concl original)
                 (P.closed_node body_fact)
           in if Portable.pointer_eq (#bridge imported,#bridge actual_import)
                 andalso Portable.pointer_eq (#bridge opened,
                   #bridge actual_open) then () else
               raise ERR "policy_execute" "body proof association changed"
           end)
        fun clean th=if null (Thm.hyp th) andalso
            null (Tag.axioms_of (Thm.tag th)) andalso
            List.all (fn name=>name="DISK_THM")
              (#1 (Tag.dest_tag (Thm.tag th))) then () else
          raise ERR "policy_execute" "lambda theorem is not clean closed"
    in W.with_step work (fn()=>
      ((guard ();
        if !phase=Ready then phase:=Running else
          raise ERR "policy_execute" "lambda plan is one-shot";
        let val bridge=run (fn()=>Thm.TRANS
              (#bridge imported) (#bridge opened))
            val body=run (fn()=>Thm.EQ_MP bridge original)
            val _=clean body
            val (lhs,rhs)=Term.dest_eq (Thm.concl body)
            val _=if Portable.pointer_eq (lhs,
                run (fn()=>G.representative graph (#body captured))) andalso
                Portable.pointer_eq (rhs,
                  run (fn()=>G.representative graph right)) then () else
              raise ERR "policy_execute" "realized body endpoints changed"
            val abstraction=run (fn()=>Thm.ABS (#binder_term captured) body)
            val (a,b)=Term.dest_eq (Thm.concl abstraction)
            val left=run (fn()=>Thm.ALPHA
              (G.representative graph (#node captured)) a)
            val right=run (fn()=>Thm.ALPHA b (G.representative graph target))
            val tail=run (fn()=>Thm.TRANS abstraction right)
            val theorem=run (fn()=>Thm.TRANS left tail)
            val _=clean theorem
            val (actual_source,actual_target)=Term.dest_eq (Thm.concl theorem)
            val _=if Portable.pointer_eq (actual_source,
                run (fn()=>G.representative graph (#node captured))) andalso
                Portable.pointer_eq (actual_target,
                  run (fn()=>G.representative graph target)) then () else
              raise ERR "policy_execute" "final canonical endpoints changed"
            val _=guard () val _=phase:=Complete
        in PolicyConversion {plan=plan,theorem=theorem} end)
       handle primary=>(pl_retire common;raise primary))) end
  fun validate_with_policy_for {graph,caller,scope,sources,work}
      (PolicyConversion {plan=PolicyPlan {common,...},...})=
    ((let val {request=held,phase,...}=common
      in if Portable.pointer_eq (work,#work held) andalso
          Portable.pointer_eq (graph,#graph held) andalso
          caller= #scope held andalso scope= #scope held andalso
          Portable.pointer_eq (sources,#sources held) then () else
        raise ERR "policy_validate" "different expected original receipt";
        pl_active common;
        if !phase=Complete then () else
          raise ERR "policy_validate" "incomplete lambda conversion" end)
     handle primary=>(W.close work;raise primary))
  fun endpoints_with_policy_for expected
      (held as PolicyConversion {plan=PolicyPlan {common,...},...})=
    (validate_with_policy_for expected held;
     let val PolicyConversion {plan=PolicyPlan {target,...},theorem}=held
     in {source= #node (#captured common),target=target,theorem=theorem} end)

  type effective_common=
    {request:policy_request,root:G.scope,binder:G.binder_closure,
     captured:captured,epoch:int,symbols:int,limits:RP.semantic_policy,
     phase:phase ref,held:(G.scope*G.closure_child) list ref}
  datatype canonical_policy_plan=CanonicalPolicyPlan of
    {common:effective_common,original:Thm.thm,right:G.node,target:G.node,
     condition:G.node option}
  datatype canonical_policy_conversion=CanonicalPolicyConversion of
    {plan:canonical_policy_plan,theorem:Thm.thm}
  datatype conditional_policy_plan=ConditionalPolicyPlan of
    canonical_policy_plan
  datatype conditional_policy_conversion=ConditionalPolicyConversion of
    canonical_policy_conversion
  fun el_retire ({request={work,...},phase,...}:effective_common)=
    (phase:=Retired;W.close work)
  fun el_active (common as {request={graph,scope,sources,work,admission,
        body_fact,native_contract,profiles,...},root,binder,captured,
        epoch,symbols,limits,phase,held}:effective_common)=
    ((NC.validate_for work native_contract;
      W.validate_policy work graph root sources limits;
      if !phase<>Retired andalso Type.type_epoch ()=epoch andalso
          Term.term_epoch ()=symbols then () else
        raise ERR "policy_active" "lambda lifetime changed";
      let val d=A.describe_with_policy_for
            {graph=graph,scope=scope,sources=sources,work=work} admission
      in if #node d= #node captured andalso
          same captured (G.binder_closure_data graph scope binder) then ()
        else raise ERR "policy_active" "different admitted binder" end;
      P.validate_closed_fact_with_policy graph (#body_frame captured)
        (#template_limit limits) body_fact;
      List.app (fn (fixed,child)=>
        ignore (G.closure_child_node graph fixed child)) (!held);
      List.app (G.validate_policy_opaque_profile graph) profiles)
     handle primary=>(el_retire common;raise primary))
  fun el_invoke common action=
    (el_active common;
     let val value=action () in el_active common;value end)
    handle primary=>(el_retire common;raise primary)
  fun prepare_canonical_policy conditional (request as
      {graph,scope,sources,work,ordinal,admission,body_fact,native_contract,
       profiles,check_type}:policy_request)=
    ((NC.validate_for work native_contract;
      W.with_step work (fn()=>
      let
        val actual=W.original_sources work
        val _=if Portable.pointer_eq (sources,actual) andalso
            Portable.pointer_eq (graph,S.owning_graph actual) then () else
          raise ERR "policy_prepare" "different original Source owner"
        val root=S.owning_scope actual
        val limits=W.semantic_policy work
        val native=NC.for_work work native_contract
        val finite= #semantic_limits native
        val type_cap=IntInf.fromInt (#type_work_limit native)
        val used=ref (0:IntInf.int)
        fun debit amount=
          if amount>=0 andalso !used+amount<=type_cap then
            (W.spend_policy work amount;used:= !used+amount)
          else raise ERR "policy_prepare" "native planning allowance exhausted"
        val _=if ordinal>=0 then () else
          raise ERR "policy_prepare" "negative lambda ordinal"
        val d=A.describe_with_policy_for
          {graph=graph,scope=scope,sources=sources,work=work} admission
        val source_cap=case #category d of A.Original=> #input_limit finite
          | A.Generated=> #output_limit finite
          | A.Auxiliary=> #template_limit finite
        val binder=G.closure_child_binder graph scope (#child d)
        val captured=G.binder_closure_data graph scope binder
        val common:effective_common=
          {request=request,root=root,binder=binder,captured=captured,
           epoch=Type.type_epoch (),symbols=Term.term_epoch (),limits=limits,
           phase=ref Preparing,held=ref []}
        fun run action=el_invoke common action
        fun tick ()=(el_active common;debit 1;el_active common)
        val body_scope= #body_frame captured
        val _=el_active common
        val _=if run (fn()=>G.scope_visible graph scope (#node_frame captured))
            andalso run (fn()=>G.scope_visible graph body_scope root) then ()
          else raise ERR "policy_prepare" "binder outside original owner"
        val statement=run (fn()=>P.closed_node body_fact)
        val (condition,equality)=if conditional then
            let
              val (partial,equality)=case run (fn()=>G.view graph statement) of
                  G.Application pair=>pair
                | _=>raise ERR "conditional_prepare"
                    "body fact is not a conditional equality"
              val (head,condition)=case run (fn()=>G.view graph partial) of
                  G.Application pair=>pair
                | _=>raise ERR "conditional_prepare"
                    "body fact has no implication head"
              val _=case run (fn()=>G.view graph head) of G.Constant id=>
                  if KernelSig.id_compare
                      (id,#Name (Term.dest_thy_constid
                        boolSyntax.implication))=EQUAL then () else
                    raise ERR "conditional_prepare"
                      "different implication declaration"
                | _=>raise ERR "conditional_prepare"
                    "nonconstant implication head"
              val _=if Type.compare
                  (run (fn()=>G.type_of graph condition),Type.bool)=EQUAL
                then () else raise ERR "conditional_prepare"
                  "condition is not Boolean"
            in (SOME condition,equality) end
          else (NONE,statement)
        val original=run (fn()=>P.closed_original body_fact)
        val (partial,right)=case run (fn()=>G.view graph equality) of
            G.Application p=>p
          | _=>raise ERR "policy_prepare" "body fact is not equality"
        val (head,left)=case run (fn()=>G.view graph partial) of
            G.Application p=>p
          | _=>raise ERR "policy_prepare" "body equality has no head"
        val _=if left= #body captured andalso
            run (fn()=>G.type_id graph left)=run (fn()=>G.type_id graph right)
          then () else raise ERR "policy_prepare" "body endpoints/types differ"
        val _=case run (fn()=>G.view graph head) of G.Constant id=>
            if KernelSig.id_compare (id,#Name (Term.dest_thy_constid
                boolSyntax.equality))=EQUAL then () else
              raise ERR "policy_prepare" "different equality declaration"
          | _=>raise ERR "policy_prepare" "nonconstant equality head"
        (* This is an actual owned proof, not an equality inferred from
           import or semantic matching. No new opening can change body IDs. *)
        val (native_left,native_right)=case condition of NONE=>
            run (fn()=>boolSyntax.dest_eq (Thm.concl original))
          | SOME antecedent=>
            let val (native_condition,native_equality)=run (fn()=>
                  boolSyntax.dest_imp (Thm.concl original))
                val _=if Portable.pointer_eq (native_condition,
                    run (fn()=>G.representative graph antecedent)) then ()
                  else raise ERR "conditional_prepare"
                    "noncanonical actual condition"
            in run (fn()=>boolSyntax.dest_eq native_equality) end
        val _=if Portable.pointer_eq (native_left,run (fn()=>
              G.representative graph (#body captured))) andalso
            Portable.pointer_eq (native_right,run (fn()=>
              G.representative graph right)) then () else
          raise ERR "canonical_prepare" "noncanonical actual body theorem"

        fun plus a b=
          if a>=0 andalso b>=0 andalso a+b<=type_cap then a+b else
            raise ERR "policy_prepare" "native repeated Type/portfolio ceiling"
        val types=ref ([]:Type.hol_type list)
        val type_memo=ref ([]:(Type.hol_type*IntInf.int) list)
        fun lookup same key []=NONE
          | lookup same key ((old,value)::rest)=
              (tick ();if same (key,old) then SOME value
               else lookup same key rest)
        fun weight ty=case lookup Portable.pointer_eq ty (!type_memo) of
            SOME n=>n
          | NONE=>
              let fun walk [] total=total
                    | walk (pending::more) total=
                        (tick ();case pending of []=>walk more total
                         | current::rest=>
                             let val next=plus total 1
                             in if run (fn()=>Type.is_vartype current)
                               then walk (rest::more) next else
                               walk ((run (fn()=> #2
                                 (Type.dest_type current)))::rest::more) next
                             end)
                  val n=walk [[ty]] 0
                  val _=types:=ty:: !types
                  val _=type_memo:=(ty,n):: !type_memo
              in n end
        val opaque_used=ref false
        val memo=ref ([]:((G.node*G.scope)*size) list)
        fun inspect fixed child=
          let val _=tick ()
              val node=run (fn()=>G.closure_child_node graph fixed child)
              val effective=run (fn()=>G.closure_child_scope graph fixed child)
              val _= #held common:=(fixed,child):: !(#held common)
          in case lookup (op =) (node,effective) (!memo) of SOME value=>value
           | NONE=>
              let val ty=weight (run (fn()=>G.type_of graph node))
                  fun opaque []=raise ERR "policy_prepare"
                        "opaque syntax lacks a genuine policy profile"
                    | opaque (profile::rest)=
                        let val _=tick ()
                        in case run (fn()=>G.opaque_profile_for_node_with_policy
                            graph effective node profile) of
                            NONE=>opaque rest
                          | SOME p=>
                            (opaque_used:=true;
                             List.app (fn t=>ignore (weight t)) (#types p);
                             {raw= #raw p,inc= #inc p,ann= #ann p,ty= #ty p})
                        end
                  val value:size=case run (fn()=>G.view graph node) of
                      G.Application _=>
                        let val (f,x)=run (fn()=>
                              G.closure_application_children graph fixed child)
                            val a=inspect fixed f val b=inspect fixed x
                        in {raw=1+ #raw a+ #raw b,inc=1+ #inc a+ #inc b,
                            ann=plus ty (plus (#ann a) (#ann b)),ty=ty} end
                    | G.AdmittedBinder _=>
                        let val closure=run (fn()=>
                              G.closure_child_binder graph fixed child)
                            val b=run (fn()=>
                              G.binder_closure_data graph fixed closure)
                            val bt=weight (run (fn()=>
                              G.type_of graph (#binder b)))
                            val subtree=inspect fixed (run (fn()=>
                              G.binder_closure_body graph fixed closure))
                        in {raw=1+ #raw subtree,inc=2+ #inc subtree,
                            ann=plus ty (plus bt (#ann subtree)),ty=ty} end
                    | G.OpaqueRetained=>opaque profiles
                    | _=>{raw=1,inc=1,ann=ty,ty=ty}
                  val _=if #ann value<=type_cap then () else
                    raise ERR "policy_prepare" "annotation ceiling exceeded"
                  val _=memo:=((node,effective),value):: !memo
              in value end
          end
        fun metric fixed node=inspect fixed
          (run (fn()=>G.closure_root graph fixed node))
        fun check label native_cap metadata (value:size)=
          if #raw value<=IntInf.fromInt native_cap andalso
              #inc value<=IntInf.fromInt native_cap andalso
              RP.allows metadata (#raw value) andalso
              RP.allows metadata (#inc value) then () else
            raise ERR "policy_prepare" (label^" exceeds native/metadata cap")
        val old=metric (#node_frame captured) (#node captured)
        val lhs=metric body_scope left val rhs=metric body_scope right
        val eq=metric body_scope equality
        val _=check "source lambda" source_cap (#source_limit d) old
        val _=check "source body" source_cap (#source_limit d) lhs
        val _=check "body right" (#output_limit finite)
          (#output_limit limits) rhs
        val _=check "body equality" (#template_limit finite)
          (#template_limit limits) eq
        val bt=weight (run (fn()=>G.type_of graph (#binder captured)))
        val result:size={raw=1+ #raw rhs,inc=2+ #inc rhs,
          ann=plus (#ty old) (plus bt (#ann rhs)),ty= #ty old}
        val _=check "lifted lambda" (#output_limit finite)
          (#output_limit limits) result
        fun equation (a:size) (b:size):size=
          {raw=3+ #raw a+ #raw b,inc=3+ #inc a+ #inc b,
           ann=plus 6 (plus (3* #ty a) (plus (#ann a) (#ann b))),ty=1}
        val lifted=[equation old old,equation result result,
                    equation old result,equation old result]
        val _=List.app (check "lift equation" (#template_limit finite)
          (#template_limit limits)) lifted
        (* This variant accepts only an already exact graph FV inventory.
           Opening an opaque condition needs its own pre-effect bridge
           portfolio; record_opened_view is not a metadata observation. *)
        val condition_portfolio=case condition of NONE=>[]
          | SOME antecedent=>
            let
              val value=metric body_scope antecedent
              val _=check "lambda condition" (#template_limit finite)
                (#template_limit limits) value
              val variables=case run (fn()=>
                  G.free_variable_nodes graph antecedent) of
                  SOME variables=>variables
                | NONE=>raise ERR "conditional_prepare"
                    "condition needs an admitted exact free-variable view"
              val _=List.app (fn variable=>
                (tick ();if variable= #binder captured then
                   raise ERR "conditional_prepare"
                     "condition depends on the actual bound variable"
                 else ())) variables
              val native=run (fn()=>G.representative graph antecedent)
              val _=if run (fn()=>Term.free_in
                  (#binder_term captured) native) then
                  raise ERR "conditional_prepare"
                    "condition captures the native binder atom"
                else ()
              (* UNDISCH's ASSUME input contributes E twice. UNDISCH,
                 ABS and both TRANS results retain exactly E. DISCH
                 creates the final closed implication. Boolean
                 implication has the same annotation profile as Boolean
                 equality, including its two application nodes. *)
              val final=equation old result
              val discharged=equation value final
              val _=check "conditional lift statement"
                (#template_limit finite) (#template_limit limits) discharged
            in [value,value,value,value,value,value,discharged] end
        (* Actual retained proof operands are admitted too. These public
           count-only traversals grant no binding or endpoint authority. *)
        fun original_input theorem=
          let val _=tick () val term=run (fn()=>Thm.concl theorem)
              val cap=IntInf.fromInt (#template_limit finite)
              val _=if null (run (fn()=>Thm.hyp theorem)) then () else
                raise ERR "policy_prepare" "surviving local hypotheses"
              fun walk [] raw inc ann=
                    {raw=raw,inc=inc,ann=ann,ty=1}:size
                | walk (current::rest) raw inc ann=
                    let val _=tick ()
                        val raw=raw+1 val inc=inc+1
                        val _=if raw<=cap andalso inc<=cap then () else
                          raise ERR "policy_prepare"
                            "actual proof input syntax ceiling"
                        val ty=run (fn()=>Term.type_of current)
                        val annotation=weight ty
                        val ann=plus ann annotation
                    in if run (fn()=>Term.is_comb current) then
                        let val (f,x)=run (fn()=>Term.dest_comb current)
                        in walk (f::x::rest) raw inc ann end
                      else if run (fn()=>Term.is_abs current) then
                        let val (domain,_)=run (fn()=>Type.dom_rng ty)
                            val bt=weight domain
                            val _=if inc+1<=cap then () else
                              raise ERR "policy_prepare"
                                "actual proof binder slot ceiling"
                            val body=run (fn()=>I.count_body current)
                        in walk (body::rest) raw (inc+1) (plus ann bt) end
                      else walk rest raw inc ann end
          in walk [term] 0 0 0 end
        val actual_inputs=List.map original_input [original]
        (* Direct canonical proof needs no import bridge, TRANS of import
           receipts, or EQ_MP. The remaining actual ABS/ALPHA/TRANS portfolio
           and full surviving-Hyp/Type input gates are retained. *)
        val portfolio=old::lhs::rhs::eq::result::
          lifted@actual_inputs@condition_portfolio
        val amount=List.foldl (fn (v:size,n)=>
          plus n (plus (#raw v) (plus (#inc v) (#ann v)))) 0 portfolio
        val _=if amount>0 andalso !used+amount<=type_cap then () else
          raise ERR "policy_prepare" "native lift portfolio exceeds allowance"
        val token=W.reserve_policy work
          {role=W.ClosedRecord,ordinal=ordinal,amount=amount}
        val _=W.consume_policy work token amount
        val _=used:= !used+amount
        val _=List.app (fn ty=>run (fn()=>check_type ty)) (List.rev (!types))
        val first=run (fn()=>if !opaque_used then
          G.recorded_abstraction_with_profile_policy graph
            (#declaring_scope captured)
            {maximum= #output_limit limits,native_limit= #output_limit finite,
             type_work_limit= #type_work_limit native,
             binder= #binder captured,body=right,body_frame=body_scope,
             profiles=profiles,step=tick}
          else G.recorded_abstraction_with_policy graph
            (#declaring_scope captured)
            (RP.AtMost (IntInf.fromInt (#output_limit finite)))
            {binder= #binder captured,body=right,body_frame=body_scope})
        val target=if #node_frame captured= #declaring_scope captured then
            first else #node (run (fn()=>G.rehome graph
              (#node_frame captured) first))
        val _=ignore (metric scope target)
        val _= #phase common:=Ready
        val _=el_active common
      in CanonicalPolicyPlan {common=common,original=original,right=right,
           target=target,condition=condition} end))
     handle primary=>(W.close work;raise primary))
  fun prepare_canonical_admitted_with_policy request=
    prepare_canonical_policy false request
  fun prepare_conditional_admitted_with_policy request=
    ConditionalPolicyPlan (prepare_canonical_policy true request)
  fun execute_canonical_with_policy (plan as CanonicalPolicyPlan
      {common,original,right,target,condition})=
    let val
      {request={graph,scope,work,body_fact,...},captured,phase,...}=common
        fun run action=el_invoke common action
        fun guard ()=
          (el_active common;
           let val theorem=run (fn()=>P.closed_original body_fact)
               val (lhs,rhs)=case condition of NONE=>
                   run (fn()=>boolSyntax.dest_eq (Thm.concl theorem))
                 | SOME antecedent=>
                   let val (actual,equality)=run (fn()=>
                         boolSyntax.dest_imp (Thm.concl theorem))
                       val _=if Portable.pointer_eq (actual,run (fn()=>
                           G.representative graph antecedent)) then () else
                         raise ERR "canonical_execute"
                           "actual conditional premise changed"
                   in run (fn()=>boolSyntax.dest_eq equality) end
           in if Portable.pointer_eq (theorem,original) andalso
                 Portable.pointer_eq (lhs,run (fn()=>
                   G.representative graph (#body captured))) andalso
                 Portable.pointer_eq (rhs,run (fn()=>
                   G.representative graph right)) then () else
               raise ERR "canonical_execute" "actual body proof changed"
           end)
        fun clean th=if null (Thm.hyp th) andalso
            null (Tag.axioms_of (Thm.tag th)) andalso
            List.all (fn name=>name="DISK_THM")
              (#1 (Tag.dest_tag (Thm.tag th))) then () else
          raise ERR "policy_execute" "lambda theorem is not clean closed"
    in W.with_step work (fn()=>
      ((guard ();
        if !phase=Ready then phase:=Running else
          raise ERR "policy_execute" "lambda plan is one-shot";
        let val _=clean original
            val body=case condition of NONE=>original
              | SOME _=>run (fn()=>Drule.UNDISCH original)
            val (lhs,rhs)=Term.dest_eq (Thm.concl body)
            val _=if Portable.pointer_eq (lhs,
                run (fn()=>G.representative graph (#body captured))) andalso
                Portable.pointer_eq (rhs,
                  run (fn()=>G.representative graph right)) then () else
              raise ERR "policy_execute" "realized body endpoints changed"
            val abstraction=run (fn()=>Thm.ABS (#binder_term captured) body)
            val (a,b)=Term.dest_eq (Thm.concl abstraction)
            val left=run (fn()=>Thm.ALPHA
              (G.representative graph (#node captured)) a)
            val right=run (fn()=>Thm.ALPHA b (G.representative graph target))
            val tail=run (fn()=>Thm.TRANS abstraction right)
            val lifted=run (fn()=>Thm.TRANS left tail)
            val theorem=case condition of NONE=>lifted
              | SOME antecedent=>run (fn()=>Thm.DISCH
                  (G.representative graph antecedent) lifted)
            val _=clean theorem
            val (actual_source,actual_target)=case condition of NONE=>
                Term.dest_eq (Thm.concl theorem)
              | SOME antecedent=>
                let val (actual,equality)=boolSyntax.dest_imp
                      (Thm.concl theorem)
                    val _=if Portable.pointer_eq (actual,run (fn()=>
                        G.representative graph antecedent)) then () else
                      raise ERR "policy_execute"
                        "final conditional premise changed"
                in Term.dest_eq equality end
            val _=if Portable.pointer_eq (actual_source,
                run (fn()=>G.representative graph (#node captured))) andalso
                Portable.pointer_eq (actual_target,
                  run (fn()=>G.representative graph target)) then () else
              raise ERR "policy_execute" "final canonical endpoints changed"
            val _=guard () val _=phase:=Complete
        in CanonicalPolicyConversion {plan=plan,theorem=theorem} end)
       handle primary=>(el_retire common;raise primary))) end
  fun validate_canonical_with_policy_for {graph,caller,scope,sources,work}
      (CanonicalPolicyConversion {plan=CanonicalPolicyPlan {common,...},...})=
    ((let val {request=held,phase,...}=common
      in if Portable.pointer_eq (work,#work held) andalso
          Portable.pointer_eq (graph,#graph held) andalso
          caller= #scope held andalso scope= #scope held andalso
          Portable.pointer_eq (sources,#sources held) then () else
        raise ERR "policy_validate" "different expected original receipt";
        el_active common;
        if !phase=Complete then () else
          raise ERR "policy_validate" "incomplete lambda conversion" end)
     handle primary=>(W.close work;raise primary))
  fun endpoints_canonical_with_policy_for expected
      (held as CanonicalPolicyConversion {plan=CanonicalPolicyPlan {common,...},...})=
    (validate_canonical_with_policy_for expected held;
     let val CanonicalPolicyConversion {plan=CanonicalPolicyPlan {target,...},theorem}=held
     in {source= #node (#captured common),target=target,theorem=theorem} end)

  fun execute_conditional_with_policy (ConditionalPolicyPlan plan)=
    ConditionalPolicyConversion (execute_canonical_with_policy plan)
  fun validate_conditional_with_policy_for expected
      (ConditionalPolicyConversion converted)=
    validate_canonical_with_policy_for expected converted
  fun endpoints_conditional_with_policy_for expected
      (ConditionalPolicyConversion converted)=
     let
       val {source,target,theorem}=
         endpoints_canonical_with_policy_for expected converted
       val CanonicalPolicyConversion
         {plan=CanonicalPolicyPlan {condition,...},...}=converted
       val antecedent=case condition of SOME node=>node
         | NONE=>raise ERR "conditional_endpoints"
             "missing authenticated condition"
     in {condition=antecedent,source=source,target=target,theorem=theorem} end

  fun conditional_native_contract_with_policy_for expected
      (held as ConditionalPolicyConversion
        (CanonicalPolicyConversion
          {plan=CanonicalPolicyPlan {common,...},...})) =
    (validate_conditional_with_policy_for expected held;
     #native_contract (#request common))
end
