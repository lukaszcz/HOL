structure SmtReplayInvocationWork :> SmtReplayInvocationWork =
struct
  structure RP = SmtReplayResourcePolicy
  structure A = SmtReplayOriginalAcquisition
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure R = ReplayRedblackPrivateWork
  structure B = SmtLib_GraphBackend
  val ERR = Feedback.mk_HOL_ERR "SmtReplayInvocationWork"
  type limits = {input_limit : int,output_limit : int,template_limit : int}
  datatype role = LawInstance | LocalCarrier | GoalDenial | ClosedRecord
    | FactAssembly | FinalFreeze
  datatype phase = Idle | Busy | Retired
  datatype token_phase = Ready | Spent
  datatype portfolio = Portfolio of
    {graph : G.graph,scope : G.scope,sources : S.sources,limits : limits,
     limit : int,used : int ref,epoch : int,phase : phase ref,
     names : ((role * int) * entitlement) list ref}
    | GuardedPortfolio of
    {graph:G.graph,scope:G.scope,sources:S.sources,limits:limits,
     limit:int,used:int ref,epoch:int,phase:phase ref,
     names:((role * int) * entitlement) list ref,path:G.scope_path,
     meter:R.scope_meter}
    | PolicyPortfolio of
    {graph:G.graph,scope:G.scope,sources:S.sources,
     limits:RP.semantic_policy,limit:RP.limit,used:IntInf.int ref,
     epoch:int,phase:phase ref,
     names:((role * int) * entitlement) list ref,
     priced:(G.scope_path * R.scope_meter) option}
    | OriginalPortfolio of
    {graph:G.graph,scope:G.scope,sources:S.sources,work:A.work,
     request:A.request,names:((role * int) * entitlement) list ref}
  and entitlement = Entitlement of
    {owner : portfolio,remaining : int ref,state : token_phase ref}
    | PolicyEntitlement of
    {owner:portfolio,remaining:IntInf.int ref,state:token_phase ref}
    | OriginalEntitlement of
    {owner:portfolio,remaining:IntInf.int ref,state:token_phase ref}
  fun close (Portfolio {phase,...}) = phase := Retired
    | close (GuardedPortfolio {phase,...}) = phase := Retired
    | close (PolicyPortfolio {phase,...}) = phase := Retired
    | close (OriginalPortfolio {work,...}) = A.retire_work work
  fun fail portfolio operation text =
    (close portfolio;raise ERR operation text)
  fun abort_work_limit portfolio =
    fail portfolio "admit" "original cumulative work allowance exhausted"

  (* Same stable Source/A Work/request. No Work counter, meter or phase. *)
  fun original_active (p as OriginalPortfolio {sources,work,...}) =
    (S.validate_original_work work sources
     handle primary => (close p;raise primary))
    | original_active p = fail p "active" "not an original portfolio"
  fun original_inside (p as OriginalPortfolio {work,...}) =
    ((original_active p;
      (* charge authenticates SAME Busy before the actual debit/effects. *)
      A.charge work 16)
     handle primary => (close p;raise primary))
    | original_inside p = fail p "admit" "not an original portfolio"
  fun original_spend (p as OriginalPortfolio {work,...}) amount =
    ((original_inside p;A.charge work 32;A.charge work amount)
     handle primary => (close p;raise primary))
    | original_spend p _ = fail p "admit" "not an original portfolio"
  fun original_reserve (p as OriginalPortfolio {work,names,...})
      {role,ordinal,amount} =
    ((let
        val _ = original_inside p
        val _ = A.charge work 64
        val _ = if ordinal >= 0 andalso amount > 0 then () else
          fail p "reserve" "malformed future entitlement"
        val key = (role,ordinal)
        fun issued entries =
          (A.charge work 16;
           case entries of [] => false
           | (old,_)::rest => old=key orelse issued rest)
        val _ = if issued (!names) then
          fail p "reserve" "future role already issued" else ()
        (* One admission on A, then retained token/table administration.
           Failure before publication cannot create usable token credit. *)
        val _ = A.charge work amount
        val _ = A.charge work 32
        val token = OriginalEntitlement
          {owner=p,remaining=ref amount,state=ref Ready}
        val _ = names := (key,token):: !names
      in token end)
     handle primary => (close p;raise primary))
    | original_reserve p _ = fail p "reserve" "not an original portfolio"
  fun original_consume (p as OriginalPortfolio {work,...}) token amount =
    ((original_inside p;A.charge work 32;
      case token of OriginalEntitlement {owner,remaining,state} =>
        (if Portable.pointer_eq(p,owner) then () else
           fail p "consume" "foreign future entitlement";
         (* Owner before any retained remaining/state read or mutation. *)
         (case !state of Spent =>
            fail p "consume" "future entitlement consumed" | Ready => ());
         if amount >= 0 andalso amount <= !remaining then
           (remaining := !remaining-amount;
            if !remaining=0 then state := Spent else ())
         else fail p "consume" "future entitlement exceeds retained reservation")
      | _ => fail p "consume" "foreign future entitlement")
     handle primary => (close p;raise primary))
    | original_consume p _ _ =
        fail p "consume" "not an original portfolio"
  fun original_int_refusal p operation =
    fail p operation "original route requires policy methods"

  (* Policy portfolios use one exact counter, including all genuine G/R
     programs. The optional path is a mode, not a second allowance. *)
  fun policy_debit (p as PolicyPortfolio {limit,used,...}) amount =
    if amount >= 0 andalso RP.allows limit (!used+amount) then
      used := !used+amount
    else fail p "admit" "original cumulative work allowance exhausted"
    | policy_debit p _ = fail p "admit" "not a policy portfolio"
  fun policy_active (p as PolicyPortfolio
      {graph,scope,sources,epoch,phase,priced,...}) =
    (((case !phase of Retired =>
        raise ERR "active" "work portfolio retired" | _ => ());
     (case priced of NONE =>
        (G.validate_scope graph scope;
         if Portable.pointer_eq (graph,S.owning_graph sources) andalso
             scope=S.owning_scope sources andalso Type.type_epoch ()=epoch
           then () else
             raise ERR "active" "original owner or epoch changed")
      | SOME(path,_) =>
        (policy_debit p (12+G.scope_path_validation_work path);
         if Type.type_epoch ()=epoch then () else
           raise ERR "active" "original owner or epoch changed";
         G.validate_scope_path graph scope path)))
    handle primary => (close p;raise primary))
    | policy_active p = fail p "active" "not a policy portfolio"
  fun policy_overhead (p as PolicyPortfolio {priced,...}) amount =
        (case priced of NONE => () | SOME _ => policy_debit p amount)
    | policy_overhead p _ = fail p "admit" "not a policy portfolio"
  fun policy_inside (p as PolicyPortfolio {phase,...}) =
    (policy_active p;policy_overhead p 8;
     case !phase of Busy => ()
       | _ => fail p "admit" "no owned work action")
    | policy_inside p = fail p "admit" "not a policy portfolio"
  fun policy_spend (p as PolicyPortfolio {priced,...}) amount =
    (policy_inside p;
     case priced of NONE => policy_debit p amount
       | SOME _ =>
         (policy_debit p 7;
          if amount >= 0 then policy_debit p (amount+6)
          else fail p "admit" "original cumulative work allowance exhausted"))
    | policy_spend p _ = fail p "admit" "not a policy portfolio"
  fun policy_reserve (p as PolicyPortfolio {names,...})
      {role,ordinal,amount} =
    let
      val _ = policy_inside p
      val _ = if ordinal >= 0 andalso amount > 0 then () else
        fail p "reserve" "malformed future entitlement"
      val _ = policy_spend p 1
      val key = (role,ordinal)
      fun issued [] = false
        | issued ((old,_)::rest) =
            (policy_spend p 1;old=key orelse issued rest)
      val _ = if issued (!names) then
          fail p "reserve" "future role already issued" else ()
      val _ = policy_spend p amount
      val _ = policy_spend p 1
      val token = PolicyEntitlement
        {owner=p,remaining=ref amount,state=ref Ready}
      val _ = names := (key,token):: !names
    in token end
    | policy_reserve p _ = fail p "reserve" "not a policy portfolio"
  fun policy_consume p (PolicyEntitlement {owner,remaining,state}) amount =
    (policy_inside p;
     if Portable.pointer_eq (p,owner) then () else
       fail p "consume" "foreign future entitlement";
     (case !state of Spent => fail p "consume" "future entitlement consumed"
       | Ready => ());
     if amount >= 0 andalso amount <= !remaining then
       (remaining := !remaining-amount;
        if !remaining=0 then state := Spent else ())
     else fail p "consume" "future entitlement exceeds retained reservation")
    | policy_consume p _ _ =
        (policy_inside p;fail p "consume" "foreign future entitlement")

  fun active_legacy (portfolio as Portfolio
      {graph,scope,sources,epoch,phase,...}) =
    ((case !phase of Retired => raise ERR "active" "work portfolio retired"
       | _ => ());
     G.validate_scope graph scope;
     if Portable.pointer_eq (graph,S.owning_graph sources) andalso
         scope = S.owning_scope sources andalso Type.type_epoch () = epoch
       then () else raise ERR "active" "original owner or epoch changed")
    handle primary => (close portfolio;raise primary)
  (* No active/spend recursion: debit the SAME private counter before
     authentic root-path execution. Six budget read/arithmetic/write events
     are included by each caller before this private payer is entered. *)
  fun scope_debit (p as GuardedPortfolio {limit,used,...}) amount =
        if amount >= 0 andalso amount <= IntInf.fromInt (limit - !used) then
          used := !used + IntInf.toInt amount
        else fail p "admit" "original cumulative work allowance exhausted"
    | scope_debit p _ = fail p "admit" "not a priced root portfolio"
  fun active (p as PolicyPortfolio _) = policy_active p
    | active (p as Portfolio _) = active_legacy p
    | active (p as GuardedPortfolio {graph,scope,epoch,phase,path,...}) =
      (((case !phase of Retired =>
          raise ERR "active" "work portfolio retired" | _ => ());
       (* Cost getter1, phase read/branch2, epoch getter/comparison/branch3,
          private counter payer6; actual G frame instructions are separate. *)
       scope_debit p (12 + G.scope_path_validation_work path);
       if Type.type_epoch () = epoch then () else
         raise ERR "active" "original owner or epoch changed";
       G.validate_scope_path graph scope path)
      handle primary => (close p;raise primary))
    | active (p as OriginalPortfolio _) = original_active p
  fun original_sources (p as Portfolio {sources,...}) = (active p;sources)
    | original_sources (p as GuardedPortfolio {sources,...}) =
      (active p;sources)
    | original_sources (p as PolicyPortfolio {sources,...}) =
        (active p;sources)
    | original_sources (p as OriginalPortfolio {sources,...}) =
        (original_active p;sources)
  fun semantic_limits (p as Portfolio {limits,...}) = (active p;limits)
    | semantic_limits (p as GuardedPortfolio {limits,...}) = (active p;limits)
    | semantic_limits (p as PolicyPortfolio _) =
        fail p "semantic_limits" "policy route has no int projection"
    | semantic_limits (p as OriginalPortfolio _) =
        original_int_refusal p "semantic_limits"
  fun work_limit (p as Portfolio {limit,...}) = (active p;limit)
    | work_limit (p as GuardedPortfolio {limit,...}) = (active p;limit)
    | work_limit (p as PolicyPortfolio _) =
        fail p "work_limit" "policy route has no int projection"
    | work_limit (p as OriginalPortfolio _) =
        original_int_refusal p "work_limit"
  fun audit (Portfolio {used,phase,...}) =
    {charged = !used,retired = case !phase of Retired => true | _ => false}
    | audit (GuardedPortfolio {used,phase,...}) =
    {charged = !used,retired = case !phase of Retired => true | _ => false}
    | audit (PolicyPortfolio _) =
        raise ERR "audit" "policy route requires exact audit_policy"
    | audit (OriginalPortfolio _) =
        raise ERR "audit" "original route requires exact audit_policy"
  fun same_limits (a : limits) (b : limits) =
    #input_limit a = #input_limit b andalso
    #output_limit a = #output_limit b andalso
    #template_limit a = #template_limit b
  fun begin graph scope sources
      {limits = limits as {input_limit,output_limit,template_limit},
       work_limit} =
    let
      (* Foreign owner/malformed pre-work requests do NOT claim that object. *)
      val _ = G.validate_scope graph scope
      val _ = if Portable.pointer_eq (graph,S.owning_graph sources) andalso
          scope = S.owning_scope sources then () else
        raise ERR "begin" "foreign original Source owner"
      val _ = if input_limit > 0 andalso output_limit > 0 andalso
          template_limit > 0 andalso work_limit > 0 then () else
        raise ERR "begin" "malformed pre-work limits"
      (* After this latch ANY failure is a consumed SAME-Source attempt.
         Fresh S.new objects are distinct: outer ownership is still required. *)
      val _ = S.claim_invocation_work sources
      val epoch = Type.type_epoch ()
    in Portfolio {graph = graph,scope = scope,sources = sources,limits = limits,
      limit = work_limit,used = ref 0,epoch = epoch,phase = ref Idle,
      names = ref []} end
  fun begin_with_scope_guard graph scope sources
      {limits=limits as {input_limit,output_limit,template_limit},work_limit} =
    let
      val original = S.owner_for_scope_guard sources
      val _ = if Portable.pointer_eq (graph,#graph original) andalso
          scope = #scope original then () else
        raise ERR "begin" "foreign original Source owner"
      val _ = if input_limit > 0 andalso output_limit > 0 andalso
          template_limit > 0 andalso work_limit > 0 then () else
        raise ERR "begin" "malformed pre-work limits"
      (* Fixed bootstrap envelope70 covers this bounded straight-line
         program: Source owner fields/record and ownership branches9,
         positive-limit branches8, plan arguments/budget/getter metadata13,
         Source claim fields/call/latch8, epoch/Work record/three refs7,
         plus19 for parameter/control/ledger primitives and6 for the
         coupled meter record/identity. Dynamic G lookup
         setup and its actual first frame program are separately authentic.
         This is not a fee for an arbitrary helper or caller quotation. *)
      fun commit () =
        let
          val _ = if work_limit >= 70 then () else
            raise ERR "begin" "original Work cannot bootstrap priced root"
          val path = G.prepare_scope_path graph scope
            {remaining_work=work_limit-70}
          val setup = G.scope_path_setup_work path
          val validation = G.scope_path_validation_work path
          val charged = 70+setup+validation
          val _ = if charged <= IntInf.fromInt work_limit then () else
            raise ERR "begin" "original Work cannot admit priced root setup"
          (* Budget decision precedes the ordinary Source latch, frame
             execution and Work publication. ONE claim/counter only. *)
          val _ = S.claim_invocation_work_with_path sources path
          val epoch = Type.type_epoch ()
          val used = ref (IntInf.toInt charged)
          val meter = R.new_scope_meter {limit=work_limit,charged=used}
        in GuardedPortfolio
          {graph=graph,scope=scope,sources=sources,limits=limits,
           limit=work_limit,used=used,epoch=epoch,
           phase=ref Idle,names=ref [],path=path,meter=meter} end
    in commit () handle primary =>
         (S.consume_scope_guard_attempt sources;raise primary) end
  (* Pure private mode/path DATA, not a new scope/proof constructor. The
     coupled meter itself is NEVER exposed by the Work interface. *)
  fun priced_root_scope_path (Portfolio _) = NONE
    | priced_root_scope_path (GuardedPortfolio {path,...}) = SOME path
    | priced_root_scope_path (PolicyPortfolio {priced,...}) =
        Option.map #1 priced
    | priced_root_scope_path (p as OriginalPortfolio _) =
        fail p "scope_path" "original priced path is not implemented"
  fun validate_priced_scope_frame
      (p as GuardedPortfolio {graph=held,scope=original,sources=old,
        limits=captured,meter,...})
      {graph,root,scope,sources,limits,epoch,symbols,path} =
    ((if Portable.pointer_eq (graph,held) andalso root=original andalso
         Portable.pointer_eq (sources,old) andalso same_limits limits captured
        then () else fail p "scope_frame" "different original owner";
      active p;
      (* Payer6 + owned fields8 + epochs6 + result projection4 + bounded
         argument/control8. The genuine dynamic G path is additional. *)
      R.scope_meter_charge meter (32+G.scope_path_validation_work path);
      G.validate_scope_path graph scope path;
      if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
        else fail p "scope_frame" "retirement epoch changed")
     handle primary => (close p;raise primary))
    | validate_priced_scope_frame (p as OriginalPortfolio _) _ =
        fail p "scope_frame" "original priced path is not implemented"
    | validate_priced_scope_frame p _ =
        fail p "scope_frame" "ordinary portfolio has no priced frame path"
  fun prepare_backend_binding_guard (Portfolio _) _ _ = NONE
    | prepare_backend_binding_guard
        (p as GuardedPortfolio {graph,meter,...}) caller origin =
      ((active p;
        R.scope_meter_charge meter 10;
        let
          val owner = B.binding_origin_owner origin
          val _ = if Portable.pointer_eq (graph,#graph owner) andalso
              caller = #parent_scope owner then () else
            fail p "binding_guard" "different genuine Backend parent"
          val program = B.prepare_binding_guard graph caller origin meter
          val _ = R.scope_meter_charge meter (32+B.binding_guard_work program)
          val _ = B.validate_binding_guard graph caller program
        in SOME program end)
       handle primary => (close p;raise primary))
    | prepare_backend_binding_guard
        (p as PolicyPortfolio {graph,priced,...}) caller origin =
      (case priced of NONE => NONE | SOME(_,meter) =>
        ((active p;
          R.scope_meter_charge meter 10;
          let
            val owner=B.binding_origin_owner origin
            val _=if Portable.pointer_eq (graph,#graph owner) andalso
                caller= #parent_scope owner then () else
              fail p "binding_guard" "different genuine Backend parent"
            val program=B.prepare_binding_guard_policy
              graph caller origin meter
            val _=R.scope_meter_charge meter
              (32+B.binding_guard_work program)
            val _=B.validate_binding_guard graph caller program
          in SOME program end)
         handle primary => (close p;raise primary)))
    | prepare_backend_binding_guard (p as OriginalPortfolio _) _ _ =
        fail p "binding_guard" "original Backend guard is not implemented"
  fun validate_backend_binding_guard
      (p as GuardedPortfolio {graph,meter,...}) caller program =
    ((if B.binding_guard_uses meter program then () else
        fail p "binding_guard" "different original Work counter";
      active p;
      R.scope_meter_charge meter (32+B.binding_guard_work program);
      B.validate_binding_guard graph caller program)
     handle primary => (close p;raise primary))
    | validate_backend_binding_guard
        (p as PolicyPortfolio {graph,priced,...}) caller program =
      (case priced of NONE =>
          fail p "binding_guard" "ordinary portfolio has no priced program"
       | SOME(_,meter) =>
         ((if B.binding_guard_uses meter program then () else
             fail p "binding_guard" "different original Work counter";
           active p;
           R.scope_meter_charge meter (32+B.binding_guard_work program);
           B.validate_binding_guard graph caller program)
          handle primary => (close p;raise primary)))
    | validate_backend_binding_guard (p as OriginalPortfolio _) _ _ =
        fail p "binding_guard" "original Backend guard is not implemented"
    | validate_backend_binding_guard p _ _ =
        fail p "binding_guard" "ordinary portfolio has no priced program"

  fun validate (p as Portfolio {graph = held,scope = owner,sources = original,
                               limits = captured,...})
      graph scope sources limits =
    (active p;
     if Portable.pointer_eq (held,graph) andalso scope = owner andalso
         Portable.pointer_eq (original,sources) andalso
         same_limits captured limits then () else
       fail p "validate" "original Source, scope or semantic caps differ")
    | validate (p as GuardedPortfolio
        {graph = held,scope = owner,sources = original,limits = captured,...})
      graph scope sources limits =
    (active p;scope_debit p 13;
     if Portable.pointer_eq (held,graph) andalso scope = owner andalso
         Portable.pointer_eq (original,sources) andalso
         same_limits captured limits then () else
       fail p "validate" "original Source, scope or semantic caps differ")
    | validate (p as PolicyPortfolio _) _ _ _ _ =
        fail p "validate" "policy route requires validate_policy"
    | validate (p as OriginalPortfolio _) _ _ _ _ =
        original_int_refusal p "validate"
  fun validate_template (p as Portfolio {graph = held,scope = owner,
                                        limits,...}) graph scope cap =
    (active p;
     if Portable.pointer_eq (held,graph) andalso scope = owner andalso
         #template_limit limits = cap then () else
       fail p "validate_template" "owner or original template cap differs")
    | validate_template (p as GuardedPortfolio {graph = held,scope = owner,
                                        limits,...}) graph scope cap =
    (active p;scope_debit p 11;
     if Portable.pointer_eq (held,graph) andalso scope = owner andalso
         #template_limit limits = cap then () else
       fail p "validate_template" "owner or original template cap differs")
    | validate_template (p as PolicyPortfolio _) _ _ _ =
        fail p "validate_template" "policy route requires policy validation"
    | validate_template (p as OriginalPortfolio _) _ _ _ =
        original_int_refusal p "validate_template"
  fun with_step (p as Portfolio {phase,...}) action =
    ((active p;
      (case !phase of Idle => phase := Busy
        | _ => fail p "with_step" "reentrant work action");
      let val result = action ()
          val _ = active p
          val _ = case !phase of Busy => ()
            | _ => fail p "with_step" "action cannot resurrect retired work"
          val _ = phase := Idle
      in result end)
     handle primary => (close p;raise primary))
    | with_step (p as GuardedPortfolio {phase,...}) action =
    ((active p;scope_debit p 9;
      (case !phase of Idle => phase := Busy
        | _ => fail p "with_step" "reentrant work action");
      let val result = action ()
          val _ = active p
          val _ = case !phase of Busy => ()
            | _ => fail p "with_step" "action cannot resurrect retired work"
          val _ = scope_debit p 9
          val _ = phase := Idle
      in result end)
     handle primary => (close p;raise primary))
    | with_step (p as PolicyPortfolio {phase,...}) action =
    ((active p;policy_overhead p 9;
      (case !phase of Idle => phase := Busy
        | _ => fail p "with_step" "reentrant work action");
      let val result=action ()
          val _=active p
          val _=case !phase of Busy => ()
            | _ => fail p "with_step" "action cannot resurrect retired work"
          val _=policy_overhead p 9
          val _=phase := Idle
      in result end)
     handle primary => (close p;raise primary))
    | with_step (p as OriginalPortfolio {work,...}) action =
        (original_active p;A.with_action work action)
  fun inside (p as Portfolio {phase,...}) =
    (active p;case !phase of Busy => ()
      | _ => fail p "admit" "no owned work action")
    | inside (p as GuardedPortfolio {phase,...}) =
    (active p;scope_debit p 8;case !phase of Busy => ()
      | _ => fail p "admit" "no owned work action")
    | inside (p as PolicyPortfolio _) = policy_inside p
    | inside (p as OriginalPortfolio _) = original_inside p
  fun spend (p as Portfolio {limit,used,...}) amount =
    (inside p;
     if amount >= 0 andalso amount <= limit - !used then used := !used+amount
     else fail p "admit" "original cumulative work allowance exhausted")
    | spend (p as GuardedPortfolio _) amount =
      (inside p;
       (* Pay the comparison and its counter payer before testing the
          original amount. A guard fee cannot turn a negative debit valid. *)
       scope_debit p 7;
       if amount >= 0 then scope_debit p (IntInf.fromInt amount+6)
       else fail p "admit" "original cumulative work allowance exhausted")
    | spend (p as PolicyPortfolio _) amount =
        policy_spend p (IntInf.fromInt amount)
    | spend (p as OriginalPortfolio _) _ =
        original_int_refusal p "spend"
  fun reserve (p as Portfolio {names,...}) {role,ordinal,amount} =
    let val _ = inside p
        val _ = if ordinal >= 0 andalso amount > 0 then () else
          fail p "reserve" "malformed future entitlement"
        (* Private finite role names have machine-int ordinals, no strings.
           Borrow the existing list spine: no unadmitted list copy. Each
           actual role comparison is charged BEFORE inspecting/comparing. *)
        val _ = spend p 1
        val key = (role,ordinal)
        fun issued [] = false
          | issued ((old,_)::rest) =
              (spend p 1;old = key orelse issued rest)
        val _ = if issued (!names) then
            fail p "reserve" "future role already issued" else ()
        val _ = spend p amount
        val _ = spend p 1 (* retained token/table entry *)
        val token = Entitlement {owner = p,remaining = ref amount,
          state = ref Ready}
        val _ = names := (key,token) :: !names
    in token end
    | reserve (p as GuardedPortfolio {names,...}) {role,ordinal,amount} =
    let val _ = inside p
        val _ = if ordinal >= 0 andalso amount > 0 then () else
          fail p "reserve" "malformed future entitlement"
        (* Private finite role names have machine-int ordinals, no strings.
           Borrow the existing list spine: no unadmitted list copy. Each
           actual role comparison is charged BEFORE inspecting/comparing. *)
        val _ = spend p 1
        val key = (role,ordinal)
        fun issued [] = false
          | issued ((old,_)::rest) =
              (spend p 1;old = key orelse issued rest)
        val _ = if issued (!names) then
            fail p "reserve" "future role already issued" else ()
        val _ = spend p amount
        val _ = spend p 1 (* retained token/table entry *)
        val token = Entitlement {owner = p,remaining = ref amount,
          state = ref Ready}
        val _ = names := (key,token) :: !names
    in token end
    | reserve (p as PolicyPortfolio _) {role,ordinal,amount} =
        policy_reserve p
          {role=role,ordinal=ordinal,amount=IntInf.fromInt amount}
    | reserve (p as OriginalPortfolio _) _ =
        original_int_refusal p "reserve"
  fun consume (p as OriginalPortfolio _) _ _ =
        original_int_refusal p "consume"
    | consume p (Entitlement {owner,remaining,state}) amount =
    (inside p;
     if Portable.pointer_eq (p,owner) then () else
       fail p "consume" "foreign future entitlement";
     (case !state of Spent => fail p "consume" "future entitlement consumed"
       | Ready => ());
     if amount >= 0 andalso amount <= !remaining then
       (remaining := !remaining-amount;
        if !remaining = 0 then state := Spent else ())
     else fail p "consume" "future entitlement exceeds retained reservation")
    | consume p (token as PolicyEntitlement _) amount =
        policy_consume p token (IntInf.fromInt amount)
    | consume p (OriginalEntitlement _) _ =
        (inside p;fail p "consume" "foreign future entitlement")
  fun same_policy (a:RP.semantic_policy) (b:RP.semantic_policy) =
    #input_limit a = #input_limit b andalso
    #output_limit a = #output_limit b andalso
    #template_limit a = #template_limit b
  fun positive_policy ({input_limit,output_limit,template_limit}
      :RP.semantic_policy) limit =
    RP.positive input_limit andalso RP.positive output_limit andalso
    RP.positive template_limit andalso RP.positive limit
  fun begin_with_policy graph scope sources {limits,work_limit} =
    let
      val _ = G.validate_scope graph scope
      val _ = if Portable.pointer_eq (graph,S.owning_graph sources) andalso
          scope=S.owning_scope sources then () else
        raise ERR "begin" "foreign original Source owner"
      val _ = if positive_policy limits work_limit then () else
        raise ERR "begin" "malformed pre-work limits"
      val _ = S.claim_invocation_work sources
      val epoch = Type.type_epoch ()
    in PolicyPortfolio {graph=graph,scope=scope,sources=sources,
      limits=limits,limit=work_limit,used=ref 0,epoch=epoch,phase=ref Idle,
      names=ref [],priced=NONE} end
  fun begin_with_scope_guard_policy graph scope sources {limits,work_limit} =
    let
      val original = S.owner_for_scope_guard sources
      val _ = if Portable.pointer_eq (graph,#graph original) andalso
          scope= #scope original then () else
        raise ERR "begin" "foreign original Source owner"
      val _ = if positive_policy limits work_limit then () else
        raise ERR "begin" "malformed pre-work limits"
      fun commit () =
        let
          val _ = if RP.allows work_limit 70 then () else
            raise ERR "begin" "original Work cannot bootstrap priced root"
          val path = G.prepare_scope_path_with_policy graph scope
            {remaining_work=RP.remaining work_limit 70}
          val setup = G.scope_path_setup_work path
          val validation = G.scope_path_validation_work path
          val charged = 70+setup+validation
          val _ = if RP.allows work_limit charged then () else
            raise ERR "begin" "original Work cannot admit priced root setup"
          val _ = S.claim_invocation_work_with_path sources path
          val epoch = Type.type_epoch ()
          val used = ref charged
          val meter = R.new_scope_meter_with_policy
            {limit=work_limit,charged=used}
        in PolicyPortfolio {graph=graph,scope=scope,sources=sources,
          limits=limits,limit=work_limit,used=used,epoch=epoch,
          phase=ref Idle,names=ref [],priced=SOME(path,meter)} end
    in commit () handle primary =>
         (S.consume_scope_guard_attempt sources;raise primary) end
  (* Source already holds the caller's exact A.request/original.
     This claims its ONE Pending invocation, never makes another A. *)
  fun begin_original sources =
    let val work = S.claim_original_work sources
    in
      (A.with_action work (fn () =>
        let
          (* Defined local construction reservation, not whole CPU tariff. *)
          val _ = A.charge work 128
          val _ = S.validate_original_work work sources
          val request = A.request_for_work work
          val {graph,scope} = S.owner_for_scope_guard sources
        in OriginalPortfolio {graph=graph,scope=scope,sources=sources,
          work=work,request=request,names=ref []} end)
       handle primary => (A.retire_work work;raise primary))
    end

  fun semantic_policy (p as OriginalPortfolio {request,...}) =
        (original_active p;#semantic_limits request)
    | semantic_policy (p as PolicyPortfolio {limits,...}) =
        (active p;limits)
    | semantic_policy p = RP.semantic_from_ints (semantic_limits p)
  fun work_policy (p as OriginalPortfolio {request,...}) =
        (original_active p;#work_limit request)
    | work_policy (p as PolicyPortfolio {limit,...}) = (active p;limit)
    | work_policy p = RP.from_int (work_limit p)
  (* Observe after activation, so priced activation's own debit is included.
     This is current budget DATA, never a future freshness lease. *)
  fun remaining_policy (p as OriginalPortfolio {work,...}) =
        (original_active p;A.remaining work)
    | remaining_policy (p as PolicyPortfolio {limit,used,...}) =
        (active p;RP.remaining limit (!used))
    | remaining_policy p =
        let val limit=work_limit p val {charged,...}=audit p
        in RP.remaining (RP.from_int limit) (IntInf.fromInt charged) end
  fun audit_policy (OriginalPortfolio {work,...}) =
        let val held=A.audit work
        in {charged= #charged held,retired= #retired held} end
    | audit_policy (PolicyPortfolio {used,phase,...}) =
        {charged= !used,retired=case !phase of Retired=>true | _=>false}
    | audit_policy p =
        let val {charged,retired}=audit p
        in {charged=IntInf.fromInt charged,retired=retired} end
  fun validate_policy (p as OriginalPortfolio
      {graph=held,scope=owner,sources=original,request,...})
      graph scope sources limits =
    (if Portable.pointer_eq(held,graph) andalso scope=owner andalso
        Portable.pointer_eq(original,sources) andalso
        same_policy (#semantic_limits request) limits then () else
       fail p "validate" "original Source, scope or semantic caps differ";
     original_active p)
    | validate_policy (p as PolicyPortfolio
      {graph=held,scope=owner,sources=original,limits=captured,...})
      graph scope sources limits =
    (active p;policy_overhead p 13;
     if Portable.pointer_eq (held,graph) andalso scope=owner andalso
         Portable.pointer_eq (original,sources) andalso
         same_policy captured limits then () else
       fail p "validate" "original Source, scope or semantic caps differ")
    | validate_policy (p as Portfolio
        {graph=held,scope=owner,sources=original,limits=captured,...})
        graph scope sources limits =
        (active p;
         if Portable.pointer_eq (held,graph) andalso scope=owner andalso
             Portable.pointer_eq (original,sources) andalso
             same_policy (RP.semantic_from_ints captured) limits then () else
           fail p "validate" "original Source, scope or semantic caps differ")
    | validate_policy (p as GuardedPortfolio
        {graph=held,scope=owner,sources=original,limits=captured,...})
        graph scope sources limits =
        (active p;scope_debit p 13;
         if Portable.pointer_eq (held,graph) andalso scope=owner andalso
             Portable.pointer_eq (original,sources) andalso
             same_policy (RP.semantic_from_ints captured) limits then () else
           fail p "validate" "original Source, scope or semantic caps differ")
  fun validate_template_policy (p as OriginalPortfolio
      {graph=held,scope=owner,request,...}) graph scope cap =
    (if Portable.pointer_eq(held,graph) andalso scope=owner andalso
        #template_limit (#semantic_limits request)=cap then () else
       fail p "validate_template" "owner or original template cap differs";
     original_active p)
    | validate_template_policy (p as PolicyPortfolio
      {graph=held,scope=owner,limits,...}) graph scope cap =
    (active p;policy_overhead p 11;
     if Portable.pointer_eq (held,graph) andalso scope=owner andalso
         #template_limit limits=cap then () else
       fail p "validate_template" "owner or original template cap differs")
    | validate_template_policy (p as Portfolio
        {graph=held,scope=owner,limits,...}) graph scope cap =
        (active p;
         if Portable.pointer_eq (held,graph) andalso scope=owner andalso
             RP.from_int (#template_limit limits)=cap then () else
           fail p "validate_template" "owner or original template cap differs")
    | validate_template_policy (p as GuardedPortfolio
        {graph=held,scope=owner,limits,...}) graph scope cap =
        (active p;scope_debit p 11;
         if Portable.pointer_eq (held,graph) andalso scope=owner andalso
             RP.from_int (#template_limit limits)=cap then () else
           fail p "validate_template" "owner or original template cap differs")
  fun validate_priced_scope_frame_policy
      (p as PolicyPortfolio {graph=held,scope=original,sources=old,
        limits=captured,priced,...})
      {graph,root,scope,sources,limits,epoch,symbols,path} =
    ((if Portable.pointer_eq (graph,held) andalso root=original andalso
         Portable.pointer_eq (sources,old) andalso same_policy limits captured
        then () else fail p "scope_frame" "different original owner";
      case priced of NONE =>
          fail p "scope_frame" "ordinary portfolio has no priced frame path"
       | SOME(_,meter) =>
         (active p;
          R.scope_meter_charge meter (32+G.scope_path_validation_work path);
          G.validate_scope_path graph scope path;
          if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
            then () else fail p "scope_frame" "retirement epoch changed"))
     handle primary => (close p;raise primary))
    | validate_priced_scope_frame_policy
        (p as GuardedPortfolio {graph=held,scope=original,sources=old,
          limits=captured,meter,...})
        {graph,root,scope,sources,limits,epoch,symbols,path} =
      ((if Portable.pointer_eq (graph,held) andalso root=original andalso
           Portable.pointer_eq (sources,old) andalso
           same_policy limits (RP.semantic_from_ints captured) then () else
          fail p "scope_frame" "different original owner";
        active p;
        R.scope_meter_charge meter (32+G.scope_path_validation_work path);
        G.validate_scope_path graph scope path;
        if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
          else fail p "scope_frame" "retirement epoch changed")
       handle primary => (close p;raise primary))
    | validate_priced_scope_frame_policy (p as OriginalPortfolio _) _ =
        fail p "scope_frame" "original priced path is not implemented"
    | validate_priced_scope_frame_policy p _ =
        fail p "scope_frame" "requires policy portfolio"
  fun spend_policy (p as OriginalPortfolio _) amount =
        original_spend p amount
    | spend_policy (p as PolicyPortfolio _) amount = policy_spend p amount
    | spend_policy (p as Portfolio {limit,used,...}) amount =
        (inside p;
         if amount >= 0 andalso amount <= IntInf.fromInt (limit- !used) then
           used := !used+IntInf.toInt amount
         else fail p "admit" "original cumulative work allowance exhausted")
    | spend_policy (p as GuardedPortfolio _) amount =
        (inside p;scope_debit p 7;
         if amount >= 0 then scope_debit p (amount+6)
         else fail p "admit" "original cumulative work allowance exhausted")
  fun reserve_finite_policy p names {role,ordinal,amount} =
    let
      val _=inside p
      val _=if ordinal >= 0 andalso amount > 0 then () else
        fail p "reserve" "malformed future entitlement"
      val _=spend_policy p 1
      val key=(role,ordinal)
      fun issued []=false
        | issued ((old,_)::rest)=
            (spend_policy p 1;old=key orelse issued rest)
      val _=if issued (!names) then
          fail p "reserve" "future role already issued" else ()
      val _=spend_policy p amount
      val _=spend_policy p 1
      (* Successful admission against the finite int counter proves this
         conversion representable. No exception from a guard is caught. *)
      val token=Entitlement
        {owner=p,remaining=ref (IntInf.toInt amount),state=ref Ready}
      val _=names := (key,token):: !names
    in token end
  fun reserve_policy (p as OriginalPortfolio _) fields =
        original_reserve p fields
    | reserve_policy (p as PolicyPortfolio _) fields =
        policy_reserve p fields
    | reserve_policy (p as Portfolio {names,...}) fields =
        reserve_finite_policy p names fields
    | reserve_policy (p as GuardedPortfolio {names,...}) fields =
        reserve_finite_policy p names fields
  fun consume_policy (p as OriginalPortfolio _) token amount =
        original_consume p token amount
    | consume_policy p (Entitlement {owner,remaining,state}) amount =
    (inside p;
     if Portable.pointer_eq (p,owner) then () else
       fail p "consume" "foreign future entitlement";
     (case !state of Spent => fail p "consume" "future entitlement consumed"
       | Ready => ());
     if amount >= 0 andalso amount <= IntInf.fromInt (!remaining) then
       (remaining := !remaining-IntInf.toInt amount;
        if !remaining=0 then state := Spent else ())
     else fail p "consume" "future entitlement exceeds retained reservation")
    | consume_policy p (PolicyEntitlement {owner,remaining,state}) amount =
    (inside p;
     if Portable.pointer_eq (p,owner) then () else
       fail p "consume" "foreign future entitlement";
     (case !state of Spent => fail p "consume" "future entitlement consumed"
       | Ready => ());
     if amount >= 0 andalso amount <= !remaining then
       (remaining := !remaining-amount;
        if !remaining=0 then state := Spent else ())
     else fail p "consume" "future entitlement exceeds retained reservation")
    | consume_policy p (OriginalEntitlement _) _ =
        (inside p;fail p "consume" "foreign future entitlement")

  (* Passive route DATA only, including after retirement. No phase change
     or native admission follows from learning this constructor mode. *)
  fun ordinary_policy_guard_mode
      (PolicyPortfolio{priced=NONE,...})=true
    | ordinary_policy_guard_mode _=false
  (* Callback-free guard bookkeeping may occur in Idle or Busy. It debits
     the SAME original counter; spend/reserve/with_step rules stay intact. *)
  fun spend_ordinary_guard_policy
      (p as PolicyPortfolio{priced=NONE,...}) amount=
    ((policy_active p;policy_debit p amount)
     handle primary=>(close p;raise primary))
    | spend_ordinary_guard_policy (p as OriginalPortfolio _) _=
        fail p "ordinary_guard" "original ordinary guard is not implemented"
    | spend_ordinary_guard_policy p _=
        fail p "ordinary_guard"
          "guard debit requires ordinary policy Work"

  (* Callback-free guard bookkeeping, not action/native authority. All
     representations debit their SAME actual counter in Idle or Busy. *)
  fun guard_payment (p as Portfolio {limit,used,...}) amount =
        (active p;
         if amount>=0 andalso amount<=IntInf.fromInt (limit- !used) then
           used := !used+IntInf.toInt amount
         else fail p "value_binding_guard"
           "original cumulative work allowance exhausted")
    | guard_payment (p as GuardedPortfolio _) amount =
        (active p;scope_debit p amount)
    | guard_payment (p as PolicyPortfolio _) amount =
        (policy_active p;policy_debit p amount)
    | guard_payment (p as OriginalPortfolio {work,...}) amount =
        (original_active p;A.charge_guard work amount)
  fun spend_guard_policy p amount =
    (guard_payment p amount handle primary => (close p;raise primary))

  (* Exact closed PREFIX forwarding. A owns its action and retained owner;
     no A Work, counter, proof, semantic Source or executor is exposed. *)
  type original_context = A.ordered_original_context
  fun prepare_ordered_original_context
      (p as OriginalPortfolio {work,...}) =
    (original_active p;A.prepare_ordered_original_context work)
    | prepare_ordered_original_context p =
        fail p "ordered_original_context" "not an original portfolio"
  fun ordered_original_progress_for
      (OriginalPortfolio {work,...}) context =
        A.ordered_original_progress_for work context
    | ordered_original_progress_for p _ =
        fail p "ordered_original_progress" "not an original portfolio"

  (* Closed SAME-work programmes. A checks immutable expected context
     owner BEFORE held lifetime, and owns the actual action itself. Do not
     add original_active here or nest these calls inside I.with_step.
     No proof, A Work, G context/storage, Source or mutable table escapes. *)
  fun advance_ordered_boolean_original
      (OriginalPortfolio {work,...}) context =
        A.advance_ordered_boolean_original work context
    | advance_ordered_boolean_original p _ =
        fail p "ordered_boolean_original" "not an original portfolio"
  fun complete_ordered_boolean_denial
      (OriginalPortfolio {work,...}) context =
        A.complete_ordered_boolean_denial work context
    | complete_ordered_boolean_denial p _ =
        fail p "ordered_boolean_denial" "not an original portfolio"
  fun prepare_ordered_original_sources
      (OriginalPortfolio {work,...}) context =
        A.prepare_ordered_original_sources work context
    | prepare_ordered_original_sources p _ =
        fail p "ordered_source_preparation" "not an original portfolio"
  fun ordered_source_preparation_for
      (OriginalPortfolio {work,...}) context =
        A.ordered_source_preparation_for work context
    | ordered_source_preparation_for p _ =
        fail p "ordered_source_preparation" "not an original portfolio"

  (* Closed goal proof on the SAME retained A Work and context.
     A authenticates expected owner before held lifetime and owns its
     action, finite quota admission, genuine native calls and retirement.
     raw_false is theorem DATA; no Source/Work/counter is extracted.
     Successful proof return does not publish semantic S Ready. *)
  fun finalise_ordered_boolean_goal
      (OriginalPortfolio {work,...}) context raw_false =
        A.finalise_ordered_boolean_goal work context raw_false
    | finalise_ordered_boolean_goal p _ _ =
        fail p "ordered_boolean_finaliser" "not an original portfolio"

  (* SAME hidden original Work/context; A owns action and admission.
     A retained function-child receipt stays private and does not complete
     a Boolean original or publish a Source. No extra I action/guard. *)
  fun prepare_ordered_function_child
      (OriginalPortfolio {work,...}) context =
        A.prepare_ordered_function_child work context
    | prepare_ordered_function_child p _ =
        fail p "ordered_function_child" "not an original portfolio"

  (* Fixed producer completion on the SAME hidden Work/context. A owns
     actual action/admission/publication; no caller Ready flag or Source. *)
  fun complete_ordered_original_acquisition
      (OriginalPortfolio {work,...}) context =
        A.complete_ordered_original_acquisition work context
    | complete_ordered_original_acquisition p _ =
        fail p "ordered_acquisition" "not an original portfolio"

  (* One actual constructor birth, stable Source wrapper and OriginalWork.
     No old Source/Work is converted or supplied an origin flag. *)
  type owned_application = A.owned_application_metadata
  fun begin_owned_boolean_application request children =
    let
      val (seed,application) =
        A.new_owned_boolean_application_metadata request children
      val sources = S.new_pending seed
      val portfolio = begin_original sources
      val _ = case portfolio of OriginalPortfolio {work,...} =>
          A.with_action work (fn () => A.charge work 32)
        | _ => raise Fail "closed original factory returned another Work"
    in {sources=sources,portfolio=portfolio,application=application} end

  (* A authenticates immutable expected owner before held lifetime and
     owns each action. No extra I guard or nested with_step is introduced. *)
  fun prepare_owned_application_context
      (OriginalPortfolio {work,...}) application =
        A.prepare_owned_application_context work application
    | prepare_owned_application_context p _ =
        fail p "owned_application_context" "not an original portfolio"
  fun complete_owned_application_source
      (OriginalPortfolio {work,...}) application context =
        A.complete_owned_application_source work application context
    | complete_owned_application_source p _ _ =
        fail p "owned_application_source" "not an original portfolio"
  fun complete_owned_application_denial
      (OriginalPortfolio {work,...}) application context =
        A.complete_owned_application_denial work application context
    | complete_owned_application_denial p _ _ =
        fail p "owned_application_denial" "not an original portfolio"


  (* This token is minted only by the I factory and consumed once. The
     CVC caller initiates birth; CheckedGraph alone takes ownership. *)
  datatype checked_owned_handoff = CheckedOwnedHandoff of
    {sources:S.sources,portfolio:portfolio,goal:Abbrev.goal,
     owned:A.request,graph:G.graph,scope:G.scope,used:bool ref}
  fun begin_ready_checked_owned_boolean_application request children =
    let
      val {sources,portfolio,application} =
        begin_owned_boolean_application request children
      fun ready () =
        let
          val {graph,scope} = S.owner_for_scope_guard sources
          val context = prepare_owned_application_context
            portfolio application
          val _ = complete_owned_application_source
            portfolio application context
          val _ = complete_owned_application_denial
            portfolio application context
          val _ = prepare_ordered_original_sources portfolio context
          val _ = complete_ordered_original_acquisition portfolio context
          val goal = S.original_goal sources
          val source_goal = #original (S.goal_source sources)
          val _ = case goal of
              ([],term) =>
                if Portable.pointer_eq (term,source_goal) then ()
                else raise ERR "begin_ready_checked_owned_boolean_application"
                  "Ready goal differs from the exact constructor result"
            | _ => raise ERR "begin_ready_checked_owned_boolean_application"
                  "owned Boolean application acquired assumptions"
        in CheckedOwnedHandoff
          {sources=sources,portfolio=portfolio,goal=goal,
           owned=request,graph=graph,scope=scope,used=ref false} end
    in ready () handle primary =>
      ((close portfolio handle _ => ());
       (let val {graph,scope}=S.owner_for_scope_guard sources
        in G.close_scope graph scope end handle _ => ());
       raise primary) end
  fun take_ready_checked_owned_boolean_application
      (CheckedOwnedHandoff {sources,portfolio,goal,owned,used,...}) =
    if !used then raise ERR "take_ready_checked_owned_boolean_application"
      "owned application handoff already consumed"
    else (used := true;
          {sources=sources,portfolio=portfolio,goal=goal,owned=owned})
  fun close_ready_checked_owned_boolean_application
      (CheckedOwnedHandoff {portfolio,graph,scope,used,...}) =
    if !used then () else
      (used := true;close portfolio;G.close_scope graph scope)

  (* Closed SAME-work staging/commit. A owns expected-owner precedence,
     action/reentry, actual payment and retirement. No extra I action. *)
  type ordered_proof_scope = A.ordered_proof_scope
  fun open_ordered_proof_scope (OriginalPortfolio {work,...}) context =
        A.open_ordered_proof_scope work context
    | open_ordered_proof_scope p _ =
        fail p "ordered_proof_scope" "not an original portfolio"
  fun ordered_proof_scope_for (OriginalPortfolio {work,...}) context held =
        A.ordered_proof_scope_for work context held
    | ordered_proof_scope_for p _ _ =
        fail p "ordered_proof_scope" "not an original portfolio"
  fun close_ordered_proof_scope (OriginalPortfolio {work,...}) context held =
        A.close_ordered_proof_scope work context held
    | close_ordered_proof_scope p _ _ =
        fail p "ordered_proof_scope" "not an original portfolio"

  (* Fixed forwarding of the SAME hidden Work and original context.
     Stage is opaque public-view DATA, never Source/native permission. *)
  type external_original_stage = A.external_original_stage
  fun prepare_ordered_external_original
      (OriginalPortfolio {work,...}) context =
        A.prepare_ordered_external_original work context
    | prepare_ordered_external_original p _ =
        fail p "external_original_stage" "not an original portfolio"
  fun ordered_external_original_summary_for
      (OriginalPortfolio {work,...}) context stage =
        A.ordered_external_original_summary_for work context stage
    | ordered_external_original_summary_for p _ _ =
        fail p "external_original_stage" "not an original portfolio"

  (* I retains both the exact portfolio and its original Source binding.
     A owns immutable paid chunks; distinct formats retain distinct types. *)
  type 'paid certificate_contents =
    {owner:portfolio,sources:S.sources,paid:'paid}
  datatype paid_cpc_certificate = PaidCpcCertificate of
    A.paid_cpc_certificate certificate_contents
  datatype paid_z3_certificate = PaidZ3Certificate of
    A.paid_z3_certificate certificate_contents

  fun capture_certificate operation capture make_receipt
      (p as OriginalPortfolio {sources,work,...}) input =
    ((original_active p;
      make_receipt {owner=p,sources=sources,paid=capture work input})
     handle primary => (close p;raise primary))
    | capture_certificate operation _ _ p _ =
        fail p operation "not an original portfolio"

  fun with_certificate_input operation open_input
      (p as OriginalPortfolio {sources,work,...})
      (held : 'paid certificate_contents) consume =
    ((if Portable.pointer_eq(p,#owner held) andalso
        Portable.pointer_eq(sources,#sources held) then () else
        fail p operation "foreign original portfolio or Source binding";
      original_active p;
      open_input work (#paid held) consume)
     handle primary => (close p;raise primary))
    | with_certificate_input operation _ p _ _ =
        fail p operation "not an original portfolio"

  fun capture_cpc_certificate work input =
    capture_certificate "capture_cpc_certificate" A.capture_cpc_certificate
      PaidCpcCertificate work input
  fun capture_z3_certificate work input =
    capture_certificate "capture_z3_certificate" A.capture_z3_certificate
      PaidZ3Certificate work input
  fun with_cpc_certificate_input work (PaidCpcCertificate held) consume =
    with_certificate_input "with_cpc_certificate_input"
      A.with_cpc_certificate_input work held consume
  fun with_z3_certificate_input work (PaidZ3Certificate held) consume =
    with_certificate_input "with_z3_certificate_input"
      A.with_z3_certificate_input work held consume

  fun unused_policy_ordinal work {role,minimum} =
    ((let
      val _ = inside work
      val _ = if minimum>=0 then () else
        fail work "unused_policy_ordinal" "negative ordinal minimum"
      val _ = spend_policy work 1
      (* Borrow the actual immutable issued-list spine. No ordinal token,
         mutable counter, future allowance or replacement names is made. *)
      val entries = case work of
          Portfolio {names,...} => !names
        | GuardedPortfolio {names,...} => !names
        | PolicyPortfolio {names,...} => !names
        | OriginalPortfolio {names,...} => !names
      fun largest [] highest = highest
        | largest (((held,index),_)::rest) highest =
            (spend_policy work 1;
             largest rest (if held=role then
               SOME (case highest of NONE => index
                 | SOME prior => Int.max (prior,index)) else highest))
      fun successor index = case Int.maxInt of
          SOME maximum => if index=maximum then NONE else SOME (index+1)
        | NONE => SOME (index+1)
      fun issued _ [] = (spend_policy work 1;false)
        | issued candidate (((held,index),_)::rest) =
            (spend_policy work 1;
             (held=role andalso index=candidate) orelse
             issued candidate rest)
      fun gap candidate =
        if not (issued candidate entries) then candidate else
          case successor candidate of SOME next => gap next
          | NONE => fail work "unused_policy_ordinal"
              "no unused ordinal at or above minimum"
      val result = case largest entries NONE of NONE => minimum
        | SOME highest => if highest<minimum then minimum else
            case successor highest of SOME next => next
            | NONE => gap minimum
      val _ = inside work
    in result end) handle primary => (close work;raise primary))

  datatype value_factory = ValueFactory of
    {work:portfolio,factory:B.value_backend,active:bool ref}
  fun close_value_factory (ValueFactory {factory,active,...}) =
    (active := false;(#close factory) ())
  fun validate_value_factory_for expected
      (ValueFactory {work,factory,active}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "value_factory" "different original Work";
      if !active then () else
        raise ERR "value_factory" "parser factory closed";
      SmtLib_GraphParserValue.validate (#context factory))
     handle primary => (close expected;raise primary))
  fun value_factory_data_for expected
      (held as ValueFactory {factory,...}) =
    (validate_value_factory_for expected held;factory)
  fun create_value_factory_with_policy expected
      {graph,scope,validate_metadata,import_limit,literal_limit,binder_limit} =
    ((let
      val sources = original_sources expected
      val actual_graph = S.owning_graph sources
      val root = S.owning_scope sources
      val _ = if Portable.pointer_eq (graph,actual_graph) andalso scope=root
        then () else
          raise ERR "value_factory" "different original Source owner"
      val limits = semantic_policy expected
      val active = ref true
      fun validate () =
        (validate_policy expected graph scope sources limits;
         if !active then () else
           raise ERR "value_factory" "parser factory closed";
         validate_metadata ();
         validate_policy expected graph scope sources limits)
      val context = SmtLib_GraphParserValue.create
        {graph=graph,scope=scope,validate=validate,
         spend=spend_policy expected,retire=fn () => close expected}
      val captured = Exn.capture (fn () => B.values_with_policy
        {context=context,graph=graph,scope=scope,
         import_limit=import_limit,literal_limit=literal_limit,
         binder_limit=binder_limit}) ()
      val factory = case captured of Exn.Res factory => factory
        | Exn.Exn primary =>
            (ignore (Exn.capture SmtLib_GraphParserValue.close context);
             raise primary)
      val result = ValueFactory {work=expected,factory=factory,active=active}
      val _ = validate_value_factory_for expected result
    in result end) handle primary => (close expected;raise primary))

  datatype value_binding_guard = ValueBindingGuard of
    {work:portfolio,graph:G.graph,root:G.scope,sources:S.sources,
     limits:RP.semantic_policy,epoch:int,symbols:int,caller:G.scope,
     factory:value_factory,program:B.value_binding_guard}
  val value_guard_payment = guard_payment
  fun validate_value_backend_binding_guard expected
      (ValueBindingGuard {work,graph,root,sources,limits,epoch,symbols,
                          caller,factory,program}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "value_binding_guard" "different original Work";
      validate_policy expected graph root sources limits;
      validate_value_factory_for expected factory;
      if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
      else raise ERR "value_binding_guard" "declaration lifetime changed";
      value_guard_payment expected (32+B.value_binding_guard_work program);
      B.validate_value_binding_guard graph caller program;
      validate_policy expected graph root sources limits)
     handle primary => (close expected;raise primary))
  (* Shallow SAME-action check only. The caller must separately validate
     the factory/context and all captured leaf/path geometry. No metadata
     callback or lifetime-programme credit belongs to this port. *)
  fun validate_value_backend_binding_header_for expected
      (ValueBindingGuard {work,graph,caller,program,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "value_binding_guard" "different original Work";
      spend_policy expected 24;
      B.validate_value_binding_header graph caller program)
     handle primary => (close expected;raise primary))
  fun prepare_value_backend_binding_guard expected factory caller origin =
    ((let
      val actual_factory = value_factory_data_for expected factory
      val sources = original_sources expected
      val graph = S.owning_graph sources val root = S.owning_scope sources
      val limits = semantic_policy expected
      val _ = validate_policy expected graph root sources limits
      val _ = spend_policy expected 12
      val owner = B.value_binding_origin_owner origin
      val _ = if Portable.pointer_eq (graph,#graph owner) andalso
          caller= #parent_scope owner andalso
          G.scope_visible graph caller root then () else
        raise ERR "value_binding_guard" "different genuine Value parent"
      val program = B.prepare_value_binding_guard actual_factory
        graph caller origin
        {root_scope=root,remaining_work=fn () => remaining_policy expected}
      val result = ValueBindingGuard
        {work=expected,graph=graph,root=root,sources=sources,limits=limits,
         epoch=Type.type_epoch (),symbols=Term.term_epoch (),caller=caller,
         factory=factory,program=program}
      val _ = validate_value_backend_binding_guard expected result
    in result end) handle primary => (close expected;raise primary))
  fun value_backend_binding_data_for expected
      (held as ValueBindingGuard {program,...}) =
    (validate_value_backend_binding_guard expected held;
     B.value_binding_guard_data program)
end
