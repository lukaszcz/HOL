(* Concrete shared protocol slice, intentionally NONSELECTABLE.
   Metadata setup/guard tariffs and the closed acquisition producer remain
   OPEN. charge is a real SAME-counter debit, not proof/admission authority. *)
structure SmtReplayOriginalAcquisition :> SmtReplayOriginalAcquisition =
struct
  structure G = SmtReplayGraph
  structure RP = SmtReplayResourcePolicy
  structure R = ReplayRedblackPrivateWork
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOriginalAcquisition"
  type native_limits = {semantic_limits:RP.semantic_policy,
    import_limit:RP.limit,type_work_limit:RP.limit}
  type request = {construction_limits:RP.graph_policy,
    semantic_limits:RP.semantic_policy,work_limit:RP.limit,
    native_limits:native_limits}
  datatype action = Idle | Busy | Retired
  datatype publication = Pending | Acquiring | Ready | Dead
  (* NONE is unknown unfolded geometry of an unopened opaque original,
     never a size-one classification or a finite native admission receipt. *)
  type shape = {raw:IntInf.int option,inc:IntInf.int option,
    ann:IntInf.int option,root_type:IntInf.int}
  type acquisition_portfolio =
    {originals:shape list,denied:shape,equalities:shape list,
     native_program:string list,qualified_initial_inspection:bool,
     full_tariff:bool}
  (* These rows are created only by the closed checked acquisition below.
     They retain exact immutable Source records, not caller origin claims. *)
  datatype ready_origin = ReadyOrigin of
    {source:G.source,canonical:Term.term}
  (* Only private ordered preparation constructs this owner. The G context
     and result reference are the SAME captured objects, never a wrapper,
     caller profile, new meter, callback or counter. *)
  datatype ordered_ready_owner = OrderedReadyOwner of
    {graph_context:G.original_import_context,
     final_result:Thm.thm option ref}
    | OwnedApplicationReadyOwner of
    {graph_context:G.original_import_context,
     final_result:Thm.thm option ref,
     completion:G.owned_application_completion}
  datatype ready_payload = ReadyPayload of
    {goal:G.source,assumptions:G.source list,denied:G.source,
     portfolio:acquisition_portfolio,revision:IntInf.int,
     origins:ready_origin list,allowed:Term.term list Array.array,
     ordinary:Term.term list Array.array,
     assumption_nodes:G.node list,reconciliation:G.source list,
     canonical_goal:Term.term,ordered_owner:ordered_ready_owner option}
  datatype seed = Seed of
    {identity:unit ref,graph:G.graph,root:G.scope,original:Abbrev.goal,
     request:request,epoch:int,symbols:int,charged:IntInf.int ref,
     claimed:bool ref,action:action ref,publication:publication ref,
     initial_revision:IntInf.int,payload:ready_payload option ref,
     source_claimed:bool ref,meter:R.scope_meter,
     fixed_storage:G.fixed_storage,native_started:bool ref,
     first_variable_source:G.source option ref,context_eligible:bool ref}
  datatype work = Work of seed
  datatype source_binding = SourceBinding of
    {seed:seed,work:work,invocation_claimed:bool ref}

  fun retire_seed (Seed {action,publication,...}) =
    (action := Retired;publication := Dead)
  fun retire_work (Work seed) = retire_seed seed
  fun fail seed operation message =
    (retire_seed seed;raise ERR operation message)
  fun positive ({construction_limits,semantic_limits,work_limit,
      native_limits}:request) =
    let val recipes = #recipe_limits construction_limits
        val native = #semantic_limits native_limits
    in List.all RP.positive
      [#import_limit construction_limits,#literal_limit construction_limits,
       #binder_limit construction_limits,#template_limit recipes,
       #index_limit recipes,#operand_limit recipes,#token_limit recipes,
       #input_limit semantic_limits,#output_limit semantic_limits,
       #template_limit semantic_limits,work_limit,#input_limit native,
       #output_limit native,#template_limit native,
       #import_limit native_limits,#type_work_limit native_limits] end

  fun new_metadata request original =
    let val _ = if positive request then () else
          raise ERR "new_metadata" "nonpositive original policy request"
        (* This preserved positive16/List.all prefix is pre-payer
           authentication, not retrospectively paid by the debit below.
           Admission control/IntInf/private epoch CPU remain qualified. *)
        val initial : IntInf.int = case #work_limit request of
            RP.Uncapped => 41
          | RP.AtMost _ => 44
        val _ = if RP.allows (#work_limit request) initial then () else
          raise ERR "new_metadata" "original bootstrap Work exhausted"
        (* All named post-auth A constructor events are admitted before
           this ONE counter/meter/graph/Seed programme. No ref0 reset. *)
        val charged = ref initial
        val meter = R.new_scope_meter_with_policy
          {limit= #work_limit request,charged=charged}
        (* Additional defined capture/storage administration. Original
           41/44 remains; no fee discount or whole tariff is asserted. *)
        val _ = R.scope_meter_charge meter 4
        val _ = R.scope_meter_charge meter 4
        val {graph,root,storage} =
          G.new_original_with_fixed_storage_bootstrap_meter meter
        val initial_revision =
          G.validation_revision_with_meter graph root meter
        val _ = R.scope_meter_charge meter 4
    in Seed {identity=ref (),graph=graph,root=root,original=original,
      request=request,epoch=Type.type_epoch (),symbols=Term.term_epoch (),
      charged=charged,claimed=ref false,action=ref Idle,
      publication=ref Pending,
      initial_revision=initial_revision,payload=ref NONE,
      source_claimed=ref false,meter=meter,fixed_storage=storage,
      native_started=ref false,first_variable_source=ref NONE,
      context_eligible=ref true} end
  fun header_metadata (Seed {graph,root,...}) = {graph=graph,root=root}
  fun original_metadata (Seed {original,...}) = original
  fun request_metadata (Seed {request,...}) = request
  fun same_seed (Seed {identity=left,...},Seed {identity=right,...}) =
    left = right

  fun active (seed as Seed {graph,root,epoch,symbols,action,
      publication,meter,...}) =
    ((case (!action,!publication) of
        (Retired,_) => raise ERR "active" "original protocol retired"
      | (_,Dead) => raise ERR "active" "original protocol retired"
      | _ => ());
     if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then ()
     else raise ERR "active" "original Type or Term epoch changed";
     (* Preliminary retired/epoch authentication above preserves its
        old Primary precedence. This debit prepays ONLY the productive
        validation-call suffix; dynamic G/R programmes bill separately. *)
     (R.scope_meter_charge meter 16;
      R.scope_meter_charge meter 1;
       G.validate_scope_with_meter graph root meter))
    handle primary => (retire_seed seed;raise primary)
  fun claim_work (seed as Seed {claimed,publication,meter,...}) =
    ((active seed;
      if !claimed then fail seed "claim_work" "original Work already claimed"
      else ();
      case !publication of Pending => ()
        | _ => fail seed "claim_work" "original is not Pending";
      (* Admit the one successful latch/store/Work construction only
         AFTER the retained one-shot/Pending authentication guards. *)
      R.scope_meter_charge meter 16;
      claimed := true;Work seed)
     handle primary => (retire_seed seed;raise primary))
  fun validate_work (Work seed) = active seed
  fun validate_for (Work expected) held graph root =
    let val Seed {graph=original_graph,root=original_root,...} = expected
    in
      ((if same_seed (expected,held) andalso
          Portable.pointer_eq (graph,original_graph) andalso
          root=original_root then () else
          fail expected "validate_for" "foreign original Work or header";
        active expected)
       handle primary => (retire_seed expected;raise primary))
    end
  fun inside (seed as Seed {action,meter,...}) =
    ((active seed;case !action of Busy =>
       (R.scope_meter_charge meter 8;())
     | _ => fail seed "inside" "original Work has no owned action")
     handle R.Limit => (retire_seed seed;raise R.Limit))
  fun with_action (Work seed) action =
    let val Seed {action=phase,meter,...} = seed
    in
      ((active seed;
        (* Entry32 + successful tail24 are reserved ONCE before Busy or
           the callback. No new tail-admin debit follows its effects.
           Tail active remains the genuine separately billed live guard. *)
        (case !phase of Idle =>
           (R.scope_meter_charge meter 56;phase := Busy)
         | _ => fail seed "with_action" "original Work action reentered");
        let val result = action ()
            val _ = active seed
            val _ = case !phase of Busy => ()
              | _ => fail seed "with_action" "original action changed"
        in phase := Idle;result end)
       handle primary => (retire_seed seed;raise primary))
    end
  fun charge (Work seed) amount =
    let val Seed {request,charged,...} = seed
    in
      ((inside seed;
        if amount >= 0 andalso RP.allows
            (RP.remaining (#work_limit request) (!charged)) amount then
          charged := !charged+amount
        else fail seed "charge" "original cumulative allowance exhausted")
       handle primary => (retire_seed seed;raise primary))
    end
  fun remaining (Work seed) =
    let val Seed {request,charged,...} = seed
    in active seed;RP.remaining (#work_limit request) (!charged) end
  (* Private fixed-program runner, never a public meter/callback port.
     W keeps its initial Source authentication. Preserve the old remaining
     guard BEFORE R/G and active/charge16/32/0 AFTER it: a planning R.Limit
     must precede any later guard failure. Together W+A still pay six active
     guards +72 on success, including the three old inside guards. A fixed
     callback-free phase header authenticates Busy before planning without
     prepaying the suffix. No Ready test, nested action or new publication
     restriction. R/G bill the SAME meter, including future finish work. *)
  fun paid_plan (work as Work seed) program =
    ((let
        val _ = remaining work
        val Seed {meter,action,...} = seed
        val _ = case !action of Busy => ()
          | _ => fail seed "inside" "original Work has no owned action"
        val result = program meter
        val _ = active seed
        val _ = charge work 16
        val _ = charge work 32
        val _ = charge work 0
      in result end)
     handle primary => (retire_seed seed;raise primary))
  fun plan_lookup_int work args =
    paid_plan work (fn meter => R.scope_plan_lookup_int meter args)
  fun plan_lookup_string work args =
    paid_plan work (fn meter => R.scope_plan_lookup_string meter args)
  fun plan_insert_int work args =
    paid_plan work (fn meter => R.scope_plan_insert_int meter args)
  fun plan_insert_string work args =
    paid_plan work (fn meter => R.scope_plan_insert_string meter args)
  fun plan_insert_int_batch work args =
    paid_plan work (fn meter => R.scope_plan_insert_int_batch meter args)
  fun plan_list_int_batch work batch =
    paid_plan work (fn meter => R.scope_plan_list_int_batch meter batch)
  fun plan_placeholders work graph scope args =
    paid_plan work (fn meter =>
      G.plan_placeholders_with_meter graph scope meter args)

  fun request_for_work (Work seed) = (active seed;request_metadata seed)
  fun close_seed (seed as Seed {graph,root,...}) =
    (retire_seed seed;G.close_scope graph root)
  fun audit (Work (Seed {charged,action,publication,...})) =
    {charged= !charged,retired=(!action=Retired),busy=(!action=Busy),
     publication=case !publication of Pending => "Pending"
       | Acquiring => "Acquiring" | Ready => "Ready" | Dead => "Dead"}
  (* Isolated SAME-payer coupling partial, still NONSELECTABLE.
     Defined productive administration: active suffix16, claim latch16,
     inside success8, action entry32 + successful tail24 prepaid at entry.
     These DO NOT retrospectively price preliminary formal/owner/phase/
     epoch/refusal authentication, failure-only retirement, pure audit,
     billing primitives/IntInf CPU or the legacy producer's OPEN work.
     Existing G/R dynamic programmes still bill the SAME original meter.
     No internal guard calls charge_guard/Ready or creates another action.
     Mutable registry/closure consumers keep their OWN dynamic guards. *)
  (* Defined SAME-meter metadata programme. Existing Busy eligibility
     is retained: an owned consumer may read a genuinely Ready Source. *)
  fun validate_ready_origins (seed as Seed {graph,root,meter,...}) origins =
    let
      val _ = R.scope_meter_charge meter 32
      val _ = if root=(R.scope_meter_charge meter 1;
          G.root_scope_with_meter graph meter) then () else
        fail seed "ready" "different acquired original root"
      fun loop rows =
        (R.scope_meter_charge meter 16;
         case rows of [] => ()
         | ReadyOrigin {source,canonical}::rest =>
             (R.scope_meter_charge meter 32;
              active seed;
              if (R.scope_meter_charge meter 1;
                  G.node_scope_with_meter graph (#node source) meter)=root
                  andalso Portable.pointer_eq
                    ((R.scope_meter_charge meter 1;
                      G.representative_with_meter graph (#node source) meter),
                     canonical) then () else
                fail seed "ready" "acquired original origin changed";
              active seed;loop rest))
      val _ = loop origins
    in active seed end

  (* No new semantic/native effect. G authenticates the captured storage,
     owner/root/epochs and complete current paid-root snapshot each time. *)
  fun validate_ordered_ready_snapshot
      (seed as Seed {fixed_storage,root,meter,...})
      (OrderedReadyOwner saved) revision =
    let
      val _ = R.scope_meter_charge meter 64
      val progress = G.original_import_progress fixed_storage root
        (#graph_context saved)
      val _ = if #revision progress=revision andalso
          #denial_complete progress then () else
        fail seed "ready" "ordered completion witness changed"
    in active seed end

    | validate_ordered_ready_snapshot
      (seed as Seed {fixed_storage,root,meter,...})
      (OwnedApplicationReadyOwner saved) revision =
    let
      val _ = R.scope_meter_charge meter 64
      val progress = G.original_import_progress fixed_storage root
        (#graph_context saved)
      val _ = if #revision progress=revision andalso
          #denial_complete progress then () else
        fail seed "ready" "ordered completion witness changed"
    in active seed end

  fun ready (seed as Seed {publication,payload,meter,...}) =
    ((active seed;
      R.scope_meter_charge meter 32;
      case (!publication,!payload) of
          (Ready,SOME (held as ReadyPayload {origins,...})) =>
            (validate_ready_origins seed origins;
             R.scope_meter_charge meter 16;
             let val ReadyPayload {revision,ordered_owner,...} = held
             in case ordered_owner of NONE => held
              | SOME owner =>
                  (validate_ordered_ready_snapshot seed owner revision;held)
             end)
        | _ => fail seed "ready" "original acquisition is not Ready")
     handle primary => (retire_seed seed;raise primary))
  fun require_ready (Work seed) = ignore (ready seed)
  fun acquisition_portfolio_for (Work seed) =
    let val ReadyPayload {portfolio,...}=ready seed in portfolio end

  (* This NEW partial route requires actual Uncapped fields, never changes
     them to Uncapped. The original construction/import request stays exact.
     Local inspection events below debit the SAME counter before effect;
     G initialization/execution and fresh guards are NOT fully invoiced. *)
  (* Additive Pending-only native component. All old functions stay literal.
     These are conservative prospective Source-operation reservations, NOT
     observed instruction counts, exact refusal equivalence or full tariff.
     No caller Term/profile/theorem/callback enters this interface. *)
  datatype boolean_original_view = BooleanOriginalView of
    {owner:seed,original:Abbrev.goal,revision:IntInf.int,
     rows:(Term.term * Thm.thm) list,count:IntInf.int,
     native_work:IntInf.int}
  type boolean_original_summary =
    {original_count:IntInf.int,original_annotations:IntInf.int,
     reflexive_raw_nodes:IntInf.int,reflexive_annotations:IntInf.int,
     prospective_native_work:IntInf.int,full_tariff:bool}
  val boolean_leaf_native_upper : IntInf.int = 74
  val boolean_reflexive_native_upper : IntInf.int = 1424
  fun boolean_pending_revision (seed as Seed {graph,root,meter,
      initial_revision,publication,...}) =
    (active seed;
     (case !publication of Pending => () | _ =>
       fail seed "boolean_original_view" "original is not Pending");
     R.scope_meter_charge meter 1;
     let val revision=G.validation_revision_with_meter graph root meter
     in if revision=initial_revision then revision else
       fail seed "boolean_original_view" "Pending graph was mutated" end)
  fun prepare_boolean_original_view (work as Work seed) =
    let val Seed {original,request,meter,native_started,...}=seed
        val _=active seed
        val Seed {context_eligible,...} = seed
        val _ = R.scope_meter_charge meter 4
        val _ = context_eligible := false
        val _=R.scope_meter_charge meter 240
    in
      with_action work (fn () =>
        let
          val revision=boolean_pending_revision seed
          val (assumptions,goal)=original
          fun observe terms =
            (R.scope_meter_charge meter 120;
             case terms of [] => SOME ([],0 : IntInf.int)
             | term::rest =>
               (R.scope_meter_charge meter boolean_leaf_native_upper;
                (* Positive atom evidence MUST precede type_of: STD is_comb
                   would also accept a hidden Clos and is never used here. *)
                if (Term.is_var term orelse Term.is_const term) andalso
                    Portable.pointer_eq (Term.type_of term,Type.bool) then
                  (case observe rest of NONE => NONE
                   | SOME (tail,count) => SOME (term::tail,count+1))
                else NONE))
        in case observe (goal::assumptions) of NONE => NONE
        | SOME (terms,count) =>
          let
            val _=R.scope_meter_charge meter 240
            val semantic= #semantic_limits request
            val native= #native_limits request
            val ns= #semantic_limits native
            val annotations=11*count
            val type_work=count*(boolean_leaf_native_upper+
              boolean_reflexive_native_upper)
            val _=if RP.allows (#input_limit semantic) count andalso
                RP.allows (#output_limit semantic) annotations andalso
                RP.allows (#template_limit semantic) annotations andalso
                RP.allows (#input_limit ns) count andalso
                RP.allows (#output_limit ns) annotations andalso
                RP.allows (#template_limit ns) annotations andalso
                RP.allows (#import_limit native) (5*count) andalso
                RP.allows (#type_work_limit native) type_work then () else
              fail seed "boolean_original_view" "native policy exhausted"
            val native_work=count*boolean_reflexive_native_upper
            (* ALL native REFL and local reflection/control work is admitted
               BEFORE the FIRST theorem effect. No refund for Count/Trace. *)
            val _=R.scope_meter_charge meter
              (count*(120+boolean_reflexive_native_upper))
            fun reflect [] = []
              | reflect (term::rest) =
                let val _=inside seed
                    val _=R.scope_meter_charge meter 4
                    val _=native_started:=true
                    val theorem=Thm.REFL term
                    val _=inside seed
                in (term,theorem)::reflect rest end
            val rows=reflect terms
            val _=if boolean_pending_revision seed=revision then () else
              fail seed "boolean_original_view" "revision changed"
          in SOME (BooleanOriginalView {owner=seed,original=original,
            revision=revision,rows=rows,count=count,native_work=native_work})
          end
        end)
    end handle primary => (retire_seed seed;raise primary)
  fun boolean_original_summary_for (work as Work expected) view =
    let
      (* Only identity is inspected on held view before expected-owner test.
         No held graph/epoch/revision/term/theorem is read on a foreign row. *)
      val BooleanOriginalView {owner=held,...}=view
      val _=if same_seed (expected,held) then () else
        fail expected "boolean_original_summary" "foreign original view"
      val _=active expected
      val Seed {meter,...}=expected
      val _=R.scope_meter_charge meter 240
    in with_action work (fn () =>
      let val BooleanOriginalView
        {original,revision,count,native_work,...}=view
          val _=if Portable.pointer_eq
              (original_metadata expected,original) andalso
              boolean_pending_revision expected=revision then () else
            fail expected "boolean_original_summary" "stale original view"
      in {original_count=count,original_annotations=count,
          reflexive_raw_nodes=5*count,reflexive_annotations=11*count,
          prospective_native_work=native_work,full_tariff=false}
      end)
    end handle primary => (retire_seed expected;raise primary)


  (* Private membership indices accompany the checked payload before
     Ready. Their mutable arrays never cross an A public interface. *)
  val source_membership_buckets = 4093
  val source_membership_hint =
    SmtReplayImport.pointer_bucket 4 source_membership_buckets
  fun source_membership_put table term =
    let val bucket = source_membership_hint term
    in Array.update (table,bucket,term::Array.sub(table,bucket)) end
  fun source_membership table term =
    List.exists (fn saved => Portable.pointer_eq(term,saved))
      (Array.sub(table,source_membership_hint term))
  fun source_membership_clean theorem =
    let val tag = Thm.tag theorem
        val (oracles,_) = Tag.dest_tag tag
    in List.all (fn name => name="DISK_THM") oracles andalso
       List.null (Tag.axioms_of tag) end

  fun uncapped RP.Uncapped=true | uncapped _=false
  fun acquisition_envelope (request:request) =
    let val semantic= #semantic_limits request
        val native= #native_limits request
        val ns= #semantic_limits native
    in List.all uncapped [#work_limit request,
      #input_limit semantic,#output_limit semantic,#template_limit semantic,
      #input_limit ns,#output_limit ns,#template_limit ns,
      #import_limit native,#type_work_limit native] end
  fun acquire_originals_uncapped (work as Work seed) =
    let val Seed {graph,root,original=(assumptions,goal),request,
          initial_revision,publication,payload,meter,...}=seed
        fun abort primary =
          (retire_seed seed;
           (G.close_scope graph root handle _ => ());raise primary)
    in
      ((with_action work (fn () =>
        let
          val _=if acquisition_envelope request then () else
            fail seed "acquire" "finite acquisition not implemented"
          val _=case !publication of Pending=>() | _=>
            fail seed "acquire" "original acquisition is one-shot"
          val _=if G.validation_revision graph root=initial_revision then ()
            else fail seed "acquire" "Pending graph was mutated"
          val _=publication:=Acquiring
          fun step ()=charge work 1
          fun invoke action=(step ();let val value=action ()
            val _=inside seed in value end)
          (* Qualified public inspection, not finite pre-ALL-Type/Clos CPU
             admission. No count_body/REFL/Beta/native proof is used here. *)
          (* The Type memo is local to this one closed acquisition action.
             Identity routes only actual immutable public Type objects;
             no structural compare or caller-supplied identity is trusted. *)
          val type_memo_epoch=invoke Type.type_epoch
          val type_memo=invoke(fn()=>
            ref ([] : (Type.hol_type * IntInf.int) list))
          fun type_weight ty : IntInf.int =
            let
              val _=inside seed
              val _=if invoke(fn()=>Type.type_epoch()=type_memo_epoch)
                then ()else fail seed "type_weight" "Type memo epoch changed"
              fun find []=NONE
                | find ((held,weight)::rest)=
                    if invoke(fn()=>Portable.pointer_eq(ty,held))
                    then SOME weight else find rest
              val entries=invoke(fn()=> !type_memo)
            in case find entries of
              SOME weight=>invoke(fn()=>weight)
            | NONE=>
                let
                  val weight=
                    if invoke(fn()=>Type.is_vartype ty) then 1 else
                      let val (_,args)=invoke(fn()=>Type.dest_type ty)
                      in List.foldl(fn(child,total)=>
                        (step();total+type_weight child)) 1 args end
                  (* The complete exact weight is published only after
                     recursive success and fresh SAME Work/Scope/epochs.
                     Each repeated child still adds the saved full weight. *)
                  val previous=invoke(fn()=> !type_memo)
                  val updated=invoke(fn()=>(ty,weight)::previous)
                  val _=invoke(fn()=>type_memo:=updated)
                in weight end
            end
          val memo=ref ([] : (Term.term * shape) list)
          fun find term []=NONE
            | find term ((held,profile)::rest)=
                (step ();if Portable.pointer_eq(term,held) then SOME profile
                 else find term rest)
          fun plus (a:IntInf.int option) (b:IntInf.int option)=case (a,b) of
            (SOME x,SOME y)=>SOME(x+y)
            | _=>NONE
          fun add (n:IntInf.int) (a:IntInf.int option)=Option.map(fn x=>n+x)a
          fun inspect term : shape =
            case find term (!memo) of SOME profile=>profile
            | NONE=>
              let val ty=invoke (fn()=>Term.type_of term)
                  val own=type_weight ty
                  val profile=
                    if invoke (fn()=>Term.is_comb term) then
                      let val(f,x)=invoke(fn()=>Term.dest_comb term)
                          val a=inspect f val b=inspect x
                      in {raw=add 1(plus (#raw a)(#raw b)),
                        inc=add 1(plus (#inc a)(#inc b)),
                        ann=add own(plus (#ann a)(#ann b)),root_type=own} end
                    else if invoke(fn()=>Term.is_abs term) then
                      (* Import retains this exact object and uses REFL.
                         Its initial Type programme is exposed above, but
                         no binder is opened for unnecessary whole geometry. *)
                      {raw=NONE,inc=NONE,ann=NONE,root_type=own}
                    else if invoke(fn()=>Term.is_var term) orelse
                        invoke(fn()=>Term.is_const term) then
                      {raw=SOME 1,inc=SOME 1,ann=SOME own,root_type=own}
                    else fail seed "inspect" "unknown public constructor"
                  val _=step ()
                  val _=memo:=(term,profile):: !memo
              in profile end
          fun boolean term=
            if invoke(fn()=>Type.compare(Term.type_of term,Type.bool))=EQUAL
            then ()else fail seed "acquire" "non-Boolean original source"
          val originals=goal::assumptions
          val _=List.app boolean originals
          val profiles=List.map inspect originals
          val positive=hd profiles
          val negation=inspect boolSyntax.negation
          (* Derive denial MK_COMB geometry BEFORE making the denial. *)
          val denial:shape={raw=add 1(plus (#raw negation)(#raw positive)),
            inc=add 1(plus (#inc negation)(#inc positive)),
            ann=add 1(plus (#ann negation)(#ann positive)),root_type=1}
          fun equality ({raw,inc,ann,root_type}:shape) : shape =
            {raw=Option.map(fn n=>3+2*n)raw,
             inc=Option.map(fn n=>3+2*n)inc,
             ann=Option.map(fn n=>6+3*root_type+2*n)ann,root_type=1}
          val portfolio:acquisition_portfolio=
            {originals=profiles,denied=denial,
             equalities=List.map equality (profiles@[denial]),
             native_program=["denial: Term.mk_comb(not,original_goal)",
               "leaf: ALPHA(original,canonical), empty Hyp",
               "opaque Abs: REFL(original), empty Hyp; no binder rule",
               "application: MK_COMB(child bridges), ALPHA endpoints",
               "application: TRANS(inner), TRANS(outer), empty Hyp"],
             qualified_initial_inspection=true,full_tariff=false}
          (* All native/Type policies above were authenticated as Uncapped.
             Known optional rows are exact; opaque-containing geometry is
             unknown, not materialized just to obtain a numeric profile.
             REFL of an unopened original has actual root-Type/pointer
             operations, not an expanded binder/output constructor rule.
             This is NOT finite admission or an executed-instruction log.
             G may reuse interned nodes; no cached fee is credited. *)
          val denied_term=invoke(fn()=>boolSyntax.mk_neg goal)
          val plans=invoke(fn()=>G.plan_imports_with_policy graph root
            (#import_limit (#construction_limits request))
            (originals@[denied_term]))
          val imported=List.map (fn plan=>
            invoke(fn()=>G.execute_import_with_policy plan)) plans
          fun clean theorem=
            let val tag=invoke(fn()=>Thm.tag theorem)
                val (oracles,_)=invoke(fn()=>Tag.dest_tag tag)
            in List.all(fn name=>name="DISK_THM") oracles andalso
               List.null(invoke(fn()=>Tag.axioms_of tag)) end
          fun check (term,source:G.source)=
            let val _=if Portable.pointer_eq(term,#original source) then ()
                  else fail seed "acquire" "original Source order changed"
                val bridge= #bridge source
                val(l,r)=invoke(fn()=>Term.dest_eq(Thm.concl bridge))
                val canonical=invoke(fn()=>(R.scope_meter_charge meter 1;
                  G.representative_with_meter graph (#node source) meter))
                val _=if Portable.pointer_eq(l,term) andalso
                    Portable.pointer_eq(r,canonical) andalso
                    List.null(invoke(fn()=>Thm.hyp bridge)) andalso
                    clean bridge then ()else
                  fail seed "acquire" "Source bridge endpoints/Hyp/tags"
            in ()end
          val _=ListPair.appEq check (originals@[denied_term],imported)
          val goal_source=hd imported
          val assumption_sources=List.take(tl imported,length assumptions)
          val denied=List.last imported
          val _=inside seed
          val revision=G.validation_revision graph root
          (* Private witness capture has no public Source/theorem/profile
             input. The original checked bridges above remain authoritative.
             Metadata/list and billing administration remain unpriced;
             converted G ports now add genuine SAME-counter debits. This
             supplies no finite/native/default or whole Ready admission. *)
          val _=if root=(R.scope_meter_charge meter 1;
          G.root_scope_with_meter graph meter) then ()else
            fail seed "acquire" "different acquired original root"
          fun origin (source:G.source) =
            let
              val _=inside seed
              val _=if (R.scope_meter_charge meter 1;
                   G.node_scope_with_meter graph (#node source) meter)=root
                     then ()else
                fail seed "acquire" "original node outside acquired root"
              val canonical=(R.scope_meter_charge meter 1;
                      G.representative_with_meter graph (#node source) meter)
              val _=inside seed
            in ReadyOrigin {source=source,canonical=canonical} end
          val origins=List.map origin imported
          val _=inside seed

          (* All membership indices and immutable Source query lists are
             ready BEFORE the private publication. This legacy producer
             requires the exact uncapped native policy; invoke remains
             qualified administration, not finite/native admission. *)
          val allowed=invoke(fn()=>Array.array(source_membership_buckets,[]))
          val ordinary=invoke(fn()=>Array.array(source_membership_buckets,[]))
          fun put_source table (source:G.source) =
            let val term=invoke(fn()=>G.representative_with_meter graph
                  (#node source) meter)
            in invoke(fn()=>source_membership_put table term) end
          val _=List.app (fn source =>
            (put_source ordinary source;put_source allowed source))
            assumption_sources
          val _=put_source allowed denied
          val assumption_nodes=invoke(fn()=>List.map #node assumption_sources)
          val reconciliation=invoke(fn()=>denied::assumption_sources)
          val canonical_goal=case origins of
              ReadyOrigin {canonical,...}::_ => canonical
            | [] => fail seed "acquire" "missing original goal origin"

          val result=ReadyPayload {goal=goal_source,
            assumptions=assumption_sources,denied=denied,
            portfolio=portfolio,revision=revision,origins=origins,
            allowed=allowed,ordinary=ordinary,
            assumption_nodes=assumption_nodes,reconciliation=reconciliation,
            canonical_goal=canonical_goal,ordered_owner=NONE}
          val _=inside seed
          (* No callback between construction and the two private stores.
             Any later exception retires the SAME seed, making Ready unusable.
               *)
          val _=payload:=SOME result
          val _=publication:=Ready
        in ()end)) handle primary=>abort primary)
    end
  fun take_ready_sources (work as Work expected) held =
    let val Seed {graph,root,source_claimed,...}=expected
        val _=validate_for work held graph root
        val _=inside expected
        val ReadyPayload {goal,assumptions,denied,...}=ready expected
        val _=if !source_claimed then
          fail expected "take_ready_sources" "Source adoption already claimed"
          else ()
        val _=source_claimed:=true
    in {graph=graph,root=root,goal=goal,assumptions=assumptions,
      denied=denied} end

  fun validate_owned_action (Work seed) = inside seed
  (* Ordinary Work guard bookkeeping is valid in Idle OR Busy, retaining
     the SAME action state. It is not implemented with a nested action. *)
  fun charge_guard (work as Work seed) amount =
    let val Seed {request,charged,...}=seed
    in
      ((require_ready work;
        if amount >= 0 andalso RP.allows
            (RP.remaining (#work_limit request) (!charged)) amount then
          charged:= !charged+amount
        else fail seed "charge_guard"
          "original cumulative allowance exhausted")
       handle primary=>(retire_seed seed;raise primary))
    end


  (* Closed work-only FIRST original Var component. This creates and keeps
     a real Source, never Ready/denial/portfolio or a caller proof token.
     A prior native attempt cannot be silently treated as fresh credit. *)
  fun prepare_first_boolean_variable_source (work as Work seed) =
    let val Seed {original,request,meter,fixed_storage,native_started,
          first_variable_source,publication,root,...}=seed
        val _ = active seed
        val Seed {context_eligible,...} = seed
        val _ = R.scope_meter_charge meter 4
        val _ = context_eligible := false
        val _ = R.scope_meter_charge meter 64
    in with_action work (fn () =>
      let
        val _ = if !publication=Pending then () else
          fail seed "first_boolean_variable_source" "original is not Pending"
        val _ = if !native_started then
          fail seed "first_boolean_variable_source" "previous native programme"
          else ()
      in case original of
          ([],goal) =>
            let
              (* Conservative once-attempt flag: even a later refusal is
                 never retried as if no original native work was paid. *)
              val _ = R.scope_meter_charge meter 4
              val _ = native_started := true
              val result = G.import_first_boolean_variable fixed_storage root
                {original=goal,limits=
                  {construction_limits= #construction_limits request,
                   semantic_limits= #semantic_limits request,
                   native_limits= #native_limits request}}
              val _ = inside seed
            in case result of NONE => false
              | SOME source =>
                  (R.scope_meter_charge meter 4;
                   first_variable_source := SOME source;true)
            end
        | _ => false
      end)
    end handle primary => (retire_seed seed;raise primary)

  (* Additive constant producer, mutually exclusive with all prior native
     attempts. The legacy-named private first_variable_source slot
     retains either actual FIRST Source; no raw proof getter or new
     Seed/counter/graph allocation is introduced. *)
  fun prepare_first_boolean_constant_source (work as Work seed) =
    let val Seed {original,request,meter,fixed_storage,native_started,
          first_variable_source,publication,root,...}=seed
        val _ = active seed
        val Seed {context_eligible,...} = seed
        val _ = R.scope_meter_charge meter 4
        val _ = context_eligible := false
        val _ = R.scope_meter_charge meter 64
    in with_action work (fn () =>
      let
        val _ = if !publication=Pending then () else
          fail seed "first_boolean_constant_source" "original is not Pending"
        val _ = if !native_started then
          fail seed "first_boolean_constant_source" "previous native programme"
          else ()
      in case original of
          ([],goal) =>
            let
              (* Conservative once-attempt flag: even a later refusal is
                 never retried as if no original native work was paid. *)
              val _ = R.scope_meter_charge meter 4
              val _ = native_started := true
              val result = G.import_first_boolean_constant fixed_storage root
                {original=goal,limits=
                  {construction_limits= #construction_limits request,
                   semantic_limits= #semantic_limits request,
                   native_limits= #native_limits request}}
              val _ = inside seed
            in case result of NONE => false
              | SOME source =>
                  (R.scope_meter_charge meter 4;
                   first_variable_source := SOME source;true)
            end
        | _ => false
      end)
    end handle primary => (retire_seed seed;raise primary)

  (* Closed ownership/list-capture PREFIX. All original occurrences are
     retained in goal-first order; no opaque Term is assigned a size1.
     The semantic/native executor and denial producer remain absent. *)
  datatype ordered_original_context = OrderedOriginalContext of
    {owner:seed,original:Abbrev.goal,request:request,
     originals:Term.term list,count:IntInf.int,
     graph_context:G.original_import_context,prepared:ready_payload option ref,
     final_result:Thm.thm option ref}

  fun prepare_ordered_original_context (work as Work seed) =
    let
      val Seed {original,request,meter,fixed_storage,root,
        native_started,context_eligible,publication,...} = seed
      val _ = active seed
      val _ = R.scope_meter_charge meter 128
    in with_action work (fn () =>
      let
        val _ = if !publication=Pending then () else
          fail seed "ordered_original_context" "original is not Pending"
        val _ = if !native_started orelse not (!context_eligible) then
          fail seed "ordered_original_context" "previous original programme"
          else ()
        val _ = boolean_pending_revision seed
        (* Consume this exact original once, before list/context effects.
           Prior classifier NONE paths also invalidate context_eligible. *)
        val _ = R.scope_meter_charge meter 16
        val _ = context_eligible := false
        val _ = publication := Acquiring
        val (assumptions,goal) = original
        fun collect terms acc count =
          (R.scope_meter_charge meter 16;
           case terms of [] => (acc,count)
           | item::rest =>
               (R.scope_meter_charge meter 16;
                collect rest (item::acc) (count+1)))
        fun restore terms acc =
          (R.scope_meter_charge meter 16;
           case terms of [] => acc
           | item::rest =>
               (R.scope_meter_charge meter 16;
                restore rest (item::acc)))
        val _ = R.scope_meter_charge meter 16
        val (reverse,count) = collect assumptions [goal] (1:IntInf.int)
        val originals = restore reverse []
        (* restore above yields goal followed by assumptions in their
           original order, with duplicates and exact pointers retained. *)
        val graph_context = G.begin_original_import_context
          fixed_storage root
          {limits={construction_limits= #construction_limits request,
                   semantic_limits= #semantic_limits request,
                   native_limits= #native_limits request},
           originals=originals}
        val _ = inside seed
        val _ = R.scope_meter_charge meter 32
        val _ = R.scope_meter_charge meter 4
        val _ = R.scope_meter_charge meter 4
      in OrderedOriginalContext {owner=seed,original=original,
        request=request,originals=originals,count=count,
        graph_context=graph_context,prepared=ref NONE,
        final_result=ref NONE} end)
    end handle primary => (retire_seed seed;raise primary)

  fun ordered_original_progress_for (work as Work expected)
      (OrderedOriginalContext saved) =
    let
      (* Expected owner rejection must precede saved backing validation. *)
      val _ = if same_seed (expected,#owner saved) then () else
        fail expected "ordered_original_progress" "foreign original context"
      val Seed {fixed_storage,root,meter,publication,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 64
        val _ = if !publication=Acquiring orelse !publication=Ready then ()
          else
          fail expected "ordered_original_progress" "original is not Acquiring"
        val progress = G.original_import_progress fixed_storage root
          (#graph_context saved)
      in {originals= #count saved,completed= #completed progress,
        usage= #usage progress,revision= #revision progress,
        denial_complete= #denial_complete progress} end)
    end handle primary => (retire_seed expected;raise primary)

  (* One binding is minted inside the owned Pending action. It stores the
     original Work, not a successor wrapper or replacement allowance. *)
  fun bind_pending_sources (work as Work expected) held =
    let
      val Seed {graph,root,...} = expected
      val _ = validate_for work held graph root
      val _ = inside expected
      val Seed {publication,source_claimed,meter,...} = expected
      val _ = R.scope_meter_charge meter 64
      val _ = if !publication=Pending then () else
        fail expected "bind_pending_sources" "original is not Pending"
      val _ = if !source_claimed then
        fail expected "bind_pending_sources" "Source adoption already claimed"
        else ()
      val result = SourceBinding
        {seed=expected,work=work,invocation_claimed=ref false}
      val _ = source_claimed := true
    in result end
    handle primary => (retire_seed expected;raise primary)

  (* Pure immutable header DATA is available before Ready. No graph
     getter, activation, native grant or counter is issued here. *)
  fun source_binding_header (SourceBinding {seed,...}) =
    header_metadata seed

  fun source_binding_validate_work expected
      (SourceBinding {seed=held,...}) =
    let val Seed {graph,root,...} = held
    in validate_for expected held graph root end

  fun source_binding_claim_work
      (SourceBinding {seed,work,invocation_claimed}) =
    with_action work (fn () =>
      let
        val Seed {publication,meter,...} = seed
        val _ = R.scope_meter_charge meter 32
        val _ = if !invocation_claimed then
          fail seed "source_binding_claim_work"
            "original Source work invocation already claimed" else ()
        val _ = if !publication=Pending then () else
          fail seed "source_binding_claim_work" "original is not Pending"
        val _ = invocation_claimed := true
      in work end)

  (* Failure-only monotone latches remain usable after Work exhaustion.
     They cannot renew a Source or create a counter/native entitlement. *)
  fun source_binding_consume_attempt
      (SourceBinding {seed,invocation_claimed,...}) =
    (invocation_claimed := true;retire_seed seed)
  fun source_binding_refuse_legacy binding =
    (source_binding_consume_attempt binding;
     raise Feedback.mk_HOL_ERR "SmtReplaySource" "claim_invocation_work"
       "original acquisition requires coupled Work")

  fun source_binding_sources (SourceBinding {seed,...}) =
    (
    let
      val ReadyPayload {goal,assumptions,denied,...} = ready seed
      val Seed {graph,root,meter,...} = seed
      val _ = R.scope_meter_charge meter 16
    in {graph=graph,root=root,goal=goal,assumptions=assumptions,
        denied=denied} end

     handle R.Limit => (retire_seed seed;raise R.Limit))

  fun source_binding_assumption_nodes (SourceBinding {seed,...}) =
    (
    let val ReadyPayload {assumption_nodes,...} = ready seed
        val Seed {meter,...} = seed
        val _ = R.scope_meter_charge meter 16
    in assumption_nodes end
     handle R.Limit => (retire_seed seed;raise R.Limit))

  fun source_binding_reconciliation (SourceBinding {seed,...}) =
    (
    let val ReadyPayload {reconciliation,...} = ready seed
        val Seed {meter,...} = seed
        val _ = R.scope_meter_charge meter 16
    in reconciliation end
     handle R.Limit => (retire_seed seed;raise R.Limit))

  fun source_binding_canonical_goal (SourceBinding {seed,...}) =
    (
    let val ReadyPayload {canonical_goal,...} = ready seed
        val Seed {meter,...} = seed
        val _ = R.scope_meter_charge meter 16
    in canonical_goal end
     handle R.Limit => (retire_seed seed;raise R.Limit))

  fun source_binding_original (SourceBinding {seed,...}) =
    (
    (ignore (ready seed);
     let val Seed {meter,...} = seed
     in R.scope_meter_charge meter 16;original_metadata seed end)
     handle R.Limit => (retire_seed seed;raise R.Limit))

  fun source_binding_require_ready (SourceBinding {seed,...}) =
    ignore (ready seed)

  (* No arbitrary Term hash/traversal is needed for a raw theorem Hyp.
     Canonical representatives are fetched by genuine paid graph lookup;
     pointer membership has exactly the old private-array predicate. *)
  fun paid_source_hypotheses (seed as Seed {graph,meter,...}) nodes theorem =
    let
      val _ = R.scope_meter_charge meter 32
      val hypset = Thm.hypset theorem
      val count = IntInf.fromInt(HOLset.numItems hypset)
      (* Protected set's cached count, never a caller cardinality/quote.
         No comparator or native Term walk occurs in listItems. *)
      val _ = R.scope_meter_charge meter (256+256*count)
      val hypotheses = HOLset.listItems hypset
      fun member term held =
        (R.scope_meter_charge meter 16;
         case held of [] => false
         | node::rest =>
             (R.scope_meter_charge meter 32;
              if Portable.pointer_eq(term,
                  G.representative_with_meter graph node meter) then true
              else member term rest))
      fun all rows =
        (R.scope_meter_charge meter 16;
         case rows of [] => true
         | term::rest =>
             (R.scope_meter_charge meter 16;active seed;
              member term nodes andalso all rest))
    in all hypotheses end

  (* Only fixed private literals enter the expected side. Reject length
     before byte comparison: unknown names cannot trigger unbounded work. *)
  fun paid_fixed_string meter expected candidate =
    let
      val _ = R.scope_meter_charge meter 16
      val size = String.size expected
      val _ = if size<=8 then () else
        raise ERR "paid_fixed_string" "nonfixed private literal"
      fun bytes index =
        (R.scope_meter_charge meter 8;
         if index=size then true else
           (R.scope_meter_charge meter 8;
            String.sub(candidate,index)=String.sub(expected,index)
            andalso bytes(index+1)))
    in if String.size candidate=size then bytes 0 else false end

  fun paid_source_tags (Seed {meter,...}) theorem =
    let
      val _ = R.scope_meter_charge meter 32
      val tag = Thm.tag theorem
      (* Tag.dest_tag maps Nonce.dest over ALL axioms. Refuse a nonempty
         axiom head first; only its genuine empty case may be unpacked. *)
    in case Tag.axioms_of tag of _::_ => false
      | [] =>
        let
          val _ = R.scope_meter_charge meter 32
          val (oracles,_) = Tag.dest_tag tag
          fun all names =
            (R.scope_meter_charge meter 16;
             case names of [] => true
             | name::rest =>
                 (R.scope_meter_charge meter 16;
                  paid_fixed_string meter "DISK_THM" name andalso all rest))
        in all oracles end
    end

  fun paid_false_conclusion (Seed {meter,...}) conclusion =
    let
      val _ = R.scope_meter_charge meter 128
    in Portable.pointer_eq(conclusion,boolSyntax.F) orelse
      (Term.is_const conclusion andalso
       let
         val {Name=id,...} = Term.dest_thy_constid conclusion
         val {Thy,Name} = KernelSig.name_of_id id
         (* Both selected same_const implementations compare the complete
            immutable KernelSig id. Bound BOTH name fields before that
            structural equality; retain the actual identity predicate. *)
       in paid_fixed_string meter "bool" Thy andalso
          paid_fixed_string meter "F" Name andalso
          Term.same_const conclusion boolSyntax.F end)
    end

  (* Legacy Ready currently originates only in its exact uncapped route.
     These paid metadata programmes do not upgrade arbitrary raw proofs
     into finite native/type admission or a complete producer tariff. *)
  fun source_binding_check_goal (SourceBinding {seed,...}) theorem =
    ((let
      val ReadyPayload {goal,assumption_nodes,...} = ready seed
      val Seed {meter,...} = seed
      val _ = R.scope_meter_charge meter 32
      val err = Feedback.mk_HOL_ERR "SmtReplaySource" "check_goal"
      val _ = if Portable.pointer_eq(Thm.concl theorem,#original goal)
        then () else raise err "source conclusion was not retained exactly"
      val _ = if paid_source_hypotheses seed assumption_nodes theorem
        then () else raise err "hypothesis is not a retained permitted source"
      val _ = if paid_source_tags seed theorem then () else
        raise err "unexpected replay tags"
    in active seed end)
    handle R.Limit => (retire_seed seed;raise R.Limit))

  fun source_binding_check_contradiction
      (SourceBinding {seed,...}) theorem =
    ((let
      val ReadyPayload {denied,assumption_nodes,...} = ready seed
      val Seed {meter,...} = seed
      val _ = R.scope_meter_charge meter 32
      val err = Feedback.mk_HOL_ERR "SmtReplaySource" "check_contradiction"
      val conclusion = Thm.concl theorem
      val _ = if paid_false_conclusion seed conclusion then () else
        raise err "replay did not prove F"
      val _ = R.scope_meter_charge meter 16
      val nodes = #node denied::assumption_nodes
      val _ = if paid_source_hypotheses seed nodes theorem then () else
        raise err "hypothesis is not a retained permitted source"
      val _ = if paid_source_tags seed theorem then () else
        raise err "unexpected replay tags"
    in active seed end)
    handle R.Limit => (retire_seed seed;raise R.Limit))

  (* Own captured ordered occurrence only; never a caller term or proof.
     Native/semantic failure retires SAME A and preserves its actual prefix.
     Even InputsComplete leaves Acquiring: denial and Ready remain absent. *)
  fun advance_ordered_boolean_original (work as Work expected)
      (OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#owner saved) then () else
        fail expected "ordered_boolean_original" "foreign original context"
      val Seed {fixed_storage,root,meter,publication,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 64
        val _ = if !publication=Acquiring then () else
          fail expected "ordered_boolean_original" "original is not Acquiring"
        val result = G.advance_original_boolean_leaf fixed_storage root
          (#graph_context saved)
        val _ = inside expected
      in result end)
    end handle primary => (retire_seed expected;raise primary)

  fun complete_ordered_boolean_denial (work as Work expected)
      (OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#owner saved) then () else
        fail expected "ordered_boolean_denial" "foreign original context"
      val Seed {fixed_storage,root,meter,publication,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 64
        val _ = if !publication=Acquiring then () else
          fail expected "ordered_boolean_denial" "original is not Acquiring"
        val _ = G.complete_original_boolean_denial fixed_storage root
          (#graph_context saved)
        val _ = inside expected
      in () end)
    end handle primary => (retire_seed expected;raise primary)

  (* Paid private preparation PREFIX. This never publishes Ready. The
     cached Sources originate only in the closed SAME-context G port. *)
  fun prepare_ordered_original_sources (work as Work expected)
      (OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#owner saved) then () else
        fail expected "ordered_source_preparation" "foreign original context"
      val Seed {fixed_storage,graph,root,meter,publication,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 128
        val _ = if !publication=Acquiring then () else
          fail expected "ordered_source_preparation"
            "original is not Acquiring"
        val _ = case !(#prepared saved) of NONE => () | SOME _ =>
          fail expected "ordered_source_preparation" "Sources already prepared"
        val data = G.classified_original_source_preparation_data fixed_storage
          root
          (#graph_context saved)
        (* Each actual fixed-size array is fully admitted BEFORE allocation.
           These are defined structural fees, not unbounded native quotes. *)
        val _ = R.scope_meter_charge meter 4109
        val ordinary : Term.term list Array.array = Array.array(4093,[])
        val _ = R.scope_meter_charge meter 4109
        val allowed : Term.term list Array.array = Array.array(4093,[])
        fun put table (canonical:Term.term,bucket) =
          (R.scope_meter_charge meter 32;
           Array.update(table,bucket,canonical::Array.sub(table,bucket)))
        fun reverse rows acc =
          (R.scope_meter_charge meter 16;
           case rows of [] => acc
           | item::rest => (R.scope_meter_charge meter 16;
               reverse rest (item::acc)))
        (* Shapes follow the exact constructor-owned programme, not a
           generic proof validation or the looser admitted quota bounds. *)
        fun atomic_shape () : shape =
          (R.scope_meter_charge meter 16;
           {raw=SOME 1,inc=SOME 1,ann=SOME 1,root_type=1})
        fun equality_shape () : shape =
          (R.scope_meter_charge meter 16;
           {raw=SOME 5,inc=SOME 5,ann=SOME 11,root_type=1})
        val _ = R.scope_meter_charge meter 32
        val (goal,assumption_rows) = case #originals data of
            (source,_)::rest => (source,rest)
          | [] => fail expected "ordered_source_preparation"
            "missing original goal"
        val (denied,denied_bucket) = #denied data
        fun assumptions rows sources nodes origins shapes equalities count =
          (R.scope_meter_charge meter 32;
           case rows of [] =>
             (sources,nodes,origins,shapes,equalities,count)
           | (source:G.source,bucket)::rest =>
               let
                 val _ = R.scope_meter_charge meter 64
                 (* Exactly one paid canonical lookup per assumption row;
                    reuse it for both membership tables and its origin. *)
                 val _ = R.scope_meter_charge meter 32
                 val canonical = G.representative_with_meter graph
                   (#node source) meter
                 val _ = put ordinary (canonical,bucket)
                 val _ = put allowed (canonical,bucket)
                 val origin = ReadyOrigin
                   {source=source,canonical=canonical}
                 val shape = atomic_shape ()
                 val equality = equality_shape ()
               in assumptions rest (source::sources) (#node source::nodes)
                 (origin::origins) (shape::shapes) (equality::equalities)
                 (count+1) end)
        val (rev_sources,rev_nodes,rev_origins,rev_shapes,rev_equalities,count)
          =
          assumptions assumption_rows [] [] [] [] [] (0:IntInf.int)
        val sources = reverse rev_sources []
        val nodes = reverse rev_nodes []
        val shapes = reverse rev_shapes []
        val _ = put allowed (#original denied,denied_bucket)
        val goal_shape = case #application data of NONE => atomic_shape ()
          | SOME _ => (R.scope_meter_charge meter 16;
              {raw=SOME 3,inc=SOME 3,ann=SOME 5,root_type=1})
        val goal_equality = case #application data of NONE => equality_shape ()
          | SOME _ => (R.scope_meter_charge meter 16;
              {raw=SOME 9,inc=SOME 9,ann=SOME 19,root_type=1})
        val _ = R.scope_meter_charge meter 128
        val denial_shape : shape = case #application data of
            NONE => {raw=SOME 3,inc=SOME 3,ann=SOME 5,root_type=1}
          | SOME _ => {raw=SOME 5,inc=SOME 5,ann=SOME 9,root_type=1}
        val denial_equality : shape = case #application data of
            NONE => {raw=SOME 9,inc=SOME 9,ann=SOME 19,root_type=1}
          | SOME _ => {raw=SOME 13,inc=SOME 13,ann=SOME 27,root_type=1}
        val portfolio : acquisition_portfolio =
          {originals=goal_shape::shapes,denied=denial_shape,
           equalities=goal_equality::reverse (denial_equality::rev_equalities)
             [],
           native_program=(case #application data of NONE =>
  ["closed ordered atomic REFL/assumption ALPHA and constructor-owned denial"]
            | SOME _ =>
              ["owned typed-child MK_COMB/ALPHA/TRANS and App denial"]),
           qualified_initial_inspection=true,full_tariff=false}
        val origin_rows = ReadyOrigin {source=goal,canonical= #original goal}::
          reverse (ReadyOrigin {source=denied,canonical= #original denied}::
            rev_origins) []
        (* New private owner record/Some and ref/field holds are paid now.
           Reuse the existing final_result ref; allocate no new counter. *)
        val _ = R.scope_meter_charge meter 16
        val result = ReadyPayload
          {goal=goal,assumptions=sources,denied=denied,portfolio=portfolio,
           revision= #revision data,origins=origin_rows,allowed=allowed,
           ordinary=ordinary,assumption_nodes=nodes,
           reconciliation=denied::sources,canonical_goal= #original goal,
           ordered_owner=SOME (case #application data of
               NONE => OrderedReadyOwner
                 {graph_context= #graph_context saved,
                  final_result= #final_result saved}
             | SOME completion =>
                 (R.scope_meter_charge meter 8;
                  OwnedApplicationReadyOwner
                    {graph_context= #graph_context saved,
                     final_result= #final_result
                       saved,completion=completion}))}
        val _ = if count+1= #count saved then () else
          fail expected "ordered_source_preparation"
            "different original inventory"
        val _ = inside expected
        val progress = G.original_import_progress fixed_storage root
          (#graph_context saved)
        val _ = R.scope_meter_charge meter 32
        val _ = if #revision progress= #revision data andalso
            #denial_complete progress then () else
          fail expected "ordered_source_preparation"
            "completion witness changed"
        (* Publication remains Acquiring. No Source/array/Ready extraction
           or setter is exported; failed postclosure retires this same A. *)
        val _ = #prepared saved := SOME result
      in () end)
    end handle primary => (retire_seed expected;raise primary)

  fun ordered_source_preparation_for (work as Work expected)
      (OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#owner saved) then () else
        fail expected "ordered_source_preparation" "foreign original context"
      val Seed {fixed_storage,root,meter,publication,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 64
        val _ = if !publication=Acquiring orelse !publication=Ready then ()
          else
          fail expected "ordered_source_preparation"
            "original is not Acquiring"
        val progress = G.original_import_progress fixed_storage root
          (#graph_context saved)
        val ReadyPayload {revision,...} = case !(#prepared saved) of
            SOME payload => payload
          | NONE => fail expected "ordered_source_preparation"
            "Sources not prepared"
        val _ = if revision= #revision progress andalso
            #denial_complete progress then () else
          fail expected "ordered_source_preparation"
            "completion witness changed"
      in {originals= #count saved,ordinary_occurrences= #count saved-1,
        allowed_occurrences= #count saved,revision=revision,
        prepared=true,full_tariff=false} end)
    end handle primary => (retire_seed expected;raise primary)

  (* Private prospective publication gate. The only exported wrapper
     returns unit. No Ready store or public payload/Source setter exists. *)
  fun ordered_prepared_publication_candidate (work as Work expected)
      (OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#owner saved) then () else
        fail expected "ordered_prepared_validation" "foreign original context"
      val Seed {fixed_storage,root,meter,publication,payload,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 128
        val _ = if !publication=Acquiring orelse !publication=Ready then ()
          else
          fail expected "ordered_prepared_validation"
            "original is not Acquiring"
        val result as ReadyPayload
          {goal,assumptions,denied,origins,revision,...} =
          case !(#prepared saved) of SOME payload => payload
          | NONE => fail expected "ordered_prepared_validation"
            "Sources not prepared"
        val _ = R.scope_meter_charge meter 16
        val _ = case !publication of Ready =>
            (case !payload of SOME committed =>
               if Portable.pointer_eq(result,committed) then () else
                 fail expected "ordered_prepared_validation"
                   "different committed ordered payload"
             | NONE => fail expected "ordered_prepared_validation"
                 "missing committed ordered payload")
          | _ => ()
        val data = G.original_source_preparation_data fixed_storage root
          (#graph_context saved)
        fun same (left:G.source,right:G.source) =
          (R.scope_meter_charge meter 32;
           #node left= #node right andalso
           Portable.pointer_eq(#original left,#original right) andalso
           Portable.pointer_eq(#bridge left,#bridge right))
        fun joined issued prepared =
          (R.scope_meter_charge meter 16;
           case (issued,prepared) of
               ([],[]) => true
             | ((source,_)::rest,held::tail) =>
                 same(source,held) andalso joined rest tail
             | _ => false)
        val _ = R.scope_meter_charge meter 16
        val retained = goal::assumptions
        val _ = if revision= #revision data andalso
            joined (#originals data) retained andalso
            same(#1(#denied data),denied) then () else
          fail expected "ordered_prepared_validation"
            "different prepared issuance"
        val _ = validate_ready_origins expected origins
        val _ = inside expected
        val progress = G.original_import_progress fixed_storage root
          (#graph_context saved)
        val _ = R.scope_meter_charge meter 32
        val _ = if revision= #revision progress andalso
            #denial_complete progress then () else
          fail expected "ordered_prepared_validation"
            "completion witness changed"
      in result end)
    end handle primary => (retire_seed expected;raise primary)

  fun validate_prepared_ordered_sources work context =
    ignore(ordered_prepared_publication_candidate work context)

  (* Genuine closed proof operation on the SAME prepared owner, before
     or after authenticated publication. No quota or result-latch renewal. *)
  (* Shared native programme, always inside the authentic SAME action.
     Both public I finalisation and Ready Source closure use this exact
     captured G context and one-shot result reference. *)
  fun finalise_ordered_owner_inside (work as Work expected)
      (OrderedReadyOwner saved) raw_false =
    (let
      val Seed {meter,...} = expected
      val _ = R.scope_meter_charge meter 128
      val _ = inside expected
      val Seed {fixed_storage,root,publication,...} = expected
      val _ = if !publication=Acquiring orelse !publication=Ready then ()
        else fail expected "ordered_boolean_finalise"
          "original is not Acquiring or Ready"
      val _ = case !(#final_result saved) of NONE => () | SOME _ =>
        fail expected "ordered_boolean_finalise" "goal already finalised"
      val _ = R.scope_meter_charge meter 32
      val result = G.finalise_original_boolean_goal fixed_storage root
        (#graph_context saved) raw_false
      val _ = inside expected
      val _ = #final_result saved := SOME result
    in result end
    handle primary => (retire_seed expected;raise primary))
    | finalise_ordered_owner_inside (work as Work expected)
        (OwnedApplicationReadyOwner saved) raw_false =
      let
        val Seed {meter,...} = expected
        val _ = R.scope_meter_charge meter 128
        val _ = inside expected
        val Seed {fixed_storage,root,publication,...} = expected
        val _ = if !publication=Acquiring orelse !publication=Ready then ()
          else fail expected "ordered_boolean_finalise"
            "original is not Acquiring or Ready"
        val _ = case !(#final_result saved) of NONE => () | SOME _ =>
          fail expected "ordered_boolean_finalise" "goal already finalised"
        val _ = R.scope_meter_charge meter 32
        val result = G.finalise_owned_application_goal fixed_storage root
          (#graph_context saved) (#completion saved) raw_false
        val _ = inside expected
        val _ = #final_result saved := SOME result
      in result end
      handle primary => (retire_seed expected;raise primary)

  fun finalise_ordered_boolean_goal (work as Work expected)
      (context as OrderedOriginalContext saved) raw_false =
    let
      val _ = if same_seed(expected,#owner saved) then () else
        fail expected "ordered_boolean_finalise" "foreign original context"
      val Seed {meter,...} = expected
      val candidate = ordered_prepared_publication_candidate work context
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 32
        val ReadyPayload {ordered_owner,...} = candidate
        val owner = case ordered_owner of SOME owner => owner
          | NONE => fail expected "ordered_boolean_finalise"
              "missing ordered completion owner"
        val result_ref = case owner of
            OrderedReadyOwner retained => #final_result retained
          | OwnedApplicationReadyOwner retained => #final_result retained
        val _ = if result_ref= #final_result saved then () else
          fail expected "ordered_boolean_finalise" "different ordered owner"
      in finalise_ordered_owner_inside work owner raw_false end)
    end handle primary => (retire_seed expected;raise primary)

  (* Authentic G Profile2 keeps these four geometry fields as monotone
     occurrence telemetry. Its closed producer checked every native call's
     actual per-payload capacities already; publication is no native call.
     Other eleven gates keep their current cumulative units unchanged. *)
  fun ordered_usage_admitted (request:request)
      (used:G.original_import_usage) =
    let
      val construction = #construction_limits request
      val recipes = #recipe_limits construction
      val semantic = #semantic_limits request
      val native = #native_limits request
      val ns = #semantic_limits native
      val allows = RP.allows
    in allows (#import_limit construction) (#construction_import used)
      andalso allows (#literal_limit construction) (#construction_literal used)
      andalso allows (#binder_limit construction) (#construction_binder used)
      andalso allows (#template_limit recipes) (#recipe_template used)
      andalso allows (#index_limit recipes) (#recipe_index used)
      andalso allows (#operand_limit recipes) (#recipe_operand used)
      andalso allows (#token_limit recipes) (#recipe_token used)
      andalso (#semantic_input used>=0)
      andalso (#semantic_output used>=0)
      andalso allows (#template_limit semantic) (#semantic_template used)
      andalso (#native_input used>=0)
      andalso (#native_output used>=0)
      andalso allows (#template_limit ns) (#native_template used)
      andalso allows (#import_limit native) (#native_import used)
      andalso allows (#type_work_limit native) (#type_work used) end

  (* Compare actual immutable request values, including Work and all
     four capacities, against the privately captured original context.
     Limits are DATA, never an external grant/profile or replacement payer.
     Caller prepays this complete fixed16-field programme before entry. *)
  fun same_ordered_request (left:request) (right:request) =
    let
      val lc= #construction_limits left
      val rc= #construction_limits right
      val lr= #recipe_limits lc
      val rr= #recipe_limits rc
      val ls= #semantic_limits left
      val rs= #semantic_limits right
      val ln= #native_limits left
      val rn= #native_limits right
      val lns= #semantic_limits ln
      val rns= #semantic_limits rn
    in #import_limit lc= #import_limit rc
      andalso #literal_limit lc= #literal_limit rc
      andalso #binder_limit lc= #binder_limit rc
      andalso #template_limit lr= #template_limit rr
      andalso #index_limit lr= #index_limit rr
      andalso #operand_limit lr= #operand_limit rr
      andalso #token_limit lr= #token_limit rr
      andalso #input_limit ls= #input_limit rs
      andalso #output_limit ls= #output_limit rs
      andalso #template_limit ls= #template_limit rs
      andalso #input_limit lns= #input_limit rns
      andalso #output_limit lns= #output_limit rns
      andalso #template_limit lns= #template_limit rns
      andalso #import_limit ln= #import_limit rn
      andalso #type_work_limit ln= #type_work_limit rn
      andalso #work_limit left= #work_limit right end

  (* Genuine closed producer publication. The complete immutable payload
     was privately built before this call; SAME Work/Source/counters stay.
     No arbitrary Ready setter or caller completion flag is exposed. *)
  fun complete_ordered_original_acquisition (work as Work expected)
      (context as OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#owner saved) then () else
        fail expected "ordered_acquisition" "foreign original context"
      val Seed {meter,...} = expected
      val result = ordered_prepared_publication_candidate work context
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 128
        val Seed {publication,payload,fixed_storage,root,request,...}=expected
        val _ = if !publication=Acquiring then () else
          fail expected "ordered_acquisition" "original is not Acquiring"
        val _ = case !payload of NONE => () | SOME _ =>
          fail expected "ordered_acquisition"
            "original payload already committed"
        val ReadyPayload {ordered_owner,revision,...} = result
        val owner = case ordered_owner of SOME owner => owner
            | NONE => fail expected "ordered_acquisition"
                "missing ordered completion owner"
        val result_ref = case owner of
            OrderedReadyOwner retained => #final_result retained
          | OwnedApplicationReadyOwner retained => #final_result retained
        val _ = if result_ref= #final_result saved then () else
          fail expected "ordered_acquisition" "different ordered owner"
        (* SAME immutable captured policy before all later publication
           validation. No context limits, native quota or counter changes. *)
        val _ = R.scope_meter_charge meter 128
        val _ = if same_ordered_request request (#request saved) then () else
          fail expected "ordered_acquisition"
            "captured original request changed"
        (* Eleven cumulative gates plus four nonnegative occurrence
           telemetry checks; actual per-payload native admission remains G.
           All precede final G/root/epoch closure and private stores. *)
        val _ = R.scope_meter_charge meter 256
        val _ = R.scope_meter_charge meter 64
        val _ = inside expected
        val progress = G.original_import_progress fixed_storage root
          (#graph_context saved)
        val _ = if #revision progress=revision andalso
            #completed progress= #count saved andalso
            #denial_complete progress then () else
          fail expected "ordered_acquisition" "completion witness changed"
        val _ = if ordered_usage_admitted request (#usage progress) then ()
          else fail expected "ordered_acquisition"
            "captured cumulative original policy exhausted"
        (* No callback or native/semantic effect between closure and these
           two private stores. Tail failure retires SAME seed/no rollback. *)
        val _ = payload := SOME result
        val _ = publication := Ready
      in () end)
    end handle primary => (retire_seed expected;raise primary)

  (* Ready OriginalSources native closure shares the exact private latch.
     Existing semantic users may already own Busy; reuse that SAME action.
     I/A finalisers above still own an action and reject nested reentry. *)
  fun source_binding_close_contradiction
      (binding as SourceBinding {seed,work,...}) theorem =
    let
      val payload = ready seed
      val Seed {meter,...} = seed
      val _ = R.scope_meter_charge meter 32
      val ReadyPayload {ordered_owner,...} = payload
    in case ordered_owner of SOME owner =>
        (let
          fun close () =
            let val result=finalise_ordered_owner_inside work owner theorem
                val _=source_binding_check_goal binding result
            in result end
          val Seed {action,...}=seed
        in case !action of Idle => with_action work close
          | Busy => (inside seed;close ())
          | Retired => (active seed;raise Fail "unreachable retired action")
        end handle primary => (retire_seed seed;raise primary))
      | NONE =>
        (* Literal legacy native semantics: this payload can only be made
           by the existing all-Uncapped producer. No finite path adopts it. *)
        let
          val _=source_binding_check_contradiction binding theorem
          val canonical=Thm.CCONTR
            (source_binding_canonical_goal binding) theorem
          val bridge= #bridge (#goal (source_binding_sources binding))
          val result=Thm.EQ_MP (Thm.SYM bridge) canonical
          val _=source_binding_check_goal binding result
        in result end
    end handle R.Limit => (retire_seed seed;raise R.Limit)


  (* This prepares a typed child, not a non-Bool hypothesis. It retains
     exact SAME Work/context and exposes no native Source or graph ID. *)
  fun prepare_ordered_function_child (work as Work expected)
      (OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#owner saved) then () else
        fail expected "ordered_function_child" "foreign original context"
      val Seed {fixed_storage,root,meter,publication,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 64
        val _ = if !publication=Acquiring then () else
          fail expected "ordered_function_child" "original is not Acquiring"
        val _ = G.prepare_original_function_child fixed_storage root
          (#graph_context saved)
        val _ = inside expected
      in () end)
    end handle primary => (retire_seed expected;raise primary)
  datatype owned_application_metadata = OwnedApplicationMetadata of
    {seed:seed,birth:G.owned_application_birth}

  (* One payer and one graph are born here. The native constructor executes
     before original Seed publication; no old Seed/Work is relabelled. *)
  fun new_owned_boolean_application_metadata request children =
    let
      val _ = if positive request then () else
        raise ERR "new_owned_application" "nonpositive original policy request"
      val initial : IntInf.int = case #work_limit request of
          RP.Uncapped => 41 | RP.AtMost _ => 44
      val _ = if RP.allows (#work_limit request) initial then () else
        raise ERR "new_owned_application" "original bootstrap Work exhausted"
      val charged = ref initial
      val meter = R.new_scope_meter_with_policy
        {limit= #work_limit request,charged=charged}
      val _ = R.scope_meter_charge meter 4
      val _ = R.scope_meter_charge meter 4
      val _ = R.scope_meter_charge meter 128
      val {function,argument} = children
      val {graph,root,storage,original,birth} =
        G.new_owned_boolean_application_with_bootstrap_meter meter
          {function=function,argument=argument,
           limits={construction_limits= #construction_limits request,
             semantic_limits= #semantic_limits request,
             native_limits= #native_limits request}}
      val initial_revision =
        G.validation_revision_with_meter graph root meter
      val _ = R.scope_meter_charge meter 36
      val seed = Seed {identity=ref (),graph=graph,root=root,
        original=([],original),request=request,
        epoch=Type.type_epoch (),symbols=Term.term_epoch (),charged=charged,
        claimed=ref false,action=ref Idle,publication=ref Pending,
        initial_revision=initial_revision,payload=ref NONE,
        source_claimed=ref false,meter=meter,fixed_storage=storage,
        native_started=ref true,first_variable_source=ref NONE,
        context_eligible=ref true}
      val owned = OwnedApplicationMetadata {seed=seed,birth=birth}
    in (seed,owned) end

  fun prepare_owned_application_context (work as Work expected)
      (OwnedApplicationMetadata retained) =
    let
      val _ = if same_seed(expected,#seed retained) then () else
        fail expected "owned_application_context" "foreign owned application"
      val Seed {original,request,meter,fixed_storage,root,
        publication,context_eligible,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 128
        val _ = if !publication=Pending then () else
          fail expected "owned_application_context" "original is not Pending"
        (* Birth is eligible exactly once. A prior legacy Boolean view
           clears this SAME latch even on classifier NONE; its real native
           history may not be discarded by carrying only birth usage. *)
        val _ = R.scope_meter_charge meter 16
        val _ = if !context_eligible then () else
          fail expected "owned_application_context"
            "previous original programme"
        val _ = context_eligible := false
        val _ = boolean_pending_revision expected
        val graph_context = G.begin_owned_application_import_context
          fixed_storage root (#birth retained)
        val _ = R.scope_meter_charge meter 64
        val originals = [#2 original]
        val _ = inside expected
        val _ = R.scope_meter_charge meter 40
        val context = OrderedOriginalContext
          {owner=expected,original=original,request=request,
           originals=originals,count=1,graph_context=graph_context,
           prepared=ref NONE,final_result=ref NONE}
        val _ = publication := Acquiring
      in context end)
    end handle primary => (retire_seed expected;raise primary)

  fun prepare_owned_application_children (work as Work expected)
      (OwnedApplicationMetadata retained) (OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#seed retained) andalso
          same_seed(expected,#owner saved) then () else
        fail expected "owned_application_children" "foreign owned application"
      val Seed {fixed_storage,root,meter,publication,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 96
        val _ = if !publication=Acquiring then () else
          fail expected "owned_application_children"
            "original is not Acquiring"
        val _ = G.prepare_owned_application_children fixed_storage root
          (#graph_context saved) (#birth retained)
        val _ = inside expected
      in () end)
    end handle primary => (retire_seed expected;raise primary)

  (* Actual private App Source issuance. The atomic-only denial consumer
     is deliberately not fed a larger goal under its old native bound. *)
  fun complete_owned_application_source (work as Work expected)
      (OwnedApplicationMetadata retained) (OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#seed retained) andalso
          same_seed(expected,#owner saved) then () else
        fail expected "owned_application_source" "foreign owned application"
      val Seed {fixed_storage,root,meter,publication,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 128
        val _ = if !publication=Acquiring then () else
          fail expected "owned_application_source" "original is not Acquiring"
        val _ = G.complete_owned_application_source fixed_storage root
          (#graph_context saved) (#birth retained)
        val _ = inside expected
      in () end)
    end handle primary => (retire_seed expected;raise primary)

  (* The birth and context, never caller terms/proofs, select this exact
     App-aware occurrence+denial programme. Old atomic bounds stay fenced. *)
  fun complete_owned_application_denial (work as Work expected)
      (OwnedApplicationMetadata retained) (OrderedOriginalContext saved) =
    let
      val _ = if same_seed(expected,#seed retained) andalso
          same_seed(expected,#owner saved) then () else
        fail expected "owned_application_denial" "foreign owned application"
      val Seed {fixed_storage,root,meter,publication,...} = expected
    in with_action work (fn () =>
      let
        val _ = R.scope_meter_charge meter 128
        val _ = if !publication=Acquiring then () else
          fail expected "owned_application_denial" "original is not Acquiring"
        val _ = G.complete_owned_application_denial fixed_storage root
          (#graph_context saved) (#birth retained)
        val _ = inside expected
      in () end)
    end handle primary => (retire_seed expected;raise primary)


  (* SAME Ready owner and prepared payload. Private workspace receipts
     expose no Work, Source, native proof, array, meter or G context. *)
  datatype ordered_proof_scope = OrderedProofScope of
    {owner:seed,final_result:Thm.thm option ref,
     workspace:G.original_proof_scope}

  fun ordered_proof_scope_payload (work as Work expected)
      (OrderedOriginalContext saved) =
    let
      val _=if same_seed(expected,#owner saved) then () else
        fail expected "ordered_proof_scope" "foreign original context"
      val Seed {meter,publication,request,...}=expected
      val _=R.scope_meter_charge meter 512
      val _=if !publication=Ready then () else
        fail expected "ordered_proof_scope" "original acquisition is not Ready"
      val result as ReadyPayload {ordered_owner,...}=ready expected
      val _=case !(#prepared saved) of SOME prepared =>
          if Portable.pointer_eq(result,prepared) then () else
            fail expected "ordered_proof_scope" "different prepared payload"
        | NONE => fail expected "ordered_proof_scope" "Sources not prepared"
      val _=case ordered_owner of SOME owner =>
          let val result_ref=case owner of
                  OrderedReadyOwner held => #final_result held
                | OwnedApplicationReadyOwner held => #final_result held
          in if result_ref= #final_result saved then () else
            fail expected "ordered_proof_scope" "different ordered owner" end
        | NONE => fail expected "ordered_proof_scope" "ordered owner required"
      val _=if same_ordered_request request (#request saved) then () else
        fail expected "ordered_proof_scope" "captured original request changed"
    in result end

  (* Literal retained fields, no array/list walk/copy or new result latch.
     The productive local512 above prepays this fixed record/SOME and the
     constant private post-tail checks/two stores below. *)
  fun ordered_proof_scope_payload_at
      (expected as Seed {fixed_storage,root,...})
      (OrderedOriginalContext saved)
      (ReadyPayload {goal,assumptions,denied,portfolio,origins,allowed,
        ordinary,assumption_nodes,reconciliation,canonical_goal,
        ordered_owner,...}) plan revision =
    let
      (* Only the closed actual scope plan can advance the opaque App
         token. Its one-use suffix was funded in G's stage1024; all A
         wrapper/variant/record allocation remains inside this stage512.
         No Source, quota, counter or final-result latch is replaced. *)
      val owner=case ordered_owner of
          SOME (OwnedApplicationReadyOwner held) =>
            SOME (OwnedApplicationReadyOwner
              {graph_context= #graph_context held,
               final_result= #final_result held,
               completion=G.stage_owned_application_completion_for_scope
                 fixed_storage root (#graph_context saved)
                 (#completion held) plan})
        | _ => ordered_owner
    in SOME (ReadyPayload
      {goal=goal,assumptions=assumptions,denied=denied,
       portfolio=portfolio,revision=revision,origins=origins,allowed=allowed,
       ordinary=ordinary,assumption_nodes=assumption_nodes,
       reconciliation=reconciliation,canonical_goal=canonical_goal,
       ordered_owner=owner}) end

  fun ordered_proof_scope_commit_guard expected
      (OrderedOriginalContext saved) prior =
    let val Seed {action,publication,payload,...}=expected
    in if !action=Idle andalso !publication=Ready andalso
        (case (!payload,!(#prepared saved)) of
            (SOME committed,SOME prepared) =>
              Portable.pointer_eq(prior,committed) andalso
              Portable.pointer_eq(prior,prepared)
          | _ => false) then () else
      fail expected "ordered_proof_scope" "private Ready payload changed"
    end

  fun open_ordered_proof_scope (work as Work expected)
      (context as OrderedOriginalContext saved) =
    let
      val _=if same_seed(expected,#owner saved) then () else
        fail expected "ordered_proof_scope" "foreign original context"
      val Seed {fixed_storage,root,payload,...}=expected
      val (prior,replacement,plan,result)=with_action work (fn () =>
        let
          val prior as ReadyPayload {revision,...}=
            ordered_proof_scope_payload work context
          val staged=G.stage_original_proof_scope fixed_storage root
            (#graph_context saved)
          val _=if #revision staged=revision+1 then () else
            fail expected "ordered_proof_scope"
              "scope revision prediction changed"
          val replacement=ordered_proof_scope_payload_at expected context prior
            (#plan staged) (#revision staged)
          val result=OrderedProofScope {owner=expected,
            final_result= #final_result saved,workspace= #workspace staged}
        in (prior,replacement,#plan staged,result) end)
      (* Existing billed action tail has completed before any graph effect.
         From here: closed prepaid checks/G stores/two private A stores. *)
      val _=ordered_proof_scope_commit_guard expected context prior
      val _=G.commit_original_proof_scope fixed_storage root
        (#graph_context saved) plan
      val _= #prepared saved := replacement
      val _=payload := replacement
    in result end
    handle primary => (retire_seed expected;raise primary)

  fun ordered_proof_scope_for (work as Work expected)
      (context as OrderedOriginalContext saved)
      (OrderedProofScope held) =
    let
      (* Both immutable expected identities precede held liveness. *)
      val _=if same_seed(expected,#owner saved) andalso
          same_seed(expected,#owner held) andalso
          #final_result held= #final_result saved then () else
        fail expected "ordered_proof_scope" "foreign original workspace"
      val Seed {fixed_storage,root,...}=expected
    in with_action work (fn () =>
      let val _=ordered_proof_scope_payload work context
      in G.original_proof_scope_for fixed_storage root
        (#graph_context saved) (#workspace held) end)
    end handle primary => (retire_seed expected;raise primary)

  fun close_ordered_proof_scope (work as Work expected)
      (context as OrderedOriginalContext saved)
      (OrderedProofScope held) =
    let
      val _=if same_seed(expected,#owner saved) andalso
          same_seed(expected,#owner held) andalso
          #final_result held= #final_result saved then () else
        fail expected "ordered_proof_scope" "foreign original workspace"
      val Seed {fixed_storage,root,payload,...}=expected
      val (prior,replacement,plan)=with_action work (fn () =>
        let
          val prior as ReadyPayload {revision,...}=
            ordered_proof_scope_payload work context
          val staged=G.stage_original_proof_scope_close fixed_storage root
            (#graph_context saved) (#workspace held)
          val _=if #revision staged=revision+1 then () else
            fail expected "ordered_proof_scope"
              "scope revision prediction changed"
          val replacement=ordered_proof_scope_payload_at expected context prior
            (#plan staged) (#revision staged)
        in (prior,replacement,#plan staged) end)
      val _=ordered_proof_scope_commit_guard expected context prior
      val _=G.commit_original_proof_scope fixed_storage root
        (#graph_context saved) plan
      val _= #prepared saved := replacement
      val _=payload := replacement
    in () end
    handle primary => (retire_seed expected;raise primary)

  (* Captured public-view visitor output only. A never exposes G context,
     row IDs, native terms/Types, Source/proof handles or mutable tables. *)
  datatype external_original_stage = ExternalOriginalStage of
    {owner:seed,context:Thm.thm option ref,
     stage:G.external_original_stage}
  type external_original_stage_summary = G.external_original_stage_summary

  fun prepare_ordered_external_original (work as Work expected)
      (OrderedOriginalContext saved) =
    let
      val _=if same_seed(expected,#owner saved) then () else
        fail expected "external_original_stage" "foreign original context"
      val Seed {fixed_storage,root,meter,publication,...}=expected
    in with_action work (fn () =>
      let
        val _=R.scope_meter_charge meter 128
        val _=if !publication=Acquiring then () else
          fail expected "external_original_stage" "original is not Acquiring"
        val _=case !(#final_result saved) of NONE => () | SOME _ =>
          fail expected "external_original_stage" "goal already finalised"
        val stage=G.prepare_external_original_stage fixed_storage root
          (#graph_context saved)
        val _=inside expected
        val _=R.scope_meter_charge meter 32
      in ExternalOriginalStage {owner=expected,context= #final_result saved,
        stage=stage} end)
    end handle primary => (retire_seed expected;raise primary)

  fun ordered_external_original_summary_for (work as Work expected)
      (OrderedOriginalContext saved) (ExternalOriginalStage held)
      : external_original_stage_summary =
    let
      (* Immutable expected ownership precedes held/context lifetime. *)
      val _=if same_seed(expected,#owner saved) andalso
          same_seed(expected,#owner held) andalso
          #final_result saved= #context held then () else
        fail expected "external_original_stage" "foreign external stage"
      val Seed {fixed_storage,root,meter,publication,...}=expected
    in with_action work (fn () =>
      let
        val _=R.scope_meter_charge meter 64
        val _=if !publication=Acquiring then () else
          fail expected "external_original_stage" "original is not Acquiring"
        val _=case !(#final_result saved) of NONE => () | SOME _ =>
          fail expected "external_original_stage" "goal already finalised"
        val result=G.external_original_stage_summary fixed_storage root
          (#graph_context saved) (#stage held)
        val _=inside expected
      in result end)
    end handle primary => (retire_seed expected;raise primary)

  (* Both formats capture the exact suffix of the caller's one
     status-positioned stream. The stream remains owned by that caller.
     This fixed cap matches the pinned current SmtResource.max_proof_bytes;
     A does not import SmtResource or reopen a path.  All requested bytes
     and the EOF probe are prepaid on the original finite Work meter. *)
  val certificate_max_bytes = 32 * 1024 * 1024
  val certificate_chunk_bytes = 64 * 1024
  datatype certificate_state = Fresh | Claimed | Spent
  type certificate_contents =
    {owner:seed,epoch:int,symbols:int,chunks:string vector,bytes:int,
     state:certificate_state ref}
  datatype paid_cpc_certificate = PaidCpcCertificate of certificate_contents
  datatype paid_z3_certificate = PaidZ3Certificate of certificate_contents

  fun capture_certificate operation format make_receipt
      (work as Work expected) input =
    let
      val Seed {request,meter,action,publication,epoch,symbols,...} =
        expected
      val _ = (case #work_limit request of RP.AtMost _ => ()
        | RP.Uncapped => fail expected operation
            ("full " ^ format ^ " capture requires finite original Work"))
      val _ = require_ready work
    in with_action work (fn () =>
      let
        val _ = (case (!action,!publication) of (Busy,Ready) => ()
          | _ => fail expected operation
              "original Work has no published owned action")
        (* 8192 setup, 128 per inputN attempt, 16 per byte prepaid into
           a private carry-forward credit before inputN, 256 per sealed
           block, 1024 before vector construction.  Credit covers the
           whole requested span before each read.  Short reads carry the
           unused credit forward; only an empty read means EOF. *)
        val _ = R.scope_meter_charge meter 8192
        val pending = ref ([]:string list)
        val pending_bytes = ref 0
        val blocks = ref ([]:string list)
        val count = ref 0
        val prepaid_credit = ref 0
        fun seal () =
          if !pending_bytes = 0 then () else
            (R.scope_meter_charge meter 256;
             blocks := String.concat (List.rev (!pending)) :: !blocks;
             pending := [];
             pending_bytes := 0)
        fun retain text =
          let
            val size = String.size text
            fun fill offset =
              if offset = size then () else
                let
                  val room = certificate_chunk_bytes - !pending_bytes
                  val take = Int.min (room,size-offset)
                  val piece = if offset = 0 andalso take = size then text
                    else String.substring (text,offset,take)
                  val _ = pending := piece :: !pending
                  val _ = pending_bytes := !pending_bytes + take
                  val _ = if !pending_bytes = certificate_chunk_bytes
                    then seal () else ()
                in fill (offset+take) end
          in fill 0 end
        fun capture () =
          let
            val room = certificate_max_bytes - !count
            val requested = if room = 0 then 1
              else Int.min (certificate_chunk_bytes,room)
            val _ = R.scope_meter_charge meter 128
            val missing = Int.max (0,requested - !prepaid_credit)
            val _ = if missing = 0 then () else
              R.scope_meter_charge meter (16 * IntInf.fromInt missing)
            val _ = prepaid_credit := !prepaid_credit + missing
            val text = TextIO.inputN (input,requested)
            val observed = String.size text
            val _ = if observed <= requested then () else
              fail expected operation
                "inputN exceeded requested bound"
            val _ = prepaid_credit := !prepaid_credit - observed
          in
            if observed = 0 then ()
            else if observed > room then
              fail expected operation
                ("32 MiB " ^ format ^ " certificate cap exceeded")
            else (retain text;count := !count + observed;capture ())
          end
        val _ = capture ()
        val _ = seal ()
        val _ = R.scope_meter_charge meter 1024
        val chunks = Vector.fromList (List.rev (!blocks))
      in make_receipt
          {owner=expected,epoch=epoch,symbols=symbols,chunks=chunks,
           bytes= !count,state=ref Fresh} end)
    end handle primary => (retire_seed expected;raise primary)

  (* Parsing reads immutable, prepaid chunks outside the capture action.
     The receipt is claimed before the callback and never reopened.  The
     only supplier is a one-pass data view; it cannot mint Source or Work. *)
  fun with_certificate_input operation format (Work expected)
      (receipt : certificate_contents) consume =
    let
      val _ = if same_seed (expected,#owner receipt) then () else
        fail expected operation
          ("foreign full " ^ format ^ " certificate")
      val Seed {action,publication,epoch,symbols,...} = expected
      val _ = active expected
      val _ = if !action = Idle andalso
          #epoch receipt = epoch andalso
          #symbols receipt = symbols andalso
          !publication = Ready then () else
        fail expected operation
          ("busy, stale or unpublished full " ^ format ^ " certificate")
      val _ = (case !(#state receipt) of Fresh => ()
        | _ => fail expected operation
            ("full " ^ format ^ " certificate already claimed"))
      val _ = #state receipt := Claimed
      val open_input = ref true
      val failed = ref (NONE:exn option)
      val block_index = ref 0
      val block_offset = ref 0
      val delivered = ref 0
      val eof_reads = ref 0
      fun next () =
        ((if !open_input andalso !(#state receipt) = Claimed
          then () else
            fail expected operation
              ("full " ^ format ^ " input is closed");
          (case (!action,!publication) of
             (Retired,_) => fail expected operation
               "original Work retired"
           | (_,Ready) => ()
           | _ => fail expected operation
               "original Work is not Ready");
          if Type.type_epoch () = epoch andalso
              Term.term_epoch () = symbols then () else
            fail expected operation
              "original Type or Term epoch changed";
          if !delivered = #bytes receipt then
            if !eof_reads < 16 then
              (eof_reads := !eof_reads + 1;NONE)
            else fail expected operation
              ("full " ^ format ^ " EOF allowance exhausted")
          else
            let
              val block = Vector.sub (#chunks receipt,!block_index)
              val offset = !block_offset
              val c = String.sub (block,offset)
              val _ = delivered := !delivered + 1
              val _ = if offset+1 = String.size block then
                (block_index := !block_index + 1;block_offset := 0)
                else block_offset := offset+1
            in SOME c end)
         handle primary =>
           ((case !failed of NONE => failed := SOME primary
             | SOME _ => ());
            retire_seed expected;raise primary))
      val outcome = Exn.capture consume next
      val _ = open_input := false
      val _ = #state receipt := Spent
    in
      case !failed of SOME primary => raise primary
      | NONE =>
          (case outcome of Exn.Exn primary => raise primary
           | Exn.Res result =>
               (if !delivered = #bytes receipt andalso
                   !eof_reads > 0 then () else
                  fail expected operation
                    ("full " ^ format ^ " input did not reach EOF");
                active expected;result))
    end handle primary => (retire_seed expected;raise primary)

  (* Distinct public constructors prevent cross-format receipt adoption.
     Only these private calls choose the data constructor and format. *)
  fun capture_cpc_certificate work input =
    capture_certificate "capture_cpc_certificate" "CPC"
      PaidCpcCertificate work input
  fun capture_z3_certificate work input =
    capture_certificate "capture_z3_certificate" "Z3"
      PaidZ3Certificate work input
  fun with_cpc_certificate_input work (PaidCpcCertificate receipt) consume =
    with_certificate_input "with_cpc_certificate_input" "CPC"
      work receipt consume
  fun with_z3_certificate_input work (PaidZ3Certificate receipt) consume =
    with_certificate_input "with_z3_certificate_input" "Z3"
      work receipt consume

end
