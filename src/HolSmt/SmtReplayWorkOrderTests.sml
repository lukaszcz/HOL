(* Task50: SAME-counter planning, including unsuccessful prefixes.
   No top-level tests: the selftest runner should call run().

   R planner budget failures retain R.Limit. G's own spends/guards retain
   the original plan_placeholders HOL_ERR diagnostics, including initial
   meter creation refusal; neither is accepted by a catch-all predicate.
   Direct G/meter tests compare these diagnostics with standalone G across
   low, middle and exact boundaries. W retires on either failure without
   refunding the successful prefix or publishing names. Cost DATA includes
   future finish reservations. *)
structure SmtReplayWorkOrderTests =
struct
  structure R = ReplayRedblackPrivateWork
  structure W = SmtReplayInvocationWork
  structure A = SmtReplayOriginalAcquisition
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure P = SmtReplayResourcePolicy

  fun require text yes = if yes then () else testutils.die text
  fun test label action =
    (testutils.tprint label; action (); testutils.OK ())
  fun limit action = (action (); false) handle R.Limit => true
  fun stale action = (action (); false) handle R.StalePlan => true
  fun hol_error action =
    (action (); false) handle Feedback.HOL_ERR _ => true
  fun hol_diagnostic err =
    (Feedback.top_structure_of err,Feedback.top_function_of err,
     Feedback.message_of err)
  fun charged w = #charged (W.audit_policy w)
  fun planner_limit w action = action () handle R.Limit =>
    (require "planner did not retire W before propagating R.Limit"
       (#retired (W.audit_policy w));
     raise R.Limit)

  datatype meter_kind = IntegerMeter | PolicyMeter
  val meter_kinds = [IntegerMeter,PolicyMeter]
  fun meter IntegerMeter cap initial =
        R.new_scope_meter
          {limit=IntInf.toInt cap,charged=ref (IntInf.toInt initial)}
    | meter PolicyMeter cap initial =
        R.new_scope_meter_with_policy
          {limit=P.AtMost cap,charged=ref initial}
  val meter_charge = R.scope_meter_charged_policy

  (* Each callback creates a fresh genuine plan, then uses its ordinary
     finisher. Comparing the WHOLE cost also checks byte/node reservations,
     not just the work scalar. Three boundaries, not a combinatorial sweep. *)
  fun boundaries ordinary metered =
    let
      val expected = ordinary 100000
      val amount = #work (expected:R.cost)
      fun one allowance =
        let val succeeds = allowance >= amount
            val ordinary_result = Exn.capture ordinary allowance
            val _ = require "standalone cost boundary"
              (case ordinary_result of
                 Exn.Res cost => succeeds andalso cost=expected
               | Exn.Exn R.Limit => not succeeds
               | Exn.Exn primary => raise primary)
            fun coupled kind =
              let val m = meter kind (7+allowance) 7
                  val result = Exn.capture metered m
                  val paid = meter_charge m
              in require "meter boundary/delta differs from standalone"
                (case result of
                   Exn.Res cost => succeeds andalso cost=expected andalso
                     paid=7+amount
                 | Exn.Exn R.Limit => not succeeds andalso
                     paid>=23 andalso paid<=7+allowance
                 | Exn.Exn primary => raise primary)
              end
        in List.app coupled meter_kinds end
    in List.app one [amount-1,amount,amount+1] end

  fun cost_then cost finish plan =
    let val answer = cost plan val _ = finish plan in answer end

  fun table_boundaries () =
    let
      val base = R.put_int (R.put_int (R.empty_int (),2,"two"),1,"one")
      val strings = R.add_string (R.empty_string (),"aaaaA")
      fun int_answer p = require "integer lookup answer"
        (R.int_lookup_value (base,p)=SOME "one")
      fun string_answer p = require "string lookup answer"
        (not (R.string_lookup_value (strings,p)))
      fun int_finish p = require "integer insertion payload"
        (R.peek_int (R.finish_int (base,p,"three"),3)=SOME "three")
      fun string_finish p = require "string insertion payload"
        (R.member_string (R.finish_string (strings,p),"aaaaZ"))
      fun batch_finish p = require "batch duplicate/order payload"
        (R.list_int (R.finish_int_batch
          (base,p,["three","new-one","last"]))=
          [(1,"new-one"),(2,"two"),(3,"last")])
      fun list_finish p = require "listing order"
        (R.finish_list_int (base,p)=[(1,"one"),(2,"two")])
      fun listing_batch () = R.insert_int_batch (base,[3,1,3],100000)
      fun batch_list_finish p =
        let val table = R.finish_int_batch_with_listing
              (base,p,["three","new-one","last"])
        in require "bound batch listing payload"
          (R.finish_batch_list_int (table,p)=
            [(1,"new-one"),(2,"two"),(3,"last")]) end
    in
      boundaries
        (fn cap => cost_then R.int_lookup_cost int_answer
          (R.lookup_int (base,1,cap)))
        (fn m => cost_then R.int_lookup_cost int_answer
          (R.scope_plan_lookup_int m (base,1)));
      boundaries
        (fn cap => cost_then R.string_lookup_cost string_answer
          (R.lookup_string (strings,"aaaaZ",cap)))
        (fn m => cost_then R.string_lookup_cost string_answer
          (R.scope_plan_lookup_string m (strings,"aaaaZ")));
      boundaries
        (fn cap => cost_then R.int_insertion_cost int_finish
          (R.insert_int (base,3,cap)))
        (fn m => cost_then R.int_insertion_cost int_finish
          (R.scope_plan_insert_int m (base,3)));
      boundaries
        (fn cap => cost_then R.string_insertion_cost string_finish
          (R.insert_string (strings,"aaaaZ",cap)))
        (fn m => cost_then R.string_insertion_cost string_finish
          (R.scope_plan_insert_string m (strings,"aaaaZ")));
      boundaries
        (fn cap => cost_then R.int_batch_cost batch_finish
          (R.insert_int_batch (base,[3,1,3],cap)))
        (fn m => cost_then R.int_batch_cost batch_finish
          (R.scope_plan_insert_int_batch m (base,[3,1,3])));
      boundaries
        (fn cap => cost_then R.int_listing_cost list_finish
          (R.list_int_plan (base,cap)))
        (fn m => cost_then R.int_listing_cost list_finish
          (R.scope_plan_list_int m base));
      boundaries
        (fn cap => cost_then R.int_batch_listing_cost batch_list_finish
          (R.list_int_batch_plan (listing_batch (),cap)))
        (fn m => cost_then R.int_batch_listing_cost batch_list_finish
          (R.scope_plan_list_int_batch m (listing_batch ())))
    end

  fun rejected_prefixes () = List.app (fn kind =>
    let
      val empty = R.empty_int () : int R.int_map
      val m = meter kind 24 0
      val _ = require "empty lookup must keep setup16 + view1"
        (limit (fn () => ignore (R.scope_plan_lookup_int m (empty,0)))
         andalso meter_charge m=17)
      val strings = R.add_string (R.empty_string (),"aaaaA")
      (* setup16, view1, search1, comparison1, lengths2, loop1,
         byte pair2, char1, loop1 =26. Next byte pair2 is indivisible. *)
      val bytes = meter kind 27 0
      val _ = require "string byte refusal lost successful byte prefix"
        (limit (fn () => ignore
          (R.scope_plan_lookup_string bytes (strings,"aaaaZ")))
         andalso meter_charge bytes=26)
      val next = meter kind 28 0
    in require "accepted byte pair was rolled back on next refusal"
      (limit (fn () => ignore
        (R.scope_plan_lookup_string next (strings,"aaaaZ")))
       andalso meter_charge next=28)
    end) meter_kinds

  fun reservations () = List.app (fn kind =>
    let
      val base = R.empty_int () : string R.int_map
      val m = meter kind 100000 0
      val insertion = R.scope_plan_insert_int m (base,4)
      val reserved = meter_charge m
      val _ = require "insertion did not reserve future tree nodes"
        (#finish_nodes (R.int_insertion_cost insertion)>0)
      val table = R.finish_int (base,insertion,"four")
      val _ = require "finish charged again or insertion reusable"
        (meter_charge m=reserved andalso
         stale (fn () => ignore (R.finish_int (base,insertion,"again")))
         andalso meter_charge m=reserved)
      val wrong = R.scope_plan_insert_int m (base,5)
      val before_wrong = meter_charge m
      val _ = require "wrong base did not burn the one-shot reservation"
        (stale (fn () => ignore (R.finish_int (table,wrong,"wrong")))
         andalso stale (fn () => ignore (R.finish_int (base,wrong,"five")))
         andalso meter_charge m=before_wrong)
      val batch = R.scope_plan_insert_int_batch m (table,[2,4,2])
      val before_list = meter_charge m
      val listing = R.scope_plan_list_int_batch m batch
      val after_list = meter_charge m
      val _ = require "listing charged underlying batch a second time"
        (after_list-before_list= #work (R.int_batch_listing_cost listing))
      val result = R.finish_int_batch_with_listing
        (table,listing,["two","new-four","last-two"])
      val rows = R.finish_batch_list_int (result,listing)
    in require "batch/list finish refunded, recharged or reusable"
      (rows=[(2,"last-two"),(4,"new-four")] andalso
       meter_charge m=after_list andalso
       stale (fn () => ignore (R.finish_batch_list_int (result,listing)))
       andalso stale (fn () => ignore
         (R.finish_int_batch (table,batch,["x","y","z"])))
       andalso meter_charge m=after_list)
    end) meter_kinds

  datatype mode = Ordinary | Finite | Uncapped | PricedInt
                | PricedFinite | PricedUncapped
  val modes = [Ordinary,Finite,Uncapped,PricedInt, PricedFinite,
               PricedUncapped]
  val bounded_modes = [Ordinary,Finite,PricedInt,PricedFinite]
  val limits = {input_limit=64,output_limit=64,template_limit=64}
  val semantic = P.semantic_from_ints limits
  val generous : IntInf.int = 2000000
  type env = {graph:G.graph,scope:G.scope,work:W.portfolio,
              nodes:G.node list}

  fun setup mode cap : env =
    let
      val g = G.new () val s = G.root_scope g
      val sources = S.new g s 64 {assumptions=[],goal=boolSyntax.T}
      val a = G.variable g s G.RigidSource
        (Term.mk_var ("work_order_a",Type.bool))
      val b = G.constant g s boolSyntax.F
      val policy = case mode of Uncapped => P.Uncapped
        | PricedUncapped => P.Uncapped | _ => P.AtMost cap
      val w = case mode of
          Ordinary => W.begin g s sources
            {limits=limits,work_limit=IntInf.toInt cap}
        | PricedInt => W.begin_with_scope_guard g s sources
            {limits=limits,work_limit=IntInf.toInt cap}
        | Finite => W.begin_with_policy g s sources
            {limits=semantic,work_limit=policy}
        | Uncapped => W.begin_with_policy g s sources
            {limits=semantic,work_limit=policy}
        | _ => W.begin_with_scope_guard_policy g s sources
            {limits=semantic,work_limit=policy}
    in {graph=g,scope=s,work=w,nodes=[a,b]} end

  fun fixture mode cap action =
    let val e = setup mode cap
        val answer = Exn.capture action e
        val cleanup = Exn.capture (fn () =>
          (W.close (#work e); G.close_scope (#graph e) (#scope e))) ()
    in case answer of Exn.Exn primary => raise primary
      | Exn.Res value => (Exn.release cleanup; value) end

  (* Known W guards, separate from the actual R/G plan cost. A successful
     priced plan pays remaining's active h + spend0's h, inside8, payer13.
     Failed R/G planning pays ONLY remaining's h, not the spend0 suffix.
     One successful action also pays entry/return h+9 each. *)
  fun guard w = case W.priced_root_scope_path w of NONE => 0
    | SOME path => 12+G.scope_path_validation_work path
  fun plan_overhead w = if guard w=0 then 0 else 2*guard w+21
  fun action_overhead w = if guard w=0 then 0 else 2*(guard w+9)

  fun paid w cost make finish =
    let val start = charged w val plan = make ()
        val amount = #work (cost plan:R.cost)
        val after_plan = charged w
        val answer = finish plan
    in require "W cost/delta mismatch or finish double charge"
         (after_plan-start=amount+plan_overhead w andalso
          charged w=after_plan);
       (answer,amount+plan_overhead w)
    end

  fun cumulative mode = fixture mode generous (fn {work=w,...}:env =>
    let
      val start = charged w
      val total = W.with_step w (fn () =>
        let
          val base = R.empty_int () : string R.int_map
          val (table,c1) = paid w R.int_insertion_cost
            (fn () => W.plan_insert_int w (base,2))
            (fn p => R.finish_int (base,p,"two"))
          val (answer,c2) = paid w R.int_lookup_cost
            (fn () => W.plan_lookup_int w (table,2))
            (fn p => R.int_lookup_value (table,p))
          val strings = R.empty_string ()
          val (names,c3) = paid w R.string_insertion_cost
            (fn () => W.plan_insert_string w (strings,"shared-prefix"))
            (fn p => R.finish_string (strings,p))
          val (found,c4) = paid w R.string_lookup_cost
            (fn () => W.plan_lookup_string w (names,"shared-prefix"))
            (fn p => R.string_lookup_value (names,p))
          val (batch,c5) = paid w R.int_batch_cost
            (fn () => W.plan_insert_int_batch w (table,[1,2,1]))
            (fn p => p)
          val (_,c6) = paid w R.int_batch_listing_cost
            (fn () => W.plan_list_int_batch w batch)
            (fn p =>
              let val result = R.finish_int_batch_with_listing
                    (table,p,["one","new-two","last-one"])
              in require "W batch listing payload"
                (R.finish_batch_list_int (result,p)=
                  [(1,"last-one"),(2,"new-two")]) end)
        in require "W lookup payloads" (answer=SOME "two" andalso found);
           c1+c2+c3+c4+c5+c6
        end)
      val _ = require "operations did not share cumulative Work"
        (charged w-start=total+action_overhead w)
      val before_second = charged w
      val (_,cost) = W.with_step w (fn () =>
        let val empty = R.empty_int () : int R.int_map
        in paid w R.int_lookup_cost
          (fn () => W.plan_lookup_int w (empty,0))
          (fn p => R.int_lookup_value (empty,p)) end)
    in require "next action reset the original allowance"
      (charged w-before_second=cost+action_overhead w andalso
       not (#retired (W.audit_policy w))) end)

  fun retired w =
    let val before_retry = charged w val called = ref false
        val refused = hol_error (fn () => W.with_step w
          (fn () => called := true))
    in require "failed attempt was reusable or retry charged again"
      (#retired (W.audit_policy w) andalso refused andalso not (!called)
       andalso charged w=before_retry) end

  (* Two operations, one allowance: the second cannot start from ref0.
     The pilot only measures deterministic setup/guards, not a new grant. *)
  fun budget_prefix mode =
    let
      val (before_second,overhead) = fixture mode generous
        (fn {work=w,...}:env => W.with_step w (fn () =>
          let val base = R.empty_int () : int R.int_map
              val first = W.plan_lookup_int w (base,0)
              val _ = ignore (R.int_lookup_value (base,first))
          in (charged w,guard w) end))
      val cap = before_second+overhead+24
    in fixture mode cap (fn {work=w,...}:env =>
      let val base = R.empty_int () : int R.int_map
          val no = limit (fn () => W.with_step w (fn () =>
            let val first = W.plan_lookup_int w (base,0)
                val _ = ignore (R.int_lookup_value (base,first))
            in planner_limit w (fn () =>
                 ignore (W.plan_lookup_int w (base,0))) end))
          val _ = require "W replaced first R.Limit or lost failed prefix"
            (no andalso charged w=before_second+overhead+17)
      in retired w end)
    end

  (* There is enough for remaining's h, but not even R's setup16. The old
     prepaid spend0 order would raise HOL_ERR instead of this first Limit. *)
  fun first_error mode =
    let
      val (prefix,h) = fixture mode generous
        (fn {work=w,...}:env => W.with_step w
          (fn () => (charged w,guard w)))
      val cap = prefix+h+1
    in fixture mode cap (fn {work=w,...}:env =>
      let
        val empty = R.empty_int () : int R.int_map
        val no = limit (fn () => W.with_step w (fn () =>
          (require "low-priced test did not leave exactly h+1"
             (cap-charged w=h+1);
           planner_limit w (fn () =>
             ignore (W.plan_lookup_int w (empty,0))))))
        val _ = require "first R.Limit paid setup or a later Work guard"
          (no andalso charged w=prefix+h)
      in retired w end)
    end

  (* Reconstruct the old finite Proof sequence, not the policy-plan 2h
     formula: remaining -> standalone R/G -> remaining -> spend(cost).
     Each legacy planner must agree with it, including the third h. *)
  fun legacy_compatibility mode = fixture mode generous
    (fn {graph=g,scope=s,work=w,nodes}:env => W.with_step w (fn () =>
      let
        val overhead = if guard w=0 then 0 else 3*guard w+21
        fun compare cost make ordinary finish =
          let
            val start = charged w
            val plan = make ()
            val amount : IntInf.int = cost plan
            val after_plan = charged w
            val answer = finish plan
            val _ = require "legacy plan missed remaining's third guard"
              (after_plan-start=amount+overhead andalso
               charged w=after_plan)
            val before_old = charged w
            val cap = case W.remaining_policy w of
                P.AtMost n => n
              | P.Uncapped => raise Fail "legacy fixture must be finite"
            val old = ordinary cap
            val old_amount = cost old
            val _ = ignore (W.remaining_policy w)
            val _ = W.spend_policy w old_amount
            val after_old = charged w
            val old_answer = finish old
            val _ = require "legacy delta differs from original pay sequence"
              (old_amount=amount andalso after_old-before_old=after_plan-start
               andalso charged w=after_old)
          in (answer,old_answer) end
        fun work cost p = #work (cost p:R.cost)
        val base = R.put_int (R.empty_int (),2,"two")
        val names = R.add_string (R.empty_string (),"legacy-name")
        val _ = compare (work R.int_lookup_cost)
          (fn () => W.legacy_plan_lookup_int w (base,2))
          (fn cap => R.lookup_int (base,2,cap))
          (fn p => require "legacy integer lookup payload"
            (R.int_lookup_value (base,p)=SOME "two"))
        val _ = compare (work R.string_lookup_cost)
          (fn () => W.legacy_plan_lookup_string w (names,"legacy-name"))
          (fn cap => R.lookup_string (names,"legacy-name",cap))
          (fn p => require "legacy string lookup payload"
            (R.string_lookup_value (names,p)))
        val _ = compare (work R.int_insertion_cost)
          (fn () => W.legacy_plan_insert_int w (base,3))
          (fn cap => R.insert_int (base,3,cap))
          (fn p => require "legacy insertion payload"
            (R.peek_int (R.finish_int (base,p,"three"),3)=SOME "three"))
        val (batch,old_batch) = compare (work R.int_batch_cost)
          (fn () => W.legacy_plan_insert_int_batch w (base,[1,2,1]))
          (fn cap => R.insert_int_batch (base,[1,2,1],cap)) (fn p => p)
        val _ = compare (work R.int_batch_listing_cost)
          (fn () => W.legacy_plan_list_int_batch w batch)
          (fn cap => R.list_int_batch_plan (old_batch,cap))
          (fn p =>
            let val table = R.finish_int_batch_with_listing
                  (base,p,["one","new-two","last-one"])
            in require "legacy batch/list payload"
              (R.finish_batch_list_int (table,p)=
                [(1,"last-one"),(2,"new-two")]) end)
        val revision = G.validation_revision g s
        val (fresh,old) = compare G.placeholder_plan_cost
          (fn () => W.legacy_plan_placeholders w g s {nodes=nodes})
          (fn cap => G.plan_placeholders_with_policy g s
            {nodes=nodes,remaining_work=P.AtMost cap})
          G.placeholder_plan_names
      in require "legacy naming changed payload or published during planning"
        (fresh=old andalso G.validation_revision g s=revision) end))

  fun action_boundary mode =
    let
      fun two ({work=w,...}:env) = W.with_step w (fn () =>
        let val base = R.empty_int () : int R.int_map
            fun one () =
              let val p = W.plan_lookup_int w (base,0)
              in ignore (R.int_lookup_value (base,p)) end
        in one (); one () end)
      val exact = fixture mode generous (fn e => (two e;charged (#work e)))
      fun check cap succeeds = fixture mode cap (fn e =>
        let val w = #work e val result = Exn.capture two e
        in case result of
            Exn.Res () => require "cumulative exact/over action failed"
              (succeeds andalso charged w=exact andalso
               not (#retired (W.audit_policy w)))
          | Exn.Exn R.Limit =>
              (require "unexpected over-budget R refusal" (not succeeds);
               retired w)
          | Exn.Exn (Feedback.HOL_ERR _) =>
              (* Priced modes can exhaust on the genuine return guard. *)
              (require "unexpected Work guard refusal" (not succeeds);
               retired w)
          | Exn.Exn primary => raise primary
        end)
    in check (exact-1) false; check exact true; check (exact+1) true end

  fun naming mode = fixture mode generous
    (fn {graph=g,scope=s,work=w,nodes}:env =>
      let
        val standalone = G.plan_placeholders_with_policy g s
          {nodes=nodes,remaining_work=P.Uncapped}
        val before_names = G.placeholder_plan_names standalone
        val revision = G.validation_revision g s
        val plan = W.with_step w (fn () =>
          let val start = charged w
              val p = W.plan_placeholders w g s {nodes=nodes}
          in require "W naming delta is not already-paid genuine cost"
            (charged w-start=G.placeholder_plan_cost p+plan_overhead w);
             p end)
        val _ = require "planning published names or changed graph"
          (G.validation_revision g s=revision andalso
           G.placeholder_plan_names plan=before_names andalso
           G.placeholder_plan_cost plan=
             G.placeholder_plan_cost standalone)
        val before_mint = charged w
        (* Guard validation/mint is separately paid; the reserved native
           suffix itself must not debit the plan's work a second time. *)
        val terms = W.with_step w (fn () =>
          (W.spend_policy w (G.placeholder_plan_guard_cost plan);
           G.mint_placeholder_terms g s plan))
        val _ = require "naming mint payload/order"
          (List.map #1 terms=nodes andalso
           List.map (fn (_,t) => #1 (Term.dest_var t)) terms=
             List.map #2 (List.rev before_names) andalso charged w>before_mint)
      in require "naming mint not one-shot"
        (hol_error (fn () => G.mint_placeholders g s plan)) end)

  (* Compare the original integer/policy G planners with their same-meter
     routes, including failures inside R and G's own spends/guards. A
     refused indivisible charge need not leave the meter exactly at cap. *)
  fun naming_diagnostics () = fixture Ordinary generous
    (fn {graph=g,scope=s,nodes,...}:env =>
      let
        val original = G.plan_placeholders_with_policy g s
          {nodes=nodes,remaining_work=P.Uncapped}
        fun answer p = (G.placeholder_plan_cost p,G.placeholder_plan_names p)
        val expected as (cost,names) = answer original
        val revision = G.validation_revision g s
        fun ordinary IntegerMeter cap = G.plan_placeholders g s
              {nodes=nodes,remaining_work=IntInf.toInt cap}
          | ordinary PolicyMeter cap = G.plan_placeholders_with_policy g s
              {nodes=nodes,remaining_work=P.AtMost cap}
        fun metered IntegerMeter m = G.plan_placeholders_with_meter g s m
              {nodes=nodes}
          | metered PolicyMeter m =
              G.plan_placeholders_with_meter g s m {nodes=nodes}
        fun same_error (R.Limit,R.Limit) = true
          | same_error (Feedback.HOL_ERR old,Feedback.HOL_ERR fresh) =
              hol_diagnostic old=hol_diagnostic fresh
          | same_error _ = false
        fun one kind cap =
          let
            val old = Exn.capture (answer o ordinary kind) cap
            val m = meter kind (7+cap) 7
            val fresh = Exn.capture (answer o metered kind) m
            val paid = meter_charge m
            val _ = require "G refusal lost or overcharged its paid prefix"
              (paid>=7 andalso paid<=7+cap)
            val _ = require "G meter changed standalone cost/names/diagnostic"
              (case (old,fresh) of
                 (Exn.Res a,Exn.Res b) => cap>=cost andalso
                   a=expected andalso b=expected andalso paid=7+cost
               | (Exn.Exn a,Exn.Exn b) => cap<cost andalso same_error (a,b)
               | _ => false)
          in require "direct G planning published names"
            (G.validation_revision g s=revision andalso
             answer (G.plan_placeholders_with_policy g s
               {nodes=nodes,remaining_work=P.Uncapped})=expected)
          end
        val _ = List.app (fn kind => List.app (one kind)
          [0,1,2,cost div 2,cost-1,cost,cost+1]) meter_kinds
        val terms = G.mint_placeholder_terms g s original
      in require "direct G refusal changed original naming snapshot"
        (List.map #1 terms=nodes andalso
         List.map (fn (_,t) => #1 (Term.dest_var t)) terms=
           List.map #2 (List.rev names)) end)

  fun naming_rejection mode =
    let
      val (prefix,overhead,cost) = fixture mode generous
        (fn {graph=g,scope=s,work=w,nodes}:env =>
          W.with_step w (fn () =>
            let val start = charged w
                val p = W.plan_placeholders w g s {nodes=nodes}
            in (start,guard w,G.placeholder_plan_cost p) end))
      (* One below R/G's full programme AFTER the initial remaining guard:
         no allowance for the later spend0 guards on this failed path.
         The final indivisible G spend retains its original diagnostic and
         successful prefix, before any publication/native mint. *)
      val cap = prefix+overhead+cost-1
    in fixture mode cap (fn {graph=g,scope=s,work=w,nodes}:env =>
      let
        val old = G.plan_placeholders_with_policy g s
          {nodes=nodes,remaining_work=P.Uncapped}
        val revision = G.validation_revision g s
        val no =
          ((W.with_step w (fn () =>
              (ignore (W.plan_placeholders w g s {nodes=nodes})
               handle primary as Feedback.HOL_ERR _ =>
                 (require "G failure did not retire W before propagating"
                    (#retired (W.audit_policy w));
                  raise primary)));
            false)
           handle Feedback.HOL_ERR err => hol_diagnostic err=
             ("SmtReplayGraph","plan_placeholders",
              "original remaining Work exhausted"))
        val _ = require "naming rejection changed diagnostic or paid prefix"
          (no andalso charged w>prefix+overhead andalso charged w<=cap)
        val fresh = G.plan_placeholders_with_policy g s
          {nodes=nodes,remaining_work=P.Uncapped}
        val _ = require "rejected naming published a name/native suffix"
          (G.validation_revision g s=revision andalso
           G.placeholder_plan_names fresh=G.placeholder_plan_names old
           andalso G.placeholder_plan_cost fresh=
             G.placeholder_plan_cost old)
        (* The OLD snapshot must still mint the original first candidates.
           This checks placeholders/reserved/next_name, not just output text.
           There is no native callback/finisher in the rejected action. *)
        val terms = G.mint_placeholder_terms g s old
        val _ = require "rejection invalidated original naming snapshot"
          (List.map #1 terms=nodes)
      in retired w end)
    end

  (* Even Uncapped must retire on a genuine planning failure; a valid
     staged first row must not escape when the second row is duplicate. *)
  fun semantic_failure mode = fixture mode generous
    (fn {graph=g,scope=s,work=w,nodes}:env =>
      let
        val old = G.plan_placeholders_with_policy g s
          {nodes=nodes,remaining_work=P.Uncapped}
        val revision = G.validation_revision g s
        val start = charged w
        val no = hol_error (fn () => W.with_step w (fn () =>
          (ignore (W.plan_placeholders w g s {nodes=[hd nodes,hd nodes]})
           handle primary as Feedback.HOL_ERR _ =>
             (require "semantic planner failure did not retire immediately"
                (#retired (W.audit_policy w));
              raise primary))))
        val _ = require "duplicate planning failure published or refunded"
          (no andalso charged w>start+plan_overhead w andalso
           G.validation_revision g s=revision)
        val _ = ignore (G.mint_placeholder_terms g s old)
      in retired w end)

  datatype original_owner = AOwner of A.work | WOwner of W.portfolio
  fun original_step (AOwner a) action = A.with_action a action
    | original_step (WOwner w) action = W.with_step w action
  fun original_audit (AOwner a) =
        let val {charged,retired,...} = A.audit a
        in {charged=charged,retired=retired} end
    | original_audit (WOwner w) = W.audit_policy w
  fun original_charged owner = #charged (original_audit owner)
  fun original_remaining (AOwner a) = A.remaining a
    | original_remaining (WOwner w) = W.remaining_policy w
  fun original_lookup (AOwner a) args = A.plan_lookup_int a args
    | original_lookup (WOwner w) args = W.plan_lookup_int w args
  (* Exact pre-coupling payer suffix, with no second remaining on A/W's
     original route. In particular, do not replace these by policy guards. *)
  fun original_pay (AOwner a) amount =
        (A.validate_work a;A.charge a 16;A.charge a 32;A.charge a amount)
    | original_pay (WOwner w) amount = W.spend_policy w amount

  fun original_fixture invocation cap action =
    let
      val request : A.request =
        {construction_limits=P.graph_from_ints
           {import_limit=64,literal_limit=64,binder_limit=64,
            recipe_limits={template_limit=64,index_limit=64,
                           operand_limit=64,token_limit=64}},
         semantic_limits=semantic,work_limit=P.AtMost cap,
         native_limits={semantic_limits=semantic,import_limit=P.AtMost 64,
                        type_work_limit=P.AtMost 64}}
      val seed = A.new_metadata request ([],boolSyntax.T)
      (* Pending binding/header operations are permitted here. Do not call
         S.owner/S.goal or pretend that acquisition has published Ready. *)
      val held = ref NONE
      val answer = Exn.capture (fn () =>
        let val owner = if invocation then
              WOwner (W.begin_original (S.new_pending seed))
            else AOwner (A.claim_work seed)
            val _ = held := SOME owner
        in action owner end) ()
      val cleanup = Exn.capture (fn () => A.close_seed seed
        handle R.Limit => require "cleanup Limit on a live original"
          (case !held of SOME owner =>
             #retired (original_audit owner) | NONE => false)) ()
    in case answer of Exn.Exn primary => raise primary
      | Exn.Res value => (Exn.release cleanup;value) end

  fun original_success invocation = original_fixture invocation generous
    (fn owner => original_step owner (fn () =>
      let
        val base = R.empty_int () : int R.int_map
        val start = original_charged owner
        val plan = original_lookup owner (base,0)
        val amount = #work (R.int_lookup_cost plan)
        val after_plan = original_charged owner
        val _ = require "original lookup payload or finish double debit"
          (R.int_lookup_value (base,plan)=NONE andalso
           original_charged owner=after_plan)
        val before_old = original_charged owner
        val cap = case original_remaining owner of
            P.AtMost n => n
          | P.Uncapped => raise Fail "original fixture must be finite"
        val old = R.lookup_int (base,0,cap)
        val old_amount = #work (R.int_lookup_cost old)
        val _ = original_pay owner old_amount
        val after_old = original_charged owner
      in require "original planner differs from its actual A/W payer guards"
        (amount=old_amount andalso after_plan-start=after_old-before_old
         andalso R.int_lookup_value (base,old)=NONE andalso
         original_charged owner=after_old andalso
         not (#retired (original_audit owner))) end))

  fun original_failure invocation =
    let
      val (prefix,overhead) = original_fixture invocation generous
        (fn owner => original_step owner (fn () =>
          let val start = original_charged owner
              val _ = original_remaining owner
          in (start,original_charged owner-start) end))
      fun check (allowance,paid_prefix) =
        original_fixture invocation (prefix+overhead+allowance) (fn owner =>
          let
            val base = R.empty_int () : int R.int_map
            val no = limit (fn () => original_step owner (fn () =>
              (require "original failure fixture changed its prefix"
                 (original_charged owner=prefix);
               (ignore (original_lookup owner (base,0)) handle R.Limit =>
                 (require "original planner did not retire before Limit"
                    (#retired (original_audit owner));
                  raise R.Limit)))))
            val before_retry = original_charged owner
            val _ = require "original failure hid Limit or paid later guards"
              (no andalso before_retry=prefix+overhead+paid_prefix)
            val called = ref false
            val refused = hol_error (fn () => original_step owner
              (fn () => called := true))
          in require "failed original planner was reusable or retry charged"
            (refused andalso not (!called) andalso
             #retired (original_audit owner) andalso
             original_charged owner=before_retry) end)
    in List.app check [(1,0),(24,17)] end

  fun run () =
    (test "Task50 R standalone/meter exact under/over" table_boundaries;
     test "Task50 R retains lookup and byte prefixes" rejected_prefixes;
     test "Task50 R finish reservations and stale one-shots" reservations;
     test "Task50 W cumulative operations in all modes"
       (fn () => List.app cumulative modes);
     test "Task50 W first R.Limit preserves failed cumulative prefix"
       (fn () => List.app budget_prefix bounded_modes);
     test "Task50 W h+1 first error is R.Limit with zero R prefix"
       (fn () => List.app first_error [PricedInt,PricedFinite]);
     test "Task50 legacy planners match original three-guard pay sequence"
       (fn () => List.app legacy_compatibility bounded_modes);
     test "Task50 original A/W planners preserve success payer sequence"
       (fn () => List.app original_success [false,true]);
     test "Task50 original A/W first Limit preserves prefix and retires"
       (fn () => List.app original_failure [false,true]);
     test "Task50 W cumulative action exact under/over"
       (fn () => List.app action_boundary bounded_modes);
     test "Task50 W placeholder cost/delta and mint"
       (fn () => List.app naming modes);
     test "Task50 G standalone/meter exact diagnostics across boundaries"
       naming_diagnostics;
     test "Task50 W rejected naming keeps G diagnostic and paid prefix"
       (fn () => List.app naming_rejection bounded_modes);
     test "Task50 W planning failure retires even Uncapped"
       (fn () => List.app semantic_failure modes))
end
