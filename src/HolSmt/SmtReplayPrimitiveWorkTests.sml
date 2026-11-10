(* Prepared policy executions must fund their complete callback-free
   native extent, including the enclosing Work action's return guard.
   No top-level tests: the selftest runner calls run().

   The fixture and balance adjustment follow selftest group 278. External
   callback order, Primary and caught reentry are covered by groups 35/49;
   these five prepared execution suffixes have no external callback. *)
structure SmtReplayPrimitiveWorkTests =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure NC = SmtReplayNativeContract
  structure RP = SmtReplayResourcePolicy
  structure O = SmtReplayRuleObservation

  fun require text yes = if yes then () else raise Fail text
  fun test label action =
    (testutils.tprint label; action (); testutils.OK ())
  fun charged w = #charged (W.audit_policy w)
  val metadata : RP.semantic_policy =
    {input_limit=RP.Uncapped,output_limit=RP.Uncapped,
     template_limit=RP.Uncapped}
  val allowance : IntInf.int = 100000000

  (* Run BOTH cleanups even when the test, setup, or first cleanup raises;
     never mask the original exception with a cleanup failure. *)
  fun fixture priced action =
    let
      val g = G.new ()
      val r = G.root_scope g
      val held = ref (NONE : W.portfolio option)
      val outcome = Exn.capture (fn () =>
        let
          val s = S.new_with_policy g r RP.Uncapped
            {goal=boolSyntax.T,assumptions=[]}
          val w = (if priced then W.begin_with_scope_guard_policy
                   else W.begin_with_policy) g r s
            {limits=metadata,work_limit=RP.AtMost allowance}
          val _ = held := SOME w
          val n = NC.capture w
            {semantic_limits={input_limit=1,output_limit=1,
               template_limit=8192},
             import_limit=1000000,type_work_limit=4000000}
        in action (g,r,w,n) end) ()
      val work_cleanup = Exn.capture (fn () =>
        case !held of NONE => () | SOME w => W.close w) ()
      val scope_cleanup = Exn.capture (fn () => G.close_scope g r) ()
    in case outcome of
         Exn.Exn primary => raise primary
       | Exn.Res value =>
           (Exn.release work_cleanup; Exn.release scope_cleanup; value)
    end

  fun fact g r proof =
    let
      val s = G.import_with_policy g r RP.Uncapped (Thm.concl proof)
      val v = G.record_opened_view_with_policy g r RP.Uncapped (#node s)
    in P.record_closed_from_import_with_policy g r
      {node= #node v,theorem=proof,template_limit=RP.Uncapped,
       check_type=fn _ => ()}
    end

  fun block w n roots facts =
    let
      val f = P.prepare_original_realization_frontier_with_policy w
        {roots=roots,closed_facts=facts,conversions=[]}
      val t = W.with_step w (fn () =>
        P.prepare_owned_realization_tables_with_policy w f)
      val p = W.with_step w (fn () =>
        P.prepare_native_realization_freeze_with_policy w
          {tables=t,contract=n,profiles=[],ordinal=0,check_type=fn _ => ()})
    in W.with_step w (fn () =>
      P.freeze_owned_realization_tables_with_policy w p)
    end

  datatype instruction = ReflexiveName | ApplyNamedArgument
                       | Symmetry | ClosedInst | Conjunction

  (* Preparing and executing are DISTINCT Work actions. All expected
     theorem construction and operand queries precede the native meter. *)
  fun prepare w b t opnode law instruction =
    W.with_step w (fn () => case instruction of
        ReflexiveName =>
          let
            val expected = Thm.REFL (P.name b t)
            val saved = P.prepare_primitive_with_policy w b
              (P.ReflexiveName t) []
          in (fn () => P.execute_primitive_with_policy w saved,expected) end
      | ApplyNamedArgument =>
          let
            val refl = P.execute_primitive_with_policy w
              (P.prepare_primitive_with_policy w b
                (P.ReflexiveName opnode) [])
            val expected = Thm.AP_THM (P.theorem b refl) (P.name b t)
            val saved = P.prepare_primitive_with_policy w b
              (P.ApplyNamedArgument t) [refl]
          in (fn () => P.execute_primitive_with_policy w saved,expected) end
      | Symmetry =>
          let
            val refl = P.execute_primitive_with_policy w
              (P.prepare_primitive_with_policy w b (P.ReflexiveName t) [])
            val expected = Thm.SYM (P.theorem b refl)
            val saved = P.prepare_primitive_with_policy w b P.Symmetry
              [refl]
          in (fn () => P.execute_primitive_with_policy w saved,expected) end
      | ClosedInst =>
          let
            val hole = Term.mk_var ("policy_work_schema_hole",Type.bool)
            val schema = Thm.REFL hole
            val substitution = [{redex=hole,residue=P.name b t}]
            val expected = Thm.INST substitution schema
            val saved = P.prepare_closed_named_inst_with_policy w b
              {substitution=substitution,theorem=schema}
          in (fn () => P.execute_closed_named_inst_with_policy w saved,
              expected) end
      | Conjunction =>
          let
            val edge = P.closed b law
            val proof = P.theorem b edge
            val expected = Thm.CONJ proof proof
            val saved = P.prepare_boolean_primitive_with_policy w b
              P.PolicyConjunction [edge,edge]
          in (fn () => P.execute_boolean_primitive_with_policy w saved,
              expected) end)

  fun same_theorem actual expected =
    let
      fun exact (a,b) = Term.compare (a,b) = EQUAL
      val a = Thm.tag actual
      val b = Thm.tag expected
    in exact (Thm.concl actual,Thm.concl expected) andalso
       ListPair.allEq exact (Thm.hyp actual,Thm.hyp expected) andalso
       Tag.dest_tag a = Tag.dest_tag b andalso
       Tag.axioms_of a = Tag.axioms_of b andalso
       Tag.dep_of a = Tag.dep_of b
    end

  fun probe priced instruction leave = fixture priced (fn (g,r,w,n) =>
    let
      val law = fact g r boolTheory.TRUTH
      val t = P.closed_node law
      val opnode = #node (G.import_with_policy g r RP.Uncapped
        boolSyntax.negation)
      val b = block w n [t,opnode] [law]
      val (execute,expected) = prepare w b t opnode law instruction
      val start = ref (charged w)
      fun action () =
        let
          val _ = case leave of NONE => () | SOME balance =>
            let
              val initial = charged w
              val _ = W.spend_policy w 0
              val overhead = charged w - initial
            in case W.remaining_policy w of
                 RP.AtMost left =>
                   W.spend_policy w (left-balance-overhead)
               | _ => raise Fail "lost finite Work"
            end
          (* audit is DATA, so checking the balance cannot itself spend. *)
          val _ = case leave of NONE => () | SOME balance =>
            require "balance adjustment did not leave the requested Work"
              (allowance-charged w=balance)
          val _ = start := charged w
        in execute () end
      val prior = Count.thm_count ()
      val (outcome,statistics) = O.with_statistics (fn () =>
        Exn.capture (fn () => W.with_step w action) ())
      (* Includes the action's real return, but NOT a later theorem query. *)
      val cost = charged w - !start
      val after_count = Count.thm_count ()
      val success = case outcome of
          Exn.Res edge =>
            let
              val rule_count = case instruction of
                  ReflexiveName => #REFL after_count - #REFL prior
                | ApplyNamedArgument => #AP_THM after_count - #AP_THM prior
                | Symmetry => #SYM after_count - #SYM prior
                | ClosedInst => #INST after_count - #INST prior
                | Conjunction => #CONJ after_count - #CONJ prior
              val _ = require "funded execution omitted its native rule"
                (rule_count=1 andalso #total after_count - #total prior=1
                 andalso #selected_returns statistics=1 andalso
                 not (#retired (W.audit_policy w)))
              (* A policy theorem query has its OWN paid owner guards.
                 Check exact Goal/Hyp/full Tag on the ample baseline only:
                 querying at the execution cutoff would wrongly enlarge
                 the tested extent, after a native effect had occurred. *)
              val _ = case leave of SOME _ => () | NONE =>
                let val proof = W.with_step w (fn () => P.theorem b edge)
                in require "execution changed exact Goal/Hyp/full Tag"
                  (same_theorem proof expected) end
            in true end
        | Exn.Exn (Feedback.HOL_ERR detail) =>
            (require "Work refusal followed a native effect or lost owner"
               (Feedback.message_of detail =
                  "original cumulative work allowance exhausted" andalso
                #selected_returns statistics=0 andalso
                after_count=prior andalso #retired (W.audit_policy w));
             false)
        | Exn.Exn ReplayRedblackPrivateWork.Limit =>
            (require "name lookup refusal followed a native effect"
               (#selected_returns statistics=0 andalso after_count=prior
                andalso #retired (W.audit_policy w)); false)
        | Exn.Exn primary => raise primary
    in (cost,success) end)

  fun check priced instruction =
    let
      val (cost,success) = probe priced instruction NONE
      val _ = require "ample baseline failed or had negative execution charge"
        (success andalso cost>=0)
      fun verify balance =
        let val (paid,succeeded) = probe priced instruction (SOME balance)
        in require "prepared execution changed its complete funded cutoff"
          (succeeded=(balance>=cost) andalso
           (not succeeded orelse paid=cost))
        end
      fun sweep balance = if balance>cost+1 then () else
        (verify balance; sweep (balance+1))
    in if priced then List.app verify [0,cost div 2,cost-1,cost,cost+1]
       else sweep 0
    end

  fun run () =
    let
      val outcome = Exn.capture (fn () =>
        (Count.counting_thms true;
         test "Prepared named REFL funds its complete native extent"
           (fn () => (check false ReflexiveName; check true ReflexiveName));
         test "Prepared named AP_THM funds its complete native extent"
           (fn () =>
             (check false ApplyNamedArgument; check true ApplyNamedArgument));
         test "Prepared policy symmetry funds its complete native extent"
           (fn () => (check false Symmetry; check true Symmetry));
         test "Prepared closed named INST funds its complete native extent"
           (fn () => (check false ClosedInst; check true ClosedInst));
         test "Prepared policy boolean funds its complete native extent"
           (fn () => (check false Conjunction; check true Conjunction)))) ()
      val _ = Count.counting_thms false
    in Exn.release outcome end
end
