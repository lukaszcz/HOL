(* Local checked-producer controls, with no external solver. Also exercise
   the replay engine's real endpoint-retention hook. *)
structure CPC_AciProducerTests =
struct
  open HolKernel
  fun require message condition = if condition then () else raise Fail message
  fun clean theorem =
    require "ACI theorem has hypotheses or non-kernel tags"
      (null (Thm.hyp theorem) andalso
       null (Tag.axioms_of (Thm.tag theorem)) andalso
       List.all (fn name => name = "DISK_THM")
         (#1 (Tag.dest_tag (Thm.tag theorem))))
  fun product target = case CPC_AciProducer.produce target of
      SOME result => result
    | NONE => raise Fail "Boolean ACI producer declined a valid schema"
  fun check target =
    let val {theorem,...} = product target in
      require "wrong ACI conclusion" (Term.aconv target (Thm.concl theorem));
      clean theorem
    end
  fun reject target =
    require "false Boolean ACI equality accepted"
      (not (Option.isSome (CPC_AciProducer.produce target)))
  fun test label action =
    (testutils.tprint label;action ();testutils.OK ())
  val a = Term.mk_var ("aci_producer_a",Type.bool)
  val b = Term.mk_var ("aci_producer_b",Type.bool)
  val c = Term.mk_var ("aci_producer_c",Type.bool)
  fun laws operation identity absorbing =
    let
      fun eq l r = check (boolSyntax.mk_eq (l,r))
    in
      eq (operation (a,b)) (operation (b,a));
      eq (operation (operation (a,b),c)) (operation (a,operation (b,c)));
      eq (operation (a,a)) a;
      eq (operation (a,identity)) a;
      eq (operation (identity,a)) a;
      eq (operation (a,absorbing)) absorbing;
      eq (operation (absorbing,a)) absorbing;
      eq (operation (operation (a,b),a)) (operation (a,b));
      eq (operation (operation (a,b),operation (c,a)))
         (operation (c,operation (b,a)))
    end
  fun run_with retain =
    let
      (* Physically larger than 8192; same-operator leaves are essential.
         A producer that always flattens first will reject this fixture. *)
      fun tree 0 index = Term.mk_var
            ("aci_opaque_" ^ Int.toString index,Type.bool)
        | tree depth index = boolSyntax.mk_disj
            (tree (depth-1) (2*index),tree (depth-1) (2*index+1))
      val opaque = tree 12 0
      val shell = boolSyntax.mk_disj (opaque,boolSyntax.F)
      val target = boolSyntax.mk_eq (shell,opaque)
      fun callback_failure first =
        let
          val calls = ref 0
          fun instantiate substitution theorem =
            (calls := !calls + 1;
             if !calls = 1 then raise first
             else Thm.INST substitution theorem)
          val result = Exn.capture
            (CPC_AciProducer.produce_with instantiate) target
          val _ = require "ACI callback was not called exactly once"
            (!calls = 1)
        in
          case result of
            Exn.Exn actual =>
              (* Poly/ML may attach a fresh raise-location wrapper. Check
                 the constructor and exact first payload, not its pointer. *)
              require "ACI callback's first exception was replaced"
                (case (actual,first) of
                   (Feedback.HOL_ERR got,Feedback.HOL_ERR expected) =>
                     got = expected
                 | (Fail got,Fail expected) => got = expected
                 | (CPC_AciProducer.Declined,CPC_AciProducer.Declined) =>
                     true
                 | _ => false)
          | Exn.Res _ => raise Fail "ACI callback exception was swallowed"
        end
    in
      test "CPC schematic conjunction ACI laws" (fn () =>
        laws boolSyntax.mk_conj boolSyntax.T boolSyntax.F);
      test "CPC schematic disjunction ACI laws" (fn () =>
        laws boolSyntax.mk_disj boolSyntax.F boolSyntax.T);
      test "CPC ACI rejects changed/removed leaves and false constants"
        (fn () => List.app reject
          [boolSyntax.mk_eq (boolSyntax.mk_disj (a,b),a),
           boolSyntax.mk_eq (boolSyntax.mk_conj (a,b),a),
           boolSyntax.mk_eq (boolSyntax.mk_disj (a,b),
                             boolSyntax.mk_disj (a,c)),
           boolSyntax.mk_eq (boolSyntax.F,boolSyntax.T)]);
      test "CPC ACI admits only its small schema, never its opaque operand"
        (fn () =>
          let
            val quota = SmtResource.max_skeleton_replay_dag_nodes
            val _ = require "fixture no longer exceeds physical allowance"
              (SmtResource.dag_nodes_up_to quota opaque > quota)
            val calls = ref 0
            fun instantiate substitution theorem =
              (calls := !calls + 1;
               require "INST input exceeded native template bound"
                 (Option.isSome (SmtReplayImport.bounded_raw_size quota
                   (Thm.concl theorem)));
               Thm.INST substitution theorem)
            val {template,operands,theorem} =
              case CPC_AciProducer.produce_with instantiate target of
                SOME result => result
              | NONE => raise Fail "large opaque shell was flattened"
            val _ = require "expected one simultaneous INST" (!calls = 1)
            val _ = require "expected one opaque operand"
              (length operands = 1 andalso
               Portable.pointer_eq (#2 (hd operands),opaque))
            val _ = require "INST descended into/replaced the opaque leaf"
              (Portable.pointer_eq
                (boolSyntax.rhs (Thm.concl theorem),opaque))
            val retained = retain template operands target theorem
            val _ = clean retained
          in require "retention lost the exact parsed target"
            (Portable.pointer_eq (Thm.concl retained,target)) end);
      test "CPC ACI preserves the first ordinary HOL_ERR callback failure"
        (fn () => callback_failure
          (Feedback.mk_HOL_ERR "CPC_AciProducerTests" "instantiate"
            "first callback failure"));
      test "CPC ACI preserves the first non-HOL callback failure"
        (fn () => callback_failure (Fail "first callback failure"));
      test "CPC ACI does not retry a callback's Declined exception"
        (fn () => callback_failure CPC_AciProducer.Declined);
      test "CPC ACI retains the original full-template physical allowance"
        (fn () =>
          case Exn.capture
              (fn () => CPC_AciProducer.schema false NONE shell opaque) () of
            Exn.Exn CPC_AciProducer.Declined => ()
          | _ => raise Fail "oversized full schema was admitted");
      test "CPC ACI does not pass an exponential shared schema to INST"
        (fn () =>
          let
            fun shared 0 = a
              | shared n = let val child = shared (n-1)
                           in boolSyntax.mk_disj (child,child) end
            val graph = shared 14
            val quota = SmtResource.max_skeleton_replay_dag_nodes
            val _ = require "shared fixture is not physically compact"
              (SmtResource.dag_nodes_up_to quota graph <= quota)
          in
            case Exn.capture
                (fn () => CPC_AciProducer.schema false NONE graph a) () of
              Exn.Exn CPC_AciProducer.Declined => ()
            | _ => raise Fail "unbounded native schema was admitted"
          end)
    end

  fun run () = run_with
    CPC_ProofReplay.retain_producer_conclusion_for_test
end
