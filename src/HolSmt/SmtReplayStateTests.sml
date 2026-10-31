(* Completed receipts retain immutable proof inputs, not optional syntax
   caches. Weak keys observe reclamation only; they never supply proof data.
   As in CPC_ProofParser's weak command-spine adapter, Poly/ML's ref-only
   Weak interface requires a representation cast. Never dereference it. *)
structure SmtReplayStateTests =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure Scope = SmtReplayOwnedScopeReceipt

  fun require text yes = if yes then () else raise Fail text
  fun weak term = Weak.weak (SOME (RunCall.unsafeCast term : unit ref))
  fun alive keys = List.length (List.filter (fn key =>
    Option.isSome (!key)) keys)
  fun live phase =
    let val _ = PolyML.fullGC ()
        val stats = PolyML.Statistics.getLocalStats ()
        val bytes = #sizeHeap stats - #sizeHeapFreeLastFullGC stats
    in print ("TASK51_LIVE phase=" ^ phase ^ " bytes=" ^
         LargeInt.toString bytes ^ "\n"); bytes end

  (* The cache owns fresh equality syntax from discarded successful
     alternatives. None is reachable from the final Source proof. *)
  fun populate w b node count =
    let fun loop 0 keys = keys
          | loop n keys =
              let val key = W.with_step w (fn () =>
                    let val edge = P.execute_primitive w
                          (P.prepare_primitive w b
                            (P.ReflexiveName node) [])
                    in weak (Thm.concl (P.theorem b edge)) end)
              in loop (n-1) (key::keys) end
    in loop count [] end

  fun retained count diagnostic =
    let
      val g = G.new () val r = G.root_scope g
      val p = Term.mk_var ("state_retained_source",Type.bool)
      val s = S.new g r 8192 {assumptions=[p,p],goal=p}
      val w = W.begin g r s
        {limits={input_limit=8192,output_limit=8192,template_limit=8192},
         work_limit=1000000000}
      fun run () =
        let
          val frame = Scope.root w
          val node = hd (S.assumption_nodes s)
          val b = P.prepare_needed_sources_with_work w
            {frame=frame,roots=[node],additional_sources=[],
             closed_facts=[],conversions=[]}
          val base = if diagnostic then live "empty" else 0
          val keys = populate w b node count
          val edge = W.with_step w (fn () => P.source b 0)
          val law_key = W.with_step w (fn () =>
            weak (Thm.concl (P.assemble b edge)))
          val _ = PolyML.fullGC ()
          val held = alive keys
          val _ = require "fixture did not retain discarded syntax/assembly"
            (held=count andalso alive [law_key]=1)
          val ready = if diagnostic then live "alternatives" else 0
          val receipt = P.realize_source_owned_receipt w b node edge
          val _ = PolyML.fullGC ()
          val remaining = alive keys
          val done = if diagnostic then live "completed" else 0
          val proof = P.source_realization_theorem_for w receipt
          val _ = require "retained receipt lost exact endpoint/Hyp/tags"
            (Portable.pointer_eq (Thm.concl proof,G.representative g node)
             andalso length (Thm.hyp proof)=1 andalso
             Portable.pointer_eq (hd (Thm.hyp proof),G.representative g node)
             andalso null (Tag.axioms_of (Thm.tag proof)) andalso
             null (#1 (Tag.dest_tag (Thm.tag proof))))
          val repeated = ((ignore (P.realize_source_owned_receipt w b node
            edge); false) handle Feedback.HOL_ERR _ => true)
          val _ = require "completed block allowed repeated realization"
            repeated
          val _ = if diagnostic then print
            ("TASK51_STATE count=" ^ Int.toString count ^
             " held=" ^ Int.toString held ^ " remaining=" ^
             Int.toString remaining ^ " base=" ^ LargeInt.toString base ^
             " ready=" ^ LargeInt.toString ready ^ " done=" ^
             LargeInt.toString done ^ "\n") else ()
          val _ = if diagnostic then () else require
            "completed receipt retained optional assembly"
            (alive [law_key]=0)
        in remaining end
      val outcome = Exn.capture run ()
      val _ = W.close w val _ = G.close_scope g r
    in Exn.release outcome end

  structure RP = SmtReplayResourcePolicy
  structure NC = SmtReplayNativeContract
  val policy:RP.semantic_policy =
    {input_limit=RP.Uncapped,output_limit=RP.Uncapped,
     template_limit=RP.Uncapped}

  (* Keep old blocks and receipts live through each check. Only weak keys
     to fresh physical syntax escape populate; the canonical source map
     and immutable projection backing must survive every transfer. *)
  fun policy_retained mode =
    let
      val g=G.new () val r=G.root_scope g
      val p=Term.mk_var ("state_policy_source",Type.bool)
      val q= #node (G.import_with_policy g r RP.Uncapped
        (Term.mk_var ("state_policy_local",Type.bool)))
      val s=S.new_with_policy g r RP.Uncapped
        {goal=boolSyntax.T,assumptions=[p,p]}
      val w=W.begin_with_policy g r s
        {limits=policy,work_limit=RP.AtMost 1000000000}
      fun run () =
        let
          val frame=Scope.root_with_policy w
          val contract=NC.capture w
            {semantic_limits={input_limit=8192,output_limit=8192,
               template_limit=8192},import_limit=1000000,
             type_work_limit=4000000}
          val node=hd (S.assumption_nodes s)
          val prefix=S.assumption_nodes s @ [S.denied_goal_node s]
          fun step f=W.with_step w f
          fun block extras ordinal =
            let val front=
                  P.prepare_scoped_original_realization_frontier_with_policy w
                    {frame=frame,roots=[node],additional_sources=extras,
                     closed_facts=[],conversions=[]}
            in step (fn () =>
              let val tables=P.prepare_owned_realization_tables_with_policy
                    w front
                  val plan=P.prepare_native_realization_freeze_with_policy w
                    {tables=tables,contract=contract,profiles=[],
                     ordinal=ordinal,check_type=fn _ => ()}
              in P.freeze_owned_realization_tables_with_policy w plan end)
            end
          fun populate b =
            let val name=step (fn () => P.name b node)
                fun loop 0 keys=keys
                  | loop n keys=
                    let val key=step (fn () =>
                          let val term=boolSyntax.mk_eq (name,name)
                              val _=P.compact_profile_with_policy w b term
                          in weak term end)
                    in loop (n-1) (key::keys) end
            in loop 256 [] end
          fun source b index=step (fn () => P.source b index)
          fun exact target receipt =
            let val proof=P.policy_source_realization_theorem_for w receipt
                val allowed=List.map (G.representative g) prefix
            in require "policy receipt changed endpoint/Hyp/tags"
              (Portable.pointer_eq (Thm.concl proof,G.representative g target)
               andalso List.all (fn original => List.exists (fn hyp =>
                 Portable.pointer_eq (hyp,original)) (Thm.hyp proof)) allowed
               andalso List.all (fn hyp => List.exists (fn original =>
                 Portable.pointer_eq (hyp,original)) allowed) (Thm.hyp proof)
               andalso null (Tag.axioms_of (Thm.tag proof)) andalso
               List.all (fn tag => tag="DISK_THM")
                 (#1 (Tag.dest_tag (Thm.tag proof)))) end
          fun realize b target edge =
            let val receipt=step (fn () =>
                  P.execute_realization_with_policy w
                    (P.prepare_realization_with_policy w b target edge))
                val _=exact target receipt
            in receipt end
          val extras=if mode="discharge" orelse mode="join" orelse
              mode="alias" then [q,q] else []
          val old=block extras 0
          val keys=populate old
          val other=if mode="join" then SOME (block extras 1) else NONE
          val other_keys=case other of NONE => [] | SOME b => populate b
          val kept_blocks=old :: (case other of NONE => [] | SOME b => [b])
          val all_keys=keys @ other_keys
          val _=PolyML.fullGC ()
          val _=require "policy fixture lost active cached syntax"
            (alive all_keys=length all_keys)
          val receipt=case mode of
              "single" => SOME (node,realize old node (source old 0))
            | "batch" =>
                let val results=step (fn () =>
                      P.execute_realization_batch_with_policy w
                        (P.prepare_realization_batch_with_policy w old
                          [(node,P.source old 0),(node,P.source old 1)]))
                    val _=require "policy batch changed result cardinality"
                      (length results=2)
                    val _=List.app (exact node) results
                in SOME (node,hd results) end
            | "empty" =>
                (require "empty policy batch emitted a result"
                  (null (step (fn () =>
                    P.execute_realization_batch_with_policy w
                      (P.prepare_realization_batch_with_policy w old []))));
                 NONE)
            | "revoke" =>
                (step (fn () => P.retire_policy_block_for w old);NONE)
            | "discharge" =>
                let val result=P.discharge_sources_with_policy w old
                      {indices=[3,4],body=q,edge=source old 3,ordinal=2,
                       check_type=fn _ => ()}
                in SOME (#target result,realize (#block result)
                  (#target result) (#edge result)) end
            | _ =>
                let val right=case other of SOME b => b | NONE => old
                    val result=P.join_blocks_with_policy w
                      {left={block=old,body=q,edge=source old 3},
                       right={block=right,body=q,edge=source right 4},
                       ordinal=2,check_type=fn _ => ()}
                    val next= #block result
                    val _=require "policy join collapsed Source occurrences"
                      (step (fn () => P.sources next)=prefix @ [q,q,q,q])
                    (* Use both transported edges, including alias case. *)
                    val _=step (fn () => P.theorem next (#left result))
                    val tail=P.discharge_sources_with_policy w next
                      {indices=[3,4,5,6],body=q,edge= #right result,
                       ordinal=3,check_type=fn _ => ()}
                in SOME (#target tail,realize (#block tail)
                  (#target tail) (#edge tail)) end
          val _=PolyML.fullGC ()
          val remaining=alive all_keys
          val _=print ("TASK51_POLICY mode=" ^ mode ^ " held=" ^
            Int.toString (length all_keys) ^ " remaining=" ^
            Int.toString remaining ^ "\n")
          val _=require "retired policy block retained optional profile syntax"
            (remaining=0)
          val _=case receipt of NONE => () | SOME (target,saved) =>
            exact target saved
          (* Query only after GC so rejection cannot itself release keys.
             The first rejection closes Work; subsequent queries keep both
             old blocks strongly live, not independent lifetime controls. *)
          val _=List.app (fn b =>
            let val repeated=((ignore (step (fn () => P.name b node));false)
                  handle Feedback.HOL_ERR _ => true)
            in require "retired policy block remained active" repeated end)
            kept_blocks
        in () end
      val outcome=Exn.capture run ()
      val _=W.close w val _=G.close_scope g r
    in Exn.release outcome end

  fun run () =
    (testutils.tprint "Completed block releases discarded syntax caches";
     require "completed receipt retained optional syntax cache"
       (retained 256 false=0);
     testutils.OK ();
     List.app (fn mode =>
       (testutils.tprint ("Policy profile release: " ^ mode);
        policy_retained mode;testutils.OK ()))
       ["single","batch","empty","discharge","join","alias","revoke"])
end
