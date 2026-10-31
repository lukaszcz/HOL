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

  fun run () =
    (testutils.tprint "Completed block releases discarded syntax caches";
     require "completed receipt retained optional syntax cache"
       (retained 256 false=0);
     testutils.OK ())
end
