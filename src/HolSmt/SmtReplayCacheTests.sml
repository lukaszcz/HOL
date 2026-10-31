(* Replay cache ownership and optional-reuse regressions. *)
open HolKernel Parse boolLib bossLib

structure Task49ContextTests =
struct
  structure S = SmtSkeletonProve
  structure W = SmtWordGraph
  structure G = SmtReplayGraph
  fun check true _ = () | check false message = raise Fail message
  val x = Term.mk_var ("task49_context_x", numSyntax.num)
  val atom = boolSyntax.mk_eq (x,x)
  val target = boolSyntax.mk_disj (atom,boolSyntax.mk_neg atom)
  val expansion = S.Expanded (Drule.EQT_INTRO (Thm.REFL x))
  val no_owners = Redblackmap.mkDict Term.compare
  fun owners name = Redblackmap.insert (no_owners,atom,name)
  fun prove context ownership = S.prove_with_owners context ownership
    (SmtResource.term_measure target) target
  fun checked theorem expected =
    (check (Term.aconv (Thm.concl theorem) expected) "wrong conclusion";
     check (null (Thm.hyp theorem)) "unexpected hypotheses";
     Library.check_oracle_tags "Task49ContextTests" "result" theorem)

  fun owner_keys () =
    let
      val a = ref 0 and b = ref 0 and c = ref 0 and fallback = ref 0
      fun expanded calls _ = (calls := !calls+1; expansion)
      fun unable calls _ = (calls := !calls+1; S.Unable)
      val context = S.new_dynamic_context
        [{name="A",expand=expanded a}, {name="B",expand=expanded b},
         {name="C",expand=unable c}]
        {name="A",expand=unable fallback}
      fun run name =
        let val result = prove context (owners name)
        in checked (#theorem result) target; #metrics result end
      val first = run "A"
      val again = run "A"
      val other = run "B"
      val other_again = run "B"
      val declined =
        (ignore (run "C"); false) handle S.PROCEDURE_UNABLE => true
      val unowned = prove context no_owners
    in
      check (!a=1 andalso !b=1 andalso !c=1 andalso declined)
        "an owner change reused another procedure's expansion";
      check (#atom_proofs first=1 andalso #atom_cache_hits again>0 andalso
        #atom_proofs other=1 andalso #atom_cache_hits other_again>0)
        "same-owner reuse or different-owner miss is wrong";
      check (!fallback>0 andalso #atom_cache_hits (#metrics unowned)=0)
        "fallback collided with an identically named explicit owner";
      checked (#theorem unowned) target
    end

  fun optional_miss () =
    let
      val calls = ref 0
      val S.Context {procedures,fallback,atom_cache,cache_generation,
                     refresh_caches,...} =
        S.new_context [{name="miss",expand=fn _ =>
          (calls := !calls+1; expansion)}]
      val context = S.Context {procedures=procedures,fallback=fallback,
        atom_cache=atom_cache,cache_generation=cache_generation,
        refresh_caches=refresh_caches,atom_index=fn _ => NONE}
      val first = prove context (owners "miss")
      val second = prove context (owners "miss")
    in
      check (!calls = #atom_requests (#metrics first) +
          #atom_requests (#metrics second) andalso
        S.cache_size context=0 andalso
        #atom_cache_hits (#metrics first)=0 andalso
        #atom_cache_hits (#metrics second)=0) "optional miss refused/reused";
      checked (#theorem first) target;
      checked (#theorem second) target
    end

  val word_target =
    ``(task49_context_word:word8) + 0w = task49_context_word``

  fun with_symbol is_type action =
    let
      val name = if is_type then "task49_context_type"
                 else "task49_context_const"
      fun allocate () = if is_type then Theory.new_type (name,0)
                        else Theory.new_constant (name,Type.bool)
      fun retire () = if is_type then Theory.delete_type name
                      else Theory.delete_const name
      fun cleanup () = retire () handle _ => ()
    in
      (action allocate retire handle exn => (cleanup (); raise exn))
      before cleanup ()
    end

  (* Allocation and unrelated deletion only discard optional hints. Both
     retained contexts and fresh graph inputs must continue to work. *)
  fun retained is_type = with_symbol is_type (fn allocate => fn retire =>
    let
      val calls = ref 0
      val context = S.new_context [{name="keep",expand=fn _ =>
        (calls := !calls+1; expansion)}]
      val sat = S.new_sat_context ()
      val sat_calls = ref 0
      fun sat_proof () = S.cached_sat_proof sat boolSyntax.T 1
        (fn () => (sat_calls := !sat_calls+1; boolTheory.TRUTH))
      val word = W.new_context ()
      fun request () =
        (checked (#theorem (prove context (owners "keep"))) target;
         checked (sat_proof ()) boolSyntax.T;
         checked (W.prove_in word word_target) word_target)
      val _ = request ()
      val _ = request ()
      val _ = check (!calls=1 andalso !sat_calls=1) "initial cache miss"
      val _ = allocate ()
      val _ = request ()
      val _ = check (!calls=2 andalso !sat_calls=2)
        "allocation failed to refresh optional hints"
      val _ = retire ()
      val _ = request ()
      val _ = request ()
      val graph = G.new ()
      val scope = G.root_scope graph
      val source = #node (G.import graph scope 8192 word_target)
      val (plan,_) = W.graph_normalize_in word graph scope source
    in
      check (!calls=3 andalso !sat_calls=3)
        "unrelated retirement refused or failed to refresh/reuse";
      checked (S.propositional_prove_in sat boolSyntax.T) boolSyntax.T;
      checked (S.congruence_prove_in sat (boolSyntax.mk_eq (x,x)))
        (boolSyntax.mk_eq (x,x));
      checked (W.prove_discovered_in word graph scope plan) word_target;
      (* A live context is not authority to use a plan with a foreign owner. *)
      check ((ignore (W.prove_discovered_in word (G.new ()) scope plan);
        false) handle Feedback.HOL_ERR _ => true)
        "foreign graph owner accepted"
    end)

  (* Restore can change signatures without changing retirement clocks. *)
  fun restored is_type = with_symbol is_type (fn allocate => fn _ =>
    let
      val saved = Context.snapshot ()
      fun run () =
        let
          val _ = allocate ()
          val calls = ref 0
          val context = S.new_context [{name="restore",expand=fn _ =>
            (calls := !calls+1; expansion)}]
          val sat = S.new_sat_context ()
          val sat_calls = ref 0
          fun sat_proof () = S.cached_sat_proof sat boolSyntax.T 1
            (fn () => (sat_calls := !sat_calls+1; boolTheory.TRUTH))
          val word = W.new_context ()
          val _ = ignore (prove context (owners "restore"))
          val _ = ignore (sat_proof ())
          val _ = checked (W.prove_in word word_target) word_target
          val types = Type.type_epoch () and symbols = Term.term_epoch ()
          val _ = Context.restore saved
          val _ = check (types=Type.type_epoch () andalso
            symbols=Term.term_epoch ()) "restore advanced retirement clocks"
          val _ = check (S.cache_size context=0)
            "restore retained atom IDs from a different signature"
          val _ = #refresh_caches sat ()
          val _ = check (null (!(#proofs sat)) andalso !(#nodes sat)=0)
            "restore retained SAT hints"
          val _ = checked (#theorem (prove context (owners "restore"))) target
          val _ = checked (sat_proof ()) boolSyntax.T
          val _ = checked (W.prove_in word word_target) word_target
        in check (!calls=2 andalso !sat_calls=2)
          "restore poisoned a valid context or reused its old hints" end
    in Portable.finally (fn () => Context.restore saved) run () end)

  (* No captured pre-callback ID is published. The valid checked result is
     still returned, and a later request can populate the refreshed cache. *)
  fun publication is_type =
    (with_symbol is_type (fn allocate => fn retire =>
      let
        val _ = allocate ()
        val first = ref true
        val calls = ref 0
        val context = S.new_context [{name="retire",expand=fn _ =>
          (calls := !calls+1;
           if !first then (first := false; retire ()) else (); expansion)}]
        val _ = checked (#theorem (prove context (owners "retire"))) target
        val _ = check (S.cache_size context=0)
          "callback retirement published an old atom ID"
        val initial_calls = !calls
        val _ = checked (#theorem (prove context (owners "retire"))) target
        val _ = checked (#theorem (prove context (owners "retire"))) target
      in check (!calls=initial_calls+1 andalso S.cache_size context=1)
        "refreshed atom cache cannot be populated/reused" end);
     with_symbol is_type (fn allocate => fn retire =>
      let
        val _ = allocate ()
        val sat = S.new_sat_context ()
        val _ = checked (S.cached_sat_proof sat boolSyntax.T 1
          (fn () => (retire (); boolTheory.TRUTH))) boolSyntax.T
        val _ = check (null (!(#proofs sat)) andalso !(#nodes sat)=0)
          "callback retirement published a SAT proof"
        val _ = checked (S.cached_sat_proof sat boolSyntax.T 1
          (fn () => boolTheory.TRUTH)) boolSyntax.T
      in check (length (!(#proofs sat))=1) "SAT cache stayed poisoned" end);
     with_symbol is_type (fn allocate => fn retire =>
      let
        val _ = allocate ()
        val calls = ref 0
        fun callback term =
          (calls := !calls+1;
           if !calls=1 then retire () else ();
           if boolSyntax.is_eq term andalso
               wordsSyntax.is_word_type (Term.type_of (boolSyntax.lhs term))
           then blastLib.WORD_SIMP_CONV term else raise Conv.UNCHANGED)
        val theorem = W.normalize_with_node_conversion callback word_target
      in
        check (!calls>0) "word callback did not run";
        check (Term.aconv (boolSyntax.lhs (Thm.concl theorem)) word_target)
          "word callback lost its valid endpoint";
        Library.check_oracle_tags "Task49ContextTests" "callback" theorem
      end))

  fun shared_callback () = with_symbol false (fn allocate => fn retire =>
    let
      val _ = allocate ()
      fun shared 0 term = term
        | shared n term = shared (n-1) (boolSyntax.mk_conj (term,term))
      val input = shared 22 word_target
      val calls = ref 0
      fun callback _ =
        (calls := !calls+1;
         if !calls=1 then retire () else ();
         raise Conv.UNCHANGED)
      val (theorem,metrics) =
        W.normalize_with_node_conversion_and_metrics callback input
    in
      check (#visited_nodes metrics<200 andalso !calls<200)
        "signature refresh disabled shared-DAG memoization";
      check (Portable.pointer_eq
        (boolSyntax.lhs (Thm.concl theorem),input)) "lost shared endpoint";
      Library.check_oracle_tags "Task49ContextTests" "shared" theorem
    end)

  (* A->B->A restores the same signature but not a reset index's IDs. *)
  fun reset_restore () =
    let
      val saved = Context.snapshot ()
      val first = ref true
      val context_ref = ref NONE
      fun expand _ =
        (if !first then
           (first := false;
            Theory.new_constant ("task49_reset", Type.bool);
            ignore (S.cache_size (Option.valOf (!context_ref)));
            Context.restore saved)
         else ();
         expansion)
      val context = S.new_context [{name="reset",expand=expand}]
      val _ = context_ref := SOME context
      fun run () =
        (checked (#theorem (prove context (owners "reset"))) target;
         check (S.cache_size context=0) "reset generation published old IDs";
         checked (#theorem (prove context (owners "reset"))) target;
         checked (#theorem (prove context (owners "reset"))) target)
    in Portable.finally (fn () => Context.restore saved) run () end

  fun retired_publication () = with_symbol false (fn allocate => fn retire =>
    let
      val _ = allocate ()
      val old = Term.mk_const ("task49_context_const",Type.bool)
      val value = Term.mk_comb
        (Term.mk_var ("task49_stale_value", Type.--> (Type.bool,numSyntax.num)),
         old)
      val stale_atom = boolSyntax.mk_eq (value,value)
      val stale_target = boolSyntax.mk_disj
        (stale_atom,boolSyntax.mk_neg stale_atom)
      val calls = ref 0
      val context = S.new_context [{name="stale",expand=fn _ =>
        (calls := !calls+1; S.Expanded (Drule.EQT_INTRO (Thm.REFL value)))}]
      val ownership = Redblackmap.insert (no_owners,stale_atom,"stale")
      val _ = retire ()
      fun run () = checked (#theorem (S.prove_with_owners context ownership
        (SmtResource.term_measure stale_target) stale_target)) stale_target
      val _ = run ()
      val before_calls = !calls
      val _ = run ()
    in check (!calls>before_calls andalso S.cache_size context=0)
      "retired endpoint acquired a reusable expansion" end)

  fun attempt_reset_restore () =
    let
      val saved = Context.snapshot ()
      val memo = SmtReplayAttempt.new
        {enabled=true,capacity=8,hash=fn _ => 0}
      val p = Term.mk_var ("task49_aba_p",Type.bool)
      val q = Term.mk_var ("task49_aba_q",Type.bool)
      val calls = ref 0
      fun identity term () =
        (calls := !calls+1; Thm.DISCH term (Thm.ASSUME term))
      fun run term worker = #run memo
        {procedure="reset",source=term,target=term,prove=worker}
      fun worker () =
        (Theory.new_constant ("task49_attempt_reset",Type.bool);
         ignore (#statistics memo ());
         Context.restore saved;
         identity p ())
      fun test () =
        (checked (run p worker) (boolSyntax.mk_imp (p,p));
         check (#retained (#statistics memo ())=0)
           "restored tables accepted old index generation";
         checked (run q (identity q)) (boolSyntax.mk_imp (q,q));
         checked (run p (identity p)) (boolSyntax.mk_imp (p,p));
         check (!calls=3) "reset collision did not use full checked worker")
    in Portable.finally (fn () => Context.restore saved) test () end

  fun run () =
    (owner_keys (); optional_miss (); reset_restore ();
     retired_publication (); attempt_reset_restore ();
     List.app retained [false,true];
     List.app restored [false,true];
     List.app publication [false,true]; shared_callback ())
end


structure SmtReplayCacheTests =
struct
  fun context () = SmtResource.with_e0_invocation_for_test
    (fn () => Task49ContextTests.run ()) ()

  fun solvers () =
  let
  fun assert (true, _) = ()
    | assert (false, message) = raise Fail ("Task49: " ^ message)
  fun tag (Fail message) = "fail:" ^ message
    | tag (Timeout.TIMEOUT _) = "timeout"
    | tag Interrupt = "interrupt"
    | tag exn = General.exnName exn
  fun propagated expected action =
    case Exn.capture action () of
      Exn.Res _ => false
    | Exn.Exn actual => tag actual = tag expected
  val disabled = Library.no_fastpath ()
  val p = Term.mk_var ("task49_p", Type.bool)
  val q = Term.mk_var ("task49_q", Type.bool)
  val first = boolSyntax.mk_eq (p, p)
  val second = boolSyntax.mk_eq (q, q)
  val boundary = CPC_ProofReplay.with_replay_memos_for_test
  val entries = CPC_ProofReplay.word_graph_tautology_entries_for_test
  val calls = ref 0
  fun worker _ target =
    (calls := !calls + 1; Thm.REFL (#1 (boolSyntax.dest_eq target)))
  fun prove target =
    CPC_ProofReplay.word_graph_tautology_using_for_test worker "task49" target
  fun checked target =
    let val theorem = prove target in
      assert (Term.aconv (Thm.concl theorem) target andalso
          HOLset.isEmpty (Thm.hypset theorem), "wrong cached theorem");
      Library.check_oracle_tags "Task49" "word graph" theorem
    end
  fun clean () = assert (entries () = 0, "CPC session retained entries")

  (* No owner: even repeated targets must use the complete worker. *)
  val _ = checked first
  val _ = checked first
  val _ = assert (!calls = 2, "CPC cached outside replay")
  val _ = clean ()
  val _ = calls := 0
  val _ = boundary 1 (fn () =>
    (checked first; checked first; checked second; checked second;
     checked first;
     assert (entries () = (if disabled then 0 else 1), "CPC cap"))) ()
  val _ = assert (!calls = (if disabled then 5 else 3),
    "CPC capacity refusal lost fallback or evicted an existing hit")
  val _ = clean ()

  (* A successful recursive miss publishes into the current owner. The
     outer worker must reread it, rather than overwrite an old snapshot. *)
  val _ = calls := 0
  val _ = boundary 8 (fn () =>
    let
      fun reentrant _ target =
        (calls := !calls + 1; checked second;
         Thm.REFL (#1 (boolSyntax.dest_eq target)))
      val _ = CPC_ProofReplay.word_graph_tautology_using_for_test
        reentrant "task49-reentrant" first
      val _ = assert (entries () = (if disabled then 0 else 2),
        "outer CPC publication overwrote successful inner work")
      val _ = checked second
      val _ = checked first
    in assert (!calls = (if disabled then 4 else 2),
      "reentrant CPC work was not reusable") end) ()
  val _ = clean ()

  (* Reentrant work gets the capacity first; a full current memo must not
     be overwritten by the outer callback's formerly empty snapshot. *)
  val _ = calls := 0
  val _ = boundary 1 (fn () =>
    let
      fun reentrant _ target =
        (calls := !calls + 1; checked second;
         Thm.REFL (#1 (boolSyntax.dest_eq target)))
      val _ = CPC_ProofReplay.word_graph_tautology_using_for_test
        reentrant "task49-reentrant-cap" first
      val _ = checked second
      val _ = checked first
    in
      assert (entries () = (if disabled then 0 else 1),
        "reentrant CPC capacity exceeded");
      assert (!calls = (if disabled then 4 else 3),
        "outer CPC publication replaced the capacity winner")
    end) ()
  val _ = clean ()

  (* The same target can also be inserted recursively; count it only once. *)
  val _ = calls := 0
  val _ = boundary 8 (fn () =>
    let
      fun reentrant _ target =
        (calls := !calls + 1; checked first;
         Thm.REFL (#1 (boolSyntax.dest_eq target)))
      val _ = CPC_ProofReplay.word_graph_tautology_using_for_test
        reentrant "task49-reentrant-same" first
      val _ = checked first
    in
      assert (entries () = (if disabled then 0 else 1),
        "reentrant CPC duplicate counted twice");
      assert (!calls = (if disabled then 3 else 2),
        "reentrant same-target fallback lost")
    end) ()
  val _ = clean ()

  (* Independent inner replay restores, rather than clears, the outer memo. *)
  val _ = calls := 0
  val _ = boundary 8 (fn () =>
    (checked first; checked first;
     boundary 8 (fn () =>
       (assert (entries () = 0, "inner CPC replay inherited entries");
        checked first; checked first)) ();
     checked first)) ()
  val _ = assert (!calls = (if disabled then 5 else 2),
    "nested CPC boundary lost isolation or outer hit")
  val _ = clean ()

  fun exception_test raised =
    let
      val attempts = ref 0
      fun broken _ _ = (attempts := !attempts + 1; raise raised)
      fun fail () = ignore
        (CPC_ProofReplay.word_graph_tautology_using_for_test
          broken "task49-failure" first)
      val _ = boundary 8 (fn () =>
        (assert (propagated raised fail, "first CPC exception swallowed");
         assert (propagated raised fail, "CPC cached an exception");
         assert (!attempts = 2 andalso entries () = 0,
           "CPC exception inserted an entry");
         checked first;
         assert (propagated raised
           (fn () => boundary 8 (fn () =>
             (checked second; raise raised)) ()), "nested exception lost");
         assert (entries () = (if disabled then 0 else 1),
           "nested failure changed outer CPC memo"))) ()
      val _ = assert (propagated raised
        (fn () => boundary 8 (fn () =>
          (checked first; raise raised)) ()), "CPC boundary swallowed exit")
    in clean () end
  val _ = List.app exception_test
    [Fail "task49-primary", Timeout.TIMEOUT Time.zeroTime, Interrupt]

  val _ = calls := 0
  val _ = boundary 0 (fn () => (checked first; checked first)) ()
  val _ = boundary (~1) (fn () => (checked first; checked first)) ()
  val _ = boundary 8 checked first
  val _ = boundary 8 checked first
  val _ = assert (!calls = 6, "zero cap or fresh session reused an entry")
  val _ = clean ()

  val production_cap =
    CPC_ProofReplay.max_word_graph_tautology_entries_for_test
  val _ = calls := 0
  val _ = boundary production_cap (fn () =>
    let
      val targets = List.tabulate (production_cap + 1, fn i =>
        let val atom = Term.mk_var ("task49_cap_" ^ Int.toString i,
          if i mod 2 = 0 then Type.bool else numSyntax.num)
        in boolSyntax.mk_eq (atom, atom) end)
      val _ = List.app checked targets
      val _ = checked (List.hd targets)
      val _ = checked (List.last targets)
    in assert (entries () = (if disabled then 0 else production_cap),
      "production CPC bound exceeded") end) ()
  val _ = assert (!calls = production_cap + (if disabled then 3 else 2),
    "production CPC cap did not preserve fallback/hit behavior")
  val _ = clean ()

  fun with_snapshot action =
    let
      val saved = Context.snapshot ()
    in
      (action () before Context.restore saved)
      handle exn => (Context.restore saved; raise exn)
    end

  (* Both retirement epochs fence the CPC memo before its next lookup. *)
  val _ = calls := 0
  val _ = with_snapshot (fn () => boundary 8 (fn () =>
    let
      val _ = checked first
      val _ = checked first
      val _ = Theory.new_constant ("task49_cpc_retire", Type.bool)
      val _ = Theory.delete_const "task49_cpc_retire"
      val _ = assert (entries () = 0, "CPC term retirement kept hints")
      val _ = checked first
      val _ = checked first
      val _ = Theory.new_type ("task49_cpc_retire_type", 0)
      val _ = Theory.delete_type "task49_cpc_retire_type"
      val _ = assert (entries () = 0, "CPC type retirement kept hints")
      val _ = checked first
      val _ = checked first
    in assert (!calls = (if disabled then 6 else 3),
      "CPC retirement did not rerun complete worker") end) ())
  val _ = clean ()

  (* Fresh extensions and snapshot restore leave retirement epochs alone.
     The signature table pointers must still invalidate both directions. *)
  fun cpc_restore_test extend =
    with_snapshot (fn () => boundary 8 (fn () =>
      let
        val saved = Context.snapshot ()
        val epochs = (Type.type_epoch (), Term.term_epoch ())
        val _ = calls := 0
        val _ = checked first
        val _ = extend ()
        val _ = assert (epochs =
          (Type.type_epoch (), Term.term_epoch ()), "CPC restore fixture")
        val _ = assert (entries () = 0, "CPC fresh signature kept hints")
        val _ = checked first
        val _ = Context.restore saved
        val _ = assert (epochs =
          (Type.type_epoch (), Term.term_epoch ()), "CPC restored epochs")
        val _ = assert (entries () = 0, "CPC restore kept branch hints")
        val _ = checked first
        val _ = checked first
      in assert (!calls = (if disabled then 4 else 3),
        "CPC signature pointer fence missed restore") end) ())
  val _ = cpc_restore_test (fn () =>
    Theory.new_constant ("task49_cpc_restore_const", Type.bool))
  val _ = cpc_restore_test (fn () =>
    Theory.new_type ("task49_cpc_restore_type", 0))
  val _ = clean ()

  (* Publication spanning a restore is discarded, without discarding a
     successful recursive insertion made in the restored signature. *)
  val _ = calls := 0
  val _ = with_snapshot (fn () =>
    let
      val saved = Context.snapshot ()
      val _ = Theory.new_constant ("task49_cpc_callback", Type.bool)
    in boundary 8 (fn () =>
      let
        fun restoring _ target =
          (calls := !calls + 1; Context.restore saved; checked second;
           Thm.REFL (#1 (boolSyntax.dest_eq target)))
        val _ = CPC_ProofReplay.word_graph_tautology_using_for_test
          restoring "task49-restore-publication" first
        val _ = assert (entries () = (if disabled then 0 else 1),
          "CPC published callback result across restore")
        val _ = checked second
        val _ = checked first
      in assert (!calls = (if disabled then 4 else 3),
        "CPC restore publication lost new-signature inner work") end) ()
    end)
  val _ = clean ()

  (* Retirement during a worker likewise drops its publication, even when
     a reentrant success has already filled the new-signature memo. *)
  val _ = calls := 0
  val _ = with_snapshot (fn () =>
    let
      val _ = Theory.new_type ("task49_cpc_callback_type", 0)
    in boundary 8 (fn () =>
      let
        fun retiring _ target =
          (calls := !calls + 1;
           Theory.delete_type "task49_cpc_callback_type";
           checked second; Thm.REFL (#1 (boolSyntax.dest_eq target)))
        val _ = CPC_ProofReplay.word_graph_tautology_using_for_test
          retiring "task49-retire-publication" first
        val _ = assert (entries () = (if disabled then 0 else 1),
          "CPC published callback result across retirement")
        val _ = checked second
        val _ = checked first
      in assert (!calls = (if disabled then 4 else 3),
        "CPC retirement publication lost reentrant work") end) ()
    end)
  val _ = clean ()

  (* A target mentioning a declaration lost on restore may still reach
     the complete worker, but must not become a reusable stale entry. *)
  val _ = with_snapshot (fn () => boundary 8 (fn () =>
    let
      val saved = Context.snapshot ()
      val _ = Theory.new_constant ("task49_cpc_stale", Type.bool)
      val atom = Term.mk_const ("task49_cpc_stale", Type.bool)
      val stale = boolSyntax.mk_eq (atom, atom)
      val _ = calls := 0
      val _ = checked stale
      val _ = Context.restore saved
      val _ = checked stale
      val _ = checked stale
    in
      assert (!calls = 3 andalso entries () = 0,
        "CPC stale target hit or skipped complete worker")
    end) ())
  val _ = clean ()

  (* All five pre-existing FP/literal cells must survive nested exits. *)
  val _ = CPC_ProofReplay.with_seeded_replay_memos_for_test (fn retained =>
    let
      fun inner () = assert (not (retained ()), "legacy memos not isolated")
      val _ = boundary 8 inner ()
      val _ = assert (retained (), "legacy memos lost on normal exit")
      fun check raised =
        (assert (propagated raised (fn () => boundary 8
           (fn () => (inner (); raise raised)) ()), "legacy exception lost");
         assert (retained (), "legacy memos lost on exceptional exit"))
    in List.app check
      [Fail "task49-legacy", Timeout.TIMEOUT Time.zeroTime, Interrupt] end)

  val zboundary = Z3_ProofReplay.with_def_axiom_cache_boundary_for_test
  val statistics = Z3_ProofReplay.def_axiom_cache_statistics_for_test
  val zentries = Z3_ProofReplay.def_axiom_cache_retained_entries_for_test
  val target = boolSyntax.mk_eq
    (boolSyntax.mk_conj (p, q), boolSyntax.mk_conj (q, p))
  fun zprove_target target =
    let val theorem = Z3_ProofReplay.def_axiom_for_test target in
      assert (Portable.pointer_eq (Thm.concl theorem, target) andalso
          HOLset.isEmpty (Thm.hypset theorem), "Z3 fallback theorem");
      Library.check_oracle_tags "Task49" "def axiom" theorem
    end
  fun zprove () = zprove_target target
  fun zclean () = assert (zentries () = 0, "Z3 boundary retained entries")

  (* Signature changes within a live dynamic boundary free capacity, before
     lookup. Nested boundaries still share hits in an unchanged signature. *)
  val _ = zboundary 1 (fn () =>
    let
      val _ = zprove ()
      val _ = zboundary 8 (fn () => zprove ()) ()
      val symbols = Term.term_epoch ()
      val _ = Theory.new_constant ("task49_epoch_constant", Type.bool)
      val _ = Theory.delete_const "task49_epoch_constant"
      val _ = assert (Term.term_epoch () <> symbols, "term epoch fixture")
      val _ = zboundary 8 (fn () => (zprove (); zprove ())) ()
      val types = Type.type_epoch ()
      val _ = Theory.new_type ("task49_epoch_type", 0)
      val _ = Theory.delete_type "task49_epoch_type"
      val _ = assert (Type.type_epoch () <> types, "type epoch fixture")
      val _ = zprove ()
      val _ = zprove ()
      val stats = statistics ()
    in
      if disabled then
        assert (#lookups stats = 0 andalso #inserts stats = 0 andalso
          #skeleton_attempts stats = 0, "D-mode Z3 cache activity")
      else
        assert (#lookups stats = 6 andalso #hits stats = 3 andalso
          #misses stats = 3 andalso #inserts stats = 3 andalso
          #skeleton_attempts stats = 3 andalso #entries stats = 1 andalso
          #capacity_refusals stats = 0, "Z3 epoch fence/nested sharing")
    end) ()
  val _ = zclean ()

  (* A branch extension and its restore do not retire declarations. Both
     pointer changes must nevertheless retire the cache's old signature. *)
  fun z3_restore_test extend =
    with_snapshot (fn () => zboundary 1 (fn () =>
      let
        val saved = Context.snapshot ()
        val epochs = (Type.type_epoch (), Term.term_epoch ())
        val _ = zprove ()
        val _ = extend ()
        val _ = assert (epochs =
          (Type.type_epoch (), Term.term_epoch ()), "Z3 extension epochs")
        val _ = zprove ()
        val _ = Context.restore saved
        val _ = assert (epochs =
          (Type.type_epoch (), Term.term_epoch ()), "Z3 restore epochs")
        val _ = zprove ()
        val _ = zprove ()
        val stats = statistics ()
      in
        assert (disabled orelse
          (#hits stats = 1 andalso #misses stats = 3 andalso
           #inserts stats = 3 andalso #entries stats = 1 andalso
           #capacity_refusals stats = 0), "Z3 signature restore fence")
      end) ())
  val _ = z3_restore_test (fn () =>
    Theory.new_constant ("task49_z3_restore_const", Type.bool))
  val _ = z3_restore_test (fn () =>
    Theory.new_type ("task49_z3_restore_type", 0))
  val _ = zclean ()

  (* A stale branch target must never hit, even if the complete worker
     itself accepts it. Ordinary worker rejection is also permitted. *)
  val _ = with_snapshot (fn () => zboundary 8 (fn () =>
    let
      val saved = Context.snapshot ()
      val _ = Theory.new_constant ("task49_z3_stale", Type.bool)
      val atom = Term.mk_const ("task49_z3_stale", Type.bool)
      val stale = boolSyntax.mk_eq
        (boolSyntax.mk_conj (p, atom), boolSyntax.mk_conj (atom, p))
      val _ = zprove_target stale
      val _ = Context.restore saved
      fun attempt () =
        case Exn.capture zprove_target stale of
          Exn.Res _ => ()
        | Exn.Exn (Feedback.HOL_ERR _) => ()
        | Exn.Exn exn => raise exn
      val _ = attempt ()
      val _ = attempt ()
      val stats = statistics ()
    in
      assert (#hits stats = 0 andalso #entries stats = 0,
        "Z3 stale branch target became a hit");
      assert (disabled orelse
        (#misses stats = 3 andalso #skeleton_attempts stats = 3),
        "Z3 stale miss bypassed complete worker")
    end) ())
  val _ = zclean ()

  (* Inner exceptional exit must not detach the enclosing Z3 boundary. *)
  val _ = zboundary 8 (fn () =>
    (zprove ();
     assert (propagated Interrupt
       (fn () => zboundary 8 (fn () => raise Interrupt) ()),
       "nested Z3 interrupt swallowed");
     zprove ();
     assert (disabled orelse #hits (statistics ()) = 1,
       "nested Z3 exception discarded outer cache"))) ()
  val _ = zclean ()
  val _ = List.app (fn raised =>
    (assert (propagated raised (fn () => zboundary 8
       (fn () => (zprove (); raise raised)) ()), "Z3 primary exit lost");
     zclean ()))
    [Fail "task49-z3", Timeout.TIMEOUT Time.zeroTime, Interrupt]

  (* Existing Task31 fixtures also cover cap refusal, bad-hit fallback,
     terminal cleanup precedence, and complete workers in D-mode. *)
  val _ = if disabled then () else
    let
      val fallback =
        Z3_ProofReplay.def_axiom_cache_probe_failure_for_test target
    in
      assert (#retained_entries fallback = 0,
        "Z3 bad-hit fallback retained cache");
      assert (#failures (#statistics fallback) = 1 andalso
        #skeleton_attempts (#statistics fallback) = 2,
        "Z3 bad hit skipped the complete procedure")
    end
  in () end
end
