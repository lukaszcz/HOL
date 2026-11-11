(* Replay cache ownership and optional-reuse regressions. *)
open HolKernel Parse boolLib bossLib

structure Task49ContextTests =
struct
  structure S = SmtSkeletonProve
  structure W = SmtWordGraph
  structure G = SmtReplayGraph
  fun check true _ = () | check false message = raise Fail message
  fun shared_type 0 = Type.bool
    | shared_type n =
        let val child = shared_type (n-1)
        in Type.mk_type ("fun",[child,child]) end
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
           then blastLib.WORD_SIMP_CANCEL_LITERAL_CONV term
           else raise Conv.UNCHANGED)
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

  (* A small source can generate a much larger bit view. Invalidate only
     after that view has populated local hints, then compare a cold result. *)
  fun generated_callback () = with_symbol false (fn allocate => fn retire =>
    let
      val _ = allocate ()
      val input = ``(late_x:word32) + late_y = late_z``
      val calls = ref 0
      fun callback term =
        (calls := !calls+1;
         if !calls=16 then retire () else ();
         blastLib.BIT_BLAST_CONV term)
      val (theorem,metrics) =
        W.normalize_using_with_metrics
          {word_conversion=blastLib.WORD_SIMP_CANCEL_LITERAL_CONV,
           bit_conversion=callback,
           node_conversion=fn _ => raise Conv.UNCHANGED} input
      val cold = W.normalize input
    in
      check (!calls>=16 andalso #generated_nodes metrics>64)
        ("late invalidation did not exercise generated syntax: " ^
         Int.toString (!calls) ^ "/" ^
         Int.toString (#generated_nodes metrics));
      check (Portable.pointer_eq
        (boolSyntax.lhs (Thm.concl theorem),input)) "lost late endpoint";
      check (Term.aconv (boolSyntax.rhs (Thm.concl theorem))
        (boolSyntax.rhs (Thm.concl cold)))
        "late invalidation changed generated normalization";
      check (null (Thm.hyp theorem)) "late normalization retained hypotheses";
      Library.check_oracle_tags "Task49ContextTests" "generated" theorem
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
      fun checked_run () =
        let val result = prove context (owners "reset")
        in checked (#theorem result) target;
           check (#skeleton_dag_nodes (#metrics result)=3)
             "cache reset changed the obligation's semantic node count" end
      fun run () =
        (checked_run ();
         check (S.cache_size context=0) "reset generation published old IDs";
         checked_run (); checked_run ())
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

  (* Publication must return a checked result even for tiny binder syntax
     with an exponentially unfolded ground range Type. Also put the unsafe
     binder below a small one: admission must precede nested count_body,
     not just the final name-preserving destructor. *)
  fun binder_publication () =
    let
      val variable = Term.mk_var ("task49_publication_b", Type.bool)
      val body = Term.mk_var ("task49_publication_y", shared_type 38)
      val huge = Term.mk_abs (variable,body)
      val predicate = Term.mk_var ("task49_publication_p",
        Type.--> (Term.type_of huge,Type.bool))
      val atom = Term.mk_comb (predicate,huge)
      val nested = Term.mk_abs (variable,atom)
      val small = Term.mk_abs (variable,variable)
      fun trial abstraction retain =
        let
          val consume = Term.mk_var ("task49_publication_consume",
            Type.--> (Term.type_of abstraction,Type.bool))
          val input = Term.mk_comb (consume,abstraction)
          (* Construct the checked endpoint BEFORE the publication watchdog. *)
          val theorem = Thm.DISCH input (Thm.ASSUME input)
          val target = Thm.concl theorem
          val context = S.new_sat_context ()
          val calls = ref 0
          fun worker () = (calls := !calls+1; theorem)
          fun run () =
            let
              val result = S.cached_sat_proof context target 16 worker
              val _ = check (Portable.pointer_eq (Thm.concl result,target))
                "publication changed the checked endpoint"
            in checked result target end
          val _ = Timeout.apply (Time.fromSeconds 2)
            (fn () => (run (); run ())) ()
        in
          check (!calls = (if retain then 1 else 2))
            "binder publication lost small reuse or huge checked misses";
          check (null (!(#proofs context)) = not retain)
            "unsafe binder was retained"
        end
    in trial huge false; trial nested false; trial small true end

  fun frontier_laws () =
    let
      val context = S.new_sat_context ()
      val source_context = S.new_context []
      fun hits () = case List.find (fn (name,_) =>
          name = "E0(skeleton/schematic-certificate-hit)_OK")
          (Profile.results ()) of NONE => 0 | SOME (_,info) => #n info
      fun target name =
        let
          val p = Term.mk_var (name ^ "_p",Type.bool)
          val q = Term.mk_var (name ^ "_q",Type.bool)
        in boolSyntax.mk_disj
          (boolSyntax.mk_neg (boolSyntax.mk_conj (p,q)),p) end
      fun prove goal = checked
        (S.clause_frontier_prove_indexed context source_context 512 goal) goal
      val first = target "frontier_first"
      (* Include a source variable spelled just like a schematic hole.
         Reuse must still instantiate the current source, not the old one. *)
      val p = Term.mk_var ("clause_frontier_atom_0",Type.bool)
      val q = Term.mk_var ("frontier_second_q",Type.bool)
      val second = boolSyntax.mk_disj
        (boolSyntax.mk_neg (boolSyntax.mk_conj (p,q)),p)
      val _ = prove first
      val prior_hits = hits ()
      val _ = prove second
      val _ = check (hits () = prior_hits+1)
        "closed frontier law was not reused"
      (* A complete positive disjunction must survive clause flattening
         when a negative literal names it, including independent copies. *)
      val disjunction = boolSyntax.mk_disj (p,q)
      val rebuilt = boolSyntax.mk_disj
        (Term.mk_var ("clause_frontier_atom_0",Type.bool),
         Term.mk_var ("frontier_second_q",Type.bool))
      val _ = prove (boolSyntax.mk_disj
        (disjunction,boolSyntax.mk_neg rebuilt))
      val _ = prove (boolSyntax.mk_disj
        (boolSyntax.mk_disj (disjunction,p),boolSyntax.mk_neg rebuilt))
      val invalid = boolSyntax.mk_disj
        (boolSyntax.mk_neg (boolSyntax.mk_conj (p,q)),
         Term.mk_var ("frontier_unrelated",Type.bool))
      val _ = check ((ignore
          (S.clause_frontier_prove_indexed context source_context 512 invalid);
          false) handle Feedback.HOL_ERR _ => true)
        "frontier reuse proved an invalid clause"
      val _ = check ((ignore (S.clause_frontier_prove_indexed
          context source_context 512 (boolSyntax.mk_disj
            (disjunction,boolSyntax.mk_neg (boolSyntax.mk_disj
              (p,Term.mk_var ("frontier_unrelated",Type.bool))))));
          false) handle Feedback.HOL_ERR _ => true)
        "composite frontier confused different disjunctions"
    in () end

  (* Public callers can share a SAT context with generated Boolean laws.
     Comparing such a law must not unfold the old polymorphic annotation. *)
  fun mixed_frontier_cache () =
    let
      val ty = shared_type 18
      val _ = SmtReplayTermBridge.admit_type ty
      val theorem = Thm.REFL (Term.mk_var ("mixed_cache_large",ty))
      val context = S.new_sat_context ()
      val _ = S.cached_sat_proof context (Thm.concl theorem) 16
        (fn () => theorem)
      val _ = check (not (null (!(#proofs context))))
        "generic certificate was not retained"
      val p = Term.mk_var ("mixed_cache_bool",Type.bool)
      val goal = boolSyntax.mk_eq (p,p)
      val _ = Timeout.apply (Time.fromSeconds 2)
        (fn () => checked (S.clause_frontier_prove_in context 512 goal)
          goal) ()
    in () end

  (* The optional index must not add a Type gate to a tiny Boolean law whose
     source atom contains an otherwise unadmittable ground annotation. *)
  fun indexed_frontier_fallback () =
    let
      val x = Term.mk_var ("frontier_fallback_x",Type.bool)
      val body = Term.mk_var ("frontier_fallback_y",shared_type 38)
      val binder = Term.mk_abs (x,body)
      val predicate = Term.mk_var ("frontier_fallback_p",
        Type.--> (Term.type_of binder,Type.bool))
      val atom = Term.mk_comb (predicate,binder)
      val goal = boolSyntax.mk_disj (atom,boolSyntax.mk_neg atom)
      fun run (source_context as S.Context {atom_index,...}) =
        Timeout.apply (Time.fromSeconds 2) (fn () =>
          (check (atom_index goal=NONE)
             "optional index did not decline the fallback fixture";
           checked (S.clause_frontier_prove_indexed (S.new_sat_context ())
             source_context 512 goal) goal)) ()
    in run (S.new_context []);
       run (S.new_context_with_index_limit 0 []) end

  fun semantic_node_counts () =
    let
      val context = S.new_context []
      val p = Term.mk_var ("metric_count_p",Type.bool)
      val q = Term.mk_var ("metric_count_q",Type.bool)
      fun run (goal,count) =
        let val result = S.prove_with_owners context no_owners
              (S.term_measure goal) goal
        in checked (#theorem result) goal;
           check (#skeleton_dag_nodes (#metrics result)=count)
             "indexed skeleton count changed semantic classes" end
      val a = Term.mk_var ("metric_bound_a",Type.bool)
      val b = Term.mk_var ("metric_bound_b",Type.bool)
      val f = Term.mk_var ("metric_count_f",
        Type.--> (Type.--> (Type.bool,Type.bool),numSyntax.num))
      fun atom variable = boolSyntax.mk_eq
        (Term.mk_comb (f,Term.mk_abs (variable,variable)),numSyntax.zero_tm)
    in List.app run
      [(boolSyntax.mk_imp (boolSyntax.mk_disj (p,p),p),3),
       (boolSyntax.mk_imp
          (boolSyntax.mk_disj (p,q),boolSyntax.mk_disj (q,p)),5),
       (boolSyntax.mk_disj (atom a,boolSyntax.mk_neg (atom b)),3)] end

  fun run () =
    (owner_keys (); optional_miss (); binder_publication (); frontier_laws ();
     mixed_frontier_cache (); indexed_frontier_fallback ();
     semantic_node_counts ();
     reset_restore ();
     retired_publication (); attempt_reset_restore ();
     List.app retained [false,true];
     List.app restored [false,true];
     List.app publication [false,true]; shared_callback ();
     generated_callback ())
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
      (* A complete child replay releases command hints before closure.
         Both successful closure and an invalid final theorem must preserve
         the enclosing session's warm word hint and all five legacy cells. *)
      val _ = boundary 8 (fn () =>
        let
          fun proof term : CPC_Proof.proof =
            {commands = [CPC_Proof.ASSUME ("@task59_phase",
               {term=term,provenance=CPC_Proof.AtomicProvenance})],
             cvc_version="1.3.4"}
          val _ = checked first
          val workers = !calls
          val theorem = CPC_ProofReplay.check_proof
            ([boolSyntax.F],boolSyntax.T,proof boolSyntax.F)
          val _ = assert
            (Term.aconv (Thm.concl theorem) boolSyntax.F andalso
             HOLset.equal (Thm.hypset theorem,
               HOLset.fromList Term.compare [boolSyntax.F]),
             "complete child replay changed its exact sequent")
          val _ = Library.check_oracle_tags "Task49" "phase child" theorem
          val _ = assert
            (case CPC_ProofReplay.replay_step_provenance_for_test
                (proof boolSyntax.F) "@task59_phase" of
               CPC_Proof.AtomicProvenance => true | _ => false,
             "closure retirement changed diagnostic command provenance")
          val failed = Exn.capture CPC_ProofReplay.check_proof
            ([boolSyntax.T],boolSyntax.T,proof boolSyntax.T)
          val _ = assert
            (case failed of Exn.Exn (Feedback.HOL_ERR detail) =>
               Feedback.top_function_of detail = "check_proof" andalso
               Feedback.message_of detail = "final CPC conclusion is not F"
             | _ => false, "child replay changed the first final error")
          val _ = checked first
        in assert (!calls = workers + (if disabled then 1 else 0),
             "complete child replay discarded the caller's warm hint") end) ()
      val _ = assert (retained (), "complete child lost legacy memos")
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
