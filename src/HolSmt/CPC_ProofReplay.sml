(* Checked replay for cvc5's native CPC proof calculus. *)

structure CPC_ProofReplay =
struct

local
  open CPC_Proof

  val ERR = Feedback.mk_HOL_ERR "CPC_ProofReplay"

  fun profile name f x =
    Profile.profile_with_exn_name name f x

  fun profile_event name = Profile.profile name (fn () => ()) ()

  fun provenance_shape AtomicProvenance = "atom"
    | provenance_shape (ApplicationProvenance (head, operands)) =
        "application(" ^ head ^ "," ^
        String.concatWith "," (List.map provenance_shape operands) ^ ")"
    | provenance_shape (BinderProvenance (head, body)) =
        "binder(" ^ head ^ "," ^ provenance_shape body ^ ")"
    | provenance_shape (EqualityProvenance (left, right)) =
        "equality(" ^ provenance_shape left ^ "," ^
        provenance_shape right ^ ")"
    | provenance_shape (ConjunctionProvenance (_, operands)) =
        "conjunction(" ^
        String.concatWith "," (List.map provenance_shape operands) ^ ")"
    | provenance_shape (UnavailableProvenance reason) =
        "unavailable(" ^ reason ^ ")"
    | provenance_shape (AmbiguousProvenance reason) =
        "ambiguous(" ^ reason ^ ")"

  (* Exact provenance that proves an occurrence contains no conjunction can
     be represented by the atomic no-conjunction marker once it enters the
     live step table.  Parsed command occurrences remain fully structured,
     so a later CONG still has the exact source tree it must rewrite.  An
     unavailable or ambiguous occurrence is deliberately not compacted: it
     may contain a conjunction and must continue to fail closed. *)
  fun definitely_no_conjunction AtomicProvenance = true
    | definitely_no_conjunction (ApplicationProvenance (_, operands)) =
        List.all definitely_no_conjunction operands
    | definitely_no_conjunction (BinderProvenance (_, body)) =
        definitely_no_conjunction body
    | definitely_no_conjunction (EqualityProvenance (left, right)) =
        definitely_no_conjunction left andalso
        definitely_no_conjunction right
    | definitely_no_conjunction (ConjunctionProvenance _) = false
    | definitely_no_conjunction (UnavailableProvenance _) = false
    | definitely_no_conjunction (AmbiguousProvenance _) = false

  (* Live metadata retains equality endpoints because several semantic rules
     select or rewrite one exact side even when neither side contains a
     conjunction.  Recursively collapse only conjunction-irrelevant
     application and binder shells; this keeps large arithmetic proofs
     bounded without erasing the semantic boundaries those rules consume. *)
  fun compact_live_provenance provenance =
    case provenance of
      EqualityProvenance (left, right) => EqualityProvenance
        (compact_live_provenance left, compact_live_provenance right)
    | ConjunctionProvenance (source, operands) =>
        ConjunctionProvenance
          (source, List.map compact_live_provenance operands)
    | ApplicationProvenance (head, operands) =>
        if definitely_no_conjunction provenance then AtomicProvenance
        else ApplicationProvenance
          (head, List.map compact_live_provenance operands)
    | BinderProvenance (head, body) =>
        if definitely_no_conjunction provenance then AtomicProvenance
        else BinderProvenance (head, compact_live_provenance body)
    | other => other

  fun term_contains_conjunction term =
    not (List.null (HolKernel.find_terms boolSyntax.is_conj term))

  (* A successful kernel theorem proves when no conjunction occurrence is
     present at all.  In that case Atomic is exact, while equality boundaries
     remain visible in HOL and can be retained recursively.  Any theorem that
     does contain a conjunction needs occurrence-specific parsed/semantic
     provenance; never guess its erased n-ary grouping here. *)
  fun conjunction_free_semantic_provenance reason term =
    if term_contains_conjunction term then UnavailableProvenance reason
    else
      case Lib.total boolSyntax.dest_eq term of
        SOME (left, right) => EqualityProvenance
          (conjunction_free_semantic_provenance reason left,
           conjunction_free_semantic_provenance reason right)
      | NONE => AtomicProvenance

  (* Keep an instrumented form of the historical broken write side for
     same-binary baseline comparisons.  Normal replay always enables the
     cache; only an explicit benchmark environment setting disables it. *)
  val theorem_cache_enabled =
    OS.Process.getEnv "HOL4_CPC_THEOREM_CACHE" <> SOME "0"

  type cache_stats = {
    hits : int ref,
    misses : int ref,
    context_rejections : int ref,
    omitted_bypasses : int ref,
    cardinality : int ref,
    peak_cardinality : int ref,
    step_cardinality : int ref
  }

  fun new_cache_stats () : cache_stats = {
    hits = ref 0,
    misses = ref 0,
    context_rejections = ref 0,
    omitted_bypasses = ref 0,
    cardinality = ref 0,
    peak_cardinality = ref 0,
    step_cardinality = ref 0
  }

  type cached_theorem = {
    thm : Thm.thm
  }

  type replay_result = {
    thm : Thm.thm,
    located : located_term
  }

  type replayed_step = {
    rule_name : string,
    result : replay_result
  }

  fun result_theorem ({thm, ...} : replay_result) = thm

  fun result_located ({located, ...} : replay_result) = located

  fun result_provenance result = #provenance (result_located result)

  fun step_theorem ({result, ...} : replayed_step) = result_theorem result

  fun step_located ({result, ...} : replayed_step) = result_located result

  fun step_provenance step = #provenance (step_located step)

  fun exact_result provenance theorem : replay_result =
    let
      val term = Thm.concl theorem
      val provenance =
        case provenance of
          UnavailableProvenance reason =>
            conjunction_free_semantic_provenance reason term
        | AmbiguousProvenance reason =>
            if term_contains_conjunction term then
              AmbiguousProvenance reason
            else conjunction_free_semantic_provenance reason term
        | exact => exact
    in
      {thm = theorem, located = {term = term, provenance = provenance}}
    end

  fun unavailable_result reason theorem =
    exact_result (UnavailableProvenance reason) theorem

  fun located_result where_ theorem (located : located_term) =
    if Term.aconv (Thm.concl theorem) (#term located) then
      {thm = theorem, located = located}
    else raise ERR where_
      ("CPC theorem/result provenance mismatch: theorem=" ^
       Library.term_to_string (Thm.concl theorem) ^ "; located=" ^
       Library.term_to_string (#term located))

  type state = {
    asserted_hyps : Term.term HOLset.set,
    scope_hyps : Term.term list,
    (* Retained for shared canonicalization: TASK_12 consumes these exact
       per-translation emitted-definition records. *)
    translation_definitions : SmtLib.emitted_definition list,
    (* The theorem and its exact occurrence provenance are installed as one
       live entry.  Reusing an id therefore replaces both synchronously. *)
    steps : (string, replayed_step) Redblackmap.dict,
    (* The read side is intentional: CPC commonly repeats normalized facts. *)
    thm_cache : cached_theorem Net.net,
    cache_stats : cache_stats
  }

  fun initial_state definitions asserted_hyps : state = {
    asserted_hyps = HOLset.addList (Term.empty_tmset, asserted_hyps),
    scope_hyps = [],
    translation_definitions = definitions,
    steps = Redblackmap.mkDict String.compare,
    thm_cache = Net.empty,
    cache_stats = new_cache_stats ()
  }

  fun cache_thm state thm =
    if not theorem_cache_enabled then
      (profile_event "CPC(cache:insert_disabled)";
       state)
    else let
      val stats = #cache_stats state
      val cardinality = !(#cardinality stats) + 1
      val () = #cardinality stats := cardinality
      val () = #peak_cardinality stats :=
        Int.max (!(#peak_cardinality stats), cardinality)
      val () = profile_event "CPC(cache:insert)"
    in {
      asserted_hyps = #asserted_hyps state,
      scope_hyps = #scope_hyps state,
      translation_definitions = #translation_definitions state,
      steps = #steps state,
      thm_cache = Net.insert (Thm.concl thm,
        {thm = thm})
        (#thm_cache state),
      cache_stats = stats
    } end

  fun cache_step state id rule_name (result : replay_result) =
  let
    val stats = #cache_stats state
    val () = #step_cardinality stats := !(#step_cardinality stats) + 1
    val theorem = result_theorem result
    val located = result_located result
    val _ = Term.aconv (Thm.concl theorem) (#term located) orelse
      raise ERR "cache_step"
        ("CPC live theorem/result provenance mismatch for step " ^ id)
    val result = {thm = theorem,
      located = {term = #term located,
        provenance = compact_live_provenance (#provenance located)}}
  in {
    asserted_hyps = #asserted_hyps state,
    scope_hyps = #scope_hyps state,
    translation_definitions = #translation_definitions state,
    steps = Redblackmap.insert (#steps state, id,
      {rule_name = rule_name, result = result}),
    thm_cache = #thm_cache state,
    cache_stats = stats
  } end

  fun assert_hyp state tm = {
    asserted_hyps = HOLset.add (#asserted_hyps state, tm),
    scope_hyps = #scope_hyps state,
    translation_definitions = #translation_definitions state,
    steps = #steps state,
    thm_cache = #thm_cache state,
    cache_stats = #cache_stats state
  }

  fun push_scope_hyp state tm = {
    asserted_hyps = #asserted_hyps state,
    scope_hyps = tm :: #scope_hyps state,
    translation_definitions = #translation_definitions state,
    steps = #steps state,
    thm_cache = #thm_cache state,
    cache_stats = #cache_stats state
  }

  fun pop_scope_hyp state =
    case #scope_hyps state of
      tm :: rest => (tm, {
        asserted_hyps = #asserted_hyps state,
        scope_hyps = rest,
        translation_definitions = #translation_definitions state,
        steps = #steps state,
        thm_cache = #thm_cache state,
        cache_stats = #cache_stats state
      })
    | [] => raise ERR "scope" "CPC scope step has no matching assume-push"

  fun find_step what state id : replayed_step =
    Redblackmap.find (#steps state, id)
    handle Redblackmap.NotFound =>
      raise ERR what ("CPC premise step '" ^ id ^ "' was not found")

  fun lookup_step state id = step_theorem
    (find_step "lookup_step" state id)

  fun lookup_premises state ids = List.map (lookup_step state) ids

  fun lookup_rule state id =
    #rule_name (find_step "lookup_rule" state id)

  fun cached_thm state tm =
    profile "CPC(cache:probe)" (fn () => let
      val available = HOLset.addList (#asserted_hyps state, #scope_hyps state)
      val stats = #cache_stats state
      fun conclusion_matches cached =
        Term.aconv (Thm.concl (#thm cached)) tm
      fun context_available cached =
        HOLset.isSubset (Thm.hypset (#thm cached), available)
      fun is_raw_assumption cached =
        HOLset.member (Thm.hypset (#thm cached), Thm.concl (#thm cached))
      val candidates = List.filter conclusion_matches
        (Net.match tm (#thm_cache state))
      val matches = List.filter context_available candidates
      val rejected = List.filter (not o context_available) candidates
      val () = #context_rejections stats :=
        !(#context_rejections stats) + List.length rejected
      val () = List.app (fn _ =>
        profile_event "CPC(cache:context_rejected)") rejected
      val derived = List.filter (not o is_raw_assumption) matches
    in
    case List.find (fn _ => true)
      (case derived of [] => matches | _ => derived) of
      SOME cached =>
        (#hits stats := !(#hits stats) + 1;
         profile_event "CPC(cache:hit)";
         if HOLset.isEmpty (Thm.hypset (#thm cached)) then
           profile_event "CPC(cache:hypfree_hit)"
         else ();
         #thm cached)
    | NONE =>
        (#misses stats := !(#misses stats) + 1;
         profile_event "CPC(cache:miss)";
         raise ERR "cached_thm" "no alpha-identical cached CPC theorem")
    end) ()

  fun cache_stats state =
    let val stats = #cache_stats state in {
      hits = !(#hits stats),
      misses = !(#misses stats),
      context_rejections = !(#context_rejections stats),
      omitted_bypasses = !(#omitted_bypasses stats),
      cardinality = !(#cardinality stats),
      peak_cardinality = !(#peak_cardinality stats),
      step_cardinality = !(#step_cardinality stats)
    } end

  fun profile_cardinalities state =
    let
      val stats = cache_stats state
      val peak = #peak_cardinality stats
      val steps = #step_cardinality stats
    in
      profile_event ("CPC(cache:peak=" ^ Int.toString peak ^ ")");
      profile_event ("CPC(steps:cardinality=" ^ Int.toString steps ^ ")")
    end

  (* Tactics receive the original theorems as lemmas, but their goal context
     must be exactly the union of the original hypotheses.  Replacing theorem
     premises with fresh assumptions loses provenance (and lets METIS
     instantiate problem variables), which is unsound for CPC replay. *)
  fun metis_prove thms target =
    let
      val hyps = List.foldl
        (fn (thm, acc) => HOLset.union (acc, Thm.hypset thm))
        Term.empty_tmset thms
    in
      profile "CPC(rung:resolution/METIS)" Tactical.TAC_PROOF
        ((HOLset.listItems hyps, target), metisLib.METIS_TAC thms)
    end

  fun expect_one_arg name args =
    case args of [arg] => arg
    | _ => raise ERR name "expected exactly one CPC :args term"

  fun expect_one_premise name prems =
    case prems of [prem] => prem
    | _ => raise ERR name "expected exactly one CPC premise"

  fun replay_refl conclusion args =
    case conclusion of
      SOME eq =>
        let val (left, right) = boolSyntax.dest_eq eq in
          if Term.aconv left right then Thm.REFL left
          else raise ERR "refl" "CPC refl conclusion is not reflexive"
        end
    | NONE => Thm.REFL (expect_one_arg "refl" args)

  fun replay_eq_refl args =
    Drule.EQT_INTRO (Thm.REFL (expect_one_arg "eq-refl" args))

  fun replay_instantiate args prems =
    Drule.SPECL args (expect_one_premise "instantiate" prems)

  fun conversion_equal name conv target =
    Library.conversion_equal name conv (boolSyntax.dest_eq target)

  fun replay_beta_reduce args =
    conversion_equal "beta-reduce"
      (Conv.TOP_DEPTH_CONV Thm.BETA_CONV)
      (expect_one_arg "beta-reduce" args)

  fun replay_lambda_elim args =
    conversion_equal "lambda-elim"
      (Conv.TOP_DEPTH_CONV Drule.ETA_CONV)
      (expect_one_arg "lambda-elim" args)

  (* CPC's HO_CONG omits both :args and its conclusion.  For an n-ary
     application cvc5 emits the function equality followed by one equality
     per argument, which is exactly a left-to-right fold of the HOL kernel's
     MK_COMB rule over the curried application. *)
  fun replay_ho_cong prems =
    case prems of
      function_equality :: (argument_equalities as _ :: _) =>
        (List.foldl
           (fn (argument_equality, applied) =>
              Thm.MK_COMB (applied, argument_equality))
           function_equality argument_equalities
         handle Feedback.HOL_ERR holerr =>
           raise ERR "ho_cong"
             ("MK_COMB rejected CPC premise types: " ^
              Feedback.message_of holerr))
    | _ => raise ERR "ho_cong"
        "expected a function equality and at least one argument equality"

  (* A CPC congruence step supplies the source term in :args and equality
     premises for the subterms rewritten by cvc5.  Reconstruct its context as
     a HOL lambda and use AP_TERM; this is the kernel congruence rule, not a
     rewriting oracle. *)
  fun replace_first old replacement tm =
    if Term.aconv tm old then SOME replacement else
    if Term.is_abs tm then
      let val (variable, body) = Term.dest_abs tm in
        Option.map (fn body' => Term.mk_abs (variable, body'))
          (replace_first old replacement body)
      end
    else
      let
        val (rator, rand) = Term.dest_comb tm
      in
        case replace_first old replacement rator of
          SOME rator' => SOME (Term.mk_comb (rator', rand))
        | NONE => Option.map (fn rand' => Term.mk_comb (rator, rand'))
            (replace_first old replacement rand)
      end
    handle _ => NONE

  fun contains_abs tm =
    Term.is_abs tm orelse
    (let val (rator, rand) = Term.dest_comb tm in
       contains_abs rator orelse contains_abs rand
     end handle _ => false)

  fun equality_orientation left =
    let
      val (a, b) = boolSyntax.dest_eq left
      val target = boolSyntax.mk_eq (boolSyntax.mk_eq (b, a), left)
    in
      profile "CPC(rung:congruence/METIS)" Tactical.TAC_PROOF
        (([], target), metisLib.METIS_TAC [])
    end

  fun expose_true_equality premise =
    let
      val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
    in
      if Term.aconv left boolSyntax.T then
        Thm.EQ_MP premise boolTheory.TRUTH
      else if Term.aconv right boolSyntax.T then
        Thm.EQ_MP (Thm.SYM premise) boolTheory.TRUTH
      else premise
    end
    handle Feedback.HOL_ERR _ => premise

  fun replay_cong conclusion args prems =
    let
      val source = expect_one_arg "cong" args
      fun expose_congruence premise =
        let val exposed = expose_true_equality premise in
          if boolSyntax.is_eq (Thm.concl exposed) then exposed
          else premise
        end
      fun nontrivial premise =
        if Term.aconv (Thm.concl premise) boolSyntax.T then
          false
        else
          let val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
          in not (Term.aconv left right) end
          handle Feedback.HOL_ERR _ => true
      val prems = List.filter nontrivial
        (List.map expose_congruence prems)
      fun apply premise current =
        let
          val premise =
            let val (left, _) = boolSyntax.dest_eq (Thm.concl premise) in
              case replace_first left left current of
                SOME _ => premise
              | NONE =>
                  let
                    val (_, right) = boolSyntax.dest_eq (Thm.concl premise)
                  in
                    case replace_first right right current of
                      SOME _ => Thm.SYM premise
                    | NONE => raise ERR "cong"
                        ("CPC congruence premise has no occurrence in its :args term; " ^
                         "current=" ^ Library.term_to_string current ^
                         "; premise=" ^ Library.thm_to_string premise)
                  end
            end
          val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
          (* The context binder must not capture a variable already present
             in the source term or equality premise. *)
          val hole = Term.variant
            (Term.free_vars current @ Term.free_vars (Thm.concl premise))
            (Term.mk_var ("cpc_cong_hole", Term.type_of left))
          val body =
            case replace_first left hole current of
              SOME body => body
            | NONE => raise ERR "cong"
                ("CPC congruence premise has no occurrence in its :args term; " ^
                 "current=" ^ Library.term_to_string current ^ "; premise=" ^
                 Library.term_to_string (Thm.concl premise))
          val context = Term.mk_abs (hole, body)
          val congr =
            if contains_abs current then
              let
                val rewritten =
                  case replace_first left right current of
                    SOME tm => tm
                  | NONE => raise ERR "cong" "internal replacement failure"
              in
                (* AP_TERM would beta-reduce the premise's free variables
                   through a binder and alpha-rename that binder.  Reprove
                   the explicitly rewritten quantified equality instead. *)
                metis_prove [premise] (boolSyntax.mk_eq (current, rewritten))
              end
            else Thm.AP_TERM context premise
        in
          Conv.CONV_RULE (Conv.TOP_DEPTH_CONV Thm.BETA_CONV) congr
        end
      fun loop current accumulated [] = accumulated
        | loop current accumulated (premise :: rest) =
            let val next = apply premise current
                val (_, next_current) = boolSyntax.dest_eq (Thm.concl next)
                val accumulated = Thm.TRANS accumulated next
                  handle Feedback.HOL_ERR _ =>
                    raise ERR "cong"
                      ("CPC congruence rewrites do not compose; first=" ^
                       Library.term_to_string (Thm.concl accumulated) ^
                       "; next=" ^ Library.term_to_string (Thm.concl next))
            in loop next_current accumulated rest end
      fun quantified_cong () =
        case prems of
          [premise] =>
            let
              fun orient body =
                let val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
                in
                  if Term.aconv body left then premise
                  else if Term.aconv body right then Thm.SYM premise
                  else raise ERR "cong"
                    "quantified congruence premise does not rewrite its body"
                end
            in
              (let
                 val (variable, body) = boolSyntax.dest_forall source
               in
                 Drule.FORALL_EQ variable (orient body)
               end
               handle Feedback.HOL_ERR _ =>
                 let
                   val (variable, body) = boolSyntax.dest_exists source
                 in
                   Drule.EXISTS_EQ variable (orient body)
                 end)
            end
        | _ => raise ERR "cong"
            "quantified congruence expects one nontrivial premise"
      fun structural_cong () =
        let
          val consume_premises =
            case conclusion of NONE => true | SOME _ => false
          val remaining = ref prems
          fun exact_rewrite tm =
            let
              fun search skipped premises =
                case premises of
                  [] => NONE
                | premise :: rest =>
                let
                  val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
                  fun matched theorem =
                    let
                      val _ =
                        if consume_premises then
                          remaining := List.revAppend (skipped, rest)
                        else
                          ()
                    in
                      SOME theorem
                    end
                in
                  if Term.aconv tm left then
                    matched premise
                  else if Term.aconv tm right then
                    matched (Thm.SYM premise)
                  else
                    search (premise :: skipped) rest
                end
            in
              search [] (if consume_premises then !remaining else prems)
            end
          fun rewrite tm =
            case exact_rewrite tm of
              SOME theorem => theorem
            | NONE =>
                if Term.is_abs tm then
                  let val (variable, body) = Term.dest_abs tm
                  in Thm.ABS variable (rewrite body) end
                else
                  let val (rator, rand) = Term.dest_comb tm
                  in Thm.MK_COMB (rewrite rator, rewrite rand) end
                  handle Feedback.HOL_ERR _ => Thm.REFL tm
          val result = rewrite source
          val (left, right) = boolSyntax.dest_eq (Thm.concl result)
          val _ = not (Term.aconv left right) orelse
            raise ERR "cong" "structural congruence made no progress"
          val _ =
            case conclusion of
              SOME _ => ()
            | NONE =>
                if List.null (!remaining) then
                  ()
                else
                  raise ERR "cong"
                    "structural congruence left an unused premise"
        in
          result
        end
      fun targeted_cong () =
        let
          val target =
            case conclusion of
              SOME target => target
            | NONE => raise ERR "cong"
                "target-guided congruence needs a certificate conclusion"
          fun exact_rewrite left right premises =
            case premises of
              [] => NONE
            | premise :: rest =>
                let
                  val (prem_left, prem_right) =
                    boolSyntax.dest_eq (Thm.concl premise)
                in
                  if Term.aconv left prem_left andalso
                     Term.aconv right prem_right
                  then SOME premise
                  else if Term.aconv left prem_right andalso
                          Term.aconv right prem_left
                  then SOME (Thm.SYM premise)
                  else exact_rewrite left right rest
                end
          fun rewrite left right =
            if Term.aconv left right then Thm.REFL left
            else
              case exact_rewrite left right prems of
                SOME theorem => theorem
              | NONE =>
                  if Term.is_abs left andalso Term.is_abs right then
                    let
                      val (left_var, left_body) = Term.dest_abs left
                      val (right_var, right_body) = Term.dest_abs right
                      val _ = Term.aconv left_var right_var orelse
                        raise ERR "cong"
                          "target-guided congruence changed a binder"
                    in
                      Thm.ABS left_var (rewrite left_body right_body)
                    end
                  else
                    let
                      val (left_rator, left_rand) = Term.dest_comb left
                      val (right_rator, right_rand) = Term.dest_comb right
                    in
                      Thm.MK_COMB
                        (rewrite left_rator right_rator,
                         rewrite left_rand right_rand)
                    end
                    handle Feedback.HOL_ERR _ => raise ERR "cong"
                      "target-guided congruence cannot reconstruct conclusion"
          val (target_left, target_right) = boolSyntax.dest_eq target
        in
          if Term.aconv source target_left then
            rewrite target_left target_right
          else if Term.aconv source target_right then
            Thm.SYM (rewrite target_right target_left)
          else raise ERR "cong"
            "certificate conclusion does not contain the congruence source"
        end
      fun sequential_cong () =
        case prems of
          [] => Thm.REFL source
        | premise :: rest =>
            let
              val first = apply premise source
              val (_, first_current) = boolSyntax.dest_eq (Thm.concl first)
            in loop first_current first rest end
      fun matches_conclusion replay =
        let
          val result = replay ()
        in
          case conclusion of
            NONE => result
          | SOME target =>
              if Term.aconv (Thm.concl result) target then result
              else raise ERR "cong"
                "congruence strategy does not match certificate conclusion"
        end
      fun fallback_cong () =
        matches_conclusion structural_cong
        handle Feedback.HOL_ERR _ => matches_conclusion sequential_cong
    in
      matches_conclusion quantified_cong
      handle Feedback.HOL_ERR _ => matches_conclusion targeted_cong
      handle Feedback.HOL_ERR _ => fallback_cong ()
    end

  (* Exact compatibility is about the erased syntax topology, never the
     diagnostic source label carried by a conjunction.  Atomic nodes match
     only when both sides prove that no conjunction boundary was erased. *)
  fun provenance_topology_compatible left right =
    let
      fun lists [] [] = true
        | lists (x :: xs) (y :: ys) =
            provenance_topology_compatible x y andalso lists xs ys
        | lists _ _ = false
    in
      case (left, right) of
        (AtomicProvenance, other) =>
          definitely_no_conjunction other
      | (other, AtomicProvenance) =>
          definitely_no_conjunction other
      | (ApplicationProvenance (_, left_operands),
         ApplicationProvenance (_, right_operands)) =>
          (* Term.aconv at the candidate occurrence already proves that the
             elaborated HOL operators agree.  Raw CPC aliases and semantic
             replay constructors can give that same operator different
             diagnostic names, so occurrence compatibility is deliberately
             about retained child topology, not those source labels. *)
          lists left_operands right_operands
      | (BinderProvenance (_, left_body),
         BinderProvenance (_, right_body)) =>
          provenance_topology_compatible left_body right_body
      | (EqualityProvenance (left_lhs, left_rhs),
         EqualityProvenance (right_lhs, right_rhs)) =>
          provenance_topology_compatible left_lhs right_lhs andalso
          provenance_topology_compatible left_rhs right_rhs
      | (ConjunctionProvenance (_, left_operands),
         ConjunctionProvenance (_, right_operands)) =>
          lists left_operands right_operands
      | _ => false
    end

  (* CPC congruence uses deterministic left-to-right preorder.  Resolve that
     occurrence once over the exact located tree, and lift the selected
     equality through the same path with kernel congruence.  Thus the theorem
     and the replacement provenance cannot disagree about which
     alpha-equivalent occurrence was rewritten. *)
  fun replay_exact_cong_result conclusion
      (source : located_term) (premise_steps : replayed_step list) =
    let
      (* Keep the parsed source's full occurrence tree.  Even a constructor
         that is conjunction-free before rewriting can contain the exact
         occurrence replaced by a conjunction-bearing endpoint.  Live step
         results may compact proven conjunction-free shells, but parsed CONG
         arguments must retain their constructor path to justify that lift. *)
      datatype occurrence_rewrite =
          OccurrenceAbsent
        | OccurrenceBlocked of string
        | OccurrenceRewritten of located_term * Thm.thm

      fun split_conjunction n term =
        if n = 1 then [term]
        else if n > 1 then
          let val (left, right) = boolSyntax.dest_conj term in
            left :: split_conjunction (n - 1) right
          end
        else raise ERR "cong_provenance"
          "conjunction provenance has no operands"

      fun mk_conjunction terms =
        case terms of
          [] => raise ERR "cong_provenance"
              "empty conjunction occurrence"
        | [term] => term
        | term :: rest => boolSyntax.mk_conj
            (term, mk_conjunction rest)

      fun binder_body head term =
        if head = "forall" then #2 (boolSyntax.dest_forall term)
        else if head = "exists" then #2 (boolSyntax.dest_exists term)
        else #2 (Term.dest_abs term)

      fun rebuild_binder head term body =
        if head = "forall" then
          boolSyntax.mk_forall (#1 (boolSyntax.dest_forall term), body)
        else if head = "exists" then
          boolSyntax.mk_exists (#1 (boolSyntax.dest_exists term), body)
        else Term.mk_abs (#1 (Term.dest_abs term), body)

      fun checked_endpoints where_ theorem old replacement =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
            handle Feedback.HOL_ERR holerr =>
              raise ERR "cong_provenance"
                (where_ ^ " did not produce an equality theorem; theorem=" ^
                 Library.term_to_string (Thm.concl theorem) ^ "; " ^
                 Feedback.message_of holerr)
        in
          if Term.aconv left old andalso Term.aconv right replacement then
            theorem
          else raise ERR "cong_provenance"
            (where_ ^ " produced endpoints different from its exact path; " ^
             "source=" ^ Library.term_to_string old ^
             "; replacement=" ^ Library.term_to_string replacement ^
             "; theorem=" ^ Library.term_to_string (Thm.concl theorem))
        end

      fun lift_context parent rebuild child_theorem =
        let
          val (old_child, new_child) =
            boolSyntax.dest_eq (Thm.concl child_theorem)
          val hole = Term.variant
            (Term.free_vars parent @
             Term.free_vars (Thm.concl child_theorem))
            (Term.mk_var ("cpc_cong_hole", Term.type_of old_child))
          val old_parent = rebuild old_child
          val _ = Term.aconv old_parent parent orelse
            raise ERR "cong_provenance"
              "occurrence context does not rebuild its source"
          val context = Term.mk_abs (hole, rebuild hole)
          val lifted = Conv.CONV_RULE
            (Conv.TOP_DEPTH_CONV Thm.BETA_CONV)
            (Thm.AP_TERM context child_theorem)
        in
          checked_endpoints "lifted occurrence" lifted parent
            (rebuild new_child)
        end

      fun term_has_occurrence candidate term =
        Option.isSome (replace_first candidate candidate term)

      fun rewrite_atomic term candidate replacement replacement_provenance
          oriented =
        if definitely_no_conjunction replacement_provenance then
          let
            fun search current =
              if Term.aconv current candidate then
                OccurrenceRewritten
                  ({term = replacement, provenance = AtomicProvenance},
                   checked_endpoints "atomic root occurrence" oriented
                     current replacement)
              else if Term.is_abs current then
                let
                  val (variable, body) = Term.dest_abs current
                in
                  case search body of
                    OccurrenceAbsent => OccurrenceAbsent
                  | OccurrenceBlocked reason => OccurrenceBlocked reason
                  | OccurrenceRewritten
                      ({term = body', ...}, body_theorem) =>
                      let
                        val term' = Term.mk_abs (variable, body')
                        val theorem = Thm.ABS variable body_theorem
                          handle Feedback.HOL_ERR holerr =>
                            raise ERR "cong_provenance"
                              ("atomic binder lift failed; body=" ^
                               Library.term_to_string
                                 (Thm.concl body_theorem) ^ "; " ^
                               Feedback.message_of holerr)
                      in
                        OccurrenceRewritten
                          ({term = term', provenance = AtomicProvenance},
                           checked_endpoints "atomic binder occurrence"
                             theorem current term')
                      end
                end
              else
                (case Lib.total Term.dest_comb current of
                   NONE => OccurrenceAbsent
                 | SOME (operator, argument) =>
                  case search operator of
                    OccurrenceBlocked reason => OccurrenceBlocked reason
                  | OccurrenceRewritten
                      ({term = operator', ...}, operator_theorem) =>
                      let
                        val term' = Term.mk_comb (operator', argument)
                        val theorem = Thm.MK_COMB
                          (operator_theorem, Thm.REFL argument)
                          handle Feedback.HOL_ERR holerr =>
                            raise ERR "cong_provenance"
                              ("atomic operator lift failed; operator=" ^
                               Library.term_to_string
                                 (Thm.concl operator_theorem) ^
                               "; argument=" ^
                               Library.term_to_string argument ^ "; " ^
                               Feedback.message_of holerr)
                      in
                        OccurrenceRewritten
                          ({term = term', provenance = AtomicProvenance},
                           checked_endpoints "atomic operator occurrence"
                             theorem current term')
                      end
                  | OccurrenceAbsent =>
                      (case search argument of
                         OccurrenceAbsent => OccurrenceAbsent
                       | OccurrenceBlocked reason =>
                           OccurrenceBlocked reason
                       | OccurrenceRewritten
                           ({term = argument', ...}, argument_theorem) =>
                           let
                             val term' = Term.mk_comb (operator, argument')
                             val theorem = Thm.MK_COMB
                               (Thm.REFL operator, argument_theorem)
                               handle Feedback.HOL_ERR holerr =>
                                 raise ERR "cong_provenance"
                                   ("atomic argument lift failed; operator=" ^
                                    Library.term_to_string operator ^
                                    "; argument=" ^
                                    Library.term_to_string
                                      (Thm.concl argument_theorem) ^ "; " ^
                                    Feedback.message_of holerr)
                           in
                             OccurrenceRewritten
                               ({term = term',
                                 provenance = AtomicProvenance},
                                checked_endpoints
                                  "atomic argument occurrence" theorem
                                  current term')
                           end))
                handle Feedback.HOL_ERR holerr =>
                  OccurrenceBlocked
                    ("atomic traversal failed at " ^
                     Library.term_to_string current ^ "; " ^
                     Feedback.message_of holerr)
          in
            search term
          end
        else if term_has_occurrence candidate term then
          OccurrenceBlocked
            "opaque conjunction-free occurrence would gain a conjunction"
        else OccurrenceAbsent

      fun rewrite_children parent terms provenances rebuild_term
          rebuild_provenance candidate candidate_provenance replacement
          replacement_provenance oriented =
        let
          fun scan _ _ [] [] = OccurrenceAbsent
            | scan term_prefix provenance_prefix
                (term :: term_rest) (provenance :: provenance_rest) =
                (case rewrite_occurrence term provenance candidate
                    candidate_provenance replacement replacement_provenance
                    oriented of
                   OccurrenceAbsent =>
                     scan (term :: term_prefix)
                       (provenance :: provenance_prefix)
                       term_rest provenance_rest
                 | OccurrenceBlocked reason => OccurrenceBlocked reason
                 | OccurrenceRewritten
                     ({term = term', provenance = provenance'}, theorem) =>
                     let
                       val terms' = List.rev term_prefix @
                         term' :: term_rest
                       val provenances' = List.rev provenance_prefix @
                         provenance' :: provenance_rest
                       val parent' = rebuild_term terms'
                       val lifted = lift_context parent
                         (fn child => rebuild_term
                           (List.rev term_prefix @ child :: term_rest))
                         theorem
                     in
                       OccurrenceRewritten
                         ({term = parent',
                           provenance =
                             rebuild_provenance provenances'},
                          checked_endpoints "child occurrence" lifted parent
                            parent')
                     end)
            | scan _ _ _ _ = OccurrenceBlocked
                "occurrence children do not align with the elaborated term"
        in
          scan [] [] terms provenances
        end

      and rewrite_occurrence term provenance candidate
          candidate_provenance replacement replacement_provenance oriented =
        if Term.aconv term candidate andalso
           provenance_topology_compatible provenance candidate_provenance
        then
          OccurrenceRewritten
            ({term = replacement, provenance = replacement_provenance},
             checked_endpoints "root occurrence" oriented term replacement)
        else
          (case provenance of
             ConjunctionProvenance (_, operands) =>
               let
                 val terms = split_conjunction
                   (List.length operands) term
               in
                 rewrite_children term terms operands mk_conjunction
                   (fn children =>
                     ConjunctionProvenance
                       (CongruenceConjunction, children))
                   candidate candidate_provenance replacement
                   replacement_provenance oriented
               end
           | EqualityProvenance (left, right) =>
               let
                 val (left_term, right_term) = boolSyntax.dest_eq term
                 fun rebuild_term [left', right'] =
                       boolSyntax.mk_eq (left', right')
                   | rebuild_term _ = raise ERR "cong_provenance"
                       "equality occurrence children are malformed"
                 fun rebuild_provenance [left', right'] =
                       EqualityProvenance (left', right')
                   | rebuild_provenance _ =
                       UnavailableProvenance
                         "equality provenance children are malformed"
               in
                 rewrite_children term [left_term, right_term]
                   [left, right] rebuild_term rebuild_provenance
                   candidate candidate_provenance replacement
                   replacement_provenance oriented
               end
           | ApplicationProvenance (head, operands) =>
               let
                 val (operator, arguments) = boolSyntax.strip_comb term
                 fun rebuild_term children =
                   Term.list_mk_comb (operator, children)
                 fun rebuild_provenance children =
                   ApplicationProvenance (head, children)
                 fun arguments_result () =
                     rewrite_children term arguments operands rebuild_term
                       rebuild_provenance candidate candidate_provenance
                       replacement replacement_provenance oriented
               in
                 if definitely_no_conjunction provenance andalso
                    definitely_no_conjunction candidate_provenance andalso
                    definitely_no_conjunction replacement_provenance
                 then
                   (* Raw CPC applications may be n-ary while their HOL
                      elaboration is nested binary.  Once all three trees
                      are proved conjunction-free, those erased boundaries
                      are semantically irrelevant: use the kernel term's
                      deterministic preorder and compact the rewritten
                      application to Atomic.  A conjunction-bearing source
                      or replacement still takes the exact structured path
                      below, so this case cannot guess an and boundary. *)
                   rewrite_atomic term candidate replacement
                     replacement_provenance oriented
                 else arguments_result ()
               end
           | BinderProvenance (head, body) =>
               let
                 val body_term = binder_body head term
               in
                 case rewrite_occurrence body_term body candidate
                     candidate_provenance replacement
                     replacement_provenance oriented of
                   OccurrenceAbsent => OccurrenceAbsent
                 | OccurrenceBlocked reason => OccurrenceBlocked reason
                 | OccurrenceRewritten
                     ({term = body', provenance = body_provenance}, theorem) =>
                     let
                       val term' = rebuild_binder head term body'
                       val variable =
                         if head = "forall" then
                           #1 (boolSyntax.dest_forall term)
                         else if head = "exists" then
                           #1 (boolSyntax.dest_exists term)
                         else #1 (Term.dest_abs term)
                       (* Quantifier congruence must deliberately bind the
                          free body variable on both sides.  A generic beta
                          context is capture-avoiding and would rename the
                          quantifier, leaving that variable free. *)
                       val lifted =
                         if head = "forall" then
                           Drule.FORALL_EQ variable theorem
                         else if head = "exists" then
                           Drule.EXISTS_EQ variable theorem
                         else Thm.ABS variable theorem
                       val _ = profile_event
                         ("CPC(cong:binder/" ^ head ^ ")")
                     in
                       OccurrenceRewritten
                         ({term = term',
                           provenance =
                             BinderProvenance (head, body_provenance)},
                          checked_endpoints "binder occurrence" lifted term
                            term')
                     end
               end
           | AtomicProvenance =>
               if definitely_no_conjunction candidate_provenance then
                 rewrite_atomic term candidate replacement
                   replacement_provenance oriented
               else OccurrenceAbsent
           | UnavailableProvenance reason =>
               if term_has_occurrence candidate term then
                 OccurrenceBlocked
                   ("source occurrence unavailable: " ^ reason)
               else OccurrenceAbsent
           | AmbiguousProvenance reason =>
               if term_has_occurrence candidate term then
                 OccurrenceBlocked
                   ("source occurrence ambiguous: " ^ reason)
               else OccurrenceAbsent)
          handle Feedback.HOL_ERR holerr =>
            OccurrenceBlocked
              ("occurrence traversal failed at " ^
               Library.term_to_string term ^ " [" ^
               provenance_shape provenance ^ "]; " ^
               Feedback.message_of holerr)

      fun expose_step (premise_step : replayed_step) =
        let
          val theorem = step_theorem premise_step
          val preserve_reflexive_occurrence =
            case (Lib.total boolSyntax.dest_eq (Thm.concl theorem),
                  step_provenance premise_step) of
              (SOME (left, right),
               EqualityProvenance
                 (left_provenance, right_provenance)) =>
                Term.aconv left right andalso
                left_provenance <> right_provenance
            | _ => false
          val exposed = if preserve_reflexive_occurrence then theorem
            else expose_true_equality theorem
          val use_exposed = boolSyntax.is_eq (Thm.concl exposed)
          val provenance =
            if not use_exposed then step_provenance premise_step
            else
              (case (Lib.total boolSyntax.dest_eq (Thm.concl theorem),
                     step_provenance premise_step) of
                 (SOME (left, right), EqualityProvenance
                    (left_provenance, right_provenance)) =>
                   if Term.aconv left boolSyntax.T then right_provenance
                   else if Term.aconv right boolSyntax.T then left_provenance
                   else step_provenance premise_step
               | _ => step_provenance premise_step)
        in
          if use_exposed then
            {rule_name = #rule_name premise_step,
             result = exact_result provenance exposed}
          else premise_step
        end

      fun nontrivial (premise_step : replayed_step) =
        if Term.aconv (Thm.concl (step_theorem premise_step))
             boolSyntax.T then false
        else
          let val (left, right) = boolSyntax.dest_eq
            (Thm.concl (step_theorem premise_step))
          in
            not (Term.aconv left right) orelse
            (case step_provenance premise_step of
               EqualityProvenance
                 (left_provenance, right_provenance) =>
                 left_provenance <> right_provenance
             | _ => false)
          end
          handle Feedback.HOL_ERR _ => true

      fun apply_premise
          (premise_step : replayed_step, current : located_term) =
        let
          val theorem = step_theorem premise_step
          val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
          val (left_provenance, right_provenance) =
            case step_provenance premise_step of
              EqualityProvenance pair => pair
            | UnavailableProvenance reason =>
                raise ERR "cong_provenance"
                  ("congruence equality unavailable: " ^ reason)
            | AmbiguousProvenance reason =>
                raise ERR "cong_provenance"
                  ("congruence equality ambiguous: " ^ reason)
            | _ => raise ERR "cong_provenance"
                "premise lacks equality occurrence provenance"
          fun apply candidate candidate_provenance replacement
              replacement_provenance oriented =
            rewrite_occurrence (#term current) (#provenance current)
              candidate candidate_provenance replacement
              replacement_provenance oriented
        in
          case apply left left_provenance right right_provenance theorem of
            OccurrenceRewritten result =>
              (profile_event "CPC(cong:exact/rewrite)"; result)
          | OccurrenceBlocked reason =>
              raise ERR "cong_provenance"
                ("left occurrence rewrite blocked for " ^
                 Library.term_to_string (Thm.concl theorem) ^ "; " ^
                 reason)
          | OccurrenceAbsent =>
              (case apply right right_provenance left left_provenance
                  (Thm.SYM theorem) of
                 OccurrenceRewritten result =>
                   (profile_event "CPC(cong:exact/rewrite)"; result)
               | OccurrenceBlocked reason =>
                   raise ERR "cong_provenance"
                     ("right occurrence rewrite blocked for " ^
                      Library.term_to_string (Thm.concl theorem) ^ "; " ^
                      reason)
               | OccurrenceAbsent => raise ERR "cong_provenance"
                   ("premise does not rewrite an exact source occurrence; " ^
                    "source=" ^ Library.term_to_string (#term current) ^
                    "; source-provenance=" ^
                    provenance_shape (#provenance current) ^
                    "; premise=" ^
                    Library.term_to_string (Thm.concl theorem) ^
                    "; premise-provenance=" ^
                    provenance_shape (step_provenance premise_step)))
        end

      val rewrite_steps = List.filter nontrivial
        (List.map expose_step premise_steps)
      fun compose (premise_step, (current, accumulated)) =
        let
          val (next, rewrite_theorem) =
            apply_premise (premise_step, current)
          val theorem = Thm.TRANS accumulated rewrite_theorem
            handle Feedback.HOL_ERR holerr =>
              raise ERR "cong_provenance"
                ("exact congruence rewrites do not compose: " ^
                 Feedback.message_of holerr)
        in
          (next, theorem)
        end

      (* Structural CONG visits source occurrences in preorder and consumes
         the first still-live premise matching each node.  Order the exact
         premise applications by that same topology-aware traversal; the
         subsequent rewrite and kernel lifting are still performed by the
         single resolver above, so path selection cannot diverge. *)
      fun structural_step current remaining =
        let
          fun root_match term provenance (_, premise_step) =
            let
              val (left, right) = boolSyntax.dest_eq
                (Thm.concl (step_theorem premise_step))
              val (left_provenance, right_provenance) =
                case step_provenance premise_step of
                  EqualityProvenance pair => pair
                | _ => raise ERR "cong_provenance"
                    "structural congruence premise lacks exact endpoints"
            in
              (Term.aconv term left andalso
               provenance_topology_compatible provenance left_provenance)
              orelse
              (Term.aconv term right andalso
               provenance_topology_compatible provenance right_provenance)
            end
            handle Feedback.HOL_ERR _ => false
          fun atomic_match term (_, premise_step) =
            let
              val (left, right) = boolSyntax.dest_eq
                (Thm.concl (step_theorem premise_step))
              val (left_provenance, right_provenance) =
                case step_provenance premise_step of
                  EqualityProvenance pair => pair
                | _ => raise ERR "cong_provenance"
                    "structural congruence premise lacks exact endpoints"
            in
              (definitely_no_conjunction left_provenance andalso
               definitely_no_conjunction right_provenance) andalso
              (term_has_occurrence left term orelse
               term_has_occurrence right term)
            end
            handle Feedback.HOL_ERR _ => false
          fun first predicate = List.find predicate remaining
          fun descend term provenance =
            case first (root_match term provenance) of
              SOME indexed => SOME indexed
            | NONE =>
                (case provenance of
                   ConjunctionProvenance (_, operands) =>
                     descend_list
                       (split_conjunction (List.length operands) term)
                       operands
                 | EqualityProvenance (left, right) =>
                     let val (left_term, right_term) = boolSyntax.dest_eq term
                     in descend_list [left_term, right_term] [left, right] end
                 | ApplicationProvenance (_, operands) =>
                     let
                       val (operator, arguments) = boolSyntax.strip_comb term
                     in
                       (case first (atomic_match operator) of
                          SOME indexed => SOME indexed
                        | NONE => descend_list arguments operands)
                     end
                 | BinderProvenance (head, body) =>
                     descend (binder_body head term) body
                 | AtomicProvenance => first (atomic_match term)
                 | UnavailableProvenance _ => NONE
                 | AmbiguousProvenance _ => NONE)
          and descend_list [] [] = NONE
            | descend_list (term :: terms)
                (provenance :: provenances) =
                (case descend term provenance of
                   SOME indexed => SOME indexed
                 | NONE => descend_list terms provenances)
            | descend_list _ _ = NONE
        in
          descend (#term current) (#provenance current)
        end

      fun remove_index wanted entries =
        List.filter (fn (index, _) => index <> wanted) entries

      fun structural_fold current accumulated remaining =
        case remaining of
          [] => (current, accumulated)
        | _ =>
            (case structural_step current remaining of
               NONE => raise ERR "cong_provenance"
                 "structural congruence left an exact premise unused"
             | SOME (index, premise_step) =>
                 let
                   val (next, rewrite_theorem) =
                     apply_premise (premise_step, current)
                   val theorem = Thm.TRANS accumulated rewrite_theorem
                 in
                   structural_fold next theorem
                     (remove_index index remaining)
                 end)

      val indexed_steps = ListPair.zip
        (List.tabulate (List.length rewrite_steps, Lib.I), rewrite_steps)
      val (result, theorem) =
        (structural_fold source (Thm.REFL (#term source)) indexed_steps
         handle Feedback.HOL_ERR structural_error =>
           (List.foldl compose
              (source, Thm.REFL (#term source)) rewrite_steps
            handle Feedback.HOL_ERR sequential_error =>
              raise ERR "cong_provenance"
                ("structural exact route: " ^
                 Feedback.message_of structural_error ^
                 "; sequential exact route: " ^
                 Feedback.message_of sequential_error)))
      val _ =
        case conclusion of
          NONE => ()
        | SOME target =>
            if Term.aconv (Thm.concl theorem) target then ()
            else raise ERR "cong"
              "exact congruence differs from the certificate conclusion"
      val provenance = EqualityProvenance
        (#provenance source, #provenance result)
    in
      exact_result provenance theorem
    end
  (* Discharge [prems] against a theory prover by proving the implication
     they guard, then eliminating them. *)
  fun prove_from_prems prove prems target =
    Drule.LIST_MP prems
      (prove (boolSyntax.list_mk_imp (List.map Thm.concl prems, target)))

  (* Arithmetic procedures normally regard free variables as their atoms, but
     reject some compound terms even when those terms are semantically opaque
     to the certificate step.  Abstract every maximal selected atom uniformly
     across premises and target, prove the resulting implication, and then
     instantiate the fresh variables back.  INST and LIST_MP keep this wholly
     proof-producing; the selector describes a term class, not recorded proof
     shapes. *)
  fun prove_from_prems_abstracting prove is_atom prems target =
    let
      fun insert tm atoms =
        if List.exists (Term.aconv tm) atoms then atoms else tm :: atoms
      fun collect tm atoms =
        if is_atom tm then insert tm atoms
        else
          (case Lib.total Term.dest_comb tm of
             SOME (operator, operand) =>
               collect operand (collect operator atoms)
           | NONE =>
               (case Lib.total Term.dest_abs tm of
                  SOME (_, body) => collect body atoms
                | NONE => atoms))
      val atoms = List.foldl
        (fn (theorem, accumulated) =>
          collect (Thm.concl theorem) accumulated)
        (collect target []) prems
      val _ = List.null atoms andalso
        raise ERR "prove_from_prems_abstracting" "no selected atoms"
      val replacements = List.map
        (fn atom => (Term.genvar (Term.type_of atom), atom)) atoms
      val abstraction = List.map
        (fn (variable, atom) => {redex = atom, residue = variable})
        replacements
      fun abstract tm = Term.subst abstraction tm
      val abstract_implication = boolSyntax.list_mk_imp
        (List.map (abstract o Thm.concl) prems, abstract target)
      val abstract_theorem = prove abstract_implication
        handle Feedback.HOL_ERR holerr =>
          raise ERR "prove_from_prems_abstracting"
            ("could not prove abstract implication " ^
             Library.term_to_string abstract_implication ^ "; " ^
             Feedback.message_of holerr)
      val concrete_theorem = Thm.INST
        (List.map (fn (variable, atom) =>
          {redex = variable, residue = atom}) replacements)
        abstract_theorem
    in
      Drule.LIST_MP prems concrete_theorem
    end

  fun canonical_term target =
    boolSyntax.rhs (Thm.concl (SmtReplayCanon.cpc_canon_conv target))

  fun canonical_operand target = boolSyntax.rhs
    (Thm.concl (SmtReplayCanon.cpc_operand_canon_conv target))

  fun canonical_conclusion conclusion = Option.map canonical_term conclusion

  (* Normalize the certificate conclusion with 'canon', check that the
     replayed result matches it, and map the result back to the conclusion
     the certificate declared.  The aconv check is the security-relevant
     step, so every restoration rung shares this one implementation. *)
  fun restore_with canon what name conclusion theorem =
    case conclusion of
      NONE => theorem
    | SOME target =>
        let
          val target_norm = canon target
          val normalized_target = boolSyntax.rhs (Thm.concl target_norm)
          val _ = Term.aconv (Thm.concl theorem) normalized_target orelse
            raise ERR name
              (what ^ " result differs from the certificate conclusion; " ^
               "result=" ^ Library.term_to_string (Thm.concl theorem) ^
               "; target=" ^ Library.term_to_string normalized_target)
        in
          Thm.EQ_MP (Thm.SYM target_norm) theorem
        end

  val restore_canonical_conclusion =
    restore_with SmtReplayCanon.cpc_canon_conv "canonical"

  fun canonical_premises prems =
    List.map SmtReplayCanon.cpc_canon_rule prems

  (* Transport an occurrence tree through the same canonical conversion used
     by a semantic replay route.  A recorded boundary survives only when
     canonicalizing each child independently produces the corresponding
     child of the route's actual normalized term. *)
  fun align_canonical_provenance canon original normalized provenance =
    let
      fun normalized_term term = boolSyntax.rhs (Thm.concl (canon term))
      fun split_conjunction n term =
        if n = 1 then [term]
        else
          let val (left, right) = boolSyntax.dest_conj term in
            left :: split_conjunction (n - 1) right
          end
      fun aligned_children originals normalizeds provenances =
        if List.length originals <> List.length normalizeds orelse
           List.length originals <> List.length provenances
        then raise ERR "canonical_provenance"
          "canonical occurrence children do not align"
        else ListPair.mapEq
          (fn ((old_term, new_term), child_provenance) =>
            let
              val expected = normalized_term old_term
              val _ = Term.aconv expected new_term orelse
                raise ERR "canonical_provenance"
                  "canonical child differs from the semantic route"
            in
              align_canonical_provenance canon old_term new_term
                child_provenance
            end)
          (ListPair.zip (originals, normalizeds), provenances)
    in
      if Term.aconv original normalized then provenance
      else
        (case provenance of
           ConjunctionProvenance (source, operands) =>
             let
               val n = List.length operands
               val originals = split_conjunction n original
               val normalizeds = split_conjunction n normalized
             in
               ConjunctionProvenance
                 (source, aligned_children originals normalizeds operands)
             end
         | EqualityProvenance (left, right) =>
             let
               val (original_left, original_right) =
                 boolSyntax.dest_eq original
               val (normalized_left, normalized_right) =
                 boolSyntax.dest_eq normalized
               val children =
                 (aligned_children [original_left, original_right]
                    [normalized_left, normalized_right] [left, right]
                  handle Feedback.HOL_ERR _ =>
                    (* cpc_canon_conv may deterministically orient an
                       equality.  Transport the endpoints through that same
                       swap instead of attaching the old order to the new
                       theorem. *)
                    aligned_children [original_right, original_left]
                      [normalized_left, normalized_right] [right, left])
             in
               case children of
                 [left', right'] => EqualityProvenance (left', right')
               | _ => raise ERR "canonical_provenance"
                   "canonical equality children are malformed"
             end
         | ApplicationProvenance (head, operands) =>
             if definitely_no_conjunction provenance andalso
                not (term_contains_conjunction normalized)
             then AtomicProvenance
             else let
               val (original_operator, originals) =
                 boolSyntax.strip_comb original
               val (normalized_operator, normalizeds) =
                 boolSyntax.strip_comb normalized
               val _ = Term.aconv original_operator normalized_operator orelse
                 raise ERR "canonical_provenance"
                   "canonical application operator changed"
             in
               ApplicationProvenance
                 (head, aligned_children originals normalizeds operands)
             end
         | BinderProvenance _ =>
             if definitely_no_conjunction provenance andalso
                not (term_contains_conjunction normalized)
             then AtomicProvenance
             else UnavailableProvenance
               "canonical binder transformation lacks exact child alignment"
         | AtomicProvenance =>
             if term_contains_conjunction normalized then
               UnavailableProvenance
                 "canonical atomic occurrence introduced a conjunction"
             else AtomicProvenance
         | UnavailableProvenance reason => UnavailableProvenance reason
         | AmbiguousProvenance reason => AmbiguousProvenance reason)
    end
    handle Feedback.HOL_ERR holerr => UnavailableProvenance
      ("canonical occurrence alignment failed: " ^
       Feedback.message_of holerr)

  fun prove_cast_arithmetic prems target =
    let
      (* Push casts through integer arithmetic first, so algebraically related
         casts share one abstract real atom.  Real linear arithmetic then sees
         the polynomial shell, and INST restores the exact division/floor
         terms without assuming anything about them. *)
      val target_normalization = SmtReplayCanon.cpc_term_canon_conv target
      val normalized_target =
        boolSyntax.rhs (Thm.concl target_normalization)
      val normalized_prems = List.map SmtReplayCanon.cpc_canon_rule prems
      val normalized_proof = prove_from_prems_abstracting
        RealField.REAL_ARITH intrealSyntax.is_real_of_int
        normalized_prems normalized_target
    in
      Thm.EQ_MP (Thm.SYM target_normalization) normalized_proof
    end

  (* Neutral arithmetic identities.  PURE_REWRITE_CONV builds its net when
     applied to the theorem list, so these nets are built once at load. *)
  val int_neutral_arithmetic =
    [integerTheory.INT_MUL_LZERO,
     integerTheory.INT_MUL_RZERO,
     integerTheory.INT_ADD_LID,
     integerTheory.INT_ADD_RID]

  val int_neutral_arithmetic_conv =
    Rewrite.PURE_REWRITE_CONV int_neutral_arithmetic

  val neutral_arithmetic_conv = Rewrite.PURE_REWRITE_CONV
    (int_neutral_arithmetic @
     [realTheory.REAL_MUL_LZERO,
      realTheory.REAL_MUL_RZERO,
      realTheory.REAL_ADD_LID,
      realTheory.REAL_ADD_RID])

  val ground_neutral_arithmetic_conv = Rewrite.PURE_REWRITE_CONV
    [integerTheory.INT_MUL_RZERO,
     integerTheory.INT_ADD_LID,
     integerTheory.INT_ADD_RID]

  (* cvc5 alternates between these definitionally equal integer spellings
     inside congruence sources and equality endpoints.  Keep one recursive,
     kernel-checked view so both terms follow the same semantic route. *)
  val cpc_integer_spelling_conv = Conv.QCONV
    (Rewrite.PURE_REWRITE_CONV
      [Conv.GSYM integerTheory.INT_NEG_LMUL,
       integerTheory.INT_MUL_LID,
       integerTheory.INT_LT_LE1,
       integerTheory.INT_GE,
       integerTheory.INT_ADD_LID,
       (* CPC rules may expose HOL's Euclidean operators after the
          translation-derived totalization identity has been consumed.
          These are representation aliases, not emitted constants. *)
       integerTheory.EDIV_DEF,
       integerTheory.EMOD_DEF])

  fun compose_normal_form_conv first second tm =
    let
      val canonical = first tm
      val canonical_tm = boolSyntax.rhs (Thm.concl canonical)
      val normalized = second canonical_tm
    in
      Thm.TRANS canonical normalized
    end

  val cpc_integer_normal_form_conv = compose_normal_form_conv
    SmtReplayCanon.cpc_canon_conv cpc_integer_spelling_conv

  (* CPC's total-division bounds theorem contains positive- and
     negative-divisor implications.  Ground divisor guards are semantic
     arithmetic, not definition unfolding; normalize them in their own rung
     so an omitted-conclusion EQ_RESOLVE need not weaken strong provenance. *)
  val cpc_ground_arithmetic_guard_conv = Conv.QCONV
    (bossLib.SIMP_CONV (bossLib.srw_ss ()) [])

  (* The only definition identities in the strong canonicalizer come from
     this proof's emitted-symbol records.  Build the rewrite net from that
     closed table, and record consumption only when one of its definitions
     actually changes the term. *)
  fun strong_cpc_canon_conv definitions =
    let
      val definition_identities =
        List.map SmtLib.emitted_definition_theorem definitions
      val definition_heads =
        List.map SmtLib.emitted_definition_head definitions
      val definition_conv =
        Rewrite.PURE_REWRITE_CONV definition_identities
      fun is_enabled head =
        List.exists (Term.same_const head) definition_heads
      fun contains_head head term =
        Lib.can (HolKernel.find_term (fn candidate =>
          Term.is_const candidate andalso
          Term.same_const candidate head)) term
      fun count_head head term =
        List.length (HolKernel.find_terms (fn candidate =>
          Term.is_const candidate andalso
          Term.same_const candidate head) term)
      fun unkeyed_heads term = List.mapPartial
        (fn ({replay_head, ...} : SmtLib.emitted_definition_spec) =>
          if not (is_enabled replay_head) andalso
             contains_head replay_head term then
            SOME (replay_head, count_head replay_head term)
          else NONE)
        (SmtLib.all_emitted_definition_specs ())
      fun require_unkeyed_heads_preserved heads term =
        if List.all (fn (head, count) => count_head head term = count)
            heads then ()
        else raise ERR "strong_cpc_canon_conv"
          "conversion changed an un-emitted replay head"
      fun unfold_emitted_definition current =
        let
          val theorem = definition_conv current
          val normalized = boolSyntax.rhs (Thm.concl theorem)
          val _ = not (Term.aconv current normalized) orelse
            raise Conv.UNCHANGED
          val () = profile_event "CPC(canon:translator-definition)"
        in theorem end
      fun finish current =
        if List.null (Term.free_vars current) then
          bossLib.SIMP_CONV (bossLib.srw_ss ())
            [HolSmtTheory.smt_rdiv_eq_div,
             intrealTheory.INT_FLOOR] current
        else bossLib.SIMP_CONV (bossLib.srw_ss ()) [] current
      fun arithmetic_decision current =
        let
          val normalization =
            SmtReplayCanon.arith_poly_norm_conversion current
          val normalized = boolSyntax.rhs (Thm.concl normalization)
          val decision =
            Drule.EQT_INTRO
              (simpLib.SIMP_PROVE (bossLib.srw_ss ())
                [] normalized)
            handle Feedback.HOL_ERR _ =>
              Drule.EQF_INTRO
                (simpLib.SIMP_PROVE (bossLib.srw_ss ())
                  []
                  (boolSyntax.mk_neg normalized))
        in
          Thm.TRANS normalization decision
        end
        handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED
             | Conv.UNCHANGED => raise Conv.UNCHANGED
      fun convert tm =
        let
          (* A CPC rule may introduce an auxiliary total operator (notably
             div_total in mod_total bounds) that the original translation
             did not emit.  Without the matching record, canonicalization
             must preserve its exact occurrence count. *)
          val unkeyed = unkeyed_heads tm
          (* This is a canonicalizer, so an already-canonical term is a
             successful reflexive result. *)
          val theorem = Conv.QCONV (SmtReplayCanon.compose
              [unfold_emitted_definition,
               SmtReplayCanon.cpc_operand_canon_conv,
               cpc_integer_spelling_conv,
               wordsLib.WORD_LOGIC_CONV,
               finish, arithmetic_decision]) tm
          val normalized = boolSyntax.rhs (Thm.concl theorem)
          val () = require_unkeyed_heads_preserved unkeyed normalized
        in
          theorem
        end
    in
      convert
    end

  fun restore_strong_canonical_conclusion canon name conclusion theorem =
    restore_with canon "strong canonical" name conclusion
      (Conv.CONV_RULE canon theorem)

  (* Canonicalization can discharge a premise completely.  Such a proof is
     logically neutral in the surrounding chain, but its hypotheses must
     still contribute to the result; a kernel conjunction projection carries
     them without depending on the premise's solver-specific spelling. *)
  fun retain_support kept support = Thm.CONJUNCT1 (Thm.CONJ kept support)

  fun retain_all theorem supports =
    List.foldl (fn (support, kept) => retain_support kept support)
      theorem supports

  fun is_reflexive_equality theorem =
    case Lib.total boolSyntax.dest_eq (Thm.concl theorem) of
      SOME (left, right) => Term.aconv left right
    | NONE => false

  fun is_reflexive_boolean_equality theorem =
    case Lib.total boolSyntax.dest_eq (Thm.concl theorem) of
      SOME (left, right) =>
        Type.compare (Term.type_of left, Type.bool) = EQUAL andalso
        Term.aconv left right
    | NONE => false

  fun replay_trans prems =
    case prems of
      [] => raise ERR "trans" "expected CPC equality premises"
    | first :: rest =>
        let
          fun attempt work = SOME (work ()) handle Feedback.HOL_ERR _ => NONE
          fun compose th accumulated =
            if Term.aconv (Thm.concl accumulated) boolSyntax.T then
              retain_support accumulated th
            else if Term.aconv (Thm.concl th) boolSyntax.T then
              retain_support th accumulated
            else if is_reflexive_equality accumulated then
              retain_support th accumulated
            else if is_reflexive_equality th then
              retain_support accumulated th
            else case attempt (fn () => Thm.TRANS accumulated th) of
              SOME result => result
            | NONE =>
              (case attempt (fn () => Thm.TRANS accumulated (Thm.SYM th)) of
                 SOME result => result
               | NONE =>
                 (case attempt (fn () => Thm.TRANS (Thm.SYM accumulated) th) of
                    SOME result => result
                  | NONE =>
                    (case attempt
                        (fn () =>
                          Thm.TRANS (Thm.SYM accumulated) (Thm.SYM th)) of
                       SOME result => result
                     | NONE => raise ERR "trans"
                         ("canonical CPC equality premises do not compose; " ^
                          "first=" ^ Library.thm_to_string accumulated ^
                          "; next=" ^ Library.thm_to_string th))))
        in
          List.foldl (fn (th, accumulated) => compose th accumulated)
            first rest
        end

  fun equality_endpoint side provenance =
    case provenance of
      EqualityProvenance (left, right) => if side = 0 then left else right
    | UnavailableProvenance reason => UnavailableProvenance
        ("trans equality endpoint unavailable: " ^ reason)
    | AmbiguousProvenance reason => AmbiguousProvenance
        ("trans equality endpoint ambiguous: " ^ reason)
    | _ => UnavailableProvenance
        "trans premise lacks equality occurrence provenance"

  fun replay_trans_with_provenance
      (premise_steps : replayed_step list) =
    let
      fun attempt work = SOME (work ()) handle Feedback.HOL_ERR _ => NONE
      fun compose (next_step, (accumulated, accumulated_provenance)) =
        let
          val next = step_theorem next_step
          val next_provenance = step_provenance next_step
          fun endpoints accumulated_side next_side theorem =
            let
              val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
              fun exact_if_conjunction_free term provenance =
                case provenance of
                  UnavailableProvenance reason =>
                    conjunction_free_semantic_provenance reason term
                | AmbiguousProvenance reason =>
                    conjunction_free_semantic_provenance reason term
                | exact => exact
            in
              (theorem, EqualityProvenance
                (exact_if_conjunction_free left
                   (equality_endpoint accumulated_side
                     accumulated_provenance),
                 exact_if_conjunction_free right
                   (equality_endpoint next_side next_provenance)))
            end
        in
          if Term.aconv (Thm.concl accumulated) boolSyntax.T then
            (retain_support accumulated next, next_provenance)
          else if Term.aconv (Thm.concl next) boolSyntax.T then
            (retain_support next accumulated, accumulated_provenance)
          else if is_reflexive_equality accumulated then
            (retain_support next accumulated, next_provenance)
          else if is_reflexive_equality next then
            (retain_support accumulated next, accumulated_provenance)
          else
            case attempt (fn () => endpoints 0 1
                (Thm.TRANS accumulated next)) of
              SOME result => result
            | NONE =>
                (case attempt (fn () => endpoints 0 0
                    (Thm.TRANS accumulated (Thm.SYM next))) of
                   SOME result => result
                 | NONE =>
                     (case attempt (fn () => endpoints 1 1
                         (Thm.TRANS (Thm.SYM accumulated) next)) of
                        SOME result => result
                      | NONE => endpoints 1 0
                          (Thm.TRANS (Thm.SYM accumulated)
                            (Thm.SYM next))))
        end
    in
      case premise_steps of
        [] => raise ERR "trans" "expected CPC equality premises"
      | first :: rest => List.foldl compose
          (step_theorem first, step_provenance first) rest
    end

  (* Use canonical forms to recognize tautological support premises without
     replacing the theorem stored for the CPC step.  Later rules can depend
     on its exact shape (notably TRUE_ELIM consuming [T = p]). *)
  fun replay_canonical_trans strong_canon prems =
    let
      (* E1(b): this terminal is the general canonical-form procedure for
         CPC trans.  It derives totalization identities from this proof's
         emitted-symbol table and otherwise uses only general canonical
         conversions.  It is coverage-bearing, so it is never a fast path. *)
      fun canonical_view theorem = expose_true_equality
        (Conv.CONV_RULE (Conv.BINOP_CONV strong_canon) theorem)
        handle Feedback.HOL_ERR _ => theorem
             | Conv.UNCHANGED => theorem
      fun compose (next, accumulated) =
        (* A non-reflexive equality may normalize to [T] or [x = x], but
           it is still the bridge to the next endpoint in a TRANS chain.
           Only an originally reflexive theorem is neutral. *)
        if is_reflexive_equality accumulated then
          retain_support next accumulated
        else if is_reflexive_equality next then
          retain_support accumulated next
        else
          profile "CPC(rung:canonical_trans/canonical)" (fn () =>
            replay_trans
              [canonical_view accumulated, canonical_view next]) ()
    in
      case prems of
        [] => raise ERR "trans" "expected CPC equality premises"
      | first :: rest => List.foldl compose first rest
    end

  fun replay_canonical_trans_with_provenance strong_canon
      (premise_steps : replayed_step list) =
    let
      fun try work fallback =
        work () handle Feedback.HOL_ERR _ => fallback ()
                      | Conv.UNCHANGED => fallback ()
      fun compose (next_step, accumulated_result) =
        let
          val (accumulated, accumulated_provenance) = accumulated_result
          val next_result =
            (step_theorem next_step, step_provenance next_step)
          val (next, next_provenance) = next_result
          (* Canonicalize only the two candidate middle endpoints, prove the
             bridge between those exact terms, and compose the unmodified
             oriented premise theorems around it.  Whole-equality conversion
             can collapse a non-reflexive CPC bridge to T and lose which
             outer endpoint this TRANS route selected. *)
          fun canonical_bridge accumulated_side next_side =
            let
              val accumulated' = if accumulated_side = 1 then accumulated
                else Thm.SYM accumulated
              val next' = if next_side = 0 then next else Thm.SYM next
              val (_, middle_left) = boolSyntax.dest_eq
                (Thm.concl accumulated')
              val (middle_right, _) = boolSyntax.dest_eq (Thm.concl next')
              fun extend conv theorem =
                let
                  val current = boolSyntax.rhs (Thm.concl theorem)
                  val refinement = Conv.QCONV conv current
                in
                  Thm.TRANS theorem refinement
                end
              fun finish left_norm right_norm =
                let
                  val bridge = Thm.TRANS left_norm (Thm.SYM right_norm)
                  val theorem = Thm.TRANS accumulated'
                    (Thm.TRANS bridge next')
                  val provenance = EqualityProvenance
                    (equality_endpoint (1 - accumulated_side)
                       accumulated_provenance,
                     equality_endpoint (1 - next_side) next_provenance)
                in
                  (theorem, provenance)
                end
              fun refine [] _ = raise ERR "trans"
                    "canonical middle endpoints have distinct normal forms"
                | refine (conv :: rest) (left_norm, right_norm) =
                    let
                      val left_norm' = extend conv left_norm
                      val right_norm' = extend conv right_norm
                      val normalized_left = boolSyntax.rhs
                        (Thm.concl left_norm')
                      val normalized_right = boolSyntax.rhs
                        (Thm.concl right_norm')
                    in
                      if Term.aconv normalized_left normalized_right then
                        finish left_norm' right_norm'
                      else refine rest (left_norm', right_norm')
                    end
            in
              refine
                [SmtReplayCanon.cpc_canon_conv,
                 cpc_integer_spelling_conv,
                 strong_canon,
                 SmtReplayCanon.reorient_equality_conv]
                (Thm.REFL middle_left, Thm.REFL middle_right)
            end
          fun canonical_orientations () =
            try (fn () => canonical_bridge 1 0) (fn () =>
              try (fn () => canonical_bridge 1 1) (fn () =>
                try (fn () => canonical_bridge 0 0) (fn () =>
                  canonical_bridge 0 1)))
        in
          if is_reflexive_equality accumulated then
            (retain_support next accumulated, next_provenance)
          else if is_reflexive_equality next then
            (retain_support accumulated next, accumulated_provenance)
          else
            (* E1(b) general terminal.  Its deterministic normal-form
               procedure accumulates kernel equalities through the shared
               CPC and integer-spelling phases, the table-derived strong
               phase, and a final equality orientation.  An earlier match is
               a completed canonical comparison, not an optional cache route.
               The original endpoint theorems and provenance remain
               unchanged. *)
            profile
              "CPC(rung:canonical_trans/provenance-canonical)"
              canonical_orientations ()
        end
    in
      case premise_steps of
        [] => raise ERR "trans" "expected CPC equality premises"
      | first :: rest => List.foldl compose
          (step_theorem first, step_provenance first) rest
    end

  fun replay_eq_resolve prems =
    let
    in case prems of
      [left, right] =>
        if Term.aconv (Thm.concl left) boolSyntax.F then left
        else if Term.aconv (Thm.concl right) boolSyntax.F then right
        else if is_reflexive_boolean_equality right then
          retain_support left right
        else if is_reflexive_boolean_equality left then
          retain_support right left
        else
          (Thm.EQ_MP right left
           handle Feedback.HOL_ERR _ =>
             (Thm.EQ_MP (Thm.SYM right) left
              handle Feedback.HOL_ERR _ =>
                (Thm.EQ_MP left right
                handle Feedback.HOL_ERR _ =>
                  (Thm.EQ_MP (Thm.SYM left) right
                   handle Feedback.HOL_ERR _ =>
                     raise ERR "eq_resolve"
                       ("canonical premises do not rewrite one another; " ^
                        "left=" ^
                       Library.term_to_string (Thm.concl left) ^
                       "; right=" ^
                       Library.term_to_string (Thm.concl right))))))
    | _ => raise ERR "eq_resolve" "expected two CPC premises"
    end

  fun eq_resolve_result_provenance provenance =
    case provenance of
      ConjunctionProvenance (_, operands) =>
        ConjunctionProvenance (EqResolveConjunction, operands)
    | other => other

  fun equality_side_provenance side provenance =
    case provenance of
      EqualityProvenance (left, right) =>
        eq_resolve_result_provenance
          (if side = 0 then left else right)
    | UnavailableProvenance reason => UnavailableProvenance
        ("eq_resolve equality-side provenance unavailable: " ^ reason)
    | AmbiguousProvenance reason => AmbiguousProvenance
        ("eq_resolve equality-side provenance ambiguous: " ^ reason)
    | _ => UnavailableProvenance
        "eq_resolve premise lacks equality occurrence provenance"

  (* Mirror the kernel EQ_MP orientation exactly.  This is semantic
     propagation from the equality side actually selected, not a lookup by
     the result term. *)
  fun replay_eq_resolve_with_provenance
      ([left_step, right_step] : replayed_step list) =
    let
      val left = step_theorem left_step
      val right = step_theorem right_step
      fun occurrence_reflexive step =
        case step_provenance step of
          EqualityProvenance (left, right) => left = right
        | _ => true
    in
      if Term.aconv (Thm.concl left) boolSyntax.F then
        (left, step_provenance left_step)
      else if Term.aconv (Thm.concl right) boolSyntax.F then
        (right, step_provenance right_step)
      else if is_reflexive_boolean_equality right andalso
              occurrence_reflexive right_step then
        (retain_support left right, step_provenance left_step)
      else if is_reflexive_boolean_equality left andalso
              occurrence_reflexive left_step then
        (retain_support right left, step_provenance right_step)
      else
        ((Thm.EQ_MP right left,
          equality_side_provenance 1 (step_provenance right_step))
         handle Feedback.HOL_ERR _ =>
           ((Thm.EQ_MP (Thm.SYM right) left,
             equality_side_provenance 0 (step_provenance right_step))
            handle Feedback.HOL_ERR _ =>
              ((Thm.EQ_MP left right,
                equality_side_provenance 1 (step_provenance left_step))
               handle Feedback.HOL_ERR _ =>
                 (Thm.EQ_MP (Thm.SYM left) right,
                  equality_side_provenance 0
                    (step_provenance left_step)))))
    end
    | replay_eq_resolve_with_provenance _ =
        raise ERR "eq_resolve" "expected two CPC premises"

  (* EQ_RESOLVE sometimes connects propositions only after datatype/record
     canonicalization.  Keep the conversion equalities so the normalized
     proposition can be transported back to the exact side consumed by
     EQ_MP; normalizing both premise theorems would discard that link. *)
  fun replay_canonical_eq_resolve strong_canon prems =
    let
      fun attempt work = SOME (work ()) handle Feedback.HOL_ERR _ => NONE
      fun stage name work =
        work () handle Feedback.HOL_ERR holerr =>
          raise ERR "eq_resolve"
            (name ^ " failed: " ^ Feedback.message_of holerr)
      fun resolve canon proposition equality =
        let
          val (left, right) = stage "equality decomposition"
            (fn () => boolSyntax.dest_eq (Thm.concl equality))
          val proposition_norm =
            stage "proposition canonicalization" (fn () =>
              canon (Thm.concl proposition))
          val normalized_proposition =
            stage "normalized proposition extraction" (fn () =>
              boolSyntax.rhs (Thm.concl proposition_norm))
          val normalized_proof = stage "proposition transport" (fn () =>
            Thm.EQ_MP proposition_norm proposition)
          fun prove_side side =
            let
              val side_norm = canon side
              val normalized_side = boolSyntax.rhs (Thm.concl side_norm)
              val _ = Term.aconv normalized_proposition normalized_side orelse
                raise ERR "eq_resolve"
                  ("canonical proposition does not match equality side; " ^
                   "proposition=" ^
                   Library.term_to_string normalized_proposition ^
                   "; side=" ^ Library.term_to_string normalized_side)
            in
              Thm.EQ_MP (Thm.SYM side_norm) normalized_proof
            end
        in
          case attempt (fn () => Thm.EQ_MP equality (prove_side left)) of
            SOME theorem => theorem
          | NONE => Thm.EQ_MP (Thm.SYM equality) (prove_side right)
        end
    in
      case prems of
        [proposition, equality] =>
          (resolve SmtReplayCanon.cpc_operand_canon_conv
           proposition equality
           handle Feedback.HOL_ERR _ =>
             (resolve cpc_integer_normal_form_conv proposition equality
              handle Feedback.HOL_ERR _ =>
                (resolve cpc_ground_arithmetic_guard_conv
                   proposition equality
                 handle Feedback.HOL_ERR _ =>
                   resolve strong_canon proposition equality)))
      | _ => raise ERR "eq_resolve" "expected two CPC premises"
    end

  fun replay_canonical_eq_resolve_with_provenance canon
      ([proposition_step, equality_step] : replayed_step list) =
    let
      val proposition = step_theorem proposition_step
      val equality = step_theorem equality_step
      val (left, right) = boolSyntax.dest_eq (Thm.concl equality)
      val proposition_norm = canon (Thm.concl proposition)
      val normalized_proposition = boolSyntax.rhs
        (Thm.concl proposition_norm)
      val normalized_proof = Thm.EQ_MP proposition_norm proposition
      fun prove_side side =
        let
          val side_norm = canon side
          val normalized_side = boolSyntax.rhs (Thm.concl side_norm)
          val _ = Term.aconv normalized_proposition normalized_side orelse
            raise ERR "eq_resolve"
              "canonical proposition does not match equality side"
        in
          Thm.EQ_MP (Thm.SYM side_norm) normalized_proof
        end
    in
      ((Thm.EQ_MP equality (prove_side left),
        equality_side_provenance 1 (step_provenance equality_step))
       handle Feedback.HOL_ERR _ =>
         (Thm.EQ_MP (Thm.SYM equality) (prove_side right),
          equality_side_provenance 0 (step_provenance equality_step)))
    end
    | replay_canonical_eq_resolve_with_provenance _ _ =
        raise ERR "eq_resolve" "expected two CPC premises"
  (* cvc5's SYMM rule also preserves the negation of an equality.  HOL's
     Thm.SYM covers the equality form directly; derive the disequality form
     from the same premise rather than treating it as a trusted rewrite. *)
  fun replay_symm prems =
    let
      val premise = expect_one_premise "symm" prems
    in
      Thm.SYM premise
      handle Feedback.HOL_ERR _ =>
        let
          val (left, right) = boolSyntax.dest_eq
            (boolSyntax.dest_neg (Thm.concl premise))
        in metis_prove [premise]
          (boolSyntax.mk_neg (boolSyntax.mk_eq (right, left))) end
    end

  fun replay_symm_result ([premise_step] : replayed_step list) =
    let
      val premise = step_theorem premise_step
    in
      (let
         val theorem = Thm.SYM premise
         val provenance =
           case step_provenance premise_step of
             EqualityProvenance (left, right) =>
               EqualityProvenance (right, left)
           | UnavailableProvenance reason => UnavailableProvenance
               ("symm equality endpoints unavailable: " ^ reason)
           | AmbiguousProvenance reason => AmbiguousProvenance
               ("symm equality endpoints ambiguous: " ^ reason)
           | _ => UnavailableProvenance
               "symm premise lacks equality occurrence provenance"
       in
         exact_result provenance theorem
       end
       handle Feedback.HOL_ERR _ => unavailable_result
         "symm used disequality reconstruction without equality endpoints"
         (replay_symm [premise]))
    end
    | replay_symm_result _ =
        raise ERR "symm" "expected exactly one CPC premise"

  fun replay_contra prems =
    case prems of
      [left, right] =>
        if Term.aconv (Thm.concl left) boolSyntax.F then left
        else if Term.aconv (Thm.concl right) boolSyntax.F then right
        else Library.gen_contradiction (Thm.CONJ left right)
    | _ => raise ERR "contra" "expected a proposition and its negation"
  fun replay_false_intro prems =
    Drule.EQF_INTRO (expect_one_premise "false_intro" prems)

  fun replay_false_elim prems =
    Drule.EQF_ELIM (expect_one_premise "false_elim" prems)

  fun replay_true_elim prems =
    let val premise = expect_one_premise "true_elim" prems in
      if Term.aconv (Thm.concl premise) boolSyntax.T then premise
      else Drule.EQT_ELIM premise
    end

  fun replay_true_intro prems =
    Drule.EQT_INTRO (expect_one_premise "true_intro" prems)

  fun replay_evaluate conclusion args =
    let val arg = expect_one_arg "evaluate" args
        val th = bossLib.EVAL arg
    in
      case conclusion of
        NONE => th
      | SOME target =>
          if Term.aconv (Thm.concl th) target then th
          else raise ERR "evaluate"
            "CPC evaluate result differs from its declared conclusion"
    end

  fun conjunction_source_name ParsedConjunction = "parsed"
    | conjunction_source_name AndIntroConjunction = "and_intro"
    | conjunction_source_name ArithReductionConjunction =
        "arith_reduction"
    | conjunction_source_name EqResolveConjunction = "eq_resolve"
    | conjunction_source_name CongruenceConjunction = "congruence"

  fun replay_and_elim conclusion args (premise_step : replayed_step) =
    let
      val premise = step_theorem premise_step
      val conjunction = Thm.concl premise
      val (source, conjunct_provenances) =
        case step_provenance premise_step of
          ConjunctionProvenance (source, conjuncts) => (source, conjuncts)
        | UnavailableProvenance reason => raise ERR "and_elim"
            ("CPC and_elim provenance unavailable: " ^ reason)
        | AmbiguousProvenance reason => raise ERR "and_elim"
            ("CPC and_elim provenance ambiguous: " ^ reason)
        | _ => raise ERR "and_elim"
            "CPC and_elim premise has no conjunction occurrence provenance"
      val arity = List.length conjunct_provenances
      val _ = arity >= 2 orelse raise ERR "and_elim"
        "CPC and_elim conjunction provenance has fewer than two operands"
      fun split n term =
        if n = 1 then [term]
        else if n > 1 then
            let val (left, right) = boolSyntax.dest_conj term in
              left :: split (n - 1) right
            end
        else raise ERR "and_elim"
            "CPC conjunction provenance arity must be positive"
      val conjuncts = split arity conjunction
        handle Feedback.HOL_ERR _ => raise ERR "and_elim"
          ("CPC conjunction provenance arity " ^ Int.toString arity ^
           " does not match premise " ^
           Library.term_to_string conjunction)
      val index =
        Arbnum.toInt (numSyntax.dest_numeral (intSyntax.dest_injected
          (expect_one_arg "and_elim" args)))
      val conjunct = List.nth (conjuncts, index)
        handle Subscript => raise ERR "and_elim"
          ("CPC conjunction index " ^ Int.toString index ^
           " is outside parsed arity " ^ Int.toString arity ^
           " for premise " ^ Library.term_to_string conjunction)
      val selected_provenance = List.nth (conjunct_provenances, index)
        handle Subscript => raise ERR "and_elim"
          ("CPC conjunction provenance index " ^ Int.toString index ^
           " is outside arity " ^ Int.toString arity)
      val _ = profile_event ("CPC(and_elim:provenance/" ^
        conjunction_source_name source ^ ")")
      val _ = case conclusion of
          NONE => ()
        | SOME target =>
            if Term.aconv target conjunct then ()
            else raise ERR "and_elim"
              "declared CPC result differs from its indexed conjunct"
    in
      case Lib.total Library.conj_elim (premise, conjunct) of
        SOME theorem => (theorem, selected_provenance)
      | NONE => raise ERR "and_elim"
          "declared CPC result is not a conjunct of its premise"
    end

  fun tautology name target =
    profile "CPC(rung:rewrite/METIS)" Tactical.TAC_PROOF
      (([], target), metisLib.METIS_TAC [])
    handle Feedback.HOL_ERR _ =>
      profile "CPC(rung:rewrite/TAUT)" tautLib.TAUT_PROVE target
    handle Feedback.HOL_ERR _ =>
      raise ERR name "could not prove the captured CPC rewrite shape"

  fun xor_tautology target =
    Tactical.TAC_PROOF (([], target),
      Tactical.THEN
        (bossLib.SIMP_TAC (bossLib.srw_ss()) [HolSmtTheory.xor_def],
         tautLib.TAUT_TAC))

  fun tautological_consequence premise target =
    Thm.MP (tautLib.TAUT_PROVE
      (boolSyntax.mk_imp (Thm.concl premise, target))) premise

  fun tautological_consequences premises target =
    let
      val implication = List.foldr
        (fn (premise, body) => boolSyntax.mk_imp (Thm.concl premise, body))
        target premises
    in
      List.foldl (fn (premise, result) => Thm.MP result premise)
        (tautLib.TAUT_PROVE implication) premises
    end

  fun resolve_binary_disjunction prems target =
    (case prems of
      [disjunction_thm, negated_thm] =>
        let
          val (left, right) = boolSyntax.dest_disj (Thm.concl disjunction_thm)
          fun normalize_negated expected theorem =
            if Term.aconv (Thm.concl theorem) (boolSyntax.mk_neg expected) then
              theorem
            else raise ERR "resolution"
              "canonical negated literal does not match its pivot"
          fun resolve eliminated result =
            let
              val negated_thm = normalize_negated eliminated negated_thm
              val contradiction = Thm.MP negated_thm (Thm.ASSUME eliminated)
              val from_false = Thm.MP (Thm.SPEC result boolTheory.FALSITY)
                contradiction
              val from_result = Thm.ASSUME result
            in
              Thm.DISJ_CASES disjunction_thm from_false from_result
            end
          fun resolve_positive left_branch negated_right =
            let
              val positive = boolSyntax.dest_neg negated_right
              val _ = Term.aconv (Thm.concl negated_thm) positive orelse
                raise ERR "resolution" "positive literal does not match clause"
              val contradiction = Thm.MP (Thm.ASSUME negated_right) negated_thm
              val from_false = Thm.MP
                (Thm.SPEC left_branch boolTheory.FALSITY) contradiction
              val from_left = Thm.ASSUME left_branch
            in
              Thm.DISJ_CASES disjunction_thm from_left from_false
            end
        in
          if Term.aconv left target then
            (SOME (resolve_positive left right)
             handle Feedback.HOL_ERR _ => SOME (resolve right left))
          else if Term.aconv right target then SOME (resolve left right)
          else NONE
        end
    | _ => NONE)
    handle _ => NONE

  (* A resolution chain may close directly on complementary unit clauses.
     This is a primitive kernel contradiction, not a disjunction rewrite. *)
  fun resolve_complementary_literals prems target =
    (if Term.aconv target boolSyntax.F then SOME (replay_contra prems)
     else NONE)
    handle _ => NONE

  (* The Seq RARE names have deliberately narrow, recorded schemas.  Keeping
     them out of the generic RARE ladder means an unrecognised Seq rule stays
     a named CPC obligation rather than becoming an accidental simplifier. *)
  fun replay_seq_rewrite name prems conclusion args =
    let
      fun prove_string target =
        List.foldl (fn (premise, proof) => Drule.PROVE_HYP premise proof)
          (SmtStringProve.string_contextual_prove
            (List.map Thm.concl prems) target) prems
      fun substr_concat_target (prefix, suffix, start, length) =
        let
          val string_ty = Term.type_of prefix
          val concat = Term.mk_thy_const {Thy = "smtstring",
            Name = "smtstr_concat", Ty = Type.--> (string_ty,
              Type.--> (string_ty, string_ty))}
          val substr = Term.mk_thy_const {Thy = "smtstring",
            Name = "smtstr_substr", Ty = Type.--> (string_ty,
              Type.--> (intSyntax.int_ty, Type.--> (intSyntax.int_ty,
                string_ty)))}
        in
          boolSyntax.mk_eq
            (Term.list_mk_comb (substr,
               [Term.list_mk_comb (concat, [prefix, suffix]), start, length]),
             Term.list_mk_comb (substr, [prefix, start, length]))
        end
    in
      case (name, conclusion, args) of
        ("str-substr-concat1", SOME target, [prefix, suffix, start, length]) =>
          let val expected = substr_concat_target (prefix, suffix, start, length)
          in
            if Term.aconv target expected then prove_string target
            else raise ERR name "conclusion does not match arguments"
          end
      | ("str-substr-concat1", NONE, [prefix, suffix, start, length]) =>
          prove_string (substr_concat_target (prefix, suffix, start, length))
      | (_, _, [target]) => SmtSeqProve.seq_prove target
      | _ => raise ERR name "expected one Seq rewrite proposition"
    end

  fun is_smtstr_type ty =
    Type.compare (ty, Type.mk_thy_type
      {Thy = "smtstring", Tyop = "smtstr", Args = []}) = EQUAL

  fun instantiate_smtstr theorem sequence =
    case List.filter (fn variable =>
        is_smtstr_type (Term.type_of variable))
      (Term.free_vars (Thm.concl theorem)) of
      [variable] => Thm.INST
        [{redex = variable, residue = sequence}] theorem
    | _ => raise ERR "instantiate_smtstr" "expected one String variable"

  fun replay_seq_rev_rev args =
    case args of
      [sequence] =>
        if is_smtstr_type (Term.type_of sequence) then
          instantiate_smtstr smtstringTheory.smtstr_rev_rev sequence
        else Drule.ISPEC sequence listTheory.REVERSE_REVERSE
    | _ => raise ERR "seq-rev-rev" "expected one sequence argument"

  fun replay_str_contains_refl args =
    case args of
      [sequence] =>
        if is_smtstr_type (Term.type_of sequence) then
          Drule.EQT_INTRO (instantiate_smtstr
            smtstringTheory.smtstr_contains_refl sequence)
        else
          let
            val sequence_ty = Term.type_of sequence
            val contains = Term.mk_thy_const {Thy = "rich_list",
              Name = "IS_SUBLIST", Ty = Type.--> (sequence_ty,
                Type.--> (sequence_ty, Type.bool))}
            val target = Term.list_mk_comb (contains, [sequence, sequence])
            val proof = Tactical.TAC_PROOF (([], target),
              bossLib.SIMP_TAC (bossLib.srw_ss ())
                [rich_listTheory.IS_SUBLIST_APPEND])
          in
            Drule.EQT_INTRO proof
          end
    | _ => raise ERR "str-contains-refl" "expected one sequence argument"

  fun replay_str_substr_full_eq args =
    case args of
      [sequence, length] =>
        if is_smtstr_type (Term.type_of sequence) then
          let
            val theorem = instantiate_smtstr
              smtstringTheory.smtstr_substr_full sequence
            val expected_length = Term.list_mk_comb
              (Term.mk_thy_const {Thy = "smtstring", Name = "smtstr_len",
                 Ty = Type.--> (Term.type_of sequence, intSyntax.int_ty)},
               [sequence])
          in
            if Term.aconv length expected_length then theorem
            else raise ERR "str-substr-full-eq" "length argument does not match"
          end
        else
          let
            val sequence_ty = Term.type_of sequence
            val extract = Term.mk_thy_const {Thy = "HolSmt",
              Name = "smt_seq_extract", Ty = Type.--> (sequence_ty,
                Type.--> (intSyntax.int_ty,
                  Type.--> (intSyntax.int_ty, sequence_ty)))}
            val expected_length = Term.mk_comb (intSyntax.int_injection,
              listSyntax.mk_length sequence)
            val target = boolSyntax.mk_eq
              (Term.list_mk_comb (extract,
                 [sequence, intSyntax.zero_tm, expected_length]), sequence)
          in
            if Term.aconv length expected_length then SmtSeqProve.seq_prove target
            else raise ERR "str-substr-full-eq" "length argument does not match"
          end
    | _ => raise ERR "str-substr-full-eq"
        "expected a sequence and its length"

  fun replay_string_at_elim sequence index =
    Drule.SPECL [sequence, index] smtstringTheory.smtstr_at_def

  fun replay_seq_at_elim conclusion args =
    case (conclusion, args) of
      (SOME target, [sequence, index]) =>
        if is_smtstr_type (Term.type_of sequence) then
          let val thm = replay_string_at_elim sequence index in
            if Term.aconv target (Thm.concl thm) then thm
            else raise ERR "str-at-elim" "String conclusion does not match"
          end
        else SmtSeqProve.seq_prove target
    | (NONE, [sequence, index]) =>
        if is_smtstr_type (Term.type_of sequence) then
          replay_string_at_elim sequence index
        else
          let
            val sequence_ty = Term.type_of sequence
            val at = Term.mk_thy_const {Thy = "HolSmt", Name = "smt_seq_at",
              Ty = Type.--> (sequence_ty,
                Type.--> (intSyntax.int_ty, sequence_ty))}
            val extract = Term.mk_thy_const {
              Thy = "HolSmt", Name = "smt_seq_extract",
              Ty = Type.--> (sequence_ty, Type.--> (intSyntax.int_ty,
                Type.--> (intSyntax.int_ty, sequence_ty)))}
            val target = boolSyntax.mk_eq
              (Term.list_mk_comb (at, [sequence, index]),
               Term.list_mk_comb (extract,
                 [sequence, index, intSyntax.one_tm]))
          in
            SmtSeqProve.seq_prove target
          end
    | _ => raise ERR "str-at-elim" "expected sequence and index arguments"

  fun replay_sets_ext prems =
    case prems of
      [premise] =>
        let
          val (left, right) = boolSyntax.dest_eq
            (boolSyntax.dest_neg (Thm.concl premise))
          val (element, range) = Type.dom_rng (Term.type_of left)
          val _ = Type.compare (range, Type.bool) = EQUAL orelse
            raise ERR "sets_ext" "expected two Sets"
          val variable = Term.variant (Term.all_varsl [left, right])
            (Term.mk_var ("sets_deq_diff_x", element))
          val witness = boolSyntax.mk_select (variable, boolSyntax.mk_neg
            (boolSyntax.mk_eq (Term.mk_comb (left, variable),
              Term.mk_comb (right, variable))))
          val target = boolSyntax.mk_neg (boolSyntax.mk_eq
            (Term.mk_comb (left, witness), Term.mk_comb (right, witness)))
        in
          SmtResource.with_resource_step_time "Set" "extensionality"
            (fn () =>
              (SmtResource.check_resource_goal "Set" "extensionality" target;
               Drule.PROVE_HYP premise
                 (Tactical.TAC_PROOF (([Thm.concl premise], target),
                   bossLib.METIS_TAC
                     [boolTheory.FUN_EQ_THM, boolTheory.SELECT_THM])))) ()
        end
    | _ => raise ERR "sets_ext" "expected one disequality premise"

  (* Set rewrites are deliberately driven by the certificate conclusion.
     Their names are closed explicitly in CPC_Proof's frozen inventory; this
     makes a future sets-* rule a versioned, loud registry error rather than
     a generic simplifier admission.  The actual proof is shared with the
     ArrayEx/set ladder because D13 represents a Set as [a -> bool]. *)
  fun replay_sets state name prems conclusion args =
    let
      fun empty set = pred_setSyntax.mk_empty (pred_setSyntax.eltype set)
      fun singleton element = pred_setSyntax.mk_insert
        (element, pred_setSyntax.mk_empty (Term.type_of element))
      fun card set = Term.mk_comb
        (intSyntax.int_injection, pred_setSyntax.mk_card set)
      fun prove target =
        if name = "sets-card-union" orelse name = "sets-card-minus" then
          let
            val context =
              HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
              List.map Thm.concl prems
            fun prove_tac context target tactic =
              SmtResource.with_resource_step_time "Set" "cardinality"
                (fn () =>
                  (SmtResource.check_resource_goal "Set" "cardinality"
                     target;
                   Tactical.TAC_PROOF ((context, target), tactic))) ()
            fun card_bound () =
              case (name, args) of
                ("sets-card-union", [left, right]) =>
                  let
                    val bound = numSyntax.mk_leq
                      (pred_setSyntax.mk_card
                         (pred_setSyntax.mk_inter (left, right)),
                       numSyntax.mk_plus
                         (pred_setSyntax.mk_card left,
                          pred_setSyntax.mk_card right))
                  in
                    prove_tac context bound
                      (bossLib.METIS_TAC
                        [pred_setTheory.CARD_INTER_LESS_EQ,
                         arithmeticTheory.LESS_EQ_ADD,
                         arithmeticTheory.LESS_EQ_TRANS])
                  end
              | ("sets-card-minus", [left, right]) =>
                  let
                    val bound = numSyntax.mk_leq
                      (pred_setSyntax.mk_card
                         (pred_setSyntax.mk_inter (left, right)),
                       pred_setSyntax.mk_card left)
                  in
                    prove_tac context bound
                      (bossLib.ASM_SIMP_TAC (bossLib.srw_ss ())
                        [pred_setTheory.CARD_INTER_LESS_EQ])
                  end
              | _ => raise ERR name "wrong cardinality arguments"
            val bound = card_bound ()
            val context = Thm.concl bound :: context
            val proof = prove_tac context target
              (bossLib.ASM_SIMP_TAC (bossLib.srw_ss ())
                [pred_setTheory.CARD_UNION_EQN,
                 pred_setTheory.CARD_DIFF_EQN,
                 integerTheory.INT_OF_NUM_ADD,
                 integerTheory.INT_SUB])
            val proof = Drule.PROVE_HYP bound proof
          in
            List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
              proof prems
          end
        else if name = "sets-eval-op" then
          (Tactical.TAC_PROOF (([], target),
             bossLib.SIMP_TAC (bossLib.srw_ss ()) [])
           handle Feedback.HOL_ERR _ => SmtArrayProve.array_prove target)
        else if SmtArrayProve.has_set_term target then
          SmtArrayProve.array_prove target
        else
          raise ERR name
            ("set rule conclusion has no native Set term: " ^
             Library.term_to_string target)
      fun omitted_target () =
        case (name, args) of
          ("sets-card-union", [left, right]) =>
            boolSyntax.mk_eq (card (pred_setSyntax.mk_union (left, right)),
              intSyntax.mk_minus
                (intSyntax.mk_plus (card left, card right),
                 card (pred_setSyntax.mk_inter (left, right))))
        | ("sets-card-minus", [left, right]) =>
            boolSyntax.mk_eq (card (pred_setSyntax.mk_diff (left, right)),
              intSyntax.mk_minus (card left,
                card (pred_setSyntax.mk_inter (left, right))))
        | ("sets-card-emp", [set, _]) =>
            boolSyntax.mk_eq (card set, intSyntax.zero_tm)
        | ("sets-card-singleton", [element]) =>
            boolSyntax.mk_eq (card (singleton element),
              intSyntax.term_of_int (Arbint.fromInt 1))
        | ("sets-choose-singleton", [element]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_choice (singleton element),
              element)
        | ("sets-eval-op", [target]) => target
        | ("sets-insert-elim", [target]) => target
        | ("sets-inter-comm", [left, right]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_inter (left, right),
              pred_setSyntax.mk_inter (right, left))
        | ("sets-inter-member", [element, left, right]) =>
            boolSyntax.mk_eq
              (pred_setSyntax.mk_in
                 (element, pred_setSyntax.mk_inter (left, right)),
               boolSyntax.mk_conj (pred_setSyntax.mk_in (element, left),
                 pred_setSyntax.mk_in (element, right)))
        | ("sets-is-empty-elim", [set, _]) =>
            let val is_empty = boolSyntax.mk_eq (set, empty set)
            in boolSyntax.mk_eq (is_empty, is_empty) end
        | ("sets-is-singleton-elim", [set]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_sing set,
              boolSyntax.mk_eq (set,
                singleton (pred_setSyntax.mk_choice set)))
        | ("sets-member-emp", [element, set, _]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_in (element, set),
              boolSyntax.F)
        | ("sets-member-singleton", [element, singleton_element]) =>
            boolSyntax.mk_eq
              (pred_setSyntax.mk_in (element, singleton singleton_element),
               boolSyntax.mk_eq (element, singleton_element))
        | ("sets-minus-member", [element, left, right]) =>
            boolSyntax.mk_eq
              (pred_setSyntax.mk_in
                 (element, pred_setSyntax.mk_diff (left, right)),
               boolSyntax.mk_conj (pred_setSyntax.mk_in (element, left),
                 boolSyntax.mk_neg (pred_setSyntax.mk_in (element, right))))
        | ("sets-minus-self", [set, _]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_diff (set, set), empty set)
        | ("sets-subset-elim", [left, right]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_subset (left, right),
              boolSyntax.mk_eq (pred_setSyntax.mk_union (left, right), right))
        | ("sets-union-comm", [left, right]) =>
            boolSyntax.mk_eq (pred_setSyntax.mk_union (left, right),
              pred_setSyntax.mk_union (right, left))
        | ("sets-union-member", [element, left, right]) =>
            boolSyntax.mk_eq
              (pred_setSyntax.mk_in
                 (element, pred_setSyntax.mk_union (left, right)),
               boolSyntax.mk_disj (pred_setSyntax.mk_in (element, left),
                 pred_setSyntax.mk_in (element, right)))
        | _ => raise ERR name
            "omitted conclusion has an unsupported recorded argument shape"
    in
      prove (case conclusion of SOME target => target | NONE => omitted_target ())
    end

  fun replay_rare_rewrite name args =
    let
      val smt_ediv_total_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_ediv_total"}
      val smt_emod_total_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_emod_total"}
      fun smt_ediv_total (a, b) = Term.list_mk_comb
        (smt_ediv_total_tm, [a, b])
      fun smt_emod_total (a, b) = Term.list_mk_comb
        (smt_emod_total_tm, [a, b])
      fun smtstring_app constant arguments =
        Term.list_mk_comb
          (Term.prim_mk_const {Thy = "smtstring", Name = constant},
           arguments)
      fun bool_xor (left, right) = Term.list_mk_comb
        (Term.prim_mk_const {Thy = "HolSmt", Name = "xor"},
         [left, right])
      fun int_literal n =
        intSyntax.term_of_int (Arbint.fromInt n)
      fun arith_leq (left, right) =
        intSyntax.mk_leq (left, right)
        handle Feedback.HOL_ERR _ => realSyntax.mk_leq (left, right)
      fun arith_geq (left, right) =
        intSyntax.mk_geq (left, right)
        handle Feedback.HOL_ERR _ => realSyntax.mk_geq (left, right)
      fun arith_ite_lift relation
          [condition, then_term, else_term, right] =
        let
          val target = boolSyntax.mk_eq
            (relation
               (boolSyntax.mk_cond (condition, then_term, else_term), right),
             boolSyntax.mk_cond
               (condition, relation (then_term, right),
                relation (else_term, right)))
        in
          Tactical.TAC_PROOF (([], target),
            Tactical.THEN (Tactic.COND_CASES_TAC,
              bossLib.SIMP_TAC boolSimps.bool_ss []))
        end
        | arith_ite_lift _ _ =
            raise ERR name "expected condition, branches, and right operand"
      fun guard_not_zero term = boolSyntax.mk_neg
        (boolSyntax.mk_eq (term, intSyntax.zero_tm))
      fun guarded name guard target tactic =
        let
          val thm = Tactical.TAC_PROOF (([guard], target), tactic)
        in
          (Thm.MP thm
             (Tactical.TAC_PROOF (([], guard), intLib.ARITH_TAC))
           handle Feedback.HOL_ERR _ => thm)
        end
      fun guard_thm guard =
        Tactical.TAC_PROOF (([], guard), intLib.ARITH_TAC)
        handle Feedback.HOL_ERR _ => Thm.ASSUME guard
      fun distinct_lemma target =
        Tactical.TAC_PROOF (([], target),
          bossLib.SIMP_TAC (bossLib.srw_ss())
            [HolSmtTheory.ALL_DISTINCT_NIL,
             HolSmtTheory.ALL_DISTINCT_CONS])
      fun total_eq_ediv a b =
        Drule.SPECL [a, b] HolSmtTheory.smt_ediv_total_eq_ediv
      fun total_eq_emod a b =
        Drule.SPECL [a, b] HolSmtTheory.smt_emod_total_eq_emod
      fun list_terms term =
        #1 (listSyntax.dest_list term)
        handle Feedback.HOL_ERR _ =>
          raise ERR name "expected a CPC :list argument"
      fun fold_int operation terms =
        case terms of
          [] => intSyntax.zero_tm
        | first :: rest => List.foldl
            (fn (right, left) => operation (left, right)) first rest
      fun mod_context c ts r ss operation =
        let
          val ts = list_terms ts
          val ss = list_terms ss
          val inner = smt_emod_total (r, c)
          val left_context = fold_int operation (ts @ [inner] @ ss)
          val right_context = fold_int operation (ts @ [r] @ ss)
          val target = boolSyntax.mk_eq
            (smt_emod_total (left_context, c),
             smt_emod_total (right_context, c))
          val guard = guard_not_zero c
        in
          guarded name guard target
            (bossLib.ASM_SIMP_TAC (bossLib.srw_ss())
              [HolSmtTheory.smt_emod_total_def,
               integerTheory.EMOD_DEF,
               integerTheory.INT_MOD_MOD,
               integerTheory.INT_MOD_ADD_MULTIPLES])
        end
      fun mod_context_add args =
        (case args of
           [c, ts, r, ss] => mod_context c ts r ss intSyntax.mk_plus
         | _ => raise ERR name "expected c, ts, r, ss arguments")
      fun mod_context_mult args =
        (case args of
           [c, ts, r, ss] => mod_context c ts r ss intSyntax.mk_mult
         | _ => raise ERR name "expected c, ts, r, ss arguments")
    in case (name, args) of
      ("exists-elim", [target]) =>
        let
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss()) [boolTheory.NOT_FORALL_THM])
        end
    | ("bool-double-not-elim", [p]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_neg p), p))
    | ("bool-impl-elim", [left, right]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_imp (left, right),
           boolSyntax.mk_disj (boolSyntax.mk_neg left, right)))
    | ("bool-eq-false", [p]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_eq (p, boolSyntax.F), boolSyntax.mk_neg p))
    | ("bool-eq-true", [p]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_eq (p, boolSyntax.T), p))
    | ("bool-xor-comm", [left, right]) =>
        xor_tautology (boolSyntax.mk_eq
          (bool_xor (left, right), bool_xor (right, left)))
    | ("bool-xor-false", [p]) =>
        xor_tautology (boolSyntax.mk_eq
          (bool_xor (p, boolSyntax.F), p))
    | ("bool-xor-true", [p]) =>
        xor_tautology (boolSyntax.mk_eq
          (bool_xor (p, boolSyntax.T), boolSyntax.mk_neg p))
    | ("bool-impl-false1", [p]) =>
        Tactical.TAC_PROOF
          (([], boolSyntax.mk_eq
            (boolSyntax.mk_imp (p, boolSyntax.F), boolSyntax.mk_neg p)),
           bossLib.SIMP_TAC boolSimps.bool_ss [])
    | ("bool-impl-true1", [p]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_imp (p, boolSyntax.T), boolSyntax.T))
    | ("bool-impl-true2", [p]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_imp (boolSyntax.T, p), p))
    | ("bool-eq-nrefl", [p]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_eq (p, boolSyntax.mk_neg p), boolSyntax.F))
    | ("eq-symm", [left, right]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_eq (left, right), boolSyntax.mk_eq (right, left)))
    | ("bool-not-eq-elim2", [left, right]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)),
           boolSyntax.mk_eq (left, boolSyntax.mk_neg right)))
    | ("bool-not-eq-elim1", [left, right]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)),
           boolSyntax.mk_eq (boolSyntax.mk_neg left, right)))
    | ("str-lt-elim", [left, right]) =>
        let
          val lt = smtstring_app "smtstr_lt" [left, right]
          val le = smtstring_app "smtstr_le" [left, right]
          val target =
            boolSyntax.mk_eq
              (lt, boolSyntax.mk_conj
                (boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)), le))
        in
          SmtStringProve.string_rewrite_prove target
        end
    | ("str-is-digit-elim", [string]) =>
        let
          val is_digit = smtstring_app "smtstr_is_digit" [string]
          val code = smtstring_app "smtstr_to_code" [string]
          val target =
            boolSyntax.mk_eq
              (is_digit, boolSyntax.mk_conj
                (intSyntax.mk_leq (int_literal 48, code),
                 intSyntax.mk_leq (code, int_literal 57)))
        in
          SmtStringProve.string_rewrite_prove target
        end
    | ("distinct-elim", [target]) => distinct_lemma target
    | ("distinct-false", [target]) => distinct_lemma target
    | ("eq-ite-lift", operands as [_, _, _, _]) =>
        arith_ite_lift boolSyntax.mk_eq operands
    | ("arith-leq-ite-lift", operands) =>
        arith_ite_lift arith_leq operands
    | ("arith-geq-ite-lift", operands) =>
        arith_ite_lift arith_geq operands
    | ("bool-or-de-morgan", [left, right, _]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_disj (left, right)),
           boolSyntax.mk_conj (boolSyntax.mk_neg left, boolSyntax.mk_neg right)))
    | ("bool-and-de-morgan", [left, right, _]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_conj (left, right)),
           boolSyntax.mk_disj (boolSyntax.mk_neg left, boolSyntax.mk_neg right)))
    | ("bool-implies-de-morgan", [left, right]) =>
        tautology name (boolSyntax.mk_eq
          (boolSyntax.mk_neg (boolSyntax.mk_imp (left, right)),
           boolSyntax.mk_conj (left, boolSyntax.mk_neg right)))
    | ("distinct-binary-elim", [left, right]) =>
        let
          val distinct = listSyntax.mk_all_distinct
            (listSyntax.mk_list ([left, right], Term.type_of left))
          val target = boolSyntax.mk_eq
            (distinct, boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)))
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [HolSmtTheory.ALL_DISTINCT_NIL,
               HolSmtTheory.ALL_DISTINCT_CONS])
        end
    | ("array-read-over-write-split",
       [array, index, value, update_index]) =>
        let
          val base = Drule.ISPECL [array, update_index, value, index]
            combinTheory.APPLY_UPDATE_THM
            handle Feedback.HOL_ERR holerr =>
              raise ERR "array-read-over-write-split"
                ("APPLY_UPDATE_THM instantiation failed: " ^
                 Feedback.message_of holerr)
          val condition_eq = Drule.ISPECL [update_index, index]
            boolTheory.EQ_SYM_EQ
            handle Feedback.HOL_ERR holerr =>
              raise ERR "array-read-over-write-split"
                ("EQ_SYM_EQ instantiation failed: " ^
                 Feedback.message_of holerr)
          val condition = Term.mk_var ("condition", Type.bool)
          val context = Term.mk_abs (condition,
            boolSyntax.mk_cond
              (condition, value, Term.mk_comb (array, index)))
          val rhs_eq = Conv.BETA_RULE (Thm.AP_TERM context condition_eq)
            handle Feedback.HOL_ERR holerr =>
              raise ERR "array-read-over-write-split"
                ("conditional congruence failed: " ^
                 Feedback.message_of holerr)
        in
          Thm.TRANS base rhs_eq
          handle Feedback.HOL_ERR holerr =>
            raise ERR "array-read-over-write-split"
              ("read-over-write composition failed: " ^
               Feedback.message_of holerr)
        end
    | ("absorb", [target]) =>
        (profile "CPC(rung:RARE/absorb/simp)" Tactical.TAC_PROOF
           (([], target), bossLib.SIMP_TAC boolSimps.bool_ss [])
         handle Feedback.HOL_ERR _ =>
           profile "CPC(rung:RARE/absorb/word_arith)"
             wordsLib.WORD_ARITH_PROVE target)
    | ("arith-div-total-zero-real", [term]) =>
        Tactical.TAC_PROOF
          (([], boolSyntax.mk_eq
            (realSyntax.mk_div (term, realSyntax.zero_tm),
             realSyntax.zero_tm)),
           bossLib.SIMP_TAC realSimps.real_ss [realTheory.REAL_DIV_ZERO])
    | ("arith-div-total-zero-int", [term]) =>
        Tactical.TAC_PROOF
          (([], boolSyntax.mk_eq
            (realSyntax.mk_div (intrealSyntax.mk_real_of_int term,
               realSyntax.zero_tm),
             realSyntax.zero_tm)),
           bossLib.SIMP_TAC realSimps.real_ss [realTheory.REAL_DIV_ZERO])
    | ("arith-int-div-total", [a, b]) =>
        Thm.SYM
          (Thm.MP (total_eq_ediv a b)
            (guard_thm (guard_not_zero b)))
    | ("arith-int-div-total-one", [a]) =>
        Thm.SPEC a HolSmtTheory.smt_ediv_total_one
    | ("arith-int-div-total-zero", [a]) =>
        Thm.SPEC a HolSmtTheory.smt_ediv_total_zero
    | ("arith-int-div-total-neg", [a, b]) =>
        Thm.MP (Drule.SPECL [a, b] HolSmtTheory.smt_ediv_total_neg)
          (guard_thm (intSyntax.mk_less (b, intSyntax.zero_tm)))
    | ("arith-int-mod-total", [a, b]) =>
        Thm.SYM
          (Thm.MP (total_eq_emod a b)
            (guard_thm (guard_not_zero b)))
    | ("arith-int-mod-total-one", [a]) =>
        Thm.SPEC a HolSmtTheory.smt_emod_total_one
    | ("arith-int-mod-total-zero", [a]) =>
        Thm.SPEC a HolSmtTheory.smt_emod_total_zero
    | ("arith-int-mod-total-neg", [a, b]) =>
        Thm.MP (Drule.SPECL [a, b] HolSmtTheory.smt_emod_total_neg)
          (guard_thm (intSyntax.mk_less (b, intSyntax.zero_tm)))
    | ("arith-divisible-elim", [n, t]) =>
        let
          val guard = guard_not_zero n
          val divisible = intSyntax.mk_divides (n, t)
          val target = boolSyntax.mk_eq
            (smt_emod_total (t, n), intSyntax.zero_tm)
          val total_eq = Thm.MP
            (Drule.SPECL [t, n] HolSmtTheory.smt_emod_total_eq_emod)
            (Thm.ASSUME guard)
          val remainder_zero = Tactical.TAC_PROOF
            (([guard, divisible],
              boolSyntax.mk_eq
                (SmtLib_Theories.mk_int_emod (t, n), intSyntax.zero_tm)),
             Tactical.THEN
               (bossLib.SIMP_TAC (bossLib.srw_ss())
                  [integerTheory.EMOD_DEF, integerTheory.INT_ABS],
                Tactical.THEN (Tactic.COND_CASES_TAC,
                  metisLib.METIS_TAC
                    [integerTheory.INT_DIVIDES_MOD0,
                     integerTheory.INT_DIVIDES_NEG])))
        in
          Thm.TRANS total_eq remainder_zero
        end
    | ("arith-mod-over-mod-1", [c, r]) =>
        let
          val guard = guard_not_zero c
          val target = boolSyntax.mk_eq
            (smt_emod_total (smt_emod_total (r, c), c),
             smt_emod_total (r, c))
        in
          guarded name guard target
            (bossLib.ASM_SIMP_TAC (bossLib.srw_ss())
              [HolSmtTheory.smt_emod_total_def,
               integerTheory.EMOD_DEF,
               integerTheory.INT_MOD_MOD])
        end
    | ("arith-mod-over-mod", args) => mod_context_add args
    | ("arith-mod-over-mod-mult", args) => mod_context_mult args
    | _ => raise ERR name "unsupported CPC RARE rewrite argument shape"
    end

  fun replay_rare_rewrite_with_provenance name
      (located_args : located_term list) =
    let
      val args = List.map (fn located => #term located) located_args
      val theorem = replay_rare_rewrite name args
      val provenance =
        case (name, located_args) of
          ("bool-double-not-elim", [located]) =>
            let val operand = #provenance located in
              EqualityProvenance
                (ApplicationProvenance ("not",
                   [ApplicationProvenance ("not", [operand])]), operand)
            end
        | ("eq-symm", [left, right]) =>
            let
              val left_provenance = #provenance left
              val right_provenance = #provenance right
            in
              EqualityProvenance
                (EqualityProvenance
                   (left_provenance, right_provenance),
                 EqualityProvenance
                   (right_provenance, left_provenance))
            end
        | _ => conjunction_free_semantic_provenance
            ("CPC RARE rewrite " ^ name ^
             " produced a result containing an exact conjunction")
            (Thm.concl theorem)
    in
      (theorem, provenance)
    end

  fun replay_aci_norm args =
    let val target = expect_one_arg "aci_norm" args
    in
      profile "CPC(rung:word/aci_norm)" wordsLib.WORD_ARITH_PROVE target
      handle Feedback.HOL_ERR holerr =>
        if SmtResource.is_resource_gate holerr then
          raise Feedback.HOL_ERR holerr
        else
          (profile "CPC(rung:seq/aci_norm)" SmtSeqProve.seq_prove target
           handle Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else
               profile "CPC(rung:word/aci_norm_tautology)"
                 (tautology "aci_norm") target)
    end

  fun replay_bv_xor_duplicate args =
    case args of
      word :: _ =>
        let
          val zero = wordsSyntax.mk_word
            (Arbnum.zero, fcpLib.index_to_num (wordsSyntax.dim_of word))
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_xor (word, word), zero)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss()) [wordsTheory.WORD_XOR_CLAUSES])
        end
    | [] => raise ERR "bv-xor-duplicate" "expected a bit-vector argument"

  fun replay_bv_not_idemp args =
    let
      val word = expect_one_arg "bv-not-idemp" args
      val target = boolSyntax.mk_eq
        (wordsSyntax.mk_word_1comp (wordsSyntax.mk_word_1comp word), word)
    in
      Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC (bossLib.srw_ss()) [wordsTheory.WORD_NOT_NOT])
    end

  fun replay_bv_shl_by_const_0 args =
    case args of
      word :: _ =>
        let
          val zero = wordsSyntax.mk_word
            (Arbnum.zero, fcpLib.index_to_num (wordsSyntax.dim_of word))
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_lsl_bv (word, zero), word)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [wordsTheory.word_lsl_bv_def, wordsTheory.w2n_n2w,
               wordsTheory.SHIFT_ZERO])
        end
    | [] => raise ERR "bv-shl-by-const-0" "expected a bit-vector argument"

  fun replay_bv_shl_by_const_2 args =
    case args of
      word :: amount :: _ =>
        let
          val amount = numSyntax.dest_numeral
            (intSyntax.dest_injected amount)
          val width = fcpLib.index_to_num (wordsSyntax.dim_of word)
          val amount_word = wordsSyntax.mk_word (amount, width)
          val zero = wordsSyntax.mk_word (Arbnum.zero, width)
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_lsl_bv (word, amount_word), zero)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [wordsTheory.word_lsl_bv_def, wordsTheory.w2n_n2w,
               wordsTheory.LSL_LIMIT])
        end
    | _ => raise ERR "bv-shl-by-const-2"
        "expected a bit-vector and a constant shift amount"

  fun replay_bv_ashr_by_const_0 args =
    case args of
      word :: _ =>
        let
          val zero = wordsSyntax.mk_word
            (Arbnum.zero, fcpLib.index_to_num (wordsSyntax.dim_of word))
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_asr_bv (word, zero), word)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [wordsTheory.word_asr_bv_def, wordsTheory.w2n_n2w,
               wordsTheory.SHIFT_ZERO])
        end
    | [] => raise ERR "bv-ashr-by-const-0" "expected a bit-vector argument"

  fun replay_bv_lshr_by_const_0 args =
    case args of
      word :: _ =>
        let
          val zero = wordsSyntax.mk_word
            (Arbnum.zero, fcpLib.index_to_num (wordsSyntax.dim_of word))
          val target = boolSyntax.mk_eq
            (wordsSyntax.mk_word_lsr_bv (word, zero), word)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC (bossLib.srw_ss())
              [wordsTheory.word_lsr_bv_def, wordsTheory.w2n_n2w,
               wordsTheory.SHIFT_ZERO])
        end
    | [] => raise ERR "bv-lshr-by-const-0" "expected a bit-vector argument"

  fun replay_bv_poly_norm args =
    let
      val target = expect_one_arg "bv_poly_norm" args
      fun bitblast_equivalence () =
        let
          val (word_equality, bit_conjunction) = boolSyntax.dest_eq target
          val _ = Term.type_of word_equality = Type.bool orelse
            raise ERR "bv_poly_norm" "expected a Boolean word equality"
          val word_thm = profile "CPC(rung:word/bitblast_word_arith)"
            wordsLib.WORD_ARITH_PROVE word_equality
          fun prove_bit tm = Tactical.TAC_PROOF (([], tm),
            Tactical.THEN
              (bossLib.SIMP_TAC (bossLib.srw_ss())
                 [HolSmtTheory.xor_def], tautLib.TAUT_TAC))
          fun prove_bits tm =
            let val (left, right) = boolSyntax.dest_conj tm in
              Thm.CONJ (prove_bits left) (prove_bits right)
            end handle Feedback.HOL_ERR _ => prove_bit tm
          val bits_thm = prove_bits bit_conjunction
        in
          (* Both sides of this Boolean equality have just been established.
             Build the equality through truth directly: asking Taut to expand
             the bit-blasted operands makes this otherwise constant-size CPC
             step grow prohibitively. *)
          Thm.TRANS (Drule.EQT_INTRO word_thm)
            (Thm.SYM (Drule.EQT_INTRO bits_thm))
        end
    in
      profile "CPC(rung:word/bitblast_equivalence)"
        bitblast_equivalence ()
      handle Feedback.HOL_ERR _ =>
      profile "CPC(rung:word/poly_norm_arith)"
        wordsLib.WORD_ARITH_PROVE target
      handle Feedback.HOL_ERR _ =>
        profile "CPC(rung:word/poly_norm_full_simp)" Tactical.TAC_PROOF
          (([], target),
          Tactical.THEN
            (bossLib.FULL_SIMP_TAC
               (simpLib.++ (simpLib.++ (simpLib.++
                 (bossLib.list_ss, boolSimps.COND_elim_ss), wordsLib.WORD_ss),
                wordsLib.WORD_BIT_EQ_ss)) [boolTheory.EQ_SYM_EQ],
             tautLib.TAUT_TAC))
    end

  fun replay_quant_unused_vars args =
    let val target = expect_one_arg "quant-unused-vars" args in
      Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC (bossLib.srw_ss()) [])
    end

  fun replay_quant_rewrite name args =
    let
      val target = expect_one_arg name args
    in
      if name = "quant-miniscope-and" then
        Tactical.TAC_PROOF (([], target),
          bossLib.SIMP_TAC bossLib.bool_ss [boolTheory.FORALL_AND_THM])
      else if name = "quant-miniscope-or" then
        Tactical.TAC_PROOF (([], target),
          bossLib.SIMP_TAC bossLib.bool_ss
            [boolTheory.LEFT_FORALL_OR_THM, boolTheory.RIGHT_FORALL_OR_THM])
      else if name = "quant-var-elim-eq" then
        Tactical.TAC_PROOF (([], target),
          bossLib.SIMP_TAC bossLib.bool_ss
            [Thm.SYM boolTheory.IMP_DISJ_THM,
             boolTheory.UNWIND_FORALL_THM1,
             boolTheory.UNWIND_FORALL_THM2])
      else Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC (bossLib.srw_ss()) [boolTheory.IMP_DISJ_THM])
    end

  fun replay_alpha_equiv args =
    let
      val source = case args of tm :: _ => tm
        | [] => raise ERR "alpha_equiv" "expected a quantified source term"
      fun replay mk_quant strip_quant =
        let
          val (bound_vars, body) = strip_quant source
          val n = List.length bound_vars
          val mappings = List.drop (args, 1)
          val _ = List.length mappings = 2 * n orelse
            raise ERR "alpha_equiv" "binder mapping arity does not match source"
          val old_vars = List.take (mappings, n)
          val new_vars = List.drop (mappings, n)
          val _ = ListPair.allEq (fn (bound, old) =>
            Term.aconv bound old) (bound_vars, old_vars) orelse
            raise ERR "alpha_equiv" "source binders do not match CPC mapping"
          val _ = List.all Term.is_var new_vars orelse
            raise ERR "alpha_equiv" "target CPC binders are not variables"
          val rhs = mk_quant (new_vars,
            Term.subst (ListPair.map (fn (old, new) =>
              {redex = old, residue = new}) (old_vars, new_vars)) body)
        in Thm.ALPHA source rhs end
    in
      replay boolSyntax.list_mk_forall boolSyntax.strip_forall
      handle Feedback.HOL_ERR _ =>
        replay boolSyntax.list_mk_exists boolSyntax.strip_exists
      handle Feedback.HOL_ERR _ =>
        replay Term.list_mk_abs Term.strip_abs
    end

  (* If the branches of a Boolean conditional are complements, cvc5 rewrites
     the conditional to equality between its condition and then-branch.  The
     sole premise records that complement relation; propositional replay
     checks the precise general shape. *)
  fun replay_ite_neg_branch args prems =
    case args of
      [condition, then_term, else_term] =>
        let
          val premise = expect_one_premise "ite-neg-branch" prems
          val target = boolSyntax.mk_eq
            (boolSyntax.mk_cond (condition, then_term, else_term),
             boolSyntax.mk_eq (condition, then_term))
        in
          tautological_consequence premise target
          handle Feedback.HOL_ERR _ =>
            raise ERR "ite-neg-branch"
              "premise does not establish complementary Boolean branches"
        end
    | _ => raise ERR "ite-neg-branch"
        "expected condition, then-branch, and else-branch arguments"

  fun replay_bv_poly_norm_eq args =
    tautology "bv_poly_norm_eq" (expect_one_arg "bv_poly_norm_eq" args)

  fun replay_not_implies_elim2 prems =
    let
      val premise = expect_one_premise "not_implies_elim2" prems
      val implication = boolSyntax.dest_neg (Thm.concl premise)
      val (_, conclusion) = boolSyntax.dest_imp implication
    in tautological_consequence premise (boolSyntax.mk_neg conclusion) end

  fun replay_not_implies_elim1 prems =
    let
      val premise = expect_one_premise "not_implies_elim1" prems
      val implication = boolSyntax.dest_neg (Thm.concl premise)
      val (antecedent, _) = boolSyntax.dest_imp implication
    in tautological_consequence premise antecedent end

  fun replay_implies_elim prems =
    let
      val premise = expect_one_premise "implies_elim" prems
      val (antecedent, consequent) = boolSyntax.dest_imp (Thm.concl premise)
    in tautological_consequence premise
      (boolSyntax.mk_disj (boolSyntax.mk_neg antecedent, consequent)) end

  fun replay_factoring prems =
    let
      val premise = expect_one_premise "factoring" prems
      fun unique [] = []
        | unique (tm :: rest) =
            tm :: unique (List.filter (fn other => not (Term.aconv tm other)) rest)
      fun mk_disj [tm] = tm
        | mk_disj (tm :: rest) = boolSyntax.mk_disj (tm, mk_disj rest)
        | mk_disj [] = raise ERR "factoring" "empty CPC factoring clause"
      val conclusion = mk_disj (unique (boolSyntax.strip_disj (Thm.concl premise)))
    in tautological_consequence premise conclusion end

  fun mk_disj_terms [tm] = tm
    | mk_disj_terms (tm :: rest) = boolSyntax.mk_disj (tm, mk_disj_terms rest)
    | mk_disj_terms [] = boolSyntax.F

  fun replay_reordering prems args =
    let
      val premise =
        Rewrite.PURE_REWRITE_RULE
          [Thm.CONJUNCT1 boolTheory.NOT_CLAUSES]
          (expect_one_premise "reordering" prems)
      val target = expect_one_arg "reordering" args
      fun derive theorem =
        Library.disj_intro (theorem, target)
        handle Feedback.HOL_ERR _ =>
          let
            val (left, right) = boolSyntax.dest_disj (Thm.concl theorem)
              handle Feedback.HOL_ERR _ => raise ERR "reordering"
                ("source literal is absent from target clause; literal=" ^
                 Library.term_to_string (Thm.concl theorem) ^ "; target=" ^
                 Library.term_to_string target)
          in
            Thm.DISJ_CASES theorem
              (derive (Thm.ASSUME left))
              (derive (Thm.ASSUME right))
          end
    in
      derive premise
    end

  fun replay_normalized_reordering canon prems target =
    let
      val normalized_prems = List.map (Conv.CONV_RULE canon) prems
      val target_norm = canon target
      val normalized_target = boolSyntax.rhs (Thm.concl target_norm)
      val theorem =
        if Term.aconv normalized_target boolSyntax.T then
          retain_all boolTheory.TRUTH normalized_prems
        else replay_reordering normalized_prems [normalized_target]
    in
      Thm.EQ_MP (Thm.SYM target_norm) theorem
    end

  val expand_real_div_conv = Conv.QCONV
    (Conv.TOP_DEPTH_CONV SmtReplayCanon.real_div_conv)

  fun real_div_reordering_conv strong_canon = compose_normal_form_conv
    expand_real_div_conv strong_canon

  fun replay_cnf name args =
    let
      fun implication tm = boolSyntax.dest_imp tm
      fun equality tm = boolSyntax.dest_eq tm
      fun neg tm = boolSyntax.mk_neg tm
      fun strip_conjunction tm =
        (let val (left, right) = boolSyntax.dest_conj tm in
           strip_conjunction left @ strip_conjunction right
         end)
        handle Feedback.HOL_ERR _ => [tm]
      fun strip_disjunction tm =
        (let val (left, right) = boolSyntax.dest_disj tm in
           strip_disjunction left @ strip_disjunction right
         end)
        handle Feedback.HOL_ERR _ => [tm]
      fun xor tm =
        let
          val (f, right) = Term.dest_comb tm
          val (_, left) = Term.dest_comb f
        in (left, right) end
      fun ite tm = boolSyntax.dest_cond tm
      fun indexed_and as_ =
        case as_ of
          [conjunction, index_tm] =>
            let
              val index = Arbnum.toInt (numSyntax.dest_numeral
                (intSyntax.dest_injected index_tm))
            in
              List.nth (strip_conjunction conjunction, index)
                handle Subscript => raise ERR name
                  "CPC cnf_and_pos index is outside the conjunction"
            end
        | _ => raise ERR name "expected conjunction and index"
      fun indexed_or as_ =
        case as_ of
          [disjunction, index_tm] =>
            let
              val index = Arbnum.toInt (numSyntax.dest_numeral
                (intSyntax.dest_injected index_tm))
            in
              List.nth (strip_disjunction disjunction, index)
                handle Subscript => raise ERR name
                  "CPC cnf_or_neg index is outside the disjunction"
            end
        | _ => raise ERR name "expected disjunction and index"
      val conclusion =
        case (name, args) of
          ("cnf_implies_neg1", [imp]) =>
            let val (left, _) = implication imp in mk_disj_terms [left, imp] end
        | ("cnf_implies_neg2", [imp]) =>
            let val (_, right) = implication imp in mk_disj_terms [neg right, imp] end
        | ("cnf_implies_pos", [imp]) =>
            let val (left, right) = implication imp
            in mk_disj_terms [neg left, right, neg imp] end
        | ("cnf_and_pos", as_) =>
            let val conjunction = List.hd as_
            in mk_disj_terms [indexed_and as_, neg conjunction] end
        | ("cnf_and_neg", [conjunction]) =>
            mk_disj_terms (conjunction ::
              List.map neg (strip_conjunction conjunction))
        | ("cnf_or_neg", as_) =>
            let val disjunction = List.hd as_
            in mk_disj_terms [disjunction, neg (indexed_or as_)] end
        | ("cnf_or_pos", [disjunction]) =>
            mk_disj_terms
              (boolSyntax.mk_neg disjunction :: strip_disjunction disjunction)
        | ("cnf_equiv_neg1", [eq]) =>
            let val (left, right) = equality eq
            in mk_disj_terms [left, right, eq] end
        | ("cnf_equiv_neg2", [eq]) =>
            let val (left, right) = equality eq
            in mk_disj_terms [neg left, neg right, eq] end
        | ("cnf_equiv_pos1", [eq]) =>
            let val (left, right) = equality eq
            in mk_disj_terms [neg left, right, neg eq] end
        | ("cnf_equiv_pos2", [eq]) =>
            let val (left, right) = equality eq
            in mk_disj_terms [left, neg right, neg eq] end
        | ("cnf_xor_pos1", [x]) =>
            let val (left, right) = xor x
            in mk_disj_terms [neg x, left, right] end
        | ("cnf_xor_pos2", [x]) =>
            let val (left, right) = xor x
            in mk_disj_terms [neg x, neg left, neg right] end
        | ("cnf_xor_neg1", [x]) =>
            let val (left, right) = xor x
            in mk_disj_terms [x, neg left, right] end
        | ("cnf_xor_neg2", [x]) =>
            let val (left, right) = xor x
            in mk_disj_terms [x, left, neg right] end
        | ("cnf_ite_pos1", [if_term]) =>
            let val (condition, then_term, _) = ite if_term
            in mk_disj_terms [neg if_term, neg condition, then_term] end
        | ("cnf_ite_pos2", [if_term]) =>
            let val (condition, _, else_term) = ite if_term
            in mk_disj_terms [neg if_term, condition, else_term] end
        | ("cnf_ite_pos3", [if_term]) =>
            let val (_, then_term, else_term) = ite if_term
            in mk_disj_terms [neg if_term, then_term, else_term] end
        | ("cnf_ite_neg1", [if_term]) =>
            let val (condition, then_term, _) = ite if_term
            in mk_disj_terms [if_term, neg condition, neg then_term] end
        | ("cnf_ite_neg2", [if_term]) =>
            let val (condition, _, else_term) = ite if_term
            in mk_disj_terms [if_term, condition, neg else_term] end
        | ("cnf_ite_neg3", [if_term]) =>
            let val (_, then_term, else_term) = ite if_term
            in mk_disj_terms [if_term, neg then_term, neg else_term] end
        | _ => raise ERR name "unsupported CPC CNF rule argument shape"
    in
      if String.isPrefix "cnf_xor_" name then xor_tautology conclusion
      else if String.isPrefix "cnf_ite_" name then
        Tactical.TAC_PROOF (([], conclusion),
          Tactical.THEN
            (Tactic.COND_CASES_TAC,
             tautLib.TAUT_TAC))
      else tautology name conclusion
    end

  fun replay_not_equiv_elim which prems =
    let
      val premise = expect_one_premise which prems
      val (left, right) = boolSyntax.dest_eq
        (boolSyntax.dest_neg (Thm.concl premise))
      val conclusion =
        if which = "not_equiv_elim1" then mk_disj_terms [left, right]
        else mk_disj_terms [boolSyntax.mk_neg left, boolSyntax.mk_neg right]
    in tautological_consequence premise conclusion end

  fun replay_equiv_elim2 conclusion prems =
    let
      val premise = expect_one_premise "equiv_elim2" prems
      fun derived () =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
        in
          tautological_consequence premise
            (boolSyntax.mk_disj (left, boolSyntax.mk_neg right))
        end
    in
      derived ()
      handle Feedback.HOL_ERR _ =>
        case conclusion of
          SOME target => tautological_consequence premise target
        | NONE => if Term.aconv (Thm.concl premise) boolSyntax.T then premise
            else raise ERR "equiv_elim2"
              "non-equality premise requires a declared conclusion"
    end

  fun replay_equiv_elim1 conclusion prems =
    let
      val premise = expect_one_premise "equiv_elim1" prems
      fun derived () =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
        in
          tautological_consequence premise
            (boolSyntax.mk_disj (boolSyntax.mk_neg left, right))
        end
    in
      derived ()
      handle Feedback.HOL_ERR _ =>
        case conclusion of
          SOME target => tautological_consequence premise target
        | NONE => if Term.aconv (Thm.concl premise) boolSyntax.T then premise
            else raise ERR "equiv_elim1"
              "non-equality premise requires a declared conclusion"
    end

  fun arith_prove target =
    profile "CPC(rung:arith/cases)" Library.arith_prove_with_cases target
    handle Feedback.HOL_ERR _ =>
      profile "CPC(rung:arith/full_simp)" Tactical.TAC_PROOF
        (([], target), bossLib.FULL_SIMP_TAC bossLib.arith_ss [])
    handle Feedback.HOL_ERR _ =>
      profile "CPC(rung:arith/int_arith)" Tactical.TAC_PROOF
        (([], target), intLib.ARITH_TAC)

  val arith_prove_from_prems = prove_from_prems arith_prove

  fun replay_arith_abs_eq args =
    case args of
      [left, right] =>
        if Lib.equal (Term.type_of left) intSyntax.int_ty then
          let
            val target = boolSyntax.mk_eq
              (boolSyntax.mk_eq
                (intSyntax.mk_absval left, intSyntax.mk_absval right),
               boolSyntax.mk_disj
                 (boolSyntax.mk_eq (left, right),
                  boolSyntax.mk_eq (left, intSyntax.mk_negated right)))
            val instantiation =
              Term.match_term
                (Thm.concl integerTheory.INT_ABS_EQ_ABS) target
          in
            Drule.INST_TY_TERM instantiation integerTheory.INT_ABS_EQ_ABS
          end
        else
          let
            val target = boolSyntax.mk_eq
              (boolSyntax.mk_eq
                (realSyntax.mk_absval left, realSyntax.mk_absval right),
               boolSyntax.mk_disj
                 (boolSyntax.mk_eq (left, right),
                  boolSyntax.mk_eq (left, realSyntax.mk_negated right)))
          in arith_prove target end
    | _ => raise ERR "arith-abs-eq" "expected two arithmetic arguments"

  fun replay_arith_abs_int_gt args =
    case args of
      [left, right] =>
        let
          val zero = intSyntax.zero_tm
          val neg_left = intSyntax.mk_negated left
          val neg_right = intSyntax.mk_negated right
          val right_nonnegative = intSyntax.mk_geq (right, zero)
          val target = boolSyntax.mk_eq
            (intSyntax.mk_greater
               (intSyntax.mk_absval left, intSyntax.mk_absval right),
             boolSyntax.mk_cond
               (intSyntax.mk_geq (left, zero),
                boolSyntax.mk_cond
                  (right_nonnegative,
                   intSyntax.mk_greater (left, right),
                   intSyntax.mk_greater (left, neg_right)),
                boolSyntax.mk_cond
                  (right_nonnegative,
                   intSyntax.mk_greater (neg_left, right),
                   intSyntax.mk_greater (neg_left, neg_right))))
          val result = Drule.SPECL [left, right]
            HolSmtTheory.smt_int_abs_gt
        in
          if Term.aconv (Thm.concl result) target then result
          else raise ERR "arith-abs-int-gt"
            "instantiated rule does not match its CPC formula"
        end
    | _ => raise ERR "arith-abs-int-gt"
        "expected two integer arguments"

  (* cvc5 uses the same CPC arithmetic rules over Int and Real.  The HOL
     constructors are type-specific, so select the integer form first and
     fall back to the real form while retaining the certificate's shape. *)
  fun arith_less (left, right) =
    intSyntax.mk_less (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_less (left, right)

  fun arith_leq (left, right) =
    intSyntax.mk_leq (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_leq (left, right)

  fun arith_greater (left, right) =
    intSyntax.mk_greater (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_greater (left, right)

  fun arith_geq (left, right) =
    intSyntax.mk_geq (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_geq (left, right)

  fun arith_mult (left, right) =
    intSyntax.mk_mult (left, right)
    handle Feedback.HOL_ERR _ => realSyntax.mk_mult (left, right)

  fun arith_dest_greater tm =
    intSyntax.dest_greater tm
    handle Feedback.HOL_ERR _ => realSyntax.dest_greater tm

  fun arith_dest_less tm =
    intSyntax.dest_less tm
    handle Feedback.HOL_ERR _ => realSyntax.dest_less tm

  fun arith_dest_leq tm =
    intSyntax.dest_leq tm
    handle Feedback.HOL_ERR _ => realSyntax.dest_leq tm

  fun arith_dest_geq tm =
    intSyntax.dest_geq tm
    handle Feedback.HOL_ERR _ => realSyntax.dest_geq tm

  fun replay_arith_mult_abs_comparison prems conclusion =
    let
      datatype direct_factor_relation =
          DirectAbsEq of
            {theorem : Thm.thm, left : Term.term, right : Term.term}
        | DirectAbsGt of
            {theorem : Thm.thm, left : Term.term, right : Term.term}
      datatype strict_factor_relation =
          StrictAbsGt of
            {theorem : Thm.thm, left : Term.term, right : Term.term}
        | StrictAbsEqNonzero of
            {equality : Thm.thm, nonzero : Thm.thm,
             left : Term.term, right : Term.term}
      fun dest_abs term = intSyntax.dest_absval term
        handle Feedback.HOL_ERR _ => realSyntax.dest_absval term
      fun absval term = intSyntax.mk_absval term
        handle Feedback.HOL_ERR _ => realSyntax.mk_absval term
      fun zero term =
        if Lib.equal (Term.type_of term) intSyntax.int_ty then
          intSyntax.zero_tm
        else if Lib.equal (Term.type_of term) realSyntax.real_ty then
          realSyntax.zero_tm
        else raise ERR "arith_mult_abs_comparison"
          "expected integer or real absolute-value factors"
      fun dest_abs_equality theorem =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
        in (dest_abs left, dest_abs right) end
        handle Feedback.HOL_ERR _ =>
          raise ERR "arith_mult_abs_comparison"
            "expected an absolute-value equality"
      fun dest_abs_greater theorem =
        let
          val (left, right) = arith_dest_greater (Thm.concl theorem)
        in (dest_abs left, dest_abs right) end
        handle Feedback.HOL_ERR _ =>
          raise ERR "arith_mult_abs_comparison"
            "expected a strict absolute-value comparison"
      fun apply_context body theorem =
        let
          val variable = Term.genvar
            (Term.type_of (#1 (boolSyntax.dest_eq (Thm.concl theorem))))
          val context = Term.mk_abs (variable, body variable)
        in Conv.BETA_RULE (Thm.AP_TERM context theorem) end
      fun transport label equivalence theorem =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl equivalence)
          val source = Thm.concl theorem
        in
          if Term.aconv source left then Thm.EQ_MP equivalence theorem
          else if Term.aconv source right then
            Thm.EQ_MP (Thm.SYM equivalence) theorem
          else raise ERR "arith_mult_abs_comparison"
            (label ^ " equivalence does not match the pairwise result")
        end
      fun finish result =
        case conclusion of
          NONE => result
        | SOME target =>
            if Term.aconv (Thm.concl result) target then result
            else raise ERR "arith_mult_abs_comparison"
              "reconstructed absolute-product relation does not match"
      fun require_same_type (left, right) =
        Lib.equal (Term.type_of left) (Term.type_of right) orelse
        raise ERR "arith_mult_abs_comparison"
          "all absolute-value factors must have the same arithmetic type"
      fun abs_mult_theorem (left, right) =
        if Lib.equal (Term.type_of left) intSyntax.int_ty then
          Drule.SPECL [left, right] integerTheory.INT_ABS_MUL
        else
          Drule.SPECL [left, right] realTheory.ABS_MUL
      fun abs_nonnegative term =
        if Lib.equal (Term.type_of term) intSyntax.int_ty then
          Drule.SPECL [term] integerTheory.INT_ABS_POS
        else
          Drule.SPECL [term] realTheory.ABS_POS
      fun greater_definition (left, right) =
        let
          val theorem =
            if Lib.equal (Term.type_of left) intSyntax.int_ty then
              integerTheory.INT_GT
            else realTheory.real_gt
        in
          Drule.SPECL [left, right] theorem
        end
      fun greater_as_less (left, right) theorem =
        transport "greater-to-less"
          (greater_definition (absval left, absval right)) theorem
      fun less_as_greater (left, right) theorem =
        transport "less-to-greater"
          (greater_definition (left, right)) theorem
      fun wrap_strict_products
          (left, right, factor, matching_factor, inner_relation) =
        let
          val left_bridge = abs_mult_theorem (left, factor)
          val right_bridge = abs_mult_theorem (right, matching_factor)
          val inner_right =
            arith_mult (absval right, absval matching_factor)
          val outer_left = absval (arith_mult (left, factor))
          val left_relation = apply_context
            (fn product => arith_greater (product, inner_right)) left_bridge
          val with_outer_left = transport
            "left absolute-product bridge" left_relation inner_relation
          val right_relation = apply_context
            (fn product => arith_greater (outer_left, product)) right_bridge
        in
          transport "right absolute-product bridge"
            right_relation with_outer_left
        end
      fun equality_pair first second =
        let
          val (left1, right1) = dest_abs_equality first
          val (left2, right2) = dest_abs_equality second
          val _ = require_same_type (left1, left2)
          val abs_right1 = #2 (boolSyntax.dest_eq (Thm.concl first))
          val abs_left2 = #1 (boolSyntax.dest_eq (Thm.concl second))
          val first_product = apply_context
            (fn factor => arith_mult (factor, abs_left2)) first
          val second_product = apply_context
            (fn factor => arith_mult (abs_right1, factor)) second
          val product_equality = Thm.TRANS first_product second_product
          val (left_bridge, right_bridge) =
            if Lib.equal (Term.type_of left1) intSyntax.int_ty then
              (Thm.SYM (Drule.SPECL [left1, left2]
                 integerTheory.INT_ABS_MUL),
               Drule.SPECL [right1, right2] integerTheory.INT_ABS_MUL)
            else
              (Drule.SPECL [left1, left2] realTheory.ABS_MUL,
               Thm.SYM (Drule.SPECL [right1, right2]
                 realTheory.ABS_MUL))
          val result = Thm.TRANS left_bridge
            (Thm.TRANS product_equality right_bridge)
        in result end
      fun strict_equal_pair
          (strict, left, right, equality, nonzero, factor,
           matching_factor) =
        (require_same_type (left, factor);
        if Lib.equal (Term.type_of left) intSyntax.int_ty then
          let
            val assumptions = Thm.CONJ strict
              (Thm.CONJ equality nonzero)
            val rule = Drule.SPECL
              [left, right, factor, matching_factor]
              HolSmtTheory.smt_int_abs_mul_gt
          in
            Thm.MP rule assumptions
          end
        else
          let
            val positive = transport "real absolute nonzero"
              (Drule.SPECL [factor] realTheory.ABS_NZ) nonzero
            val scaled_equivalence = Thm.MP
              (Drule.SPECL
                [absval right, absval left, absval factor]
                realTheory.REAL_LT_RMUL)
              positive
            val scaled_less = transport "positive real scaling"
              scaled_equivalence
              (greater_as_less (left, right) strict)
            val scaled = less_as_greater
              (arith_mult (absval left, absval factor),
               arith_mult (absval right, absval factor)) scaled_less
            val replace_right_factor = apply_context
              (fn right_factor =>
                arith_greater
                  (arith_mult (absval left, absval factor),
                   arith_mult (absval right, right_factor)))
              equality
            val inner = transport "equal real factor"
              replace_right_factor scaled
          in
            wrap_strict_products
              (left, right, factor, matching_factor, inner)
          end)
      fun strict_strict_pair
          (first, left, right, second, factor, matching_factor) =
        let
          val _ = require_same_type (left, factor)
          val first_less = greater_as_less (left, right) first
          val second_less = greater_as_less
            (factor, matching_factor) second
          val assumptions = Thm.CONJ (abs_nonnegative right)
            (Thm.CONJ (abs_nonnegative matching_factor)
              (Thm.CONJ first_less second_less))
          val rule =
            if Lib.equal (Term.type_of left) intSyntax.int_ty then
              Drule.SPECL
                [absval right, absval left, absval matching_factor,
                 absval factor]
                integerTheory.INT_LT_MUL2
            else
              Drule.SPECL
                [absval right, absval left, absval matching_factor,
                 absval factor]
                realTheory.REAL_LT_MUL2
          val inner_less = Thm.MP rule assumptions
          val inner = less_as_greater
            (arith_mult (absval left, absval factor),
             arith_mult (absval right, absval matching_factor)) inner_less
        in
          wrap_strict_products
            (left, right, factor, matching_factor, inner)
        end
      fun direct_relation theorem =
        if Lib.can dest_abs_greater theorem then
          let val (left, right) = dest_abs_greater theorem
          in DirectAbsGt
            {theorem = theorem, left = left, right = right}
          end
        else
          let val (left, right) = dest_abs_equality theorem
          in DirectAbsEq
            {theorem = theorem, left = left, right = right}
          end
      fun malformed_strict_tail () =
        raise ERR "arith_mult_abs_comparison"
          "expected |t| > |s| or (|t| = |s| and t <> 0)"
      fun dest_guarded_equality theorem =
        let
          val _ = boolSyntax.dest_conj (Thm.concl theorem)
          val equality = Thm.CONJUNCT1 theorem
          val nonzero = Thm.CONJUNCT2 theorem
          val (left, right) = dest_abs_equality equality
          val expected_zero = zero left
          val (guard_left, guard_right) =
            boolSyntax.dest_eq (boolSyntax.dest_neg (Thm.concl nonzero))
        in
          (equality, nonzero, left, right, expected_zero,
           guard_left, guard_right)
        end
        handle Feedback.HOL_ERR _ => malformed_strict_tail ()
      fun strict_tail_relation theorem =
        if Lib.can dest_abs_greater theorem then
          let val (left, right) = dest_abs_greater theorem
          in StrictAbsGt
            {theorem = theorem, left = left, right = right}
          end
        else if Lib.can dest_abs_equality theorem then
          raise ERR "arith_mult_abs_comparison"
            "strict mode requires a nonzero side condition on equal factors"
        else
          let
            val (equality, nonzero, left, right, expected_zero,
                 guard_left, guard_right) = dest_guarded_equality theorem
            val oriented_nonzero =
              if Term.aconv guard_left left andalso
                 Term.aconv guard_right expected_zero
              then nonzero
              else if Term.aconv guard_left expected_zero andalso
                      Term.aconv guard_right left
              then
                let
                  val expected = boolSyntax.mk_eq (left, expected_zero)
                  val symmetry = Thm.SYM (Thm.ASSUME expected)
                  val contradiction = Thm.MP (Thm.NOT_ELIM nonzero)
                    symmetry
                in
                  Thm.NOT_INTRO (Thm.DISCH expected contradiction)
                end
              else raise ERR "arith_mult_abs_comparison"
                "nonzero side condition does not match its left factor"
          in
            StrictAbsEqNonzero
              {equality = equality, nonzero = oriented_nonzero,
               left = left, right = right}
          end
      fun equality_fold (theorem, result) = equality_pair result theorem
      fun strict_fold (theorem, (result, left, right)) =
        case strict_tail_relation theorem of
          StrictAbsGt
            {theorem, left = factor, right = matching_factor} =>
            (strict_strict_pair
               (result, left, right, theorem, factor, matching_factor),
             arith_mult (left, factor),
             arith_mult (right, matching_factor))
        | StrictAbsEqNonzero
            {equality, nonzero, left = factor,
             right = matching_factor} =>
            (strict_equal_pair
               (result, left, right, equality, nonzero, factor,
                matching_factor),
             arith_mult (left, factor),
             arith_mult (right, matching_factor))
    in
      case prems of
        [] => raise ERR "arith_mult_abs_comparison"
          "expected at least one absolute-value factor premise"
      | first :: rest =>
          let
            val first_relation = direct_relation first
              handle Feedback.HOL_ERR _ =>
                raise ERR "arith_mult_abs_comparison"
                  "first premise must be |t1| = |s1| or |t1| > |s1|"
          in
            case first_relation of
              DirectAbsEq _ => finish (List.foldl equality_fold first rest)
            | DirectAbsGt {left, right, ...} =>
                finish (#1 (List.foldl strict_fold
                  (first, left, right) rest))
          end
    end

  fun arith_list_mk_plus terms =
    intSyntax.list_mk_plus terms
    handle Feedback.HOL_ERR _ => realSyntax.list_mk_plus terms

  fun arith_zero tm =
    let val _ = intSyntax.mk_geq (tm, intSyntax.zero_tm)
    in intSyntax.zero_tm end
    handle Feedback.HOL_ERR _ => realSyntax.zero_tm

  fun replay_arith_max_geq1 args =
    case args of
      [left, right] =>
        let
          val maximum = boolSyntax.mk_cond
            (arith_geq (left, right), left, right)
          val target = boolSyntax.mk_eq
            (arith_geq (maximum, left), boolSyntax.T)
        in
          arith_prove target
        end
    | _ => raise ERR "arith-max-geq1" "expected two arithmetic arguments"

  fun replay_arith_min_lt2 args =
    case args of
      [left, right] =>
        let
          val minimum = boolSyntax.mk_cond
            (boolSyntax.mk_neg (arith_geq (left, right)), left, right)
          val target = boolSyntax.mk_eq
            (arith_leq (minimum, right), boolSyntax.T)
        in
          arith_prove target
        end
    | _ => raise ERR "arith-min-lt2" "expected two arithmetic arguments"

  fun replay_arith_int_geq_tighten (integer, real_bound, rounded) =
    let
      fun real_of_int_leq (left, right) =
        let
          val target = boolSyntax.mk_eq
            (realSyntax.mk_leq (intrealSyntax.mk_real_of_int left,
              intrealSyntax.mk_real_of_int right),
             intSyntax.mk_leq (left, right))
        in
          Drule.INST_TY_TERM
            (Term.match_term (Thm.concl intrealTheory.real_of_int_le) target)
            intrealTheory.real_of_int_le
        end
      val left = realSyntax.mk_geq
        (intrealSyntax.mk_real_of_int integer, real_bound)
      val right = intSyntax.mk_geq (integer, rounded)
      val target = boolSyntax.mk_eq (left, right)
      val not_right = boolSyntax.mk_neg right
      val predecessor = intSyntax.mk_minus (rounded, intSyntax.one_tm)
      val integer_at_most_predecessor = Tactical.TAC_PROOF
        (([not_right], intSyntax.mk_leq (integer, predecessor)),
         intLib.ARITH_TAC)
      val real_at_most_predecessor = Thm.EQ_MP (Thm.SYM
        (real_of_int_leq (integer, predecessor)))
        integer_at_most_predecessor
      val left_normalization = Conv.REWR_CONV realTheory.real_ge left
      val bound_lt_real_predecessor = Tactical.TAC_PROOF
        (([], realSyntax.mk_less
          (intrealSyntax.mk_real_of_int predecessor, real_bound)),
         Tactical.THEN
           (bossLib.SIMP_TAC (bossLib.srw_ss()) [realTheory.real_div],
            Tactic.CONV_TAC RealField.REAL_RAT_REDUCE_CONV))
      val q_at_integer = Thm.EQ_MP left_normalization (Thm.ASSUME left)
      val q_at_most_predecessor = Drule.PROVE_HYP q_at_integer
        (Drule.PROVE_HYP real_at_most_predecessor
          (Tactical.TAC_PROOF
            (([Thm.concl q_at_integer, Thm.concl real_at_most_predecessor],
              realSyntax.mk_leq (real_bound,
                intrealSyntax.mk_real_of_int predecessor)),
             metisLib.METIS_TAC [realTheory.REAL_LE_TRANS])))
      val no_q_at_most_predecessor = Drule.PROVE_HYP
        bound_lt_real_predecessor
        (Tactical.TAC_PROOF
          (([Thm.concl bound_lt_real_predecessor],
            boolSyntax.mk_neg (Thm.concl q_at_most_predecessor)),
           metisLib.METIS_TAC [realTheory.REAL_NOT_LE]))
      val contradiction = Thm.MP (Thm.NOT_ELIM no_q_at_most_predecessor)
        q_at_most_predecessor
      val forward = Thm.DISCH left
        (Thm.MP (Thm.SPEC right HolSmtTheory.NOT_NOT_ELIM)
          (Thm.NOT_INTRO (Thm.DISCH not_right contradiction)))
      val right_normalization = Conv.REWR_CONV integerTheory.int_ge right
      val real_at_least_rounded = Thm.EQ_MP (Thm.SYM
        (real_of_int_leq (rounded, integer)))
        (Thm.EQ_MP right_normalization (Thm.ASSUME right))
      val bound_at_most_rounded = Tactical.TAC_PROOF
        (([], realSyntax.mk_leq
          (real_bound, intrealSyntax.mk_real_of_int rounded)),
         Tactical.THEN
           (bossLib.SIMP_TAC (bossLib.srw_ss()) [realTheory.real_div],
            Tactic.CONV_TAC RealField.REAL_RAT_REDUCE_CONV))
      val reverse = Thm.DISCH right
        (Thm.EQ_MP (Thm.SYM left_normalization)
          (Drule.PROVE_HYP bound_at_most_rounded
            (Drule.PROVE_HYP real_at_least_rounded
              (Tactical.TAC_PROOF
                (([Thm.concl bound_at_most_rounded,
                   Thm.concl real_at_least_rounded],
                  boolSyntax.rhs (Thm.concl left_normalization)),
                 metisLib.METIS_TAC [realTheory.REAL_LE_TRANS])))))
    in Drule.IMP_ANTISYM_RULE forward reverse end
    handle Feedback.HOL_ERR holerr =>
      raise ERR "arith-int-geq-tighten" (Feedback.message_of holerr)
    | exn => raise ERR "arith-int-geq-tighten" (General.exnMessage exn)

  fun replay_arith_rule name args =
    if name = "arith-int-geq-tighten" then
      (case args of
         [integer, real_bound, rounded] =>
           replay_arith_int_geq_tighten (integer, real_bound, rounded)
       | _ => raise ERR name "unsupported CPC arithmetic rule argument shape")
    else let
      val target =
        case (name, args) of
          ("arith_poly_norm", [eq]) => eq
        | ("arith-elim-lt", [left, right]) =>
            boolSyntax.mk_eq (arith_less (left, right),
              boolSyntax.mk_neg (arith_geq (left, right)))
        | ("arith-elim-leq", [left, right]) =>
            boolSyntax.mk_eq (arith_leq (left, right),
              arith_geq (right, left))
        | ("arith-elim-gt", [left, right]) =>
            boolSyntax.mk_eq (arith_greater (left, right),
              boolSyntax.mk_neg (arith_geq (right, left)))
        | ("arith-leq-norm", [left, right]) =>
            boolSyntax.mk_eq (intSyntax.mk_leq (left, right),
              boolSyntax.mk_neg (intSyntax.mk_geq
                (left, intSyntax.mk_plus (right, intSyntax.one_tm))))
        | ("arith-eq-elim-int", [left, right]) =>
            boolSyntax.mk_eq
              (boolSyntax.mk_eq (left, right),
               boolSyntax.mk_conj
                 (intSyntax.mk_geq (left, right), intSyntax.mk_leq (left, right)))
        | ("arith-geq-norm1-int", [left, right]) =>
            boolSyntax.mk_eq (intSyntax.mk_geq (left, right),
              intSyntax.mk_geq
                (intSyntax.mk_minus (left, right), intSyntax.zero_tm))
        | ("arith-geq-norm1-real", [left, right]) =>
            boolSyntax.mk_eq (realSyntax.mk_geq (left, right),
              realSyntax.mk_geq
                (realSyntax.mk_minus (left, right), realSyntax.zero_tm))
        | ("arith-geq-tighten", [left, right]) =>
            boolSyntax.mk_eq
              (boolSyntax.mk_neg (intSyntax.mk_geq (left, right)),
               intSyntax.mk_geq
                 (right, intSyntax.mk_plus (left, intSyntax.one_tm)))
        | _ => raise ERR name "unsupported CPC arithmetic rule argument shape"
    in
      if name = "arith-elim-lt" then
        (case args of
           [left, right] =>
             Thm.SYM (Drule.SPECL [right, left]
               (if Lib.equal (Term.type_of left) intSyntax.int_ty then
                  integerTheory.INT_NOT_LE
                else realTheory.REAL_NOT_LE))
         | _ => raise ERR name "unsupported CPC arithmetic rule argument shape")
      else if name = "arith_poly_norm" then
        profile "CPC(rung:arith/poly_norm_canonical)"
          SmtReplayCanon.arith_poly_norm_prove target
      else if name = "arith-leq-norm" then
        simpLib.SIMP_PROVE (bossLib.srw_ss())
          [integerTheory.int_ge, integerTheory.INT_NOT_LE,
           integerTheory.INT_NOT_LT, integerTheory.INT_LE_LT1] target
      else arith_prove target
    end

  (* Couple arithmetic relation rewrites to the exact syntax constructed by
     the successful semantic rule.  In particular, ARITH_EQ_ELIM_INT creates
     a binary conjunction here; recording that boundary is construction, not
     recovery from the erased HOL term or from a producer-name lookup. *)
  fun replay_arith_rule_result name
      (located_args : located_term list) =
    let
      val args = List.map (fn located => #term located) located_args
      val theorem = replay_arith_rule name args
      val provenance =
        case (name, located_args) of
          ("arith_poly_norm", [target]) => #provenance target
        | ("arith-eq-elim-int", [left, right]) =>
            let
              val left_provenance = #provenance left
              val right_provenance = #provenance right
            in
              EqualityProvenance
                (EqualityProvenance
                   (left_provenance, right_provenance),
                 ConjunctionProvenance
                   (ArithReductionConjunction,
                    [AtomicProvenance, AtomicProvenance]))
            end
        | _ => conjunction_free_semantic_provenance
            ("arithmetic relation rewrite contains an exact conjunction")
            (Thm.concl theorem)
    in
      exact_result provenance theorem
    end

  fun replay_arrays_select_const args =
    case args of
      [target] => Tactical.TAC_PROOF (([], target),
        bossLib.SIMP_TAC boolSimps.bool_ss [])
    | _ => raise ERR "arrays-select-const" "expected one equality"

  (* Compact CPC omits the conclusion of the read-over-write rules and gives
     only the selected update term.  Reconstruct the equality specified by
     the rule before handing it to the bounded, kernel-checked array prover. *)
  fun replay_arrays_read_over_write name prems conclusion args =
    let
      fun selected_update selected =
        let
          val (updated, selected_index) = Term.dest_comb selected
          val ((stored_index, stored_value), array) =
            combinSyntax.dest_update_comb updated
        in
          (selected_index, stored_index, stored_value, array)
        end
        handle Feedback.HOL_ERR _ =>
          raise ERR name "expected a select from a stored array"
      fun omitted_target () =
        case args of
          [selected] =>
            let
              val (selected_index, stored_index, stored_value, array) =
                selected_update selected
              val right =
                if name = "arrays_read_over_write_1" then
                  if Term.aconv selected_index stored_index then stored_value
                  else raise ERR name "select and store indices differ"
                else
                  Term.mk_comb (array, selected_index)
            in
              boolSyntax.mk_eq (selected, right)
            end
        | _ => raise ERR name "expected one selected update term"
      val target =
        case conclusion of SOME target => target | NONE => omitted_target ()
    in
      prove_from_prems SmtArrayProve.array_prove prems target
    end

  fun replay_ite_not_cond args =
    case args of
      [condition, then_tm, else_tm] =>
        let val target = boolSyntax.mk_eq
          (boolSyntax.mk_cond (boolSyntax.mk_neg condition, then_tm, else_tm),
           boolSyntax.mk_cond (condition, else_tm, then_tm))
        in
          Tactical.TAC_PROOF (([], target),
            Tactical.THEN (Tactic.BOOL_CASES_TAC condition,
              bossLib.ASM_SIMP_TAC boolSimps.bool_ss []))
        end
    | _ => raise ERR "ite-not-cond" "expected condition and two branches"

  fun replay_ite_true_cond args =
    case args of
      [then_tm, else_tm] =>
        let
          val target = boolSyntax.mk_eq
            (boolSyntax.mk_cond (boolSyntax.T, then_tm, else_tm), then_tm)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC boolSimps.bool_ss [])
        end
    | _ => raise ERR "ite-true-cond" "expected two branches"

  fun replay_ite_then_true args =
    case args of
      [condition, else_tm] =>
        let
          val target = boolSyntax.mk_eq
            (boolSyntax.mk_cond (condition, boolSyntax.T, else_tm),
             boolSyntax.mk_disj (condition, else_tm))
        in
          Tactical.TAC_PROOF (([], target),
            Tactical.THEN (Tactic.BOOL_CASES_TAC condition,
              bossLib.ASM_SIMP_TAC boolSimps.bool_ss []))
        end
    | _ => raise ERR "ite-then-true" "expected condition and else branch"

  fun replay_ite_false_cond args =
    case args of
      [then_tm, else_tm] =>
        let
          val target = boolSyntax.mk_eq
            (boolSyntax.mk_cond (boolSyntax.F, then_tm, else_tm), else_tm)
        in
          Tactical.TAC_PROOF (([], target),
            bossLib.SIMP_TAC boolSimps.bool_ss [])
        end
    | _ => raise ERR "ite-false-cond" "expected two branches"

  (* cvc5 can emit a TRUST_THEORY_REWRITE equating its unconstrained
     division-by-zero term with HOL's total division.  That equality is not
     valid for smt_rdiv, so never assert it.  Return only a reflexive theorem
     for this exact shape; irrelevant congruence branches discard reflexive
     premises, while any proof that actually needs the rewrite still fails. *)
  fun replay_trust state prems args =
    let
      val target = expect_one_arg "trust" args
      fun context_terms () =
        HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
        List.map Thm.concl prems
      fun discharge_prems thm =
        List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
          thm prems
      fun prove_scoped_arithmetic () =
        discharge_prems (Tactical.TAC_PROOF ((context_terms (), target),
          Tactical.THEN
            (Tactical.REPEAT Tactic.COND_CASES_TAC,
             Tactical.THEN
               (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                intLib.ARITH_TAC))))
      fun replay_rdiv () =
        let
          val (left, right) = boolSyntax.dest_eq target
          val (f, operands) = boolSyntax.strip_comb left
          val smt_rdiv = Term.prim_mk_const
            {Thy = "HolSmt", Name = "smt_rdiv"}
          val (numerator, denominator) =
            case operands of [x, y] => (x, y)
            | _ => raise ERR "trust" "expected binary smt_rdiv term"
          val _ = Term.same_const f smt_rdiv orelse
            raise ERR "trust" "unsupported trusted operator"
          fun valid_nonzero_rewrite () =
            let
              val nonzero = Tactical.TAC_PROOF
                (([], boolSyntax.mk_neg
                    (boolSyntax.mk_eq (denominator, realSyntax.zero_tm))),
                 bossLib.SIMP_TAC (bossLib.srw_ss()) [])
              val to_div = Thm.MP
                (Drule.SPECL [numerator, denominator]
                  HolSmtTheory.smt_rdiv_eq_div) nonzero
              val div_to_right = Tactical.TAC_PROOF
                (([], boolSyntax.mk_eq
                    (realSyntax.mk_div (numerator, denominator), right)),
                 bossLib.SIMP_TAC (bossLib.srw_ss()) [realTheory.real_div])
            in
              Thm.TRANS to_div div_to_right
            end
          fun irrelevant_zero_rewrite () =
            let
              val _ = Term.aconv right
                (realSyntax.mk_div (numerator, denominator)) orelse
                raise ERR "trust" "trusted rewrite is not rdiv-to-division"
              val _ = Tactical.TAC_PROOF
                (([], boolSyntax.mk_eq (denominator, realSyntax.zero_tm)),
                 bossLib.SIMP_TAC (bossLib.srw_ss()) [])
            in
              Thm.REFL left
            end
        in
          profile "CPC(rung:trust/rdiv_nonzero)" valid_nonzero_rewrite ()
          handle Feedback.HOL_ERR _ =>
            profile "CPC(rung:trust/rdiv_zero_irrelevant)"
              irrelevant_zero_rewrite ()
        end
      fun replay_set () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          val thm = SmtResource.with_resource_step_time "Set" "contextual"
            (fn () =>
              (List.app (SmtResource.check_resource_goal "Set" "contextual")
                 (target :: context);
               Tactical.TAC_PROOF ((context, target),
                 bossLib.ASM_SIMP_TAC (bossLib.srw_ss ()) []))) ()
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else
            SmtArrayProve.array_prove target
      fun unsupported_set () =
        raise ERR "trust"
          ("unsupported CPC Set step: rule=trust; theory=set; " ^
           "conclusion=" ^ Library.term_to_string target)
      fun replay_bag () =
        SmtBagProve.bag_prove_with_arith arith_prove target
      fun prove_scoped_bag () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          val thm = SmtResource.with_resource_step_time "Bag" "contextual"
            (fn () =>
              (SmtResource.check_resource_goal "Bag" "contextual" target;
               Tactical.TAC_PROOF ((context, target),
                 Tactical.THEN
                   (Tactical.REPEAT Tactic.COND_CASES_TAC,
                    Tactical.THEN
                      (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                       intLib.ARITH_TAC))))) ()
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else
            raise ERR "trust"
              ("unsupported CPC Bag step: rule=trust; theory=bag; " ^
               "conclusion=" ^ Library.term_to_string target)
      fun replay_fp () =
        SmtFpProve.fp_prove_with_decompositions_and_arith
          arith_prove [] target
      fun unsupported_fp () =
        raise ERR "trust"
          ("unsupported CPC FP step: rule=trust; theory=fp; " ^
           "conclusion=" ^ Library.term_to_string target)
      fun next prover continuation =
        prover ()
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else continuation ()
      fun replay_seq () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          val thm =
            SmtSeqProve.seq_prove target
            handle Feedback.HOL_ERR holerr =>
              if SmtResource.is_resource_gate holerr then
                raise Feedback.HOL_ERR holerr
              else
                SmtSeqProve.seq_contextual_prove context target
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
      fun string_context () =
        List.exists SmtStringProve.has_string_theory_term
          (target :: context_terms ())
      fun replay_string () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          val thm =
            SmtStringProve.string_rewrite_prove target
            handle Feedback.HOL_ERR _ =>
              SmtStringProve.string_prove arith_prove target
            handle Feedback.HOL_ERR _ =>
              SmtStringProve.string_contextual_prove context target
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
      fun set_context () =
        List.exists SmtArrayProve.has_set_term (target :: context_terms ())
      fun bag_context () =
        List.exists SmtBagProve.has_native_bag_encoding
          (target :: context_terms ())
      fun fp_context () =
        List.exists SmtFpProve.has_fp_theory_term (target :: context_terms ())
    in
      (* Native Seq, Set, and Bag trusts have no unchecked fallback.  Bag's
         second rung is the checked contextual simplifier used by its shared
         D2 prover; failure records a theory-specific CPC obligation. *)
      if SmtSeqProve.has_seq_type target then
        profile "CPC(rung:trust/seq)" replay_seq ()
      else if string_context () then
        profile "CPC(rung:trust/string)" replay_string ()
      else if bag_context () then
        next (fn () => profile "CPC(rung:trust/bag)" replay_bag ())
          (fn () => profile "CPC(rung:trust/bag_context)"
            prove_scoped_bag ())
      else if set_context () then
        next (fn () => profile "CPC(rung:trust/set)" replay_set ())
          unsupported_set
      else if fp_context () then
        next (fn () => profile "CPC(rung:trust/fp)" replay_fp ())
          unsupported_fp
      else
        next (fn () => profile "CPC(rung:trust/scoped_arithmetic)"
          prove_scoped_arithmetic ())
          (fn () => profile "CPC(rung:trust/rdiv)" replay_rdiv ())
    end

  fun replay_ite_eq args =
    let
      val ite_tm = expect_one_arg "ite_eq" args
      val (condition, then_tm, else_tm) = boolSyntax.dest_cond ite_tm
      val target = boolSyntax.mk_cond
        (condition, boolSyntax.mk_eq (ite_tm, then_tm),
         boolSyntax.mk_eq (ite_tm, else_tm))
    in
      Tactical.TAC_PROOF (([], target),
        Tactical.THEN (Tactic.COND_CASES_TAC,
          bossLib.ASM_SIMP_TAC boolSimps.bool_ss []))
    end

  fun replay_ite_elim1 prems =
    let
      val premise = expect_one_premise "ite_elim1" prems
    in
      if Term.aconv (Thm.concl premise) boolSyntax.T then premise
      else
        let
          val (condition, then_tm, _) =
            boolSyntax.dest_cond (Thm.concl premise)
            handle Feedback.HOL_ERR _ => raise ERR "ite_elim1"
              ("premise is not a conditional: " ^
               Library.term_to_string (Thm.concl premise))
        in tautological_consequence premise
          (mk_disj_terms [boolSyntax.mk_neg condition, then_tm]) end
    end

  fun replay_ite_elim2 prems =
    let
      val premise = expect_one_premise "ite_elim2" prems
    in
      if Term.aconv (Thm.concl premise) boolSyntax.T then premise
      else
        let
          val (condition, _, else_tm) =
            boolSyntax.dest_cond (Thm.concl premise)
            handle Feedback.HOL_ERR _ => raise ERR "ite_elim2"
              ("premise is not a conditional: " ^
               Library.term_to_string (Thm.concl premise))
        in tautological_consequence premise
          (mk_disj_terms [condition, else_tm]) end
    end

  fun replay_scope state prems =
    let
      val premise = expect_one_premise "scope" prems
      (* Canonical replay can retain [T] as support when a syntactically
         nontrivial equality reduces to truth inside a TRANS or resolution
         chain.  It is not a CPC scope assumption: discharge it with the
         kernel theorem [|- T] before auditing the hypotheses that survive
         the pop. *)
      val premise =
        if HOLset.member (Thm.hypset premise, boolSyntax.T) then
          Drule.PROVE_HYP boolTheory.TRUTH premise
        else premise
      val (hyp, state) = pop_scope_hyp state
      val thm = Thm.DISCH hyp premise
      val allowed = HOLset.addList (#asserted_hyps state, #scope_hyps state)
      val _ = HOLset.isSubset (Thm.hypset thm, allowed) orelse
        raise ERR "scope"
          ("CPC scope pop did not close all of its local assumptions; " ^
           "popped=" ^ Library.term_to_string hyp ^ "; residual=" ^
           String.concatWith ", " (List.map Library.term_to_string
             (HOLset.listItems (HOLset.difference (Thm.hypset thm, allowed)))))
    in
      (state, thm)
    end

  fun replay_process_scope strong_canon args prems =
    let
      val premise = expect_one_premise "process_scope" prems
      (* The CPC printer records the original body conclusion as its sole
         argument.  Stop uncurrying at that exact term: the body itself may
         be an implication, which is not an additional scoped assumption. *)
      val scope_result = case args of [tm] => tm
        | _ => raise ERR "process_scope" "expected one CPC :args term"
      fun dest_scope tm acc =
        if Term.aconv tm scope_result then (List.rev acc, NONE)
        else if Term.aconv (canonical_term tm) (canonical_term scope_result)
        then (List.rev acc, SOME tm)
        else
          let val (antecedent, consequent) = boolSyntax.dest_imp tm
          in dest_scope consequent (antecedent :: acc) end
          handle Feedback.HOL_ERR _ =>
            (List.rev acc, SOME tm)
      fun mk_conj [tm] = tm
        | mk_conj (tm :: rest) = boolSyntax.mk_conj (tm, mk_conj rest)
        | mk_conj [] = raise ERR "process_scope" "empty scope implication"
      val (antecedents, normalized_result) =
        dest_scope (Thm.concl premise) []
      val conjunction = mk_conj antecedents
      val target = if Term.aconv scope_result boolSyntax.F then
        boolSyntax.mk_neg conjunction
      else boolSyntax.mk_imp (conjunction, scope_result)
      val conjunction_thm = Thm.ASSUME conjunction
      val applied = List.foldl
        (fn (antecedent, implication) =>
          Thm.MP implication (Library.conj_elim
            (conjunction_thm, antecedent)))
        premise antecedents
      val normalized = case normalized_result of
          NONE => applied
        | SOME tm =>
            let
              fun bridge canon =
                let
                  val tm_norm = canon tm
                  val result_norm = canon scope_result
                in Thm.TRANS tm_norm (Thm.SYM result_norm) end
              fun arithmetic_bridge () =
                let
                  val tm_norm = SmtReplayCanon.cpc_canon_conv tm
                  val result_norm =
                    SmtReplayCanon.cpc_canon_conv scope_result
                  val normalized_tm = boolSyntax.rhs (Thm.concl tm_norm)
                  val normalized_result =
                    boolSyntax.rhs (Thm.concl result_norm)
                  val middle = arith_prove
                    (boolSyntax.mk_eq (normalized_tm, normalized_result))
                in
                  Thm.TRANS tm_norm
                    (Thm.TRANS middle (Thm.SYM result_norm))
                end
              val bridge =
                bridge SmtReplayCanon.cpc_canon_conv
                handle Feedback.HOL_ERR _ =>
                  (arithmetic_bridge ()
                   handle Feedback.HOL_ERR _ =>
                     (bridge strong_canon
                      handle Feedback.HOL_ERR holerr =>
                        raise ERR "process_scope"
                          ("scope result canonicalization failed; local=" ^
                           Library.term_to_string tm ^ "; expected=" ^
                           Library.term_to_string scope_result ^ "; " ^
                           Feedback.message_of holerr)))
            in Thm.EQ_MP bridge applied end
      val discharged = Thm.DISCH conjunction normalized
      val result =
        if Term.aconv scope_result boolSyntax.F then Thm.NOT_INTRO discharged
        else discharged
    in
      if Term.aconv (Thm.concl result) target then result
      else raise ERR "process_scope" "direct scope normalization shape mismatch"
    end

  fun replay_not_and prems =
    let
      val premise = expect_one_premise "not_and" prems
      val conjunction =
        (boolSyntax.dest_neg (Thm.concl premise)
         handle Feedback.HOL_ERR _ =>
           let
             val (antecedent, consequent) =
               boolSyntax.dest_imp (Thm.concl premise)
             val _ = Term.aconv consequent boolSyntax.F orelse
               raise ERR "not_and" "implication consequent is not false"
           in antecedent end)
        handle Feedback.HOL_ERR _ => raise ERR "not_and"
          ("premise is neither a negation nor an implication to false: " ^
           Library.term_to_string (Thm.concl premise))
      val target = mk_disj_terms
        (List.map boolSyntax.mk_neg (boolSyntax.strip_conj conjunction))
    in tautological_consequence premise target end

  fun replay_not_or_elim args prems =
    let
      val premise = expect_one_premise "not_or_elim" prems
      val index_term = expect_one_arg "not_or_elim" args
      val index = Arbnum.toInt
        (numSyntax.dest_numeral index_term
         handle Feedback.HOL_ERR _ =>
           numSyntax.dest_numeral (intSyntax.dest_injected index_term))
      val disjunction = boolSyntax.dest_neg (Thm.concl premise)
      val selected = List.nth (boolSyntax.strip_disj disjunction, index)
        handle Subscript => raise ERR "not_or_elim"
          "CPC disjunction index is outside the premise"
    in
      tautological_consequence premise (boolSyntax.mk_neg selected)
    end

  fun replay_not_not_elim prems =
    let
      val premise = expect_one_premise "not_not_elim" prems
      val result = boolSyntax.dest_neg (boolSyntax.dest_neg (Thm.concl premise))
    in
      tautological_consequence premise result
    end

  fun replay_and_intro (premise_steps : replayed_step list) =
    let
      val prems = List.map
        step_theorem premise_steps
      fun construct theorems =
        case theorems of
          [] => raise ERR "and_intro" "expected CPC premises"
        | [premise] => premise
        | premise :: rest => Thm.CONJ premise (construct rest)
    in
      case premise_steps of
        [] => raise ERR "and_intro" "expected CPC premises"
      | [premise] => (step_theorem premise, step_provenance premise)
      | _ => (construct prems,
          ConjunctionProvenance (AndIntroConjunction,
            List.map step_provenance premise_steps))
    end

  fun replay_skolemize prems =
    let
      fun select_witnesses thm =
        if boolSyntax.is_exists (Thm.concl thm) then
          select_witnesses (Drule.SELECT_RULE thm)
        else
          let
            val quantified = boolSyntax.dest_neg (Thm.concl thm)
            val _ = boolSyntax.dest_forall quantified
            val exposed = Thm.EQ_MP
              (Conv.HO_REWR_CONV boolTheory.NOT_FORALL_THM (Thm.concl thm)) thm
          in
            select_witnesses exposed
          end
          handle Feedback.HOL_ERR _ => thm
    in
      select_witnesses (expect_one_premise "skolemize" prems)
    end

  fun replay_arith_mult_neg args =
    case args of
      [coefficient, equality] =>
        let
          datatype relation = Eq | Lt | Le | Gt | Ge
          val (relation, left, right) =
            (let val (left, right) = boolSyntax.dest_eq equality
             in (Eq, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_less equality
             in (Lt, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_leq equality
             in (Le, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_greater equality
             in (Gt, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_geq equality
             in (Ge, left, right) end
             handle Feedback.HOL_ERR _ =>
            raise ERR "arith_mult_neg"
              "expected relation (=, <, <=, >, or >=)")
          val product_left = arith_mult (coefficient, left)
          val product_right = arith_mult (coefficient, right)
          val result =
            case relation of
              Eq => boolSyntax.mk_eq (product_left, product_right)
            | Lt => arith_greater (product_left, product_right)
            | Le => arith_geq (product_left, product_right)
            | Gt => arith_less (product_left, product_right)
            | Ge => arith_leq (product_left, product_right)
          val target = boolSyntax.mk_imp
            (boolSyntax.mk_conj
             (arith_less (coefficient, arith_zero coefficient), equality),
             result)
        in arith_prove target end
    | _ => raise ERR "arith_mult_neg"
      "expected a coefficient and an arithmetic relation"

  fun replay_arith_mult_pos args =
    case args of
      [coefficient, equality] =>
        let
          datatype relation = Eq | Lt | Le | Gt | Ge
          val (relation, left, right) =
            (let val (left, right) = boolSyntax.dest_eq equality
             in (Eq, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_less equality
             in (Lt, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_leq equality
             in (Le, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_greater equality
             in (Gt, left, right) end
             handle Feedback.HOL_ERR _ =>
            let val (left, right) = arith_dest_geq equality
             in (Ge, left, right) end)
          val product_left = arith_mult (coefficient, left)
          val product_right = arith_mult (coefficient, right)
          val result =
            case relation of
              Eq => boolSyntax.mk_eq (product_left, product_right)
            | Lt => arith_less (product_left, product_right)
            | Le => arith_leq (product_left, product_right)
            | Gt => arith_greater (product_left, product_right)
            | Ge => arith_geq (product_left, product_right)
          val target = boolSyntax.mk_imp
            (boolSyntax.mk_conj
             (arith_greater (coefficient, arith_zero coefficient), equality),
             result)
        in arith_prove target end
    | _ => raise ERR "arith_mult_pos"
      "expected a coefficient and a non-negative arithmetic literal"

  (* CPC uses this rule to establish that two strictly positive factors have
     a strictly positive product. *)
  fun replay_arith_mult_sign args =
    case args of
      [positive_factors, product] =>
        arith_prove (boolSyntax.mk_imp
          (positive_factors,
           arith_greater (product, arith_zero product)))
    | _ => raise ERR "arith_mult_sign"
      "expected a conjunction of positive factors and their product"

  fun replay_arith_trichotomy declared prems =
    let
      datatype relation = Eq | Lt | Le | Gt | Ge
      fun dest_relation tm =
        let val (left, right) = boolSyntax.dest_eq tm in (Eq, left, right) end
        handle Feedback.HOL_ERR _ =>
        let val (left, right) = arith_dest_less tm in (Lt, left, right) end
        handle Feedback.HOL_ERR _ =>
        let val (left, right) = arith_dest_leq tm in (Le, left, right) end
        handle Feedback.HOL_ERR _ =>
        let val (left, right) = arith_dest_greater tm in (Gt, left, right) end
        handle Feedback.HOL_ERR _ =>
        let val (left, right) = arith_dest_geq tm in (Ge, left, right) end
      fun negate_relation (Lt, left, right) = (Ge, left, right)
        | negate_relation (Le, left, right) = (Gt, left, right)
        | negate_relation (Gt, left, right) = (Le, left, right)
        | negate_relation (Ge, left, right) = (Lt, left, right)
        | negate_relation (Eq, _, _) =
            raise ERR "arith_trichotomy"
              "CPC arithmetic trichotomy does not accept a disequality literal"
      fun normalize_not tm =
        let
          fun strip parity term =
            (strip (not parity) (boolSyntax.dest_neg term)
             handle Feedback.HOL_ERR _ => (parity, term))
          val (negated, atom) = strip true tm
          val result = dest_relation atom
        in if negated then negate_relation result else result end
      fun relation_name Eq = "="
        | relation_name Lt = "<"
        | relation_name Le = "<="
        | relation_name Gt = ">"
        | relation_name Ge = ">="
      fun reverse_relation Eq = Eq
        | reverse_relation Lt = Gt
        | reverse_relation Le = Ge
        | reverse_relation Gt = Lt
        | reverse_relation Ge = Le
      fun conclusion (Eq, Lt, left, right) = arith_greater (left, right)
        | conclusion (Eq, Gt, left, right) = arith_less (left, right)
        | conclusion (Gt, Eq, left, right) = arith_less (left, right)
        | conclusion (Lt, Eq, left, right) = arith_greater (left, right)
        | conclusion (Ge, Le, left, right) = boolSyntax.mk_eq (left, right)
        | conclusion (Le, Ge, left, right) = boolSyntax.mk_eq (left, right)
        | conclusion (Gt, Lt, left, right) = boolSyntax.mk_eq (left, right)
        | conclusion (Lt, Gt, left, right) = boolSyntax.mk_eq (left, right)
        | conclusion (relation1, relation2, _, _) =
            raise ERR "arith_trichotomy"
              ("normalized CPC relations " ^ relation_name relation1 ^
               " and " ^ relation_name relation2 ^
               " do not form a supported trichotomy")
      val alias_rewrites = [integerTheory.INT_GE, realTheory.real_ge]
      fun normalize_aliases tm =
        boolSyntax.rhs (Thm.concl
          (Rewrite.PURE_REWRITE_CONV alias_rewrites tm))
        handle Conv.UNCHANGED => tm
      fun normalize_operand tm =
        let
          val aliased = boolSyntax.rhs
            (Thm.concl (SmtReplayCanon.cpc_term_canon_conv
              (normalize_aliases tm)))
        in
          boolSyntax.rhs (Thm.concl
            (SmtReplayCanon.arith_poly_norm_conversion aliased))
          handle Conv.UNCHANGED => aliased
               | Feedback.HOL_ERR _ => aliased
        end
      fun antisym left right left_le_right right_le_left =
        let
          val rule =
            if Lib.equal (Term.type_of left) intSyntax.int_ty then
              integerTheory.INT_LE_ANTISYM
            else realTheory.REAL_LE_ANTISYM
        in
          Thm.MP (Drule.SPECL [left, right] rule)
            (Thm.CONJ left_le_right right_le_left)
        end
      fun prove_declared fallback =
        case declared of
          SOME target => arith_prove_from_prems prems target
        | NONE => arith_prove_from_prems prems fallback
    in
      case prems of
        [premise1, premise2] =>
          let
            val (relation1, left, right) = normalize_not (Thm.concl premise1)
            val (relation2_raw, a, b) =
              normalize_not (Thm.concl premise2)
            val normalized_left = normalize_operand left
            val normalized_right = normalize_operand right
            val normalized_a = normalize_operand a
            val normalized_b = normalize_operand b
            val same_operands =
              Term.aconv normalized_left normalized_a andalso
              Term.aconv normalized_right normalized_b
            val reversed_operands =
              Term.aconv normalized_left normalized_b andalso
              Term.aconv normalized_right normalized_a
            val relation2 =
              if reversed_operands then reverse_relation relation2_raw
              else relation2_raw
            val premise1' = Rewrite.PURE_REWRITE_RULE alias_rewrites premise1
            val premise2' = Rewrite.PURE_REWRITE_RULE alias_rewrites premise2
          in
          if same_operands orelse reversed_operands then
            ((case (relation1, relation2) of
               (Ge, Le) => antisym (normalize_aliases left)
                 (normalize_aliases right) premise2' premise1'
             | (Le, Ge) => antisym (normalize_aliases left)
                 (normalize_aliases right) premise1' premise2'
             | _ => arith_prove_from_prems prems
                 (conclusion (relation1, relation2, left, right)))
             handle Feedback.HOL_ERR _ =>
               prove_declared
                 (conclusion (relation1, relation2, left, right)))
          else prove_declared
            (conclusion (relation1, relation2, left, right))
          end
      | _ => raise ERR "arith_trichotomy" "expected two CPC premises"
    end

  (* Over integer terms, a strict integral upper bound can be tightened by
     one.  CPC emits this after arith-elim-lt has exposed an Int '<' atom. *)
  fun replay_int_tight_ub prems =
    let
      val premise = expect_one_premise "int_tight_ub" prems
      val (left, right) =
        intSyntax.dest_less (Thm.concl premise)
        handle Feedback.HOL_ERR _ =>
          Lib.swap (intSyntax.dest_greater (Thm.concl premise))
      val target = intSyntax.mk_leq
        (left, if Term.aconv right intSyntax.one_tm then intSyntax.zero_tm
               else intSyntax.mk_minus (right, intSyntax.one_tm))
    in arith_prove_from_prems [premise] target end

  (* Over integer terms, a strict integral lower bound can be tightened by
     one, while a non-strict bound is left unchanged. *)
  fun replay_int_tight_lb prems =
    let
      val premise = expect_one_premise "int_tight_lb" prems
      val (left, right, strict) =
        (let val (left, right) = intSyntax.dest_greater (Thm.concl premise)
         in (left, right, true) end
         handle Feedback.HOL_ERR _ =>
           (let val (left, right) = intSyntax.dest_geq (Thm.concl premise)
            in (left, right, false) end
            handle Feedback.HOL_ERR _ =>
              (let val (right, left) =
                 intSyntax.dest_less (Thm.concl premise)
               in (left, right, true) end
               handle Feedback.HOL_ERR _ =>
                 let val (right, left) =
                   intSyntax.dest_leq (Thm.concl premise)
                 in (left, right, false) end)))
      val target = intSyntax.mk_geq
        (left, if strict then intSyntax.mk_plus (right, intSyntax.one_tm)
               else right)
    in arith_prove_from_prems [premise] target end

  fun replay_arith_reduction args =
    let
      val reduction = expect_one_arg "arith_reduction" args
      val (head, operands) = boolSyntax.strip_comb reduction
      val int_ediv_tm = Term.prim_mk_const
        {Thy = "integer", Name = "ediv"}
      val int_emod_tm = Term.prim_mk_const
        {Thy = "integer", Name = "emod"}
      val smt_ediv_total_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_ediv_total"}
      val smt_emod_total_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_emod_total"}
      val smt_rdiv_tm = Term.prim_mk_const
        {Thy = "HolSmt", Name = "smt_rdiv"}
      fun total (constant, a, b) = Term.list_mk_comb
        (constant, [a, b])
      fun exact_nonconjunction detail term =
        conjunction_free_semantic_provenance
          ("arith_reduction " ^ detail ^ " unexpectedly contains a conjunction")
          term
      fun exact_theorem detail theorem =
        exact_nonconjunction detail (Thm.concl theorem)
      fun exact_binary_conjunction detail theorem =
        let
          val (left, right) = boolSyntax.dest_conj (Thm.concl theorem)
        in
          ConjunctionProvenance (ArithReductionConjunction,
            [exact_nonconjunction (detail ^ " left conjunct") left,
             exact_nonconjunction (detail ^ " right conjunct") right])
        end
      fun nonconjunction theorem =
        (theorem, conjunction_free_semantic_provenance
          "arith_reduction unexpectedly produced a conjunction"
          (Thm.concl theorem))
      fun guarded_conditional (a, b, total_term, equality) =
        let
          val condition = boolSyntax.mk_eq (b, intSyntax.zero_tm)
          val target = boolSyntax.mk_eq
            (reduction, boolSyntax.mk_cond
              (condition, equality, total_term))
        in
          nonconjunction (Tactical.TAC_PROOF (([], target),
             Tactical.THEN (Tactic.COND_CASES_TAC,
               bossLib.ASM_SIMP_TAC bossLib.arith_ss
                 [HolSmtTheory.smt_ediv_total_def,
                  HolSmtTheory.smt_emod_total_def])))
        end
      fun div_reduction () =
        (case operands of
           [a, b] => guarded_conditional (a, b,
             total (smt_ediv_total_tm, a, b),
             SmtLib_Theories.mk_int_ediv (a, intSyntax.zero_tm))
         | _ => raise ERR "arith_reduction"
             "ediv reduction expects two operands")
      fun mod_reduction () =
        (case operands of
           [a, b] =>
             let
               val condition = boolSyntax.mk_eq (b, intSyntax.zero_tm)
               val target = boolSyntax.mk_eq
                 (reduction, boolSyntax.mk_cond
                   (condition,
                    SmtLib_Theories.mk_int_emod
                      (a, intSyntax.zero_tm),
                    total (smt_emod_total_tm, a, b)))
             in
               nonconjunction (Tactical.TAC_PROOF (([], target),
                  Tactical.THEN (Tactic.COND_CASES_TAC,
                    bossLib.ASM_SIMP_TAC bossLib.arith_ss
                      [HolSmtTheory.smt_emod_total_def])))
             end
         | _ => raise ERR "arith_reduction"
             "emod reduction expects two operands")
      fun real_div_reduction () =
        (case operands of
           [a, b] =>
             let
               val condition = boolSyntax.mk_eq (b, realSyntax.zero_tm)
               val target = boolSyntax.mk_eq
                 (reduction, boolSyntax.mk_cond
                   (condition,
                    total (smt_rdiv_tm, a, realSyntax.zero_tm),
                    realSyntax.mk_div (a, b)))
             in
               nonconjunction (Tactical.TAC_PROOF (([], target),
                  Tactical.THEN (Tactic.COND_CASES_TAC,
                    bossLib.ASM_SIMP_TAC bossLib.arith_ss
                      [HolSmtTheory.smt_rdiv_eq_div])))
             end
         | _ => raise ERR "arith_reduction"
             "real division reduction expects two operands")
      fun total_div_reduction () =
        (case operands of
           [a, b] => let
             val equality = Thm.REFL reduction
             val bounds = Drule.SPECL [a, b]
               HolSmtTheory.smt_ediv_total_bounds
           in
             (Thm.CONJ equality bounds,
              ConjunctionProvenance (ArithReductionConjunction,
                [exact_theorem "equality conjunct" equality,
                 exact_binary_conjunction "bounds" bounds]))
           end
         | _ => raise ERR "arith_reduction"
             "div_total reduction expects two operands")
      fun total_mod_reduction () =
        (case operands of
           [a, b] =>
             let
               val equality = Drule.SPECL [a, b]
                 HolSmtTheory.smt_emod_total_ediv
               val target = boolSyntax.mk_eq (reduction,
                 intSyntax.mk_plus
                   (a, intSyntax.mk_negated
                     (intSyntax.mk_mult
                       (b, total (smt_ediv_total_tm, a, b)))))
             in
               (Thm.CONJ equality
                  (Drule.SPECL [a, b] HolSmtTheory.smt_ediv_total_bounds),
                ConjunctionProvenance (ArithReductionConjunction,
                  [exact_theorem "equality conjunct" equality,
                   exact_binary_conjunction "bounds"
                     (Drule.SPECL [a, b]
                       HolSmtTheory.smt_ediv_total_bounds)]))
             end
         | _ => raise ERR "arith_reduction"
             "mod_total reduction expects two operands")
      fun total_real_div_reduction () =
        (case operands of
           [a, b] =>
             let
               val side = boolSyntax.mk_imp
                 (boolSyntax.mk_neg
                   (boolSyntax.mk_eq (b, realSyntax.zero_tm)),
                  boolSyntax.mk_eq
                    (realSyntax.mk_mult
                       (b, realSyntax.mk_div (a, b)), a))
               val side_thm = Tactical.TAC_PROOF (([], side),
                 metisLib.METIS_TAC [realTheory.REAL_DIV_LMUL])
             in
               (Thm.CONJ (Thm.REFL reduction) side_thm,
                ConjunctionProvenance (ArithReductionConjunction,
                  [exact_theorem "equality conjunct"
                     (Thm.REFL reduction),
                   exact_theorem "nonzero-side conjunct" side_thm]))
             end
         | _ => raise ERR "arith_reduction"
             "/_total reduction expects two operands")
      fun floor_reduction () =
        let
          val real = intrealSyntax.dest_INT_FLOOR reduction
          val bounds = Thm.SPEC real HolSmtTheory.int_floor_remainder_bounds
        in
          (Thm.CONJ (Thm.REFL reduction) bounds,
           ConjunctionProvenance (ArithReductionConjunction,
             [exact_theorem "equality conjunct" (Thm.REFL reduction),
              exact_binary_conjunction "bounds" bounds]))
        end
      fun abs_reduction () =
        let
          val value = intSyntax.dest_absval reduction
          val target = boolSyntax.mk_eq (reduction,
            boolSyntax.mk_cond (intSyntax.mk_less (value, intSyntax.zero_tm),
              intSyntax.mk_negated value, value))
        in
          nonconjunction (Tactical.TAC_PROOF (([], target),
             Tactical.THEN (Tactic.COND_CASES_TAC,
               bossLib.ASM_SIMP_TAC bossLib.arith_ss
                 [integerTheory.INT_ABS])))
        end
    in
      if Term.aconv head intrealSyntax.INT_FLOOR_tm then floor_reduction ()
      else if Term.aconv head intSyntax.absval_tm then abs_reduction ()
      else if Term.aconv head int_ediv_tm then div_reduction ()
      else if Term.aconv head int_emod_tm then mod_reduction ()
      else if Term.aconv head smt_rdiv_tm then real_div_reduction ()
      else if Term.aconv head smt_ediv_total_tm then total_div_reduction ()
      else if Term.aconv head smt_emod_total_tm then total_mod_reduction ()
      else if Term.aconv head realSyntax.div_tm then total_real_div_reduction ()
      else raise ERR "arith_reduction"
        ("unsupported arithmetic reduction head " ^
         Library.term_to_string head)
    end

  fun replay_modus_ponens prems =
    case prems of
      [left, right] =>
        (Thm.MP right left
         handle Feedback.HOL_ERR _ =>
           (Thm.MP left right
            handle Feedback.HOL_ERR _ =>
              raise ERR "modus_ponens"
                ("canonical premises are not applicable; left=" ^
                 Library.term_to_string (Thm.concl left) ^ "; right=" ^
                 Library.term_to_string (Thm.concl right))))
    | _ => raise ERR "modus_ponens" "expected two CPC premises"

  (* Canonical matching must not replace an implication by its normalized
     consequence: omitted CPC conclusions are inferred from the original
     implication and later steps depend on that exact endpoint.  Normalize
     only to establish that the proposition proves the antecedent, transport
     it back, and apply the untouched implication. *)
  fun replay_canonical_modus_ponens strong_canon prems =
    let
      fun apply canon proposition implication =
        let
          val (antecedent, _) = boolSyntax.dest_imp (Thm.concl implication)
          val proposition_norm = canon (Thm.concl proposition)
          val antecedent_norm = canon antecedent
          val normalized_proposition =
            boolSyntax.rhs (Thm.concl proposition_norm)
          val normalized_antecedent =
            boolSyntax.rhs (Thm.concl antecedent_norm)
          val _ = Term.aconv normalized_proposition normalized_antecedent orelse
            raise ERR "modus_ponens"
              "canonical proposition does not match the exact antecedent"
          val proposition' = Thm.EQ_MP proposition_norm proposition
          val antecedent' = Thm.EQ_MP (Thm.SYM antecedent_norm) proposition'
        in
          Thm.MP implication antecedent'
        end
      fun oriented canon left right =
        apply canon left right
        handle Feedback.HOL_ERR _ => apply canon right left
    in
      case prems of
        [left, right] =>
          (oriented SmtReplayCanon.cpc_operand_canon_conv left right
           handle Feedback.HOL_ERR _ =>
             oriented strong_canon left right)
      | _ => raise ERR "modus_ponens" "expected two CPC premises"
    end

  (* Some arithmetic CPC certificates state an antecedent in an algebraically
     equivalent, rather than canonically identical, form.  Derive only that
     antecedent from the recorded proposition and then apply the untouched
     implication.  The arithmetic prover and MP remain kernel checked, and
     both premise hypothesis sets are retained. *)
  fun replay_arithmetic_modus_ponens prems =
    let
      fun apply proposition implication =
        let
          val (antecedent, _) = boolSyntax.dest_imp (Thm.concl implication)
          val antecedent_theorem =
            arith_prove_from_prems [proposition] antecedent
        in
          Thm.MP implication antecedent_theorem
        end
      fun oriented left right =
        apply left right
        handle Feedback.HOL_ERR _ => apply right left
    in
      case prems of
        [left, right] => oriented left right
      | _ => raise ERR "modus_ponens" "expected two CPC premises"
    end

  fun replay_arith_sum_ub prems =
    let
      fun equality_as_leq premise left right =
        let
          val reflexive_target = arith_leq (left, left)
          val (leq_const, _) = boolSyntax.strip_comb reflexive_target
          val reflexive =
            Drule.ISPEC left integerTheory.INT_LE_REFL
            handle Feedback.HOL_ERR _ =>
              Drule.ISPEC left realTheory.REAL_LE_REFL
          val transported = Thm.AP_TERM
            (Term.mk_comb (leq_const, left)) premise
        in
          Thm.EQ_MP transported reflexive
        end
      fun dest_bound premise =
        (let val (left, right) = arith_dest_less (Thm.concl premise)
         in (true, left, right, premise) end
        handle Feedback.HOL_ERR _ =>
          let val (left, right) = arith_dest_leq (Thm.concl premise)
           in (false, left, right, premise) end
           handle Feedback.HOL_ERR _ =>
             let val (left, right) = boolSyntax.dest_eq (Thm.concl premise)
             in (false, left, right,
               equality_as_leq premise left right) end)
      fun add_bounds ((left_strict, left_lhs, left_rhs, left_thm),
                      (right_strict, right_lhs, right_rhs, right_thm)) =
        let
          val int_rule =
            case (left_strict, right_strict) of
              (true, true) => integerTheory.INT_LT_ADD2
            | (false, true) => integerTheory.INT_LET_ADD2
            | (true, false) => integerTheory.INT_LTE_ADD2
            | (false, false) => integerTheory.INT_LE_ADD2
          val real_rule =
            case (left_strict, right_strict) of
              (true, true) => realTheory.REAL_LT_ADD2
            | (false, true) => realTheory.REAL_LET_ADD2
            | (true, false) => realTheory.REAL_LTE_ADD2
            | (false, false) => realTheory.REAL_LE_ADD2
          val rule =
            if Lib.equal (Term.type_of left_lhs) intSyntax.int_ty then int_rule
            else real_rule
          val combined = Thm.MP
            (Drule.SPECL [left_lhs, left_rhs, right_lhs, right_rhs] rule)
            (Thm.CONJ left_thm right_thm)
          (* Normalize each partial sum before adding the next bound.  CPC
             certificates use the polynomial normal form of the combined
             relation; retaining the unreduced expression here duplicates
             shared conditional terms exponentially and forces the following
             EQ_RESOLVE to rediscover the same linear cancellation. *)
          val combined = Conv.CONV_RULE
            (SmtReplayCanon.compose
              [SmtReplayCanon.cpc_operand_canon_conv,
               Conv.BINOP_CONV
                 (Conv.QCONV
                   SmtReplayCanon.arith_poly_norm_conversion)]) combined
          val (combined_lhs, combined_rhs) =
            if left_strict orelse right_strict then
              arith_dest_less (Thm.concl combined)
            else arith_dest_leq (Thm.concl combined)
        in
          (left_strict orelse right_strict,
           combined_lhs, combined_rhs, combined)
        end
      val bounds = List.map dest_bound prems
      val (_, _, _, result) =
        case bounds of
          first :: rest => List.foldl
            (fn (next, accumulated) => add_bounds (accumulated, next))
            first rest
        | [] => raise ERR "arith_sum_ub" "expected CPC premises"
    in result end

  fun replay_arith_rel prems args =
    let
      val target = expect_one_arg "arith_poly_norm_rel" args
      fun has_real_of_int tm =
        intrealSyntax.is_real_of_int tm orelse
        ((let val (f, x) = Term.dest_comb tm in
            has_real_of_int f orelse has_real_of_int x
          end) handle _ =>
          ((let val (_, body) = Term.dest_abs tm in has_real_of_int body end)
           handle _ => false))
      val needs_real_normalization = has_real_of_int target orelse
        List.exists (has_real_of_int o Thm.concl) prems
      fun mixed_ge_lift () =
        let
          val (real_relation, int_relation) = boolSyntax.dest_eq target
          val _ = realSyntax.dest_geq real_relation
          val (int_left, int_right) = intSyntax.dest_geq int_relation
          val lifted_target = boolSyntax.mk_eq
            (realSyntax.mk_leq (intrealSyntax.mk_real_of_int int_right,
               intrealSyntax.mk_real_of_int int_left),
             intSyntax.mk_leq (int_right, int_left))
          val lifted_raw = Drule.INST_TY_TERM
            (Term.match_term (Thm.concl intrealTheory.real_of_int_le)
              lifted_target) intrealTheory.real_of_int_le
          val lifted = Rewrite.PURE_REWRITE_RULE
            [intrealTheory.real_of_int_neg, intrealTheory.real_of_int_num,
             integerTheory.INT_GE, realTheory.real_ge] lifted_raw
            handle Conv.UNCHANGED => lifted_raw
          val target_eq_normalized = simpLib.SIMP_CONV (bossLib.srw_ss())
            [integerTheory.int_ge, realTheory.real_ge,
             realTheory.real_div] target
        in
          Thm.EQ_MP (Thm.SYM target_eq_normalized) lifted
        end
      fun int_real_geq_tighten () =
        let
          val (int_relation, real_relation) = boolSyntax.dest_eq target
          val (real_integer, real_bound) = realSyntax.dest_geq real_relation
          val integer = intrealSyntax.dest_real_of_int real_integer
          val ceiling = intrealSyntax.mk_INT_CEILING real_bound
          val ceiling_eval = bossLib.EVAL ceiling
          val (_, rounded) = boolSyntax.dest_eq (Thm.concl ceiling_eval)
          val tightened_relation = intSyntax.mk_geq (integer, rounded)
          val int_normalization = Tactical.TAC_PROOF
            (([], boolSyntax.mk_eq (int_relation, tightened_relation)),
             intLib.ARITH_TAC)
          val real_normalization =
            replay_arith_int_geq_tighten (integer, real_bound, rounded)
        in Thm.TRANS int_normalization (Thm.SYM real_normalization) end
      fun direct () =
        let
          val (left, right) = boolSyntax.dest_eq target
          fun lift_leq x y =
            Tactical.TAC_PROOF (([], boolSyntax.mk_eq
              (intSyntax.mk_leq (x, y),
               realSyntax.mk_leq (intrealSyntax.mk_real_of_int x,
                 intrealSyntax.mk_real_of_int y))),
              bossLib.SIMP_TAC (bossLib.srw_ss()) [])
          fun lift_int_relation tm =
            (let
              val (a, b) = intSyntax.dest_leq tm
             in lift_leq a b end)
            handle Feedback.HOL_ERR leq_error =>
              ((let
                 val (a, b) = intSyntax.dest_geq tm
                 val int_ge_eq_le = simpLib.SIMP_CONV (bossLib.srw_ss())
                   [integerTheory.int_ge] tm
                 val leq_eq = lift_leq b a
                 val real_le_eq_ge = simpLib.SIMP_CONV (bossLib.srw_ss())
                   [realTheory.real_ge]
                   (boolSyntax.rhs (Thm.concl leq_eq))
               in Thm.TRANS int_ge_eq_le
                 (Thm.TRANS leq_eq real_le_eq_ge)
               end)
               handle Feedback.HOL_ERR geq_error =>
                 raise ERR "arith_poly_norm_rel"
                   ("could not lift integer relation " ^
                    Library.term_to_string tm ^ "; leq error=" ^
                    Feedback.message_of leq_error ^ "; geq error=" ^
                    Feedback.message_of geq_error))
          fun lift_target () =
            let
              val variable = Term.mk_var ("rel", Type.bool)
              val left_context = Term.mk_abs (variable,
                boolSyntax.mk_eq (variable, right))
              val right_context = Term.mk_abs (variable,
                boolSyntax.mk_eq (left, variable))
            in
              Thm.AP_TERM left_context (lift_int_relation left)
              handle Feedback.HOL_ERR left_error =>
                (Thm.AP_TERM right_context (lift_int_relation right)
                 handle Feedback.HOL_ERR right_error =>
                   raise ERR "arith_poly_norm_rel"
                     ("could not lift either relation; left=" ^
                      Library.term_to_string left ^ "; right=" ^
                      Library.term_to_string right ^ "; left error=" ^
                      Feedback.message_of left_error ^ "; right error=" ^
                      Feedback.message_of right_error))
            end
          val target_eq_target' =
            ((realSyntax.dest_leq left; realSyntax.dest_leq right;
              Thm.REFL target)
             handle Feedback.HOL_ERR _ =>
              ((realSyntax.dest_geq left; realSyntax.dest_geq right;
                simpLib.SIMP_CONV (bossLib.srw_ss()) [realTheory.real_ge]
                  target)
               handle Feedback.HOL_ERR _ => lift_target ()))
          val target' = boolSyntax.rhs (Thm.concl target_eq_target')
          val normalized_prems = List.map
            (simpLib.SIMP_RULE (bossLib.srw_ss())
              [intrealTheory.real_of_int_sub, intrealTheory.real_of_int_neg,
               intrealTheory.real_of_int_add, intrealTheory.real_of_int_mul])
            prems
          val difference = case normalized_prems of
              [premise] => premise
            | _ => raise ERR "arith_poly_norm_rel"
                "real/int relational normalization expected one equality premise"
          val negated_difference = simpLib.SIMP_RULE (bossLib.srw_ss())
            [realTheory.REAL_NEG_SUB]
            (Thm.AP_TERM realSyntax.negate_tm difference)
          val thm = Tactical.TAC_PROOF (([], target'),
            bossLib.SIMP_TAC (bossLib.srw_ss()) [])
            handle Feedback.HOL_ERR _ =>
              Tactical.TAC_PROOF (([Thm.concl negated_difference], target'),
                bossLib.ASM_SIMP_TAC (bossLib.srw_ss())
                  [Thm.SYM realTheory.REAL_SUB_LE, realTheory.REAL_NEG_SUB])
        in Thm.EQ_MP (Thm.SYM target_eq_target') thm end
      fun abstract_cast_atoms () =
        prove_cast_arithmetic prems target
    in
      if needs_real_normalization then
        (profile "CPC(rung:arith_rel/mixed_ge_lift)" mixed_ge_lift ()
         handle Feedback.HOL_ERR _ =>
           profile "CPC(rung:arith_rel/relation_simp)" Tactical.TAC_PROOF
             (([], target), bossLib.SIMP_TAC (bossLib.srw_ss())
               [integerTheory.int_ge, realTheory.real_ge])
         handle Feedback.HOL_ERR _ =>
           profile "CPC(rung:arith_rel/geq_tighten)"
             int_real_geq_tighten ()
         handle Feedback.HOL_ERR _ =>
           profile "CPC(rung:arith_rel/direct)" direct ()
         handle Feedback.HOL_ERR _ =>
           profile "CPC(rung:arith_rel/target_simp)" Tactical.TAC_PROOF
             (([], target), bossLib.SIMP_TAC (bossLib.srw_ss()) [])
         handle Feedback.HOL_ERR _ =>
           profile "CPC(rung:arith_rel/from_prems)"
             (arith_prove_from_prems prems) target
         handle Feedback.HOL_ERR _ =>
           (profile "CPC(rung:arith_rel/abstract_cast_atoms)"
              abstract_cast_atoms ()
            handle Feedback.HOL_ERR abstract_error =>
              raise ERR "arith_poly_norm_rel"
                ("arithmetic atom abstraction failed for target " ^
                 Library.term_to_string target ^ "; premises=" ^
                 String.concatWith ", "
                   (List.map (Library.term_to_string o Thm.concl) prems) ^
                 "; underlying error=" ^
                 Feedback.message_of abstract_error)))
      else
        (profile "CPC(rung:arith_rel/from_prems_direct)"
           (arith_prove_from_prems prems) target
         handle Feedback.HOL_ERR _ =>
           profile "CPC(rung:arith_rel/neg_eq_simp)" Tactical.TAC_PROOF
             (([], target), bossLib.SIMP_TAC (bossLib.srw_ss())
               [realTheory.REAL_NEG_EQ, boolTheory.EQ_SYM_EQ])
         handle Feedback.HOL_ERR _ =>
           (profile "CPC(rung:arith_rel/ring)" RealField.REAL_RING target
            handle Feedback.HOL_ERR _ =>
              profile "CPC(rung:arith_rel/from_prems_retry)"
                (arith_prove_from_prems prems) target
            handle Feedback.HOL_ERR _ =>
              (profile "CPC(rung:arith_rel/abstract_cast_atoms)"
                 abstract_cast_atoms ()
               handle Feedback.HOL_ERR abstract_error =>
                 raise ERR "arith_poly_norm_rel"
                   ("arithmetic atom abstraction failed for target " ^
                    Library.term_to_string target ^ "; premises=" ^
                    String.concatWith ", "
                      (List.map (Library.term_to_string o Thm.concl) prems) ^
                    "; underlying error=" ^
                    Feedback.message_of abstract_error))))
    end

  fun replay_datatype args =
    case args of
      [left, right] =>
        profile "CPC(rung:datatype/prove)" SmtDatatypeProve.datatype_prove
          (boolSyntax.mk_neg (boolSyntax.mk_eq (left, right)))
    | _ => raise ERR "datatype" "expected two constructor values"

  fun replay_dt_split args =
    case args of
      [scrutinee] =>
        let
          val ty = Term.type_of scrutinee
          val constructors = SmtDatatypeProve.constructors_of ty
          val testers = List.map
            (fn constructor =>
              SmtDatatypeProve.datatype_tester_term
                ty constructor scrutinee)
            constructors
          val target = mk_disj_terms testers
        in
          profile "CPC(rung:datatype/split)"
            SmtDatatypeProve.datatype_prove target
        end
    | _ => raise ERR "dt_split" "expected one datatype scrutinee"

  fun replay_datatype_eq args =
    profile "CPC(rung:datatype/prove_eq)" SmtDatatypeProve.datatype_prove
      (expect_one_arg "datatype_eq" args)

  fun replay_resolution prems conclusion args =
    let
      (* Premises, target and annotations enter this handler in the shared
         CPC normal form, so literal identity is just alpha-equivalence. *)
      fun literal_equal left right = Term.aconv left right
      fun convert_literal theorem target =
        if Term.aconv (Thm.concl theorem) target then theorem
        else raise ERR "resolution" "incompatible canonical CPC literals"
      fun strip_clause term =
        (let val (left, right) = boolSyntax.dest_disj term in
           left :: strip_clause right
         end)
        handle Feedback.HOL_ERR _ => [term]
      fun remove_first literal [] = NONE
        | remove_first literal (candidate :: rest) =
            if literal_equal literal candidate then SOME rest
            else Option.map (fn rest' => candidate :: rest')
              (remove_first literal rest)
      fun complement literal =
        boolSyntax.dest_neg literal
        handle Feedback.HOL_ERR _ => boolSyntax.mk_neg literal
      fun resolve_pair_on first_pivot first second =
        let
          val first_lits = strip_clause (Thm.concl first)
          val second_lits = strip_clause (Thm.concl second)
          val second_pivot = complement first_pivot
          val first_removed = remove_first first_pivot first_lits
          val second_removed = remove_first second_pivot second_lits
          val first_rest = case first_removed of SOME rest => rest | NONE => first_lits
          val second_rest = case second_removed of SOME rest => rest | NONE => second_lits
          val first_tail = mk_disj_terms first_rest
          val second_tail = mk_disj_terms second_rest
          val result = mk_disj_terms (first_rest @ second_rest)
          fun prove_member literal target =
            if literal_equal literal target then
              convert_literal (Thm.ASSUME literal) target
            else
              let val (left, right) = boolSyntax.dest_disj target in
                if literal_equal literal left then
                  Thm.DISJ1 (convert_literal (Thm.ASSUME literal) left) right
                else Thm.DISJ2 left (prove_member literal right)
              end
          fun reorder_clause theorem pivot tail =
            let
              val target = boolSyntax.mk_disj (pivot, tail)
              fun branch theorem =
                (let val (left, right) = boolSyntax.dest_disj (Thm.concl theorem) in
                   Thm.DISJ_CASES theorem (branch (Thm.ASSUME left))
                     (branch (Thm.ASSUME right))
                 end)
                handle Feedback.HOL_ERR _ =>
                  if literal_equal (Thm.concl theorem) pivot then
                    Thm.DISJ1 (convert_literal theorem pivot) tail
                  else Thm.DISJ2 pivot (prove_member (Thm.concl theorem) tail)
            in branch theorem end
          fun inject_clause theorem target =
            let
              fun branch theorem =
                (let val (left, right) = boolSyntax.dest_disj (Thm.concl theorem) in
                   Thm.DISJ_CASES theorem (branch (Thm.ASSUME left))
                     (branch (Thm.ASSUME right))
                 end)
                handle Feedback.HOL_ERR _ =>
                  prove_member (Thm.concl theorem) target
            in branch theorem end
          fun first_normal () = reorder_clause first first_pivot first_tail
            handle Feedback.HOL_ERR _ => raise ERR "resolution"
              "could not normalize the first resolution clause"
          fun second_normal () = reorder_clause second second_pivot second_tail
            handle Feedback.HOL_ERR _ => raise ERR "resolution"
              "could not normalize the second resolution clause"
          val from_false = fn contradiction => Thm.MP
            (Thm.SPEC result boolTheory.FALSITY) contradiction
          fun inject_or_false theorem =
            if Term.aconv (Thm.concl theorem) boolSyntax.F then from_false theorem
            else inject_clause theorem result
          val first_case = Thm.ASSUME first_pivot
          val second_case = Thm.ASSUME second_pivot
          val contradiction =
            (boolSyntax.dest_neg first_pivot;
             Thm.MP first_case second_case)
            handle Feedback.HOL_ERR _ => Thm.MP second_case first_case
          val second_false_branch = from_false contradiction
          val second_tail_branch = inject_or_false (Thm.ASSUME second_tail)
          fun resolve_pivot () = Thm.DISJ_CASES (second_normal ()) second_false_branch
            second_tail_branch
            handle Feedback.HOL_ERR _ => raise ERR "resolution"
              ("could not discharge the second resolution clause; false branch=" ^
               Library.term_to_string (Thm.concl second_false_branch) ^
               "; tail branch=" ^
               Library.term_to_string (Thm.concl second_tail_branch))
          fun resolve_rest () = inject_or_false (Thm.ASSUME first_tail)
        in
          case (first_removed, second_removed) of
            (SOME _, SOME _) =>
              (let
                 val first_normalized = first_normal ()
                 val pivot_result = resolve_pivot ()
                 val rest_result = resolve_rest ()
               in
                 Thm.DISJ_CASES first_normalized pivot_result rest_result
               end
               handle Feedback.HOL_ERR _ => raise ERR "resolution"
                 "could not discharge the first resolution clause")
          (* cvc5 permits a missing pivot as a weakening: retain that
             uneliminated premise and inject it into the result clause. *)
          | (NONE, _) => inject_clause first result
          | (_, NONE) => inject_clause second result
        end
        handle Feedback.HOL_ERR holerr =>
          raise ERR "resolution"
            ("kernel resolution failed on pivot " ^
             Library.term_to_string first_pivot ^ ": " ^
             Feedback.message_of holerr)
      fun replay_chain target polarities pivots =
        let
          val expected = List.length prems - 1
          val _ = List.length polarities = expected andalso
                  List.length pivots = expected orelse
            raise ERR "resolution" "resolution-chain annotation arity mismatch"
          fun signed_pivot polarity pivot =
            if Term.aconv polarity boolSyntax.T then pivot
            else if Term.aconv polarity boolSyntax.F then complement pivot
            else raise ERR "resolution" "resolution-chain polarity is not Boolean"
          fun prove_member literal target =
            if literal_equal literal target then
              convert_literal (Thm.ASSUME literal) target
            else
              let val (left, right) = boolSyntax.dest_disj target in
                if literal_equal literal left then
                  Thm.DISJ1 (convert_literal (Thm.ASSUME literal) left) right
                else Thm.DISJ2 left (prove_member literal right)
              end
          fun factor theorem =
            let
              fun seen literal literals =
                List.exists (literal_equal literal) literals
              fun unique literals =
                List.rev (List.foldl (fn (literal, kept) =>
                  if seen literal kept then kept else literal :: kept) [] literals)
              val factored = mk_disj_terms (unique
                (strip_clause (Thm.concl theorem)))
            in
              if Term.aconv (Thm.concl theorem) factored then theorem
              else
                let
                  fun branch theorem =
                    case (SOME (boolSyntax.dest_disj (Thm.concl theorem))
                          handle Feedback.HOL_ERR _ => NONE) of
                      SOME (left, right) =>
                        Thm.DISJ_CASES theorem (branch (Thm.ASSUME left))
                          (branch (Thm.ASSUME right))
                    | NONE => prove_member (Thm.concl theorem) factored
                in branch theorem end
            end
          fun reorder_to_target theorem =
            let
              fun branch theorem =
                case (SOME (boolSyntax.dest_disj (Thm.concl theorem))
                      handle Feedback.HOL_ERR _ => NONE) of
                  SOME (left, right) =>
                    Thm.DISJ_CASES theorem (branch (Thm.ASSUME left))
                      (branch (Thm.ASSUME right))
                | NONE =>
                    (prove_member (Thm.concl theorem) target
                     handle Feedback.HOL_ERR _ => raise ERR "resolution"
                       ("chain result contains literal outside declared target: " ^
                        Library.term_to_string (Thm.concl theorem)))
            in branch theorem end
          fun contextual_target theorem =
            Tactical.TAC_PROOF ((Thm.hyp theorem, target),
              bossLib.FULL_SIMP_TAC boolSimps.bool_ss [theorem])
          val result = case prems of
              first :: rest => List.foldl
                (fn ((next, (polarity, pivot)), accumulated) =>
                  let val next_result = factor
                    (resolve_pair_on (signed_pivot polarity pivot)
                      accumulated next)
                  in next_result end)
                first (ListPair.zip (rest, ListPair.zip (polarities, pivots)))
            | [] => raise ERR "resolution" "empty resolution chain"
        in
          if Term.aconv (Thm.concl result) target then result
          else
            (reorder_to_target result
             handle Feedback.HOL_ERR _ => contextual_target result
             handle Feedback.HOL_ERR _ =>
               tautological_consequences prems target)
        end
      fun has_non_arithmetic_equality tm =
        let
          fun arithmetic_type ty =
            Type.compare (ty, Type.bool) = EQUAL orelse
            Type.compare (ty, numSyntax.num) = EQUAL orelse
            Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
            Type.compare (ty, realSyntax.real_ty) = EQUAL orelse
            wordsSyntax.is_word_type ty
          fun search term =
            case Lib.total boolSyntax.dest_eq term of
              SOME (left, right) =>
                not (arithmetic_type (Term.type_of left)) orelse
                search left orelse search right
            | NONE =>
                (case Lib.total Term.dest_comb term of
                   SOME (operator, operand) =>
                     search operator orelse search operand
                 | NONE =>
                     (case Lib.total Term.dest_abs term of
                        SOME (_, body) => search body
                      | NONE => false))
        in search tm end
      fun resolution_result polarity pivot =
        case prems of
          [first, second] =>
            let
              val first_lits = strip_clause (Thm.concl first)
              val second_lits = strip_clause (Thm.concl second)
              val first_pivot =
                if Term.aconv polarity boolSyntax.T then pivot
                else if Term.aconv polarity boolSyntax.F then
                  boolSyntax.mk_neg pivot
                else raise ERR "resolution"
                  "CPC resolution polarity is not Boolean"
              val second_pivot = boolSyntax.mk_neg first_pivot
              val first_rest =
                case remove_first first_pivot first_lits of
                  SOME rest => rest
                | NONE => raise ERR "resolution"
                  "CPC resolution pivot is absent from its first clause"
              val second_rest =
                case remove_first second_pivot second_lits of
                  SOME rest => rest
                | NONE => raise ERR "resolution"
                  ("CPC resolution pivot is absent from its second clause; pivot=" ^
                   Library.term_to_string second_pivot ^ "; second clause=" ^
                   Library.term_to_string (Thm.concl second))
            in mk_disj_terms (first_rest @ second_rest) end
        | _ => raise ERR "resolution" "expected two CPC resolution premises"
      fun prove target =
        (profile "CPC(rung:resolution/tautological)" (fn () =>
         if List.length prems > 2 then
           let val n = List.length prems - 1 in
             case args of
               _ :: annotation =>
                 if List.length annotation = 2 * n then
                   (replay_chain target
                      (List.take (annotation, n))
                      (List.drop (annotation, n))
                    handle Feedback.HOL_ERR _ =>
                      tautological_consequences prems target)
                 else tautological_consequences prems target
           | [] => raise ERR "resolution" "missing resolution-chain annotation"
           end
         else tautological_consequences prems target) ()
         handle Feedback.HOL_ERR _ =>
           (case profile "CPC(rung:resolution/complementary)"
             (fn () => resolve_complementary_literals prems target) () of
              SOME thm => thm
            | NONE =>
                (case profile "CPC(rung:resolution/binary)"
                  (fn () => resolve_binary_disjunction prems target) () of
                   SOME thm => thm
                 | NONE =>
                     (* HOL reconstruction can expose equality congruences
                        between certificate literals (notably datatype and
                        record constructor/selector terms).  These are beyond
                        propositional TAUT but remain the semantics of
                        resolution from the exact premise theorems. *)
                     if List.exists has_non_arithmetic_equality
                          (target :: List.map Thm.concl prems) then
                       metis_prove prems target
                     else raise ERR "resolution"
                       "resolution requires no equality-congruence fallback")))
    in
      case (conclusion, args) of
        (SOME target, _) => prove target
      | (NONE, [target, polarity, pivot]) =>
          replay_chain target [polarity] [pivot]
      | (NONE, [polarity, pivot]) => prove (resolution_result polarity pivot)
      | (NONE, [target]) => prove target
      | (NONE, target :: _) => prove target
      | (NONE, _) => raise ERR "resolution"
          "CPC resolution omitted its conclusion or pivot annotation"
    end

  fun replay_bool prems conclusion =
    case conclusion of
      SOME target => metis_prove prems target
    | NONE => raise ERR "bool" "CPC boolean step omitted its conclusion"

  fun replay_arith prems conclusion =
    case conclusion of
      SOME target => arith_prove_from_prems prems target
    | NONE => raise ERR "arith" "CPC arithmetic step omitted its conclusion"

  fun replay_string state name prems conclusion args =
    let
      fun is_empty_string tm =
        case boolSyntax.strip_comb tm of
          (head, [chars]) =>
            (case Lib.total Term.dest_thy_const head of
               SOME {Thy, Name, ...} =>
                 Thy = "smtstring" andalso Name = "SmtStr" andalso
                 listSyntax.is_nil chars
             | NONE => false)
        | _ => false
      fun inferred_target () =
        case (name, args) of
          ("str-len-concat-rec", [left, right, empty]) =>
            if listSyntax.is_nil empty orelse is_empty_string empty then
              if is_smtstr_type (Term.type_of left) then
                Thm.concl (Drule.SPECL [left, right]
                  smtstringTheory.smtstr_len_concat)
              else
                let
                  fun length sequence = Term.mk_comb
                    (intSyntax.int_injection, listSyntax.mk_length sequence)
                in
                  boolSyntax.mk_eq
                    (length (listSyntax.mk_append (left, right)),
                     intSyntax.mk_plus (length left, length right))
                end
            else raise ERR "string" "expected an empty sequence argument"
        | (_, [target]) =>
            if Type.compare (Term.type_of target, Type.bool) = EQUAL then
              target
            else raise ERR "string"
              ("CPC string step " ^ name ^
               " omitted its conclusion; tracked replay obligation")
        | _ => raise ERR "string"
            ("CPC string step " ^ name ^
             " omitted its conclusion; tracked replay obligation")
      val target =
        case conclusion of
          SOME target => target
        | NONE => inferred_target ()
      (* Only this rung needs the assertion set, and it is reached only after
         the cheaper string rungs have failed, so the flattening stays behind
         a thunk.  ASM_SIMP_TAC turns every context assumption it uses into a
         hypothesis, so the premise conclusions are discharged again against
         the premises themselves; only the tracked assertion and scope
         hypotheses may survive into the replayed theorem. *)
      fun contextual_prove () =
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            (SmtStringProve.string_contextual_prove context target) prems
        end
      fun fail () =
        raise ERR "string"
          ("unsupported CPC string step: rule=" ^ name ^
           "; conclusion=" ^ Library.term_to_string target ^
           "; attempted rungs=[rewrite, theory, contextual]")
    in
      (* `str` is cvc5's macro name for both String and Seq theory steps.
         Dispatch on HOL's carrier, rather than the macro spelling, so the
         Phase-4 String route remains unchanged. *)
      if SmtSeqProve.has_seq_type target then
        let
          val context =
            HOLset.listItems (#asserted_hyps state) @ #scope_hyps state @
            List.map Thm.concl prems
          val thm = profile "CPC(rung:string/seq_contextual)"
            (fn target =>
              SmtSeqProve.seq_prove target
              handle Feedback.HOL_ERR holerr =>
                if SmtResource.is_resource_gate holerr then
                  raise Feedback.HOL_ERR holerr
                else
                  SmtSeqProve.seq_contextual_prove context target) target
        in
          List.foldl (fn (premise, proved) => Drule.PROVE_HYP premise proved)
            thm prems
        end
      else
        profile "CPC(rung:string/rewrite)"
          SmtStringProve.string_rewrite_prove target
        handle Feedback.HOL_ERR _ =>
        profile "CPC(rung:string/theory)"
          (SmtStringProve.string_prove arith_prove) target
        handle Feedback.HOL_ERR _ =>
        profile "CPC(rung:string/contextual)" contextual_prove ()
        handle Feedback.HOL_ERR _ =>
        profile "CPC(rung:string/unsupported)" fail ()
    end

  fun unsupported_step ({id, rule, conclusion, ...} : step) =
    let
      val conclusion_text =
        case conclusion of NONE => "<omitted>"
        | SOME located => Library.term_to_string (#term located)
    in
      raise ERR "replay_step"
        ("unsupported CPC step: rule=" ^ #name rule ^ "; namespace=" ^
         namespace_name (#namespace rule) ^ "; step=" ^ id ^
         "; conclusion=" ^ conclusion_text)
    end

  fun replay_step state (step : step) =
    let
      val {id, conclusion = located_conclusion, rule, premises,
        args = located_args} = step
      val conclusion = Option.map
        (fn (located : located_term) => #term located) located_conclusion
      val args = List.map (fn (located : located_term) => #term located)
        located_args
      val premise_steps = List.map
        (find_step "replay_step" state) premises
      val prems = List.map step_theorem premise_steps
      val premise_rules = List.map (lookup_rule state) premises
      val strong_canon =
        strong_cpc_canon_conv (#translation_definitions state)
      fun opaque theorem = exact_result
        (conjunction_free_semantic_provenance
          ("CPC rule " ^ #name rule ^
           " omitted a result containing an exact conjunction")
          (Thm.concl theorem)) theorem
      (* Arithmetic relation rewrites construct both equality endpoints from
         their typed operands.  When the successful theorem contains no HOL
         conjunction at either endpoint, Atomic is exact: there is no erased
         conjunction boundary to recover or guess. *)
      fun conjunction_free_equality_result reason theorem =
        let val _ = boolSyntax.dest_eq (Thm.concl theorem) in
          exact_result
            (conjunction_free_semantic_provenance reason
              (Thm.concl theorem)) theorem
        end
        handle Feedback.HOL_ERR _ => unavailable_result reason theorem
      fun require_declared name theorem =
        case conclusion of
          NONE => theorem
        | SOME target =>
            if Term.aconv (Thm.concl theorem) target then theorem
            else raise ERR name
              "direct result differs from the declared conclusion"
      fun attempt work fallback =
        work () handle Feedback.HOL_ERR _ => fallback ()
      (* Canonical rung shared by trans and eq_resolve: replay canonically,
         then restore the declared conclusion through the weak canonicalizer
         and, failing that, the strong one. *)
      fun canonical_rung name replay =
        let val theorem = replay prems in
          require_declared name theorem
          handle Feedback.HOL_ERR _ =>
            (restore_canonical_conclusion name conclusion
               (SmtReplayCanon.cpc_canon_rule theorem)
             handle Feedback.HOL_ERR _ =>
               restore_strong_canonical_conclusion strong_canon
                 name conclusion theorem)
        end
      fun canonical_handler name replay =
        let val exposed = List.map expose_true_equality prems in
          require_declared name (replay exposed)
        handle Feedback.HOL_ERR _ =>
          (restore_canonical_conclusion name conclusion
             (replay
               (List.map expose_true_equality
                 (canonical_premises exposed)))
           handle Feedback.HOL_ERR _ =>
             restore_strong_canonical_conclusion strong_canon
               name conclusion
               (replay
                 (List.map expose_true_equality
                   (List.map
                     (Conv.CONV_RULE strong_canon) exposed))))
        end
      fun arithmetic_bridge theorems target =
        let
          val hypotheses = HOLset.listItems
            (HOLset.fromList Term.compare
              (List.filter boolSyntax.is_eq
                (List.concat (List.map Thm.hyp theorems))))
          val assumptions = List.map Thm.ASSUME hypotheses
          fun relation_bridge proposition =
            let
              val arithmetic_type = SmtReplayCanon.is_arith_type
              fun private_integer_division tm =
                let
                  val (head, _) = boolSyntax.strip_comb tm
                  val {Thy, Name, ...} = Term.dest_thy_const head
                in
                  Thy = "integer" andalso
                  (Name = "ediv" orelse Name = "emod")
                end
                handle Feedback.HOL_ERR _ => false
              fun total_integer_division tm =
                let val (head, _) = boolSyntax.strip_comb tm in
                  Term.is_const head andalso
                  (Term.same_const head SmtReplayCanon.smt_ediv_total_tm
                   orelse Term.same_const head
                     SmtReplayCanon.smt_emod_total_tm)
                end
                handle Feedback.HOL_ERR _ => false
              fun opaque_arithmetic tm =
                arithmetic_type (Term.type_of tm) andalso
                (boolSyntax.is_cond tm orelse intSyntax.is_div tm orelse
                 intSyntax.is_mod tm orelse private_integer_division tm orelse
                 total_integer_division tm)
              fun is_relation tm =
                Lib.can arith_dest_less tm orelse
                Lib.can arith_dest_leq tm orelse
                Lib.can arith_dest_greater tm orelse
                Lib.can arith_dest_geq tm
              fun normalize_arithmetic_equality tm =
                let
                  val (left, right) = boolSyntax.dest_eq tm
                  val _ = arithmetic_type (Term.type_of left) andalso
                          arithmetic_type (Term.type_of right) orelse
                    raise Conv.UNCHANGED
                in
                  Conv.CHANGED_CONV
                    (Conv.BINOP_CONV
                      (Conv.QCONV
                        SmtReplayCanon.arith_poly_norm_conversion)) tm
                end
              fun normalize_endpoint tm =
                if is_relation tm orelse
                   arithmetic_type (Term.type_of tm) then
                  SmtReplayCanon.compose
                    [neutral_arithmetic_conv,
                     Conv.DEPTH_CONV normalize_arithmetic_equality,
                     SmtReplayCanon.cpc_operand_canon_conv,
                     SmtReplayCanon.arith_poly_norm_conversion]
                    tm
                else raise ERR "trans"
                  "middle endpoint is not arithmetic"
              fun normalized_prove target =
                let
                  val (target_left, target_right) =
                    boolSyntax.dest_eq target
                  val left_norm = normalize_endpoint target_left
                  val right_norm = normalize_endpoint target_right
                  val normalized_left =
                    boolSyntax.rhs (Thm.concl left_norm)
                  val normalized_right =
                    boolSyntax.rhs (Thm.concl right_norm)
                  val same = Term.aconv normalized_left normalized_right
                  val _ = same orelse
                    raise ERR "trans"
                      "polynomial relation endpoints differ"
                  val theorem = Thm.TRANS left_norm (Thm.SYM right_norm)
                in theorem end
              fun abstract_bridge () =
                prove_from_prems_abstracting normalized_prove
                  opaque_arithmetic [] proposition
            in
              abstract_bridge ()
              handle Feedback.HOL_ERR _ => normalized_prove proposition
            end
          fun division_prove proposition =
            let
              val total_div = SmtReplayCanon.smt_ediv_total_tm
              fun dest_total term =
                let val (head, operands) = boolSyntax.strip_comb term in
                  case operands of
                    [dividend, divisor] =>
                      if Term.same_const head total_div then
                        (dividend, divisor)
                      else raise ERR "trans" "not a totalized division"
                  | _ => raise ERR "trans" "not a totalized division"
                end
              val pairs =
                List.map intSyntax.dest_div
                  (HolKernel.find_terms intSyntax.is_div proposition) @
                List.map intSyntax.dest_mod
                  (HolKernel.find_terms intSyntax.is_mod proposition) @
                List.map dest_total
                  (HolKernel.find_terms (Lib.can dest_total) proposition)
              fun division_identities (dividend, divisor) =
                let
                  val nonzero = simpLib.SIMP_PROVE (bossLib.srw_ss ()) []
                    (boolSyntax.mk_neg
                      (boolSyntax.mk_eq (divisor, intSyntax.zero_tm)))
                  val division = Thm.SPEC dividend
                    (Thm.MP (Thm.SPEC divisor integerTheory.INT_DIVISION)
                      nonzero)
                  val identity = Thm.CONJUNCT1 division
                in
                  [identity, Thm.SYM identity]
                end
                handle Feedback.HOL_ERR _ => []
              val identities = List.concat
                (List.map division_identities pairs)
              fun adapt theorem =
                let
                  val (theorem_left, theorem_right) =
                    boolSyntax.dest_eq (Thm.concl theorem)
                  val (target_left, target_right) =
                    boolSyntax.dest_eq proposition
                  fun polynomial_bridge left right =
                    SmtReplayCanon.prove_polynomial_equality
                      (boolSyntax.mk_eq (left, right))
                in
                  if Term.aconv theorem_left target_left then
                    Thm.TRANS theorem
                      (polynomial_bridge theorem_right target_right)
                  else if Term.aconv theorem_right target_left then
                    Thm.TRANS (Thm.SYM theorem)
                      (polynomial_bridge theorem_left target_right)
                  else if Term.aconv theorem_left target_right then
                    Thm.TRANS
                      (polynomial_bridge target_left theorem_right)
                      (Thm.SYM theorem)
                  else if Term.aconv theorem_right target_right then
                    Thm.TRANS
                      (polynomial_bridge target_left theorem_left) theorem
                  else raise ERR "trans"
                    "division identity has different endpoints"
                end
            in
              (Lib.tryfind adapt identities
               handle Feedback.HOL_ERR _ =>
                 Tactical.TAC_PROOF (([], proposition),
                   bossLib.FULL_SIMP_TAC bossLib.arith_ss
                     (identities @
                      [HolSmtTheory.smt_ediv_total_def,
                       integerTheory.EDIV_DEF])))
              handle Feedback.HOL_ERR holerr =>
                raise ERR "trans"
                  ("division identity proof failed; proposition=" ^
                   Library.term_to_string proposition ^
                   "; pairs=" ^ Int.toString (List.length pairs) ^
                   "; identities=" ^ String.concatWith "; "
                     (List.map
                       (Library.term_to_string o Thm.concl) identities) ^
                   "; underlying=" ^ Feedback.message_of holerr)
            end
          fun contradiction theorem =
            let
              val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
              val (equality, proposition) =
                if Term.aconv right boolSyntax.F then (theorem, left)
                else if Term.aconv left boolSyntax.F then
                  (Thm.SYM theorem, right)
                else raise ERR "trans"
                  "division contradiction premise is not false-valued"
              val contradiction_thm = Thm.EQ_MP equality
                (division_prove proposition)
            in
              Thm.MP (Thm.SPEC target boolTheory.FALSITY) contradiction_thm
            end
          fun false_valued theorem =
            let val (left, right) = boolSyntax.dest_eq (Thm.concl theorem) in
              Term.aconv left boolSyntax.F orelse
              Term.aconv right boolSyntax.F
            end
            handle Feedback.HOL_ERR _ => false
          fun fallback () =
            (prove_from_prems division_prove
               (assumptions @ theorems) target
             handle Feedback.HOL_ERR _ =>
               arith_prove_from_prems assumptions target)
        in
          relation_bridge target
          handle Feedback.HOL_ERR _ =>
          case List.find false_valued theorems of
            SOME theorem =>
              (contradiction theorem
               handle Feedback.HOL_ERR division_error =>
                 (fallback ()
                  handle Feedback.HOL_ERR _ =>
                    raise Feedback.HOL_ERR division_error))
          | NONE => fallback ()
        end
      fun arithmetic_trans () =
        let
          fun oriented theorem reverse =
            if reverse then Thm.SYM theorem else theorem
          fun compose (next, accumulated) =
            let
              fun attempt reverse_accumulated reverse_next =
                let
                  val accumulated' =
                    oriented accumulated reverse_accumulated
                  val next' = oriented next reverse_next
                  val (_, middle_left) =
                    boolSyntax.dest_eq (Thm.concl accumulated')
                  val (middle_right, _) =
                    boolSyntax.dest_eq (Thm.concl next')
                  val bridge = arithmetic_bridge [accumulated', next']
                    (boolSyntax.mk_eq (middle_left, middle_right))
                in
                  Thm.TRANS (Thm.TRANS accumulated' bridge) next'
                end
            in
              attempt false false
              handle Feedback.HOL_ERR _ => attempt false true
              handle Feedback.HOL_ERR _ => attempt true false
              handle Feedback.HOL_ERR _ => attempt true true
            end
        in
          case prems of
            [] => raise ERR "trans" "expected CPC equality premises"
          | first :: rest => List.foldl compose first rest
        end
      fun arithmetic_eq_resolve_pair proposition equality =
        let
          val (left, right) = boolSyntax.dest_eq (Thm.concl equality)
          fun prove_side premise side =
            arith_prove_from_prems [premise] side
          val simplified =
            bossLib.SIMP_RULE (bossLib.srw_ss ()) [] proposition
          fun resolve_simplified () =
            Thm.EQ_MP equality simplified
            handle Feedback.HOL_ERR _ =>
              Thm.EQ_MP (Thm.SYM equality) simplified
          fun prove side =
            prove_side proposition side
            handle Feedback.HOL_ERR _ =>
              (* arith_reduction states both positive- and negative-divisor
                 bounds as guarded implications.  Discharge literal guards
                 in this semantic arithmetic rung, independently of strong
                 definition canonicalization. *)
              prove_side
                simplified side
        in
          resolve_simplified ()
          handle Feedback.HOL_ERR _ => Thm.EQ_MP equality (prove left)
          handle Feedback.HOL_ERR _ =>
            Thm.EQ_MP (Thm.SYM equality) (prove right)
        end
      fun arithmetic_eq_resolve () =
        (case prems of
          [left, right] =>
            (arithmetic_eq_resolve_pair left right
             handle Feedback.HOL_ERR _ =>
               arithmetic_eq_resolve_pair right left)
        | _ => raise ERR "eq_resolve" "expected two CPC premises")
      fun normalized_proposition_eq_resolve () =
        let
          fun normalize theorem =
            Conv.CONV_RULE strong_canon theorem
        in
          case prems of
            [left, right] =>
              (arithmetic_eq_resolve_pair (normalize left) right
               handle Feedback.HOL_ERR _ =>
                 arithmetic_eq_resolve_pair (normalize right) left)
          | _ => raise ERR "eq_resolve" "expected two CPC premises"
        end
      fun eq_resolve_from_scope_hypotheses target =
        let
          val hypotheses = HOLset.listItems
            (HOLset.fromList Term.compare
              (List.concat (List.map Thm.hyp prems)))
          val _ = List.null hypotheses andalso
            raise ERR "eq_resolve" "premises have no scope hypotheses"
          val assumptions = List.map Thm.ASSUME hypotheses
        in
          arith_prove_from_prems assumptions target
          handle Feedback.HOL_ERR holerr =>
            raise ERR "eq_resolve"
              ("scope-hypothesis arithmetic failed for " ^
               Library.term_to_string
                 (boolSyntax.list_mk_imp (hypotheses, target)) ^ "; " ^
               Feedback.message_of holerr)
        end
      fun canonical_trans () =
        let
          fun direct () = require_declared "trans" (replay_trans prems)
          fun evaluated_arithmetic () =
            let
              fun is_total subterm =
                Term.is_const subterm andalso
                (Term.same_const subterm SmtReplayCanon.smt_ediv_total_tm
                 orelse Term.same_const subterm
                   SmtReplayCanon.smt_emod_total_tm)
              fun has_total theorem =
                not (List.null
                  (HolKernel.find_terms is_total (Thm.concl theorem)))
              fun arithmetic_expression_equality theorem =
                let
                  val (left, right) =
                    boolSyntax.dest_eq (Thm.concl theorem)
                  fun arithmetic_operand tm =
                    SmtReplayCanon.is_arith_type (Term.type_of tm)
                in
                  arithmetic_operand left andalso arithmetic_operand right
                end
                handle Feedback.HOL_ERR _ => false
              val evaluate_chain =
                List.exists (fn name => name = "evaluate") premise_rules
              val expression_chain =
                List.all arithmetic_expression_equality prems
            in
            if not (Option.isSome conclusion) andalso
                (evaluate_chain orelse expression_chain) andalso
                List.exists has_total prems then
              arithmetic_trans ()
            else raise ERR "trans"
              "no omitted evaluate endpoint for arithmetic preflight"
            end
          fun canonical () = canonical_rung "trans"
            (replay_canonical_trans strong_canon)
          fun fallback () =
            case conclusion of
              (* E1(b): general arithmetic implication proving is the
                 coverage terminal after canonical composition. *)
              SOME target =>
                profile "CPC(rung:canonical_trans/general-arithmetic)"
                  (fn () => arith_prove_from_prems prems target) ()
            | NONE =>
                (arithmetic_trans ()
                 handle Feedback.HOL_ERR holerr =>
                   raise ERR "trans"
                     ("checked middle-equality reconstruction failed; " ^
                      "premises=" ^ String.concatWith "; "
                        (List.map Library.thm_to_string prems) ^
                      "; underlying=" ^ Feedback.message_of holerr))
        in
          attempt direct (fn () =>
            attempt evaluated_arithmetic (fn () =>
              attempt canonical fallback))
        end
      fun canonical_eq_resolve () =
        let
          fun direct () =
            require_declared "eq_resolve" (replay_eq_resolve prems)
          fun ground_false () =
            let
              fun prove_false theorem =
                let
                  val proposition = Thm.concl theorem
                  val _ = List.null (Term.free_vars proposition) orelse
                    raise ERR "eq_resolve"
                      "ground contradiction premise has free variables"
                  val evaluation = bossLib.EVAL proposition
                  val normalized = boolSyntax.rhs (Thm.concl evaluation)
                  val _ = Term.aconv normalized boolSyntax.F orelse
                    raise ERR "eq_resolve"
                      "closed premise does not evaluate to false"
                in
                  Thm.EQ_MP evaluation theorem
                end
              val contradiction = Lib.tryfind prove_false prems
              val with_support = retain_all contradiction prems
            in
              require_declared "eq_resolve" with_support
            end
          fun arithmetic () =
            case conclusion of
              SOME _ =>
                if List.exists (fn theorem =>
                     SmtResource.term_nodes_up_to 1000
                       (Thm.concl theorem) > 1000) prems
                then raise ERR "eq_resolve"
                  "large arithmetic equality uses canonical replay first"
                else if List.exists (fn theorem =>
                     HOLset.member (Thm.hypset theorem, boolSyntax.T)) prems
                then raise ERR "eq_resolve"
                  "arithmetic preflight retains a trivial scope hypothesis"
                else if List.exists (fn theorem =>
                     not (List.null (HolKernel.find_terms (fn tm =>
                       Type.compare (Term.type_of tm,
                         realSyntax.real_ty) = EQUAL)
                       (Thm.concl theorem)))) prems
                then raise ERR "eq_resolve"
                  "mixed real arithmetic uses canonical replay first"
                else
                  require_declared "eq_resolve" (arithmetic_eq_resolve ())
            | NONE => raise ERR "eq_resolve"
                "arithmetic preflight requires a declared conclusion"
          fun canonical () =
            canonical_rung "eq_resolve"
              (replay_canonical_eq_resolve strong_canon)
          fun normalized () =
            require_declared "eq_resolve"
              (normalized_proposition_eq_resolve ())
          fun fallbacks () =
            case conclusion of
              SOME target =>
                (arith_prove_from_prems prems target
                 handle Feedback.HOL_ERR _ =>
                   (eq_resolve_from_scope_hypotheses target
                    handle Feedback.HOL_ERR scope_error =>
                      (prove_cast_arithmetic prems target
                       handle Feedback.HOL_ERR cast_error =>
                         raise ERR "eq_resolve"
                           ("scope fallback: " ^
                            Feedback.message_of scope_error ^
                            "; cast fallback: " ^
                            Feedback.message_of cast_error))))
            | NONE => raise ERR "eq_resolve"
                ("canonical premises do not rewrite one another; " ^
                 "premises=" ^ String.concatWith "; "
                   (List.map (Library.term_to_string o Thm.concl) prems))
        in
          attempt direct (fn () =>
            attempt ground_false (fn () =>
              attempt arithmetic (fn () =>
                attempt canonical (fn () =>
                  attempt normalized fallbacks))))
        end
      fun canonical_resolution () =
        let
          (* Compact chain resolution may omit the conclusion while recording
             it as the first argument.  Keep that inferred endpoint available
             for restoration; a two-argument binary resolution instead
             records polarity and pivot, so its result is premise-derived. *)
          val replay_target =
            case (conclusion, args) of
              (SOME target, _) => SOME target
            | (NONE, [_, _]) => NONE
            | (NONE, target :: _) => SOME target
            | (NONE, []) => NONE
          val normalized_prems = List.map
            (Conv.CONV_RULE SmtReplayCanon.cpc_operand_canon_conv) prems
          val normalized_conclusion = Option.map canonical_operand conclusion
          val normalized_args = List.map canonical_operand args
          fun restore theorem =
            case replay_target of
              NONE => theorem
            | SOME target =>
                Thm.EQ_MP
                  (Thm.SYM (SmtReplayCanon.cpc_operand_canon_conv target))
                  theorem
          fun restore_strong theorem =
            restore_with strong_canon "strong" "resolution"
              replay_target theorem
          fun integer_resolution () =
            let
              val integer_prems = List.map
                (Conv.CONV_RULE cpc_integer_normal_form_conv) prems
              val integer_conclusion = Option.map (fn target =>
                boolSyntax.rhs
                  (Thm.concl (cpc_integer_normal_form_conv target)))
                conclusion
              val integer_args = List.map (fn argument =>
                boolSyntax.rhs
                  (Thm.concl (cpc_integer_normal_form_conv argument))) args
              val theorem = replay_resolution integer_prems
                integer_conclusion integer_args
            in
              restore_with cpc_integer_normal_form_conv
                "integer spelling" "resolution" replay_target theorem
            end
        in
        (require_declared "resolution"
           (replay_resolution prems conclusion args)
         handle Feedback.HOL_ERR _ =>
           (restore (replay_resolution normalized_prems
                normalized_conclusion normalized_args)
            handle Feedback.HOL_ERR _ =>
              (integer_resolution ()
               handle Feedback.HOL_ERR _ =>
               let
                val strong_prems =
                  List.map (Conv.CONV_RULE strong_canon) prems
                val strong_args = List.map (fn arg =>
                  boolSyntax.rhs
                    (Thm.concl (strong_canon arg))) args
                val strong_conclusion = Option.map (fn target =>
                  boolSyntax.rhs
                    (Thm.concl (strong_canon target))) conclusion
                val theorem =
                  case strong_conclusion of
                    SOME target =>
                      if Term.aconv target boolSyntax.T then
                        retain_all boolTheory.TRUTH strong_prems
                      else replay_resolution strong_prems
                        strong_conclusion strong_args
                  | NONE => replay_resolution strong_prems
                      strong_conclusion strong_args
              in
                restore_strong theorem
              end)))
        handle Feedback.HOL_ERR _ =>
          (case replay_target of
             SOME target =>
               (arith_prove_from_prems prems target
                handle Feedback.HOL_ERR holerr =>
                  raise ERR "resolution"
                    ("explicit target resolution failed; target=" ^
                     Library.term_to_string target ^ "; premises=" ^
                     String.concatWith "; "
                       (List.map
                         (Library.term_to_string o Thm.concl) prems) ^
                     "; arithmetic fallback: " ^
                     Feedback.message_of holerr))
           | NONE => raise ERR "resolution"
               ("canonical CPC clauses do not resolve; premises=" ^
                String.concatWith "; "
                  (List.map (Library.term_to_string o Thm.concl) prems) ^
                "; arguments=" ^ String.concatWith "; "
                  (List.map Library.term_to_string args)))
        end
      fun canonical_reordering () =
        let
          val target = expect_one_arg "reordering" args
          fun contains_real_div term =
            Library.contains_const SmtReplayCanon.smt_rdiv_tm term orelse
            not (List.null
              (HolKernel.find_terms realSyntax.is_div term))
          val uses_real_div =
            List.exists contains_real_div
              (target :: List.map Thm.concl prems)
          fun real_div_reordering () =
            if uses_real_div then
              profile "CPC(rung:reordering/real_div)"
                (fn () => replay_normalized_reordering
                  (real_div_reordering_conv strong_canon) prems target) ()
            else
              raise ERR "reordering"
                "real-division normalization is inapplicable"
        in
          replay_normalized_reordering SmtReplayCanon.cpc_canon_conv
            prems target
          handle Feedback.HOL_ERR _ =>
            real_div_reordering ()
          handle Feedback.HOL_ERR _ =>
            replay_normalized_reordering strong_canon prems target
        end
      fun canonical_cong () =
        restore_canonical_conclusion "cong" conclusion
          (replay_cong (canonical_conclusion conclusion)
            (List.map canonical_term args) (canonical_premises prems))
      fun canonical_cong_result_with canon description =
        case conclusion of
          SOME _ => unavailable_result
            ("declared " ^ description ^
             " congruence uses its exact conclusion")
            (canonical_cong ())
        | NONE =>
            let
              fun normalized_term term =
                boolSyntax.rhs (Thm.concl (canon term))
              val normalized_args = List.map normalized_term args
              val normalized_prems =
                List.map (Conv.CONV_RULE canon) prems
            in
              case (located_args, normalized_args) of
                ([source], [normalized_source]) =>
                  let
                    val source_normalization = canon (#term source)
                    val normalized_located = {
                      term = normalized_source,
                      provenance = align_canonical_provenance
                        canon (#term source) normalized_source
                        (#provenance source)
                    }
                    fun normalized_step
                        ((premise_step : replayed_step), normalized_theorem) =
                      let
                        val original_theorem = step_theorem premise_step
                        val normalized_provenance =
                          align_canonical_provenance
                            canon (Thm.concl original_theorem)
                            (Thm.concl normalized_theorem)
                            (step_provenance premise_step)
                      in
                        {rule_name = #rule_name premise_step,
                         result = exact_result normalized_provenance
                           normalized_theorem}
                      end
                    val normalized_steps = ListPair.mapEq normalized_step
                      (premise_steps, normalized_prems)
                    val exact = replay_exact_cong_result NONE
                      normalized_located normalized_steps
                    val theorem = Thm.TRANS source_normalization
                      (result_theorem exact)
                    val rewritten_provenance =
                      case #provenance (result_located exact) of
                        EqualityProvenance (_, right) => right
                      | other => other
                  in
                    exact_result
                      (EqualityProvenance
                        (#provenance source, rewritten_provenance))
                      theorem
                  end
              | _ => raise ERR "cong_provenance"
                  (description ^
                   " congruence lacks one exact source occurrence")
            end
      fun canonical_cong_result () =
        canonical_cong_result_with SmtReplayCanon.cpc_canon_conv
          "canonical"
      fun strong_canonical_cong_result () =
        canonical_cong_result_with strong_canon
          "strong canonical"
      fun integer_spelling_cong_result () =
        canonical_cong_result_with cpc_integer_normal_form_conv
          "integer spelling canonical"
      fun reducing_cong () =
        let
          val source = expect_one_arg "cong" args
          val polynomial_normalization = Conv.QCONV
            SmtReplayCanon.arith_poly_norm_conversion source
          val polynomial_source =
            boolSyntax.rhs (Thm.concl polynomial_normalization)
          val ground_normalization =
            Conv.QCONV ground_neutral_arithmetic_conv polynomial_source
          val normalization =
            Thm.TRANS polynomial_normalization ground_normalization
          val normalized_source =
            boolSyntax.rhs (Thm.concl normalization)
          (* Once [normalization] is exactly the declared conclusion, an
             unused premise is logically irrelevant, but still contributes
             its hypotheses. *)
          fun retained () = retain_all normalization prems
          val theorem =
            (Thm.TRANS normalization
              (replay_cong NONE [normalized_source] prems)
             handle Feedback.HOL_ERR _ => retained ())
        in
          require_declared "cong" theorem
          handle Feedback.HOL_ERR _ =>
            restore_canonical_conclusion "cong" conclusion
              (SmtReplayCanon.cpc_canon_rule theorem)
        end
      fun reducing_cong_result () =
        let
          val source =
            case located_args of
              [located] => located
            | _ => raise ERR "cong_provenance"
                "reducing congruence lacks one exact source occurrence"
          val polynomial_conv = Conv.QCONV
            SmtReplayCanon.arith_poly_norm_conversion
          val polynomial_normalization = polynomial_conv (#term source)
          val polynomial_source = boolSyntax.rhs
            (Thm.concl polynomial_normalization)
          val polynomial_provenance = align_canonical_provenance
            polynomial_conv (#term source) polynomial_source
            (#provenance source)
          val ground_conv = Conv.QCONV ground_neutral_arithmetic_conv
          val ground_normalization = ground_conv polynomial_source
          val normalization = Thm.TRANS polynomial_normalization
            ground_normalization
          val normalized_source = boolSyntax.rhs (Thm.concl normalization)
          val normalized_provenance = align_canonical_provenance
            ground_conv polynomial_source normalized_source
            polynomial_provenance
          val normalized_located = {
            term = normalized_source,
            provenance = normalized_provenance
          }
          fun normalize_step (premise_step : replayed_step) =
            let
              val original_theorem = step_theorem premise_step
              val polynomial_theorem =
                Conv.CONV_RULE polynomial_conv original_theorem
              val polynomial_premise_provenance =
                align_canonical_provenance polynomial_conv
                  (Thm.concl original_theorem)
                  (Thm.concl polynomial_theorem)
                  (step_provenance premise_step)
              val normalized_theorem =
                Conv.CONV_RULE ground_conv polynomial_theorem
              val normalized_premise_provenance =
                align_canonical_provenance ground_conv
                  (Thm.concl polynomial_theorem)
                  (Thm.concl normalized_theorem)
                  polynomial_premise_provenance
            in
              {rule_name = #rule_name premise_step,
               result = exact_result normalized_premise_provenance
                 normalized_theorem}
            end
            handle Feedback.HOL_ERR holerr =>
              raise ERR "cong_provenance"
                ("reducing congruence could not normalize premise " ^
                 Library.term_to_string
                   (Thm.concl (step_theorem premise_step)) ^ "; " ^
                 Feedback.message_of holerr)
          val normalized_steps = List.map normalize_step premise_steps
        in
          let
            val exact = replay_exact_cong_result NONE normalized_located
              normalized_steps
              handle Feedback.HOL_ERR holerr =>
                raise ERR "cong_provenance"
                  ("reducing congruence exact rewrite failed: " ^
                   Feedback.message_of holerr ^ "; source=" ^
                   Library.term_to_string normalized_source ^
                   "; premises=" ^ String.concatWith "; "
                     (List.map (fn premise =>
                       Library.term_to_string
                         (Thm.concl (step_theorem premise)) ^
                       " [" ^ provenance_shape
                         (step_provenance premise) ^ "]")
                       normalized_steps))
            val theorem = Thm.TRANS normalization (result_theorem exact)
            val result = result_located exact
          in
            exact_result
              (EqualityProvenance
                (#provenance source,
                 (case #provenance result of
                    EqualityProvenance (_, right) => right
                  | other => other)))
              theorem
          end
        end
      (* Cache/proforma probe precedes general provers.  We can only probe a
         declared conclusion; omitted CPC conclusions are rule-derived. *)
      fun omitted_conclusion () =
            (#omitted_bypasses (#cache_stats state) :=
               !(#omitted_bypasses (#cache_stats state)) + 1;
             profile_event "CPC(cache:omitted_conclusion)";
             NONE)
      val cached =
        if #replay_handler rule = "scope" then
          (case conclusion of
             NONE => omitted_conclusion ()
           | SOME _ =>
               (profile_event "CPC(cache:scope_bypass)"; NONE))
        else case conclusion of
          SOME target => (SOME (cached_thm state target)
            handle Feedback.HOL_ERR _ => NONE)
        | NONE => omitted_conclusion ()
      val (state, result) =
        if #replay_handler rule = "scope" then
          let
            val (state, theorem) =
              profile ("CPC(handler:" ^ namespace_name (#namespace rule) ^
                "/" ^ #name rule ^ ")")
                (fn () => replay_scope state prems) ()
          in
            (state, opaque theorem)
          end
        else
          let
            val result = case cached of
              SOME theorem =>
                (case located_conclusion of
                   SOME located =>
                     located_result "cached CPC step" theorem located
                 | NONE => raise ERR "replay_step"
                     "omitted CPC conclusion unexpectedly used theorem cache")
            | NONE =>
              (profile ("CPC(handler:" ^ namespace_name (#namespace rule) ^
                 "/" ^ #name rule ^ ")") (fn () =>
               (case #replay_handler rule of
           "refl" =>
               let
                 val theorem = replay_refl conclusion args
                 val provenance =
                   case located_args of
                     [located] => EqualityProvenance
                       (#provenance located, #provenance located)
                   | _ => UnavailableProvenance
                       "refl lacks one exact operand occurrence"
               in exact_result provenance theorem end
           | "eq_refl" =>
               let
                 val theorem = replay_eq_refl args
                 val provenance =
                   case located_args of
                     [located] => EqualityProvenance
                       (#provenance located, #provenance located)
                   | _ => UnavailableProvenance
                       "eq_refl lacks one exact operand occurrence"
               in exact_result provenance theorem end
           | "symm" => replay_symm_result premise_steps
           | "trans" =>
               (case conclusion of
                  SOME _ => opaque (canonical_trans ())
                | NONE =>
                    let
                      val (theorem, provenance) =
                        (replay_trans_with_provenance premise_steps
                         handle Feedback.HOL_ERR direct_error =>
                           let
                             val canonical =
                               replay_canonical_trans_with_provenance
                                 strong_canon
                                 premise_steps
                           in
                             canonical
                           end
                           handle Feedback.HOL_ERR canonical_error =>
                             (canonical_trans (),
                              UnavailableProvenance
                                ("trans exact endpoint unavailable; direct: " ^
                                 Feedback.message_of direct_error ^
                                 "; canonical: " ^
                                 Feedback.message_of canonical_error ^
                                 "; premises: " ^
                                 String.concatWith "; "
                                   (List.map (fn premise =>
                                     Library.term_to_string
                                       (Thm.concl
                                         (step_theorem premise)) ^
                                     " [" ^ provenance_shape
                                       (step_provenance premise) ^ "]")
                                     premise_steps)))
                           )
                    in exact_result provenance theorem end)
           | "cong" =>
               ((case (conclusion, located_args) of
                   (NONE, [source]) =>
                     replay_exact_cong_result NONE source premise_steps
                | _ => unavailable_result
                     "declared congruence uses its exact conclusion"
                     (require_declared "cong"
                       (replay_cong conclusion args prems)))
                handle Feedback.HOL_ERR direct_error =>
                  (canonical_cong_result ()
                   handle Feedback.HOL_ERR canonical_error =>
                     (integer_spelling_cong_result ()
                      handle Feedback.HOL_ERR spelling_error =>
                        (strong_canonical_cong_result ()
                         handle Feedback.HOL_ERR strong_error =>
                           (case conclusion of
                              NONE =>
                                (reducing_cong_result ()
                                 handle Feedback.HOL_ERR reducing_error =>
                                   raise ERR "cong_provenance"
                                     ("direct: " ^
                                      Feedback.message_of direct_error ^
                                      "; canonical: " ^
                                      Feedback.message_of canonical_error ^
                                      "; integer spelling: " ^
                                      Feedback.message_of spelling_error ^
                                      "; strong: " ^
                                      Feedback.message_of strong_error ^
                                      "; reducing: " ^
                                      Feedback.message_of reducing_error))
                            | SOME _ => unavailable_result
                                ("congruence exact occurrence unavailable; " ^
                                 "direct: " ^
                                 Feedback.message_of direct_error ^
                                 "; canonical: " ^
                                 Feedback.message_of canonical_error ^
                                 "; integer spelling: " ^
                                 Feedback.message_of spelling_error ^
                                 "; strong: " ^
                                 Feedback.message_of strong_error)
                                (reducing_cong ()))))))
           | "ho_cong" => opaque ( replay_ho_cong prems)
           | "beta_reduce" => opaque ( replay_beta_reduce args)
           | "lambda_elim" => opaque ( replay_lambda_elim args)
           | "eq_resolve" =>
               (case conclusion of
                  SOME _ => opaque (canonical_eq_resolve ())
                | NONE =>
                    let
                      val (theorem, provenance) =
                        (replay_eq_resolve_with_provenance premise_steps
                         handle Feedback.HOL_ERR _ =>
                           (replay_canonical_eq_resolve_with_provenance
                              SmtReplayCanon.cpc_operand_canon_conv
                              premise_steps
                            handle Feedback.HOL_ERR _ =>
                              (replay_canonical_eq_resolve_with_provenance
                                 cpc_integer_normal_form_conv premise_steps
                               handle Feedback.HOL_ERR _ =>
                                 (replay_canonical_eq_resolve_with_provenance
                                    cpc_ground_arithmetic_guard_conv
                                    premise_steps
                                  handle Feedback.HOL_ERR _ =>
                                    (replay_canonical_eq_resolve_with_provenance
                                       strong_canon premise_steps
                                     handle Feedback.HOL_ERR _ =>
                                       let
                                         val fallback =
                                           canonical_eq_resolve ()
                                       in
                                         (fallback, UnavailableProvenance
                                           "eq_resolve used reconstruction without an exact equality-side occurrence")
                                       end)))))
                    in exact_result provenance theorem end)
           | "contra" => opaque ( canonical_handler "contra" replay_contra)
           | "false_intro" => opaque ( replay_false_intro prems)
           | "false_elim" => opaque ( replay_false_elim prems)
           | "true_elim" => opaque ( replay_true_elim prems)
           | "true_intro" => opaque ( replay_true_intro prems)
           | "evaluate" =>
               conjunction_free_equality_result
                 "evaluation result contains an exact conjunction"
                 (replay_evaluate conclusion args)
           | "and_elim" =>
               (case premise_steps of
                  [premise_step] =>
                    let
                      val (theorem, provenance) =
                        replay_and_elim conclusion args premise_step
                    in exact_result provenance theorem end
                | _ => raise ERR "and_elim"
                    "expected exactly one CPC premise")
           | "instantiate" => opaque ( replay_instantiate args prems)
           | "not_implies_elim2" =>
               let
                 val theorem = replay_not_implies_elim2 prems
                 val provenance =
                   case premise_steps of
                     [premise] =>
                       (case step_provenance premise of
                          ApplicationProvenance
                            ("not", [ApplicationProvenance
                              (_, [_, consequent])]) =>
                            ApplicationProvenance ("not", [consequent])
                        | _ => UnavailableProvenance
                            ("not_implies_elim2 lacks exact implication syntax; " ^
                             "premise=" ^ provenance_shape
                               (step_provenance premise)))
                   | _ => UnavailableProvenance
                       "not_implies_elim2 has wrong premise count"
               in exact_result provenance theorem end
           | "not_implies_elim1" =>
               let
                 val theorem = replay_not_implies_elim1 prems
                 val provenance =
                   case premise_steps of
                     [premise] =>
                       (case step_provenance premise of
                          ApplicationProvenance
                            ("not", [ApplicationProvenance
                              (_, [antecedent, _])]) => antecedent
                        | _ => UnavailableProvenance
                            ("not_implies_elim1 lacks exact implication syntax; " ^
                             "premise=" ^ provenance_shape
                               (step_provenance premise)))
                   | _ => UnavailableProvenance
                       "not_implies_elim1 has wrong premise count"
                 val provenance =
                   case provenance of
                     UnavailableProvenance reason =>
                       conjunction_free_semantic_provenance reason
                         (Thm.concl theorem)
                   | exact => exact
               in exact_result provenance theorem end
           | "implies_elim" => opaque ( replay_implies_elim prems)
           | "factoring" => opaque ( replay_factoring prems)
           | "reordering" => opaque (
               (replay_reordering prems args
                handle Feedback.HOL_ERR _ => canonical_reordering ()))
           | "exists_elim" => opaque ( replay_rare_rewrite "exists-elim" args)
           | "cnf" => opaque ( replay_cnf (#name rule) args)
           | "not_equiv_elim1" => opaque ( replay_not_equiv_elim "not_equiv_elim1" prems)
           | "not_equiv_elim2" => opaque ( replay_not_equiv_elim "not_equiv_elim2" prems)
           | "equiv_elim2" => opaque ( replay_equiv_elim2 conclusion prems)
           | "equiv_elim1" => opaque ( replay_equiv_elim1 conclusion prems)
           | "arith_rule" =>
               replay_arith_rule_result (#name rule) located_args
           | "arith_rel" => opaque ( replay_arith_rel prems args)
           | "arith_abs_eq" => opaque ( replay_arith_abs_eq args)
           | "arith_abs_int_gt" => opaque ( replay_arith_abs_int_gt args)
           | "arrays_select_const" => opaque ( replay_arrays_select_const args)
           | "arrays_read_over_write" => opaque (
               replay_arrays_read_over_write (#name rule) prems conclusion args)
           | "ite_not_cond" => opaque ( replay_ite_not_cond args)
           | "ite_true_cond" => opaque ( replay_ite_true_cond args)
           | "ite_then_true" => opaque ( replay_ite_then_true args)
           | "ite_false_cond" => opaque ( replay_ite_false_cond args)
           | "ite_neg_branch" => opaque ( replay_ite_neg_branch args prems)
           | "trust" => opaque ( replay_trust state prems args)
           | "ite_eq" => opaque ( replay_ite_eq args)
           | "ite_elim1" => opaque ( replay_ite_elim1 prems)
           | "ite_elim2" => opaque ( replay_ite_elim2 prems)
           | "quant_unused_vars" => opaque ( replay_quant_unused_vars args)
           | "quant_rewrite" =>
               let
                 val theorem = replay_quant_rewrite (#name rule) args
               in
                 case located_args of
                   [located] => located_result
                     "quantifier rewrite exact argument" theorem located
                 | _ => unavailable_result
                     "quantifier rewrite lacks one exact equality argument"
                     theorem
               end
           | "alpha_equiv" => opaque ( replay_alpha_equiv args)
           | "process_scope" => opaque (
               replay_process_scope strong_canon args prems)
           | "not_and" => opaque ( replay_not_and prems)
           | "not_or_elim" => opaque ( replay_not_or_elim args prems)
           | "not_not_elim" =>
               let
                 val theorem = replay_not_not_elim prems
                 val provenance =
                   case premise_steps of
                     [premise] =>
                       (case step_provenance premise of
                          ApplicationProvenance
                            ("not", [ApplicationProvenance
                              ("not", [inner])]) => inner
                        | UnavailableProvenance reason =>
                            UnavailableProvenance
                              ("not_not_elim operand unavailable: " ^ reason)
                        | AmbiguousProvenance reason =>
                            AmbiguousProvenance
                              ("not_not_elim operand ambiguous: " ^ reason)
                        | _ => UnavailableProvenance
                            "not_not_elim premise lacks exact double-negation syntax")
                   | _ => UnavailableProvenance
                       "not_not_elim has wrong premise count"
               in exact_result provenance theorem end
           | "and_intro" =>
               let
                 val (theorem, provenance) =
                   replay_and_intro premise_steps
               in exact_result provenance theorem end
           | "skolemize" => opaque ( replay_skolemize prems)
           | "arith_mult_neg" => opaque ( replay_arith_mult_neg args)
           | "arith_mult_pos" => opaque ( replay_arith_mult_pos args)
           | "arith_mult_sign" => opaque ( replay_arith_mult_sign args)
           | "arith_trichotomy" => opaque ( replay_arith_trichotomy conclusion prems)
           | "arith_reduction" =>
               let
                 val (theorem, provenance) = replay_arith_reduction args
               in exact_result provenance theorem end
           | "arith_max_geq1" => opaque ( replay_arith_max_geq1 args)
           | "arith_min_lt2" => opaque ( replay_arith_min_lt2 args)
           | "int_tight_lb" => opaque ( replay_int_tight_lb prems)
           | "int_tight_ub" => opaque ( replay_int_tight_ub prems)
           | "modus_ponens" => opaque (
               (require_declared "modus_ponens" (replay_modus_ponens prems)
                 handle Feedback.HOL_ERR _ =>
                   require_declared "modus_ponens"
                    (replay_canonical_modus_ponens strong_canon prems)
                 handle Feedback.HOL_ERR _ =>
                   require_declared "modus_ponens"
                     (replay_arithmetic_modus_ponens prems)))
           | "arith_sum_ub" => opaque ( replay_arith_sum_ub prems)
           | "arith_mult_abs_comparison" => opaque (
               replay_arith_mult_abs_comparison prems conclusion)
           | "aci_norm" =>
               (case located_args of
                  [target] => located_result "aci_norm result"
                    (replay_aci_norm args) target
                | _ => unavailable_result
                    "aci_norm lacks one exact target occurrence"
                    (replay_aci_norm args))
           | "bv_xor_duplicate" => opaque ( replay_bv_xor_duplicate args)
           | "bv_not_idemp" => opaque ( replay_bv_not_idemp args)
           | "bv_shl_by_const_0" => opaque ( replay_bv_shl_by_const_0 args)
           | "bv_shl_by_const_2" => opaque ( replay_bv_shl_by_const_2 args)
           | "bv_lshr_by_const_0" => opaque ( replay_bv_lshr_by_const_0 args)
           | "bv_ashr_by_const_0" => opaque ( replay_bv_ashr_by_const_0 args)
           | "bv_poly_norm" => opaque ( replay_bv_poly_norm args)
           | "bv_poly_norm_eq" => opaque ( replay_bv_poly_norm_eq args)
           | "seq_rewrite" => opaque (
               replay_seq_rewrite (#name rule) prems conclusion args)
           | "seq_rev_rev" => opaque ( replay_seq_rev_rev args)
           | "str_contains_refl" => opaque ( replay_str_contains_refl args)
           | "str_substr_full_eq" => opaque ( replay_str_substr_full_eq args)
           | "seq_at_elim" => opaque ( replay_seq_at_elim conclusion args)
           | "sets" => opaque ( replay_sets state (#name rule) prems conclusion args)
           | "sets_ext" => opaque ( replay_sets_ext prems)
           | "sets_rewrite" => opaque (
               replay_sets state (#name rule) prems conclusion args)
           | "rewrite" =>
               let
                 val (theorem, provenance) =
                   replay_rare_rewrite_with_provenance
                     (#name rule) located_args
               in exact_result provenance theorem end
           | "datatype" => opaque ( replay_datatype args)
           | "dt_split" => opaque ( replay_dt_split args)
           | "datatype_eq" =>
               let
                 val theorem = replay_datatype_eq args
                 val provenance =
                   case located_args of
                     [located] => #provenance located
                   | _ => UnavailableProvenance
                       "datatype equality lacks its exact result argument"
               in exact_result provenance theorem end
           | "resolution" => opaque ( canonical_resolution ())
           | "bool" => opaque ( replay_bool prems conclusion)
           | "arith" => opaque ( replay_arith prems conclusion)
           | "string" => opaque (
               replay_string state (#name rule) prems conclusion args)
           | _ => unsupported_step step)) ()
           handle Conv.UNCHANGED =>
             raise ERR "replay_step"
               ("CPC step " ^ id ^ " (rule " ^ #name rule ^
                ") failed: proof-producing conversion reported unchanged")
                | Feedback.HOL_ERR holerr =>
             if SmtResource.is_resource_gate holerr then
               raise Feedback.HOL_ERR holerr
             else
               raise ERR "replay_step"
                 ("CPC step " ^ id ^ " (rule " ^ #name rule ^
                  ") failed: " ^ Feedback.message_of holerr))
          in (state, result) end
      val theorem = result_theorem result
      val _ = profile "CPC(check:step_conclusion)" (fn () =>
        case conclusion of
          NONE => ()
        | SOME target => if Term.aconv (Thm.concl theorem) target then () else
            raise ERR "replay_step" ("CPC rule " ^ #name rule ^
              " produced a conclusion different from its certificate")) ()
      val result = case located_conclusion of
          SOME located => located_result "replay_step" theorem located
        | NONE => result
      val state = cache_step state id (#name rule) result
    in
      (if Option.isSome cached then state else cache_thm state theorem,
       theorem)
    end

  fun replay_commands state commands =
    case commands of
      [] => raise ERR "replay_commands" "empty CPC proof"
    | [ASSUME (id, {term, provenance})] =>
        let val thm = Thm.ASSUME term
            val state = cache_step (assert_hyp state term) id "assume"
              (exact_result provenance thm)
        in (cache_thm state thm, thm) end
    | ASSUME (id, {term, provenance}) :: rest =>
        let val thm = Thm.ASSUME term
            val state = cache_step (assert_hyp state term) id "assume"
              (exact_result provenance thm)
        in replay_commands (cache_thm state thm) rest end
    | [ASSUME_PUSH (id, {term, provenance})] =>
        let val thm = Thm.ASSUME term
            val state = cache_step (push_scope_hyp state term) id
              "assume-push" (exact_result provenance thm)
        in (cache_thm state thm, thm) end
    | ASSUME_PUSH (id, {term, provenance}) :: rest =>
        let val thm = Thm.ASSUME term
            val state = cache_step (push_scope_hyp state term) id
              "assume-push" (exact_result provenance thm)
        in replay_commands (cache_thm state thm) rest end
    | [STEP step] => replay_step state step
    | STEP step :: rest =>
        let val (state, _) = replay_step state step
        in replay_commands state rest end

  (* cvc5's preprocessing can expose record and datatype eliminators in a
     proof assumption while the HOL goal retains its surface selector/update
     form.  Discharge only hypotheses that follow from the original replay
     context; this is a checked normalization bridge, never an assumption
     drop. *)
  fun remove_extra_hyps (asl, g, thm) =
    let
      val expected = HOLset.addList (Term.empty_tmset,
        boolSyntax.mk_neg g :: asl)
      val bad_hyps = HOLset.difference (Thm.hypset thm, expected)
      fun prove_from_context hyp =
        let
          val context = boolSyntax.mk_neg g :: asl
        in
          Tactical.TAC_PROOF ((context, hyp),
            Tactical.THEN
              (Tactical.REPEAT Tactic.COND_CASES_TAC,
               Tactical.THEN
                 (bossLib.FULL_SIMP_TAC (bossLib.srw_ss()) [],
                  intLib.ARITH_TAC)))
        end
      fun prove_hyp hyp =
        profile "CPC(remove_extra_hyps:ceiling_floor)" Lib.tryfind
          (fn assumption =>
            let
              val rewritten = Rewrite.PURE_REWRITE_RULE
                [HolSmtTheory.int_ceiling_floor] (Thm.ASSUME assumption)
            in
              if Term.aconv (Thm.concl rewritten) hyp then rewritten
              else raise ERR "remove_extra_hyps"
                "ceiling/floor rewrite did not match extra hypothesis"
            end)
          (boolSyntax.mk_neg g :: asl)
        handle Feedback.HOL_ERR _ =>
          profile "CPC(remove_extra_hyps:full_simp)" Tactical.TAC_PROOF
            ((boolSyntax.mk_neg g :: asl, hyp),
             bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
               [smtfloatTheory.smtfp_nan_bits,
                smtfloatTheory.smtfp_pzero_bits,
                smtfloatTheory.smtfp_nzero_bits,
                smtfloatTheory.smtfp_pinf_bits,
                smtfloatTheory.smtfp_ninf_bits])
        handle Feedback.HOL_ERR _ =>
          profile "CPC(remove_extra_hyps:floor_ceiling_neg)"
            Tactical.TAC_PROOF
            ((boolSyntax.mk_neg g :: asl, hyp),
             bossLib.FULL_SIMP_TAC (bossLib.srw_ss())
               [intrealTheory.INT_FLOOR_NEG, intrealTheory.INT_CEILING_NEG])
        handle Feedback.HOL_ERR _ =>
          profile "CPC(remove_extra_hyps:METIS)" Tactical.TAC_PROOF
            ((boolSyntax.mk_neg g :: asl, hyp), metisLib.METIS_TAC
               [smtfloatTheory.smtfp_bits_pzero,
                smtfloatTheory.smtfp_pzero_bits,
                smtfloatTheory.smtfp_bits_nzero,
                smtfloatTheory.smtfp_nzero_bits])
        handle Feedback.HOL_ERR _ =>
          profile "CPC(remove_extra_hyps:datatype)"
            SmtDatatypeProve.datatype_consequence_prove
            (boolSyntax.mk_neg g :: asl, hyp)
        handle Feedback.HOL_ERR _ =>
          if Library.contains_conditional hyp then
            profile "CPC(remove_extra_hyps:conditional_arith)"
              prove_from_context hyp
          else raise ERR "remove_extra_hyps"
            "extra hypothesis is not a conditional arithmetic consequence"
      fun remove_hyp (hyp, result) =
        Drule.PROVE_HYP (prove_hyp hyp) result
        handle Feedback.HOL_ERR holerr =>
          raise ERR "remove_extra_hyps"
            ("extra hypothesis is not one of the enumerated cvc5 semantic " ^
             "bridges; hypothesis=" ^ Library.term_to_string hyp ^
             "; attempted=[ceiling/floor, FP special values, floor/ceiling " ^
             "negation, datatype normalization, conditional arithmetic]; " ^
             "underlying=" ^ Feedback.message_of holerr)
    in
      HOLset.foldl remove_hyp thm bad_hyps
    end

in
  val theorem_cache_enabled_for_test = theorem_cache_enabled

  val strong_cpc_canon_conv_for_test = strong_cpc_canon_conv

  fun replay_rare_rewrite_for_test name args =
    replay_rare_rewrite name args

  fun replay_arith_reduction_for_test args =
    #1 (replay_arith_reduction args)

  fun replay_and_elim_provenance_for_test premise provenance index
      conclusion =
    let
      val index_term = intSyntax.mk_injected
        (numSyntax.mk_numeral (Arbnum.fromInt index))
      val step : replayed_step =
        {rule_name = "test", result = exact_result provenance premise}
    in
      #1 (replay_and_elim conclusion [index_term] step)
    end

  fun replay_result_alignment_for_test theorem located =
    ignore (located_result "test result alignment" theorem located)

  fun replay_cnf_for_test name args =
    replay_cnf name args

  fun replay_arith_abs_eq_for_test args =
    replay_arith_abs_eq args

  fun replay_arith_abs_int_gt_for_test args =
    replay_arith_abs_int_gt args

  fun replay_arith_mult_abs_comparison_for_test prems conclusion =
    replay_arith_mult_abs_comparison prems (SOME conclusion)

  fun replay_arith_mult_neg_for_test args =
    replay_arith_mult_neg args

  fun replay_arith_mult_pos_for_test args =
    replay_arith_mult_pos args

  fun check_proof_impl definitions (asl, g, proof : proof) =
    let
      val (state, thm) = replay_commands (initial_state definitions asl)
        (proof_commands proof)
      val _ = profile_cardinalities state
      val _ = profile "CPC(check:conclusion)"
        (fn (left, right) => Term.aconv left right)
        (Thm.concl thm, boolSyntax.F) orelse
        raise ERR "check_proof" "final CPC conclusion is not F"
      val thm = profile "CPC(check:remove_extra_hyps)" remove_extra_hyps
        (asl, g, thm)
      val allowed = HOLset.addList (Term.empty_tmset,
        boolSyntax.mk_neg g :: asl)
      val _ = profile "CPC(check:hypotheses)" HOLset.isSubset
        (Thm.hypset thm, allowed) orelse
        raise ERR "check_proof"
          ("CPC proof retains unexpected hypotheses: " ^
           String.concatWith ", " (List.map Library.term_to_string
             (HOLset.listItems (HOLset.difference (Thm.hypset thm, allowed)))) ^
           "; allowed: " ^ String.concatWith ", "
             (List.map Library.term_to_string (HOLset.listItems allowed)))
    in
      thm
    end

  fun check_proof_with_definitions definitions args =
    profile "CPC(check_proof:total)" (check_proof_impl definitions) args

  fun check_proof args = check_proof_with_definitions [] args

  fun replay_root_with_definitions_for_test definitions proof =
    let
      val (state, thm) = replay_commands (initial_state definitions [])
        (proof_commands proof)
      val _ = profile_cardinalities state
    in thm end

  fun replay_root_for_test proof =
    replay_root_with_definitions_for_test [] proof

  fun replay_step_provenance_with_definitions_for_test definitions proof id =
    let
      val (state, _) = replay_commands
        (initial_state definitions [])
        (proof_commands proof)
    in
      step_provenance (find_step "test provenance" state id)
    end

  fun replay_step_provenance_for_test proof id =
    replay_step_provenance_with_definitions_for_test [] proof id

  fun replay_root_with_cache_stats_and_definitions_for_test definitions proof =
    let
      val (state, thm) = replay_commands
        (initial_state definitions [])
        (proof_commands proof)
      val _ = profile_cardinalities state
    in (thm, cache_stats state) end

  fun replay_root_with_cache_stats_for_test proof =
    replay_root_with_cache_stats_and_definitions_for_test [] proof
end

end
