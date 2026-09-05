open HolKernel testutils

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

fun raises thunk =
  ((thunk (); false)
   handle Portable.Interrupt => raise Portable.Interrupt
        | HOL_ERR _ => true)

fun raises_with fragments thunk =
  ((thunk (); false)
   handle Portable.Interrupt => raise Portable.Interrupt
        | HOL_ERR error =>
            List.all
              (fn fragment =>
                String.isSubstring fragment (Feedback.message_of error))
              fragments)

val provenance =
  {file = "src/HOL/HOL.thy", line = 1, commit = "f7e02b7e"}

val p = mk_var ("bench_unit_p", bool)
val q = mk_var ("bench_unit_q", bool)

val solved_goal : benchLib.corpus_goal =
  {id = "unit-solved", goal = boolSyntax.mk_eq (p, p),
   source_method = "simp", recipe = benchLib.Invoke (benchLib.Simp, []),
   excl = [],
   provenance = provenance, representative = true}

(* A hand-built fixture names its own recipe, which is what makes it a
   fixture: the corpus reaches [benchLib.prepare_goal] only through
   [benchDerive.prepare], where the recipe is derived. *)
fun prepared ({id, goal, source_method, recipe, provenance,
               representative, ...} : benchLib.corpus_goal) =
  benchLib.prepare_goal recipe
    {id = id, goal = goal, source_method = source_method,
     provenance = provenance, representative = representative}

(* ---- the time budget has to preempt, not merely label it --------- *)

(* A budget that merely labels an overrun would let one goal run
   without bound, so this asserts the elapsed time, not just the
   verdict.  [Timeout.apply] runs its payload under the caller's thread
   attributes; those are observed here to admit the timer's interrupt,
   which is what makes the cut-off real.

   The payload stops itself after ten seconds so that a regression here
   fails rather than hanging the suite. *)
val _ =
  check
    ("a runaway computation is cut off at its budget",
     fn () =>
       let
         fun spin deadline =
           if Time.> (Time.now (), deadline) then () else spin deadline
         val started = Time.now ()
         val outcome =
           benchLib.within_budget (Time.fromSeconds 1)
             (fn () => spin (Time.+ (Time.now (), Time.fromSeconds 10)))
         val elapsed = Time.- (Time.now (), started)
       in
         not (isSome outcome) andalso Time.< (elapsed, Time.fromSeconds 5)
       end)

val failed_goal : benchLib.corpus_goal =
  {id = "unit-failed", goal = p,
   source_method = "simp", recipe = benchLib.Invoke (benchLib.Simp, []),
   excl = [],
   provenance = provenance, representative = true}

val duplicate_solved_goal : benchLib.corpus_goal =
  {id = "unit-solved-duplicate", goal = boolSyntax.mk_eq (p, p),
   source_method = "simp", recipe = benchLib.Invoke (benchLib.Simp, []),
   excl = [],
   provenance = provenance, representative = true}

val failed_shortfall : benchLib.shortfall =
  {id = "unit-failed", cause = benchLib.UnderIteration,
   date = "2026-08-10", note = "unit-test accounting sentinel"}

val translation_gap : benchLib.shortfall =
  {id = "unit-untranslatable", cause = benchLib.TranslationGap,
   date = "2026-08-10", note = "unit-test translation sentinel"}

val _ =
  check
    ("benchmark harness records a mapped-tactic success",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (benchLib.Invoke (benchLib.Simp, [])) solved_goal))

val _ =
  check
    ("benchmark harness enforces a zero time budget",
     fn () =>
       case benchLib.run_goal Time.zeroTime
              (benchLib.Invoke (benchLib.Simp, [])) solved_goal of
           benchLib.TIMEOUT => true
         | _ => false)

val _ =
  check
    ("benchmark harness accepts exact solved and shortfall sets",
     fn () =>
       let
         val result =
           benchLib.run_family
             {family = "unit",
              goals = map prepared [solved_goal, failed_goal],
              shortfalls = [failed_shortfall],
              budget = Time.fromSeconds 5, battery = [], level = 1}
       in
         length (#gated result) = 2 andalso null (#battery result)
       end)

val _ =
  check
    ("benchmark accounting rejects a newly solved registered shortfall",
     fn () =>
       raises
         (fn () =>
           benchLib.assert_accounting
             {family = "unit-improvement", goals = [failed_goal],
              shortfalls = [failed_shortfall],
              gated = [("unit-failed", benchLib.SOLVED Time.zeroTime)]}))

val _ =
  check
    ("benchmark accounting rejects an unregistered failure",
     fn () =>
       raises
         (fn () =>
           benchLib.assert_accounting
             {family = "unit-regression", goals = [solved_goal],
             shortfalls = [],
             gated = [("unit-solved", benchLib.FAILED "sentinel")]}))

val _ =
  check
    ("benchmark accounting accepts a goal-free translation gap",
     fn () =>
       (benchLib.assert_accounting
          {family = "unit-translation", goals = [solved_goal],
           shortfalls = [translation_gap],
           gated = [("unit-solved", benchLib.SOLVED Time.zeroTime)]};
        true))

val _ =
  check
    ("benchmark accounting rejects a goal-free non-translation gap",
     fn () =>
       raises
         (fn () =>
           benchLib.assert_accounting
             {family = "unit-unknown", goals = [solved_goal],
              shortfalls = [failed_shortfall],
              gated = [("unit-solved", benchLib.SOLVED Time.zeroTime)]}))

val _ =
  check
    ("benchmark accounting rejects aconv corpus duplicates",
     fn () =>
       raises
         (fn () =>
           benchLib.assert_accounting
             {family = "unit-aconv",
              goals = [solved_goal, duplicate_solved_goal],
              shortfalls = [], gated = []}))

val analogue = Drule.SPECL [p, q] boolTheory.OR_INTRO_THM1
val analogue_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE}
val analogue_cs =
  clasetLib.add_rule analogue_spec
    ("unit$self_analogue", analogue) clasetLib.empty_cs
val excluded_goal : benchLib.corpus_goal =
  {id = "unit-exclusion", goal = boolSyntax.mk_disj (p, q),
   source_method = "blast", recipe = benchLib.Invoke (benchLib.Blast, []),
   excl = [{name = "unit$self_analogue", theorem = analogue}],
   provenance = provenance, representative = true}

val _ =
  check
    ("self-analogue exclusion removes every aconv claset copy",
     fn () => benchLib.exclusions_effective analogue_cs excluded_goal)

val _ =
  check
    ("level-2 battery outcomes are recorded but not gated",
     fn () =>
       let
         val result =
           benchLib.run_family
             {family = "unit-battery",
              goals = map prepared [solved_goal],
              shortfalls = [], budget = Time.fromSeconds 5,
              battery = [benchLib.Auto, benchLib.Aesop], level = 2}
       in
         length (#gated result) = 1 andalso
         length (#battery result) =
           (if OS.Process.getEnv "HOLBENCHNOBATTERY" = SOME "1"
            then 0 else 2)
       end)

fun recipe_goal id recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = "recipe selftest",
   recipe = recipe, excl = [], provenance = provenance,
   representative = true}

fun recipe_solves recipe goal =
  let
    val entry = recipe_goal "unit-recipe" recipe goal
    val outcome = benchLib.run_goal (Time.fromSeconds 5) recipe entry
    fun outcome_text (benchLib.SOLVED elapsed) =
          "solved:" ^ Time.toString elapsed
      | outcome_text benchLib.TIMEOUT = "timeout"
      | outcome_text (benchLib.FAILED message) = "failed:" ^ message
    val _ =
      if benchLib.outcome_solved outcome orelse
          OS.Process.getEnv "HOLBENCHRECIPEFAIL" <> SOME "1"
      then ()
      else TextIO.print ("recipe failure: " ^ outcome_text outcome ^
                         "\n")
  in
    benchLib.outcome_solved outcome
  end

val conjunction_commute = boolTheory.CONJ_COMM
val disjunction_commute = boolTheory.DISJ_COMM
val r = mk_var ("bench_unit_r", bool)
val nested_conjunction_commute =
  boolSyntax.mk_eq
    (boolSyntax.mk_conj (p, boolSyntax.mk_conj (q, r)),
     boolSyntax.mk_conj (boolSyntax.mk_conj (q, r), p))
val nested_disjunction_commute =
  boolSyntax.mk_eq
    (boolSyntax.mk_disj (p, boolSyntax.mk_disj (q, r)),
     boolSyntax.mk_disj (boolSyntax.mk_disj (q, r), p))

val rewrite_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.RewriteAdd
        {name = "unit$conjunction_commute",
         theorem = conjunction_commute}])
val definition_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "unit$disjunction_commute",
         theorem = disjunction_commute}])
val mislabeled_definition_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "unit$not_a_definition",
         theorem = conjunction_commute}])

val _ =
  check
    ("an empty exclusion list cannot admit the measured theorem",
     fn () =>
       not
         (recipe_solves rewrite_recipe (Thm.concl conjunction_commute)))

val _ =
  check
    ("a definition label cannot admit the measured theorem",
     fn () =>
       not
         (recipe_solves mislabeled_definition_recipe
            (Thm.concl conjunction_commute)))

val truth_wrapped_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.RewriteAdd
        {name = "unit$conjunction_commute_as_truth",
         theorem = Drule.EQT_INTRO conjunction_commute}])

val _ =
  check
    ("a goal-as-truth wrapper cannot admit the measured theorem",
     fn () =>
       benchLib.theorem_is_goal
         (Thm.concl conjunction_commute)
         (Drule.EQT_INTRO conjunction_commute) andalso
       not
         (recipe_solves truth_wrapped_recipe
            (Thm.concl conjunction_commute)))

(* The ambient bridge rewrites a goal from the translation's
   [source_sorted_wrt] into SORTED wherever transitivity is
   dischargeable, which leaves a rule cited in the translation's
   spelling on the wrong side of it.  The crossing offers that rule in
   the goal's spelling too, with the bridge's own condition last so a
   destruction rule's major premise stays first. *)
val sorted_wrt_drop_rule =
  {name = "parityTranslation$source_sorted_wrt_drop",
   theorem = DB.fetch "parityTranslation" "source_sorted_wrt_drop"}

(* Two drops, so the goal is not the rule with its premises in another
   order -- which is a self-analogue A1 withholds, and would leave this
   check asserting the crossing on a rule the measurement never
   offers. *)
val crossing_goal =
  ``relation$transitive bench_cross_le ==>
    sorting$SORTED bench_cross_le bench_cross_xs ==>
    sorting$SORTED bench_cross_le (DROP bench_cross_n bench_cross_xs) /\
    sorting$SORTED bench_cross_le (DROP bench_cross_m bench_cross_xs)``

val crossing_recipe =
  benchLib.Invoke
    (benchLib.Auto,
     [benchLib.DestAdd (benchLib.UnsafeRule, sorted_wrt_drop_rule)])

val _ =
  check
    ("a supplied rule is offered across the ambient correspondence",
     fn () =>
       let
         val entry = recipe_goal "unit-crossing" crossing_recipe crossing_goal
         val crossings =
           List.filter
             (fn benchLib.DestAdd (_, {name, ...}) =>
                   name = "parityTranslation$source_sorted_wrt_drop[bridged]"
               | _ => false)
             (benchLib.across_correspondence entry
               [benchLib.DestAdd (benchLib.UnsafeRule, sorted_wrt_drop_rule)])
       in
         case crossings of
             [benchLib.DestAdd (_, {theorem, ...})] =>
               let
                 fun mentions name term =
                   List.exists
                     (fn constant => #1 (Term.dest_const constant) = name)
                     (find_terms Term.is_const term)
                 val (premises, conclusion) =
                   boolSyntax.strip_imp_only
                     (snd (boolSyntax.strip_forall (Thm.concl theorem)))
               in
                 List.length premises = 2 andalso
                 mentions "SORTED" (List.hd premises) andalso
                 mentions "transitive" (List.nth (premises, 1)) andalso
                 mentions "SORTED" conclusion
               end
           | _ => false
       end)

val _ =
  check
    ("the crossed rule is what closes a goal on the far side",
     fn () => recipe_solves crossing_recipe crossing_goal)

val implication_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.FactAdd
        {name = "unit$conjunction_commute_under_assumption",
         theorem = DISCH p conjunction_commute}])

val nested_then_recipe =
  benchLib.Then
    (benchLib.Invoke (benchLib.Safe, []), rewrite_recipe)

val nested_all_goals_recipe =
  benchLib.AllGoals
    (benchLib.Invoke (benchLib.Safe, []), truth_wrapped_recipe)

fun raw_recipe_rejected id argument_name recipe =
  raises_with [id, argument_name]
    (fn () =>
      benchLib.validate_raw_goal
        (recipe_goal id recipe (Thm.concl conjunction_commute)))

val _ =
  check
    ("raw validation rejects a direct measured theorem with diagnostics",
     fn () =>
       raw_recipe_rejected
         "unit-raw-direct" "unit$conjunction_commute" rewrite_recipe)

val _ =
  check
    ("raw validation rejects a truth-wrapped measured theorem",
     fn () =>
       raw_recipe_rejected
         "unit-raw-truth" "unit$conjunction_commute_as_truth"
         truth_wrapped_recipe)

val _ =
  check
    ("raw validation rejects an implication with the measured conclusion",
     fn () =>
       raw_recipe_rejected
         "unit-raw-implication"
         "unit$conjunction_commute_under_assumption" implication_recipe)

val _ =
  check
    ("raw validation rejects a theorem falsely labelled as a definition",
     fn () =>
       raw_recipe_rejected
         "unit-raw-definition" "unit$not_a_definition"
         mislabeled_definition_recipe)

val _ =
  check
    ("raw validation descends through Then recipes",
     fn () =>
       raw_recipe_rejected
         "unit-raw-then" "unit$conjunction_commute"
         nested_then_recipe)

val _ =
  check
    ("raw validation descends through AllGoals recipes",
     fn () =>
       raw_recipe_rejected
         "unit-raw-all-goals" "unit$conjunction_commute_as_truth"
         nested_all_goals_recipe)

val _ =
  check
    ("preparation rejects rather than deleting a forbidden raw argument",
     fn () =>
       raises_with ["unit-raw-prepare", "unit$conjunction_commute"]
         (fn () =>
           ignore
             (prepared
               (recipe_goal "unit-raw-prepare" rewrite_recipe
                  (Thm.concl conjunction_commute)))))

val _ =
  check
    ("recipe-local schemas still close non-analogue instances",
     fn () =>
       recipe_solves rewrite_recipe nested_conjunction_commute andalso
       recipe_solves definition_recipe nested_disjunction_commute andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            nested_conjunction_commute) andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            nested_disjunction_commute))

val length_reverse =
  {name = "list$LENGTH_REVERSE", theorem = listTheory.LENGTH_REVERSE}
val length_reverse_goal =
  Thm.concl
    (SPEC ``[T]``
      (INST_TYPE [Type.alpha |-> Type.bool] listTheory.LENGTH_REVERSE))
val fact_recipe =
  benchLib.Invoke
    (benchLib.Safe, [benchLib.FactAdd length_reverse])
val intro_recipe =
  benchLib.Invoke
    (benchLib.Safe,
     [benchLib.IntroAdd (benchLib.SafeRule, length_reverse)])

val _ =
  check
    ("recipe-local fact closes a goal that bare safe leaves",
     fn () =>
       recipe_solves fact_recipe length_reverse_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Safe, []))
            length_reverse_goal))

val _ =
  check
    ("recipe-local safe introduction closes a goal when omitted does not",
     fn () =>
       recipe_solves intro_recipe length_reverse_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Safe, []))
            length_reverse_goal))

val _ =
  check
    ("classical recipe phases ignore simpset-only arguments",
     fn () =>
       recipe_solves
         (benchLib.Invoke
            (benchLib.Safe,
             [benchLib.RewriteAdd length_reverse,
              benchLib.IntroAdd
                (benchLib.SafeRule, length_reverse)]))
         length_reverse_goal)

val _ =
  check
    ("recipe compilation does not mutate the persistent tactic context",
     fn () =>
       let
         val rules_before = map (#1 o #2) (clasetLib.rules_of
           (clasetLib.the_claset ()))
         val fragments_before = simpLib.all_named_frags ()
         val _ = recipe_solves intro_recipe length_reverse_goal
         val _ = recipe_solves rewrite_recipe
           (Thm.concl conjunction_commute)
         val rules_after = map (#1 o #2) (clasetLib.rules_of
           (clasetLib.the_claset ()))
         val fragments_after = simpLib.all_named_frags ()
       in
         rules_before = rules_after andalso
         fragments_before = fragments_after
       end)

val paired_length_reverse =
  boolSyntax.mk_conj (length_reverse_goal, length_reverse_goal)
val split_safe = benchLib.Invoke (benchLib.Safe, [])
val solve_length =
  benchLib.Invoke
    (benchLib.Safe,
     [benchLib.IntroAdd (benchLib.SafeRule, length_reverse)])

val _ =
  check
    ("Then continues only the first residual goal",
     fn () =>
       not
         (recipe_solves
           (benchLib.Then (split_safe, solve_length))
           paired_length_reverse))

val _ =
  check
    ("AllGoals continues every residual goal",
     fn () =>
       recipe_solves
         (benchLib.AllGoals (split_safe, solve_length))
         paired_length_reverse andalso
       not
         (recipe_solves
           (benchLib.AllGoals
             (split_safe, benchLib.Invoke (benchLib.Safe, [])))
           paired_length_reverse))

val recipe_constructor_names =
  benchLib.recipe_name
    (benchLib.Invoke
      (benchLib.Auto,
       [benchLib.RewriteDelete "unit$delete",
        benchLib.SplitAdd length_reverse,
        benchLib.IntroAdd (benchLib.UnsafeRule, length_reverse),
        benchLib.ElimAdd (benchLib.SafeRule, length_reverse),
        benchLib.DestAdd (benchLib.UnsafeRule, length_reverse),
        benchLib.CongruenceAdd length_reverse]))

val _ =
  check
    ("every remaining recipe constructor has a stable diagnostic",
     fn () =>
       List.all
         (fn text => String.isSubstring text recipe_constructor_names)
         ["rewrite-delete(unit$delete)", "split(list$LENGTH_REVERSE)",
          "intro-unsafe(list$LENGTH_REVERSE)",
          "elim-safe(list$LENGTH_REVERSE)",
          "dest-unsafe(list$LENGTH_REVERSE)",
          "cong(list$LENGTH_REVERSE)"] andalso
       String.isSubstring "otherwise("
         (benchLib.recipe_name
           (benchDerive.recipe_of ``!i : int. i * 1 = i`` "by algebra")))

(* ---- The stricter ambient set ------------------------------------ *)

(* Isabelle makes a [fun] definition ambient and a plain [definition]
   not.  The corpus does not record which introduced a constant, so
   recursion stands in, and the report measures the corpus under both
   sets.  What has to hold is that the strict set is a subset -- it can
   only withhold -- and that withholding actually reaches the recipes
   of the methods that read the ambient context. *)
val _ =
  check
    ("the strict ambient set withholds and never adds",
     fn () =>
       let
         val strict = map #name benchAmbient.recursive_definitions
         val generous = map #name benchAmbient.definitions
         val _ =
           TextIO.print
             (" [strict " ^ Int.toString (length strict) ^ " of " ^
              Int.toString (length generous) ^ "] ")
       in
         not (null strict) andalso
         length strict < length generous andalso
         List.all (fn name => List.exists (equal name) generous) strict
       end)

val _ =
  check
    ("restricting the ambient set narrows the recipes that read it",
     fn () =>
       let
         val goals = benchSets.goals
         val restricted =
           benchDerive.restrict_ambient benchAmbient.recursive_arguments
             goals
         fun width (entry : benchLib.corpus_goal) =
           length (benchLib.recipe_arguments (#recipe entry))
         val widths = ListPair.zip (map width goals, map width restricted)
       in
         length goals = length restricted andalso
         List.all (fn (generous, strict) => strict <= generous) widths
         andalso List.exists (fn (generous, strict) => strict < generous)
           widths
       end)

(* A goal the corpus did not derive has no Isabelle method to re-derive
   from, so restricting the context must leave it exactly as it was. *)
val _ =
  check
    ("restricting the ambient set leaves a HOL4-native goal alone",
     fn () =>
       let
         val native =
           List.filter
             (fn (entry : benchLib.corpus_goal) =>
               not (String.isPrefix "src/HOL/" (#file (#provenance entry))))
             benchPresburger.goals
         val restricted =
           benchDerive.restrict_ambient benchAmbient.recursive_arguments
             native
       in
         not (null native) andalso
         ListPair.all
           (fn (before_cut, after_cut) =>
             benchLib.recipe_name (#recipe before_cut) =
             benchLib.recipe_name (#recipe after_cut))
           (native, restricted)
       end)

(* ---- Phase A detectors ------------------------------------------- *)

fun guard_entry id method arguments goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = benchLib.Invoke (benchLib.Simp, arguments),
   excl = [], provenance = provenance, representative = true}

val subset_goal = Thm.concl (Drule.SPEC_ALL pred_setTheory.SUBSET_DEF)
val subset_flipped = Conv.GSYM pred_setTheory.SUBSET_DEF

val _ =
  check
    ("A1 catches a supplied theorem that is the goal with a flipped iff",
     fn () =>
       benchLib.theorem_is_goal subset_goal subset_flipped andalso
       benchGuards.recognition_route subset_goal subset_flipped =
       SOME "syntactic")

(* The shape that made this necessary: a translation lemma stating a
   membership characterisation with its conjuncts in the other order
   and its equation the other way round is the goal it would be handed
   to, and comparing the terms as written does not see it. *)
val member_goal =
  ``MEM (x : num) xs <=> ?i. i < LENGTH xs /\ EL i xs = x``

val member_commuted =
  Rewrite.PURE_ONCE_REWRITE_RULE [boolTheory.CONJ_COMM]
    (Drule.SPEC_ALL
      (Thm.INST_TYPE [Type.alpha |-> numSyntax.num] listTheory.MEM_EL))

val _ =
  check
    ("A1 catches a supplied theorem that is the goal reordered",
     fn () => benchLib.theorem_is_goal member_goal member_commuted)

val _ =
  check
    ("A1 leaves a supplied theorem that states something else alone",
     fn () =>
       not
         (benchLib.theorem_is_goal member_goal
            (Thm.INST_TYPE [Type.alpha |-> numSyntax.num]
              listTheory.MEM_APPEND)))

(* A citation can be the goal and still carry premises, and a
   comparison that strips only the citation puts its conclusion beside
   the whole goal and never sees it.  The quantifier prefix is where
   the two drift apart: the same statement written with the bound
   variables in another order is not alpha-equivalent to it, which is
   how a translation stated as its own goal went unnoticed. *)
val premised_goal =
  ``!l1 l2 n. n < LENGTH (l1 : 'a list) ==> EL n (l1 ++ l2) = EL n l1``

val _ =
  check
    ("A1 catches a supplied theorem that is a goal carrying premises",
     fn () =>
       benchLib.theorem_is_goal premised_goal rich_listTheory.EL_APPEND1)

val _ =
  check
    ("A1 leaves a theorem whose premise the goal does not carry alone",
     fn () =>
       not
         (benchLib.theorem_is_goal premised_goal
            rich_listTheory.EL_APPEND2))

(* [clean_simpset] filters whole theorems, and the simpset then splits
   what survives into one rewrite per conjunct.  So a conjunctive rule
   carrying the goal among its conjuncts reaches the goal as a rewrite
   that is it, and each conjunct has to be read on its own. *)
val _ =
  check
    ("A1 catches a conjunct of a supplied theorem that is the goal",
     fn () =>
       benchLib.theorem_is_goal ``!l. [] ++ l = l`` listTheory.APPEND)

val _ =
  check
    ("A1 leaves a conjunctive theorem no conjunct of which is the goal",
     fn () =>
       not
         (benchLib.theorem_is_goal
            ``!l1 l2. LENGTH (l1 ++ l2) = LENGTH l1 + LENGTH l2``
            listTheory.APPEND))

val _ =
  check
    ("A1 catches a goal-as-truth wrapper through the cheap pre-filter",
     fn () =>
       benchGuards.recognition_route subset_goal
         (Drule.EQT_INTRO (Drule.SPEC_ALL pred_setTheory.SUBSET_DEF)) =
       SOME "syntactic")

val guarded_length_reverse =
  Drule.GEN_ALL
    (Thm.DISCH boolSyntax.T (Drule.SPEC_ALL listTheory.LENGTH_REVERSE))

val _ =
  check
    ("A1 catches a supplied theorem behind a dischargeable hypothesis",
     fn () =>
       not
         (benchLib.theorem_is_goal length_reverse_goal
            guarded_length_reverse) andalso
       Option.isSome
         (benchGuards.recognition_route length_reverse_goal
            guarded_length_reverse))

val _ =
  check
    ("A1 does not call an unrelated supplied theorem recognition",
     fn () =>
       benchGuards.recognition_route length_reverse_goal
         boolTheory.CONJ_COMM = NONE)

val _ =
  check
    ("A1 does not credit a theorem for a goal the ambient route closes",
     fn () =>
       benchGuards.recognition_route
         (boolSyntax.mk_disj (p, boolSyntax.mk_neg p))
         boolTheory.CONJ_COMM = NONE)

(* ---- the comparison reads through a translation wrapper --------- *)

(* A corpus goal wears the translation's constant while an ambient rule
   wears HOL4's, and [source_lenlex] *is* [SHORTLEX] by definition.  A
   comparison of the two terms as written cannot see the analogy, so a
   rule that states such a goal would be handed to it undetected.  Both
   statements here are synthetic; neither is a corpus goal. *)
val wrapped_goal =
  ``!R xs ys.
      source_lenlex R xs ys /\ source_lenlex R ys xs ==>
      source_lenlex R xs ys``

val unwrapped_rule =
  Tactical.prove
    (``!R xs ys. SHORTLEX R xs ys /\ SHORTLEX R ys xs ==> SHORTLEX R xs ys``,
     bossLib.metis_tac [])

fun without_definitions body =
  let
    val installed = benchLib.definitional_theorems ()
    val value = body () handle exception_raised =>
      (benchLib.set_definitional_context installed; raise exception_raised)
  in
    benchLib.set_definitional_context installed; value
  end

val _ =
  check
    ("A1 catches an ambient rule that is the goal under its wrapper",
     fn () =>
       let
         val plain =
           without_definitions
             (fn () =>
               (benchLib.set_definitional_context [];
                benchLib.theorem_is_goal wrapped_goal unwrapped_rule))
       in
         not plain andalso
         benchLib.theorem_is_goal wrapped_goal unwrapped_rule
       end)

val _ =
  check
    ("A1 leaves an ambient rule about the same constant alone",
     fn () =>
       not
         (benchLib.theorem_is_goal wrapped_goal listTheory.SHORTLEX_NIL2))

(* Unfolding a definition against itself leaves [t = t], which matches
   every other vacuous statement.  The wrapper's own definition must not
   be read as stating an arbitrary goal. *)
val _ =
  check
    ("A1 does not read a wrapper definition as stating the goal",
     fn () =>
       not
         (benchLib.theorem_is_goal wrapped_goal
            parityTranslationTheory.source_lenlex_def))

(* A [define_new_type_bijections] theorem is registered as a definition
   and is equational, so it reaches the ambient rewrite set; reading it
   as an unfolding would make [source_literal_implode_valid] and the
   round-trip goal the same term. *)
val _ =
  check
    ("A1 does not read a type-bijection characterisation as an unfolding",
     fn () =>
       not
         (benchLib.theorem_is_goal
            (Thm.concl
               parityTranslationTheory.source_literal_explode_implode)
            parityTranslationTheory.source_literal_implode_valid))

val _ =
  check
    ("the ambient sweep collects the definitions the goal's wrapper needs",
     fn () =>
       List.exists
         (fn theorem =>
           Term.aconv (Thm.concl theorem)
             (Thm.concl parityTranslationTheory.source_lenlex_def))
         (benchGuards.relevant_definitions wrapped_goal))

(* Collecting the candidates is not the same as consulting them: A1 has
   to run the sweep, or a rule the corpus declares for every goal is
   never judged at all.  The witness is taken from the live claset --
   the set the sweep reads -- so the test does not depend on which
   rules the seeds happen to declare. *)
val ambient_rule =
  let
    val logical =
      ["/\\", "\\/", "~", "==>", "=", "!", "?", "?!", "T", "F",
       "COND", "@"]
    fun ordinary constant =
      not (List.exists (equal (#1 (Term.dest_const constant))) logical)
    fun translated constant =
      String.isPrefix "source_" (#1 (Term.dest_const constant))
    (* A rule in the translation's own constants would be filtered out
       of the candidates by the goal's unfolded reading, so the witness
       is one written in HOL4's. *)
    fun substantial ({thm, ...} : clasetLib.aesop_rule) =
      let val constants = find_terms Term.is_const (Thm.concl thm)
      in
        List.exists ordinary constants andalso
        not (List.exists translated constants)
      end
  in
    case List.filter substantial
           (clasetLib.all_rules (clasetLib.the_claset ())) of
        [] => raise Fail "the benchmark claset declares no ordinary rule"
      | rule :: _ => #thm rule
  end

val _ =
  check
    ("A1 reports an ambient rule that states the goal",
     fn () =>
       List.exists
         (fn ({detector, detail, ...} : benchGuards.finding) =>
           detector = "A1" andalso String.isPrefix "ambient " detail)
         (benchGuards.recognition_findings
            [guard_entry "unit-a1-ambient" "by simp" []
               (Thm.concl ambient_rule)]))

val translation_fact =
  benchLib.FactAdd
    {name = "parityTranslation$source_widget_iff",
     theorem = boolTheory.TRUTH}

val _ =
  check
    ("A2 rejects a translation lemma the Isabelle method never names",
     fn () =>
       benchGuards.provenance_violations
         (guard_entry "unit-a2-unnamed" "by blast" [translation_fact]
            subset_goal) =
       ["parityTranslation$source_widget_iff"])

val _ =
  check
    ("A2 accepts a translation lemma named modulo a documented suffix",
     fn () =>
       null
         (benchGuards.provenance_violations
            (guard_entry "unit-a2-named" "by (blast intro: widget)"
               [translation_fact] subset_goal)))

val _ =
  check
    ("A2 accepts a registered definition of a constant of the goal",
     fn () =>
       null
         (benchGuards.provenance_violations
            (guard_entry "unit-a2-definition" "by blast"
               [benchLib.DefinitionAdd
                  {name = "parityTranslation$source_subset_def",
                   theorem = pred_setTheory.SUBSET_DEF}]
               subset_goal)))

val _ =
  check
    ("A2 ignores arguments that are not translation lemmas",
     fn () =>
       null
         (benchGuards.provenance_violations
            (guard_entry "unit-a2-library" "by blast"
               [benchLib.RewriteAdd
                  {name = "pred_set$SUBSET_DEF",
                   theorem = pred_setTheory.SUBSET_DEF}]
               subset_goal)))

val _ =
  check
    ("A3 classifies Isabelle methods by their head",
     fn () =>
       List.all benchGuards.is_search_method
         ["by blast", "by (auto simp: dom_def)", "by force",
          "using takeWhile_eq_Nil_iff by fastforce", "by(clarsimp)"]
       andalso
       not
         (List.exists benchGuards.is_search_method
            ["by simp", "by (simp add: fun_eq_iff)", "by linarith"]))

val a3_budget = Time.fromSeconds 10

val _ =
  check
    ("A3 reports a search-method goal closed with no search work",
     fn () =>
       length
         (benchGuards.search_work_findings a3_budget
            [guard_entry "unit-a3-idle" "by blast"
               [benchLib.RewriteAdd length_reverse] length_reverse_goal]) = 1)

val a3_search_goal =
  boolSyntax.mk_imp
    (boolSyntax.mk_imp (p, q),
     boolSyntax.mk_imp (boolSyntax.mk_neg q, boolSyntax.mk_neg p))

val a3_search_entry : benchLib.corpus_goal =
  {id = "unit-a3-search", goal = a3_search_goal,
   source_method = "by blast",
   recipe = benchLib.Invoke (benchLib.Blast, []),
   excl = [], provenance = provenance, representative = true}

val _ =
  check
    ("A3 accepts a search-method goal that the engine actually searched",
     fn () =>
       let
         val (outcome, work) =
           benchGuards.measured_run a3_budget a3_search_entry
       in
         benchLib.outcome_solved outcome andalso
         searchWork.total work >= benchGuards.work_floor andalso
         null (benchGuards.search_work_findings a3_budget [a3_search_entry])
       end)

val _ =
  check
    ("A3 leaves goals whose method is not a search method alone",
     fn () =>
       null
         (benchGuards.search_work_findings a3_budget
            [guard_entry "unit-a3-simp" "by simp"
               [benchLib.RewriteAdd length_reverse] length_reverse_goal]))

val a4_goals =
  [guard_entry "unit-a4-one" "by blast" [translation_fact] subset_goal,
   guard_entry "unit-a4-two" "by auto" [] length_reverse_goal]

val _ =
  check
    ("A4 reports a translation lemma used by one goal that never names it",
     fn () =>
       map #id (benchGuards.single_use_findings a4_goals) = ["unit-a4-one"])

val _ =
  check
    ("A4 leaves a translation lemma shared by two goals alone",
     fn () =>
       null
         (benchGuards.single_use_findings
            [guard_entry "unit-a4-shared-one" "by blast"
               [translation_fact] subset_goal,
             guard_entry "unit-a4-shared-two" "by auto"
               [translation_fact] length_reverse_goal]))

val alias_audit = benchGuards.alias_findings ()

val _ =
  check
    ("A5 reports every goal-shaped display alias",
     fn () =>
       List.all
         (fn name => List.exists (fn item => #id item = name) alias_audit)
         ["list$nub_set_for_card_set",
          "list$ALL_DISTINCT_CARD_LIST_TO_SET_for_nub"])

val _ =
  check
    ("A5 leaves an Isabelle attribute rendering alone",
     fn () =>
       not
         (List.exists
            (fn item => #id item = "list$SNOC_APPEND[symmetric]")
            alias_audit))

val _ =
  check
    ("A5 reports a display name mapped to a different theorem",
     fn () =>
       List.exists
         (fn item =>
           #id item = "list$LIST_REL_NIL" andalso
           String.isSubstring "different theorem" (#detail item))
         alias_audit)

val bound_x = ``!bench_guard_x. bench_guard_x = bench_guard_x``
val bound_y = ``!bench_guard_y. bench_guard_y = bench_guard_y``

val _ =
  check
    ("A6 signatures ignore bound variable names",
     fn () =>
       benchGuards.goal_signature bound_x =
       benchGuards.goal_signature bound_y)

val _ =
  check
    ("A6 signatures separate different statements",
     fn () =>
       benchGuards.goal_signature subset_goal <>
       benchGuards.goal_signature length_reverse_goal andalso
       benchGuards.goal_signature p <> benchGuards.goal_signature q)

(* ---- Phase B: the method parser ---------------------------------- *)

fun parses text = benchRecipe.parse text

fun parse_fails text =
  ((parses text; false)
   handle Portable.Interrupt => raise Portable.Interrupt
        | benchRecipe.Unparseable _ => true)

val _ =
  check
    ("the parser reads a bare method",
     fn () =>
       let val {facts, unfolded, methods} = parses "by blast"
       in
         null facts andalso null unfolded andalso
         map #name methods = ["blast"] andalso
         List.all (null o #modifiers) methods
       end)

val _ =
  check
    ("the parser reads simp add: and its one-token spelling alike",
     fn () =>
       benchRecipe.render (parses "by (auto simp add: dom_def fun_eq_iff)") =
       benchRecipe.render (parses "by(auto simp: dom_def fun_eq_iff)"))

fun modifiers_of text = #modifiers (hd (#methods (parses text)))

val _ =
  check
    ("the parser separates safe and unsafe rule modifiers",
     fn () =>
       modifiers_of
         "by (auto intro!: inj_onI dest: inj_onD elim: split_list)"
       = [benchRecipe.Intro (benchLib.SafeRule, ["inj_onI"]),
          benchRecipe.Dest (benchLib.UnsafeRule, ["inj_onD"]),
          benchRecipe.Elim (benchLib.UnsafeRule, ["split_list"])])

val _ =
  check
    ("the parser keeps deletions and additions apart",
     fn () =>
       modifiers_of
         ("by (auto simp del: map_of_eq_Some_iff " ^
          "simp: map_of_eq_Some_iff [symmetric])")
       = [benchRecipe.SimpDelete ["map_of_eq_Some_iff"],
          benchRecipe.SimpAdd ["map_of_eq_Some_iff[symmetric]"]])

val _ =
  check
    ("simp flip: reads its names right to left",
     fn () =>
       modifiers_of "by (auto simp flip: sorted_key_list_of_set_unique)"
       = [benchRecipe.SimpAdd
            ["sorted_key_list_of_set_unique[symmetric]"]])

val _ =
  check
    ("the parser attaches an attribute to the name it qualifies",
     fn () =>
       benchRecipe.cited_names
         (parses "by (blast dest!: set_update_subset_insert [THEN subsetD])")
       = ["set_update_subset_insert[THEN subsetD]"])

val _ =
  check
    ("the parser keeps a quoted term inside its attribute",
     fn () =>
       benchRecipe.cited_names
         (parses "by (blast intro: image_eqI [where ?x = \"u - {a}\" for u])")
       = ["image_eqI[where ?x = \"u - {a}\" for u]"])

val _ =
  check
    ("the parser reads using premises",
     fn () =>
       let
         val {facts, methods, ...} =
           parses "using takeWhile_eq_Nil_iff by fastforce"
       in
         facts = ["takeWhile_eq_Nil_iff"] andalso
         map #name methods = ["fastforce"]
       end)

val _ =
  check
    ("the parser reads unfolding names",
     fn () =>
       let
         val {unfolded, methods, ...} =
           parses "unfolding rel_fun_def rel_set_def set_Cons_def by fastforce"
       in
         unfolded = ["rel_fun_def", "rel_set_def", "set_Cons_def"] andalso
         map #name methods = ["fastforce"]
       end)

val _ =
  check
    ("the parser reads a terminal method after the first",
     fn () =>
       map #name (#methods (parses "by auto (auto elim!: le_funE)"))
       = ["auto", "auto"])

(* Isabelle's [+] repeats the method it follows.  The corpus records the
   source method verbatim, so the grammar has to carry the combinator
   rather than the transcription dropping it. *)
val _ =
  check
    ("the parser reads the + repetition combinator",
     fn () =>
       let
         val {methods, ...} =
           parses "unfolding listrel1_def by auto (blast intro: le_funE)+"
       in
         map #name methods = ["auto", "blast"] andalso
         map #repeated methods = [false, true]
       end)

val _ =
  check
    ("+ survives the render round trip",
     fn () =>
       benchRecipe.render (parses "by auto (blast intro: le_funE)+")
       = "by auto (blast intro: le_funE)+")

val _ =
  check
    ("a repeated method becomes a repeated recipe",
     fn () =>
       let
         val once =
           benchLib.recipe_name
             (benchDerive.recipe_of ``!x : bool. x \/ ~x`` "by blast")
         val repeated =
           benchLib.recipe_name
             (benchDerive.recipe_of ``!x : bool. x \/ ~x`` "by blast+")
       in
         repeated = "repeat(" ^ once ^ ")"
       end)

(* [metis] takes its facts unkeyed, so a bare name run inside a method
   is that method's fact list rather than a parse error. *)
val _ =
  check
    ("the parser reads an unkeyed fact list",
     fn () =>
       modifiers_of "by (metis in_set_conv_decomp)"
       = [benchRecipe.Facts ["in_set_conv_decomp"]] andalso
       benchRecipe.render (parses "by (metis in_set_conv_decomp)")
       = "by (metis in_set_conv_decomp)")

(* [list.distinct(1)] names one equation of a multi-clause fact.  The
   index belongs to the name; [by(auto ...)] still opens a method. *)
val _ =
  check
    ("the parser reads an indexed fact name",
     fn () =>
       modifiers_of "by (metis dropWhile_eq_Nil_conv list.distinct(1))"
       = [benchRecipe.Facts ["dropWhile_eq_Nil_conv", "list.distinct(1)"]]
       andalso
       map #name (#methods (parses "by(auto simp: dom_def)")) = ["auto"])

val _ =
  check
    ("the parser drops an Isabelle comment",
     fn () =>
       benchRecipe.render (parses "by blast (* somewhat slow *)")
       = "by blast")

(* Isabelle's [algebra] presimplifies with its [add:] theorems before
   it normalizes -- groebner.ML seeds a simpset with them -- so [add:]
   means the same thing there as everywhere else. *)
val _ =
  check
    ("add: is a simpset entry for every method that spells it",
     fn () =>
       modifiers_of "by (algebra add: sq_def)"
       = [benchRecipe.SimpAdd ["sq_def"]] andalso
       modifiers_of "by (simp add: sq_def)"
       = [benchRecipe.SimpAdd ["sq_def"]])

val _ =
  check
    ("an uncovered method string is an error, not a bare tactic",
     fn () =>
       parse_fails "apply (induct xs) apply simp done" andalso
       parse_fails "by (auto frobnicate: x)" andalso
       parse_fails "by (auto simp add:)")

val _ =
  check
    ("rendering a parsed method is idempotent",
     fn () =>
       let
         fun stable text =
           let val once = benchRecipe.render (parses text)
               val twice = benchRecipe.render (parses once)
           in
             once = twice orelse
             (print ("\n  " ^ text ^ "\n  -> " ^ once ^ "\n  -> " ^
                     twice ^ "\n"); false)
           end
       in
         List.all stable
           ["by blast", "by (simp add: dom_def)", "by(auto simp: Pow_def)",
            "using assms by (algebra add: collinear_def)",
            "unfolding mono_def by auto",
            "by auto (auto elim!: le_funE)",
            "by (auto simp del: X simp: X [symmetric])"]
       end)

(* Every Isabelle method string in the corpus parses.  This is the
   coverage claim B1 makes: no fallback, no hand-written override. *)
fun from_isabelle (entry : benchLib.corpus_goal) =
  String.isPrefix "src/HOL/" (#file (#provenance entry))

val corpus_goals =
  List.concat (map #goals parityLib.families)

val corpus_methods =
  let
    val seen = ref ([] : string list)
    fun note method =
      if List.exists (equal method) (!seen) then ()
      else seen := method :: !seen
  in
    app (note o #source_method) (List.filter from_isabelle corpus_goals);
    List.rev (!seen)
  end

val unparseable_methods =
  List.filter
    (fn method =>
      ((benchRecipe.parse method; false)
       handle Portable.Interrupt => raise Portable.Interrupt
            | benchRecipe.Unparseable _ => true))
    corpus_methods

val _ =
  check
    ("every Isabelle method string in the corpus parses",
     fn () =>
       (if null unparseable_methods then ()
        else
          print
            ("\nunparseable: " ^
             String.concatWith "\n             " unparseable_methods ^ "\n");
        null unparseable_methods))

(* ---- Phase B: the name table ------------------------------------- *)

(* Every name an Isabelle method cites has to resolve, or the recipe
   cannot be derived from the method. *)
val cited_by_corpus =
  let
    val seen = ref ([] : string list)
    fun note name =
      if List.exists (equal name) (!seen) then () else seen := name :: !seen
  in
    app (fn method => app note (benchRecipe.cited_names
                                  (benchRecipe.parse method)))
      corpus_methods;
    List.rev (!seen)
  end

val unresolved_names =
  List.filter (fn name => not (isSome (benchNames.lookup name)))
    cited_by_corpus

val _ =
  check
    ("the name table covers every name the corpus cites",
     fn () =>
       (if null unresolved_names then ()
        else
          print
            ("\nunresolved (" ^ Int.toString (length unresolved_names) ^
             " of " ^ Int.toString (length cited_by_corpus) ^ "):\n" ^
             String.concatWith "\n" unresolved_names ^ "\n");
        null unresolved_names))

(* A citation that names no theorem has to say why.  [Native] is the
   one kind an agent could abuse to make a shortfall disappear, so the
   table's whole native set is pinned here by name. *)
val native_citations =
  List.filter
    (fn name =>
      case benchNames.resolve name of
          benchNames.Native => true
        | _ => false)
    benchNames.names

val _ =
  check
    ("only the documented citations resolve as engine-native",
     fn () =>
       Portable.sort (fn a => fn b => String.<= (a, b)) native_citations =
       ["arg_cong2[where f=nths, OF refl]", "classical",
        "exI[where ?x = \"- u\" for u]", "if_split_asm", "if_splits",
        "list.distinct(1)", "nat_less_le", "pairwiseI"])

(* A goal identifier in the table would make it a per-goal hint table. *)
val _ =
  check
    ("no corpus goal identifier appears in the name table",
     fn () =>
       let
         val identifiers = map #id corpus_goals
       in
         List.all
           (fn name =>
             List.all (fn id => not (String.isSubstring id name)) identifiers)
           benchNames.names
       end)

(* An entry nothing cites is somewhere to park a convenient lemma
   against a goal that does not exist yet -- the channel A2 closes,
   left open from the other end.  The table covers the corpus exactly. *)
val uncited_entries =
  List.filter
    (fn name => not (List.exists (equal name) cited_by_corpus))
    benchNames.names

val _ =
  check
    ("the name table carries no entry the corpus does not cite",
     fn () =>
       (if null uncited_entries then ()
        else
          print
            ("\nuncited (" ^ Int.toString (length uncited_entries) ^
             " of " ^ Int.toString (length benchNames.names) ^ "):\n" ^
             String.concatWith "\n" uncited_entries ^ "\n");
        null uncited_entries))

(* Two entries under one citation is two answers to one question, and
   [lookup] silently takes the first: the second is unreachable and can
   contradict the one that wins.  Five did -- three calling a citation
   unrepresented that the winning entry resolves to a translation
   lemma, two naming a different translation lemma for it. *)
val repeated_entries =
  let
    fun repeats [] = []
      | repeats (name :: rest) =
          (if List.exists (equal name) rest then [name] else []) @
          repeats (List.filter (not o equal name) rest)
  in
    repeats benchNames.names
  end

val _ =
  check
    ("the name table answers each citation once",
     fn () =>
       (if null repeated_entries then ()
        else
          print
            ("\nrepeated:\n" ^ String.concatWith "\n" repeated_entries ^
             "\n");
        null repeated_entries))

(* ---- Phase B: the method dispatcher ------------------------------- *)

val corpus_method_heads =
  let
    val seen = ref ([] : string list)
    fun note name =
      if List.exists (equal name) (!seen) then () else seen := name :: !seen
  in
    app (fn method => app note (benchRecipe.method_heads
                                  (benchRecipe.parse method)))
      corpus_methods;
    List.rev (!seen)
  end

val uncovered_heads =
  List.filter
    (fn head => not (List.exists (equal head) benchTactics.methods))
    corpus_method_heads

val _ =
  check
    ("the dispatcher covers every method head the corpus uses",
     fn () =>
       (if null uncovered_heads then ()
        else
          print
            ("\nuncovered heads: " ^
             String.concatWith ", " uncovered_heads ^ "\n");
        null uncovered_heads))

(* The goal is read for its carrier and nothing else, so a
   non-arithmetic method must answer the same whatever it is shown. *)
val _ =
  check
    ("a non-arithmetic method ignores the goal it is shown",
     fn () =>
       List.all
         (fn name =>
           benchTactics.tactics name ``T`` =
           benchTactics.tactics name ``!n : num. n + 0 = n``)
         ["simp", "auto", "blast", "force", "fastforce", "metis"])

val _ =
  check
    ("algebra picks its instances from the goal's carrier",
     fn () =>
       benchTactics.tactics "algebra" ``!n : num. n * 1 = n`` =
         [benchLib.NumRing] andalso
       benchTactics.tactics "algebra" ``!r : real. r * 1 = r`` =
         [benchLib.RealField])

(* Isabelle's [algebra_tac] is [ring_tac ORELSE ideal_tac].  The
   integer carrier is the one where HOL4 has both procedures, and it
   offers both rather than reading the goal to pick one.  What the
   shape of the goal must not do is decide: an existential conclusion
   used to route the goal straight to the ideal procedure. *)
val _ =
  check
    ("algebra offers the ring normaliser before the ideal procedure",
     fn () =>
       benchTactics.tactics "algebra" ``!i : int. i * 1 = i`` =
         [benchLib.IntRing, benchLib.IntIdeal] andalso
       benchTactics.tactics "algebra"
         ``!a b n : int. ?d. b - a = n * d`` =
         [benchLib.IntRing, benchLib.IntIdeal])

val _ =
  check
    ("an integer algebra method derives an Otherwise chain",
     fn () =>
       case benchDerive.recipe_of ``!i : int. i * 1 = i`` "by algebra" of
           benchLib.Otherwise
             (benchLib.Invoke (benchLib.IntRing, []),
              benchLib.Invoke (benchLib.IntIdeal, [])) => true
         | _ => false)

(* The case the two readings disagree on.  [intLib.INT_RING_TAC]
   declines a divisibility goal, and its conclusion is not existential,
   so the chooser this replaced would have stopped at the normaliser
   and reported no proof.  Not a corpus goal. *)
val divides_goal =
  ``!a b c : int. a int_divides b ==> a int_divides (b * c)``

val _ =
  check
    ("the second alternative closes what the first declines",
     fn () =>
       recipe_solves (benchDerive.recipe_of divides_goal "by algebra")
         divides_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.IntRing, []))
            divides_goal))

val _ =
  check
    ("an uncovered Isabelle method is an error, not a default tactic",
     fn () =>
       raises_with ["no HOL4 tactic", "sledgehammer"]
         (fn () => benchTactics.tactics "sledgehammer" ``T``))

(* ---- Phase B: recipes derived from the source method -------------- *)

(* The end-to-end claim Phase B makes: what the harness runs on a
   translated goal follows from the method string and the goal's
   carrier type alone.  A corpus entry has no recipe field to write,
   so this cannot be satisfied by editing entries; it fails if a goal
   reaches the harness by any route other than [benchDerive.prepare]. *)
fun derivation_mismatch (entry : benchLib.corpus_goal) =
  let
    val derived =
      benchDerive.recipe_of (#goal entry) (#source_method entry)
  in
    if benchLib.recipe_name derived = benchLib.recipe_name (#recipe entry)
    then NONE
    else
      SOME (#id entry ^ ":\n    run     " ^
            benchLib.recipe_name (#recipe entry) ^ "\n    derived " ^
            benchLib.recipe_name derived)
  end
  handle Portable.Interrupt => raise Portable.Interrupt
       | exn => SOME (#id entry ^ ": " ^ Feedback.exn_to_string exn)

val translated_goals = List.filter from_isabelle corpus_goals

val mismatched = List.mapPartial derivation_mismatch translated_goals

val _ =
  check
    ("every translated goal runs the recipe its source method denotes",
     fn () =>
       (if null mismatched then ()
        else
          print
            ("\n  " ^
             String.concatWith "\n  " (List.take (mismatched, 10)) ^
             "\n  (" ^ Int.toString (length mismatched) ^ " in all)\n");
        null mismatched))

(* The one route by which a tactic is named rather than derived is
   confined to goals that have no Isabelle proof to be measured
   against. *)
val _ =
  check
    ("a translated goal cannot be given a named tactic",
     fn () =>
       raises_with ["comes from Isabelle", "unit-native"]
         (fn () =>
           ignore
             (benchDerive.native benchLib.Blast
               {id = "unit-native", goal = boolSyntax.mk_eq (p, p),
                source_method = "by blast", provenance = provenance,
                representative = false})))

(* The goals with no Isabelle method are the HOL4 integer regression
   goals the corpus adds; they are named here so a new one cannot slip
   past the parser by having no method to parse. *)
val _ =
  check
    ("only the HOL4 regression goals lack an Isabelle method",
     fn () =>
       List.all
         (fn entry => #file (#provenance entry) =
                      "src/integer/testing/test_cases.sml")
         (List.filter (not o from_isabelle) corpus_goals))

fun registered_definition theorem =
  List.exists
    (fn location =>
      let
        val name =
          case location of
              DB.Local local_name => local_name
            | DB.Stored stored_name => KernelSig.name_toString stored_name
      in
        String.isSuffix "_def" name orelse String.isSuffix "_DEF" name
      end)
    (DB.revlookup theorem)

fun argument_theorem (benchLib.RewriteAdd {theorem, ...}) = SOME theorem
  | argument_theorem (benchLib.SplitAdd {theorem, ...}) = SOME theorem
  | argument_theorem (benchLib.IntroAdd (_, {theorem, ...})) = SOME theorem
  | argument_theorem (benchLib.ElimAdd (_, {theorem, ...})) = SOME theorem
  | argument_theorem (benchLib.DestAdd (_, {theorem, ...})) = SOME theorem
  | argument_theorem (benchLib.CongruenceAdd {theorem, ...}) = SOME theorem
  | argument_theorem (benchLib.FactAdd {theorem, ...}) = SOME theorem
  | argument_theorem (benchLib.DefinitionAdd {theorem, ...}) =
      if registered_definition theorem then NONE else SOME theorem
  | argument_theorem (benchLib.RewriteDelete _) = NONE

fun argument_name (benchLib.RewriteAdd {name, ...}) = SOME name
  | argument_name (benchLib.SplitAdd {name, ...}) = SOME name
  | argument_name (benchLib.IntroAdd (_, {name, ...})) = SOME name
  | argument_name (benchLib.ElimAdd (_, {name, ...})) = SOME name
  | argument_name (benchLib.DestAdd (_, {name, ...})) = SOME name
  | argument_name (benchLib.CongruenceAdd {name, ...}) = SOME name
  | argument_name (benchLib.FactAdd {name, ...}) = SOME name
  | argument_name (benchLib.DefinitionAdd {name, ...}) = SOME name
  | argument_name (benchLib.RewriteDelete _) = NONE

fun recipe_theorems (benchLib.Invoke (_, arguments)) =
      List.mapPartial argument_theorem arguments
  | recipe_theorems (benchLib.Then (left, right)) =
      recipe_theorems left @ recipe_theorems right
  | recipe_theorems (benchLib.AllGoals (left, right)) =
      recipe_theorems left @ recipe_theorems right
  | recipe_theorems (benchLib.Otherwise (left, right)) =
      recipe_theorems left @ recipe_theorems right
  | recipe_theorems (benchLib.Repeat inner) = recipe_theorems inner

fun recipe_argument_names (benchLib.Invoke (_, arguments)) =
      List.mapPartial argument_name arguments
  | recipe_argument_names (benchLib.Then (left, right)) =
      recipe_argument_names left @ recipe_argument_names right
  | recipe_argument_names (benchLib.AllGoals (left, right)) =
      recipe_argument_names left @ recipe_argument_names right
  | recipe_argument_names (benchLib.Otherwise (left, right)) =
      recipe_argument_names left @ recipe_argument_names right
  | recipe_argument_names (benchLib.Repeat inner) =
      recipe_argument_names inner

fun first_recipe_arguments (benchLib.Invoke (_, arguments)) = arguments
  | first_recipe_arguments (benchLib.Then (left, _)) =
      first_recipe_arguments left
  | first_recipe_arguments (benchLib.AllGoals (left, _)) =
      first_recipe_arguments left
  | first_recipe_arguments (benchLib.Otherwise (left, _)) =
      first_recipe_arguments left
  | first_recipe_arguments (benchLib.Repeat inner) =
      first_recipe_arguments inner

fun last_recipe_arguments (benchLib.Invoke (_, arguments)) = arguments
  | last_recipe_arguments (benchLib.Then (_, right)) =
      last_recipe_arguments right
  | last_recipe_arguments (benchLib.AllGoals (_, right)) =
      last_recipe_arguments right
  | last_recipe_arguments (benchLib.Otherwise (_, right)) =
      last_recipe_arguments right
  | last_recipe_arguments (benchLib.Repeat inner) =
      last_recipe_arguments inner

fun without_argument_names names arguments =
  List.filter
    (fn argument =>
      case argument_name argument of
          SOME name => not (List.exists (equal name) names)
        | NONE => true)
    arguments

val every_corpus_goal =
  benchClassical.goals @ benchSets.goals @ benchListMap.goals @
  benchLinarith.goals @ benchPresburger.goals @ benchAlgebra.goals

(* A [split:] element the splitter cannot analyse is dropped with a
   warning, and the goal is then measured under a method it was not
   given.  Isabelle's [t.split] is the datatype package's rule and HOL4's
   counterpart is derived from TypeBase; the [t_case_eq] theorems are
   equations about a case term -- [list_CASE x v f = v' <=> ...] -- and
   are not split rules at all. *)
fun split_argument (benchLib.SplitAdd {name, theorem}) = SOME (name, theorem)
  | split_argument _ = NONE

fun recipe_splits (benchLib.Invoke (_, arguments)) =
      List.mapPartial split_argument arguments
  | recipe_splits (benchLib.Then (left, right)) =
      recipe_splits left @ recipe_splits right
  | recipe_splits (benchLib.AllGoals (left, right)) =
      recipe_splits left @ recipe_splits right
  | recipe_splits (benchLib.Otherwise (left, right)) =
      recipe_splits left @ recipe_splits right
  | recipe_splits (benchLib.Repeat inner) = recipe_splits inner

val corpus_split_arguments =
  List.concat
    (map (fn ({recipe, ...} : benchLib.corpus_goal) => recipe_splits recipe)
       every_corpus_goal)

val unusable_split_arguments =
  List.filter
    (fn (_, theorem) => not (can splitLib.split_forms theorem))
    corpus_split_arguments

val _ =
  check
    ("every recipe split rule is one the splitter applies",
     fn () =>
       (if null unusable_split_arguments then ()
        else
          print
            ("\nunusable splits: " ^
             String.concatWith ", " (map #1 unusable_split_arguments) ^ "\n");
        not (null corpus_split_arguments) andalso
        null unusable_split_arguments))

val direct_recipe_goals =
  List.filter
    (fn ({goal, recipe, ...} : benchLib.corpus_goal) =>
      List.exists (benchLib.theorem_is_goal goal) (recipe_theorems recipe))
    every_corpus_goal

val _ =
  check
    ("no benchmark recipe supplies its measured theorem",
     fn () =>
       if null direct_recipe_goals then true
       else
         (print
            ("\ncircular recipes: " ^
             String.concatWith ", "
               (map
                 (fn ({id, goal, recipe, ...} : benchLib.corpus_goal) =>
                   id ^ "=[" ^
                   String.concatWith ", "
                     (List.mapPartial argument_name
                       (List.filter
                         (fn argument =>
                           case argument_theorem argument of
                               SOME theorem =>
                                 benchLib.theorem_is_goal goal theorem
                             | NONE => false)
                         (let
                            fun arguments (benchLib.Invoke (_, args)) = args
                              | arguments (benchLib.Then (left, right)) =
                                  arguments left @ arguments right
                              | arguments
                                  (benchLib.AllGoals (left, right)) =
                                  arguments left @ arguments right
                              | arguments
                                  (benchLib.Otherwise (left, right)) =
                                  arguments left @ arguments right
                              | arguments (benchLib.Repeat inner) =
                                  arguments inner
                          in
                            arguments recipe
                          end))) ^ "]")
                 direct_recipe_goals) ^ "\n");
          false))

(* A rule argument only reaches the search if the claset accepts the
   mapped theorem in the role the method gives it.  clasetRules rejects a
   shape it cannot canonicalise -- an equivalence offered as an
   elimination, say -- and the goal then fails before any search, which a
   shortfall record would misread as an engine limitation.  Auditing
   every corpus recipe keeps that a name-table error. *)
fun classical_rule_spec argument =
  let
    fun spec kind strength =
      SOME {kind = kind, safe = strength = benchLib.SafeRule, prio = NONE}
  in
    case argument of
        benchLib.IntroAdd (strength, _) => spec clasetRules.Intro strength
      | benchLib.ElimAdd (strength, _) => spec clasetRules.Elim strength
      | benchLib.DestAdd (strength, _) => spec clasetRules.Dest strength
      | _ => NONE
  end

fun recipe_arguments (benchLib.Invoke (_, arguments)) = arguments
  | recipe_arguments (benchLib.Then (left, right)) =
      recipe_arguments left @ recipe_arguments right
  | recipe_arguments (benchLib.AllGoals (left, right)) =
      recipe_arguments left @ recipe_arguments right
  | recipe_arguments (benchLib.Otherwise (left, right)) =
      recipe_arguments left @ recipe_arguments right
  | recipe_arguments (benchLib.Repeat inner) = recipe_arguments inner

fun uninstallable_rule_arguments recipe =
  List.mapPartial
    (fn argument =>
      case (classical_rule_spec argument, argument_name argument,
            argument_theorem argument) of
          (SOME spec, SOME name, SOME theorem) =>
            if can (clasetLib.add_rule spec (name, theorem))
                 clasetLib.empty_cs
            then NONE
            else SOME name
        | _ => NONE)
    (recipe_arguments recipe)

val goals_with_uninstallable_rules =
  List.mapPartial
    (fn ({id, recipe, ...} : benchLib.corpus_goal) =>
      case uninstallable_rule_arguments recipe of
          [] => NONE
        | names => SOME (id ^ "=[" ^ String.concatWith ", " names ^ "]"))
    every_corpus_goal

val _ =
  check
    ("every corpus rule argument is installable in its declared role",
     fn () =>
       if null goals_with_uninstallable_rules then true
       else
         (print
            ("\nrules the claset refuses: " ^
             String.concatWith ", " goals_with_uninstallable_rules ^ "\n");
          false))

fun goal_named id goals =
  case List.filter
         (fn ({id = candidate, ...} : benchLib.corpus_goal) =>
           candidate = id) goals of
      [goal] => goal
    | _ => raise mk_HOL_ERR "selftest" "goal_named" id

(* The engine tests below name their own recipe.  A corpus entry's
   recipe is derived from its Isabelle method string, so reading one
   here would make an engine test change meaning whenever the
   derivation does; what is under test is the tactic, not the
   derivation. *)
val linarith_recipe = benchLib.Invoke (benchLib.Linarith, [])
val blast_recipe = benchLib.Invoke (benchLib.Blast, [])
val auto_recipe = benchLib.Invoke (benchLib.Auto, [])

val absolute_recurrence_goal =
  recipe_goal "unit-absolute-recurrence" linarith_recipe
    (#goal (goal_named "presburger_L102" benchPresburger.goals))

val _ =
  check
    ("absolute recurrence uses the deterministic pruned split tree",
     fn () =>
       let
         val outcome =
           benchLib.run_goal (Time.fromSeconds 5)
             linarith_recipe absolute_recurrence_goal
         val {nodes, refutations, disjunction_splits,
              operator_splits, augmentations} =
           linarithLib.last_search_stats ()
       in
         benchLib.outcome_solved outcome andalso
         nodes = 363 andalso refutations = 243 andalso
         disjunction_splits = 121 andalso operator_splits = 120 andalso
         operator_splits < 511 andalso augmentations = 0
       end)

val satisfiable_absolute_value_goal : benchLib.corpus_goal =
  {id = "unit-satisfiable-absolute-value",
   goal = ``ABS (x : int) = x``, source_method = "arith soundness",
   recipe = benchLib.Invoke (benchLib.Linarith, []), excl = [],
   provenance = provenance, representative = true}

val _ =
  check
    ("interleaved sign splitting rejects a satisfiable sign system",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
             (#recipe satisfiable_absolute_value_goal)
             satisfiable_absolute_value_goal)))

(* The pair rule is support for the translation's spelling of a set of
   pairs, and a goal with no pair in it neither needs it nor can afford
   it: it goes in as an assumption, and a universal assumption is
   instantiated afresh on every branch the search opens.  This goal
   closes in a third of a second when the rule is withheld and does not
   return inside the budget when it is not.  It is not a corpus entry. *)
val _ =
  check
    ("the pair rule is withheld from a goal with no pair in it",
     fn () =>
       recipe_solves (benchLib.Invoke (benchLib.Blast, []))
         ``(!s t. bench_apart s t <=> !x. x IN s ==> x NOTIN t) ==>
           bench_apart (A : 'a -> bool) B ==> bench_apart B A``)

val _ =
  check
    ("mapped BLAST distributes BIGINTER over pointwise intersection",
     fn () =>
       recipe_solves (benchLib.Invoke (benchLib.Blast, []))
         ``BIGINTER
             (IMAGE
               (\x : 'i.
                  (biginter_left : 'i -> 'a set) x INTER
                  (biginter_right : 'i -> 'a set) x)
               (biginter_family : 'i set)) =
           BIGINTER
             (IMAGE (biginter_left : 'i -> 'a set)
                (biginter_family : 'i set)) INTER
           BIGINTER
             (IMAGE (biginter_right : 'i -> 'a set)
                (biginter_family : 'i set))``)

val _ =
  check
    ("predicate abstraction handles a non-numeric datatype",
     fn () =>
       recipe_solves auto_recipe
         ``((!aset : bool set.
              T IN aset /\
              (!value. value IN aset ==> ~value IN aset) ==>
              F IN aset) /\
            (property : bool -> bool) T /\
            (!value. property value ==> property (~value))) ==>
           property F``)

val _ =
  check
    ("predicate abstraction instantiates a closure set comprehension",
     fn () =>
       recipe_solves auto_recipe
         ``((!aset : bool option set.
              NONE IN aset /\
              (!value. value IN aset ==> SOME T IN aset) ==>
              SOME T IN aset) /\
            (property : bool option -> bool) NONE /\
            (!value. property value ==> property (SOME T))) ==>
           property (SOME T)``)

(* What survives of the lfp-witness coverage is the soundness half.
   [lfp_witness_tac] reduces [?x. x = body x] to a monotonicity
   subgoal, and BLAST does not discharge that subgoal from general
   inputs: the positive cases here used to be closed by the fixed-point
   lemmas the corpus supplied, which is what A2 rejects.  The gap is
   recorded in the Phase C ledger against [set_theory_L79], and the
   positive cases belong with the fix. *)
val _ =
  check
    ("lfp witness rejects an antitone complement transformer",
     fn () =>
       not
         (recipe_solves blast_recipe
            ``?fixed : bool set. fixed = COMPL fixed``))

val _ =
  check
    ("predicate abstraction rejects an unsupported open pattern",
     fn () =>
       not
         (recipe_solves auto_recipe
            ``(!aset : bool set. T IN aset ==> T IN aset) ==>
              (property : bool -> bool) T``))

val _ =
  check
    ("predicate abstraction rejects a scope-escaping candidate",
     fn () =>
       let
         val recipe = auto_recipe
         val target =
           ``(!aset : bool set.
                !hidden. hidden IN aset ==> hidden IN aset) ==>
             (property : bool -> bool) T``
       in
         case benchLib.run_goal (Time.fromSeconds 5) recipe
                (recipe_goal "unit-scope-escape" recipe target) of
             benchLib.FAILED _ => true
           | _ => false
       end)

val _ =
  check
    ("predicate abstraction fairly tries competing set assumptions",
     fn () =>
       recipe_solves auto_recipe
         ``((!aset : bool set. T IN aset ==> T IN aset) /\
            (!aset : bool set. T IN aset ==> F IN aset) /\
            (property : bool -> bool) T) ==>
           property F``)

val sorted_wrt_distinction_goal =
  ``sorting$SORTED
      (\left right : num. right = SUC left) [0; 1; 2] /\
    ~parityTranslation$source_sorted_wrt
      (\left right : num. right = SUC left) [0; 1; 2]``

val _ =
  check
    ("source sorted_wrt is stronger than adjacent SORTED without transitivity",
     fn () =>
       aconv
         (Thm.concl
           parityTranslationTheory.source_sorted_wrt_not_adjacent)
         sorted_wrt_distinction_goal)

val fold_representation_distinction_goal =
  ``parityTranslation$source_fold CONS [0 : num; 1] [] =
      REVERSE [0; 1] /\
    REVERSE [0; 1] <> FOLDR CONS [] [0; 1]``

val _ =
  check
    ("source fold is not HOL4 FOLDR",
     fn () =>
       recipe_solves
         (benchLib.Invoke
            (benchLib.Simp,
             [benchLib.DefinitionAdd
                {name = "parityTranslation$source_fold_def",
                 theorem = parityTranslationTheory.source_fold_def}]))
         fold_representation_distinction_goal)

(* src/HOL/List.thy:226-231 @ f7e02b7e.  The source defines extract by
   dropWhile and takeWhile and proves every result about it by rewriting
   with those two, whose equations are ambient.  The goal below is not a
   corpus entry -- it walks two constructors and reads off the prefix --
   and the definition reaches it only when it is stated over the same
   decomposition; a paraphrase over some other one states the same
   function and leaves the walk with nothing to reduce it. *)
val extract_decomposition_goal =
  ``!predicate first second rest.
      ~predicate first ==> predicate second ==>
      parityTranslation$source_extract predicate (first::second::rest) =
        SOME ([first], second, rest)``

val _ =
  check
    ("the extract definition walks a list by the ambient equations",
     fn () =>
       recipe_solves
         (benchLib.Invoke
            (benchLib.Auto,
             [benchLib.DefinitionAdd
                {name = "parityTranslation$source_extract_def",
                 theorem = parityTranslationTheory.source_extract_def}]))
         extract_decomposition_goal)

val _ =
  check
    ("rotation modulo normalization applies to an unrelated periodic function",
     fn () =>
       let
         val target =
           ``FUNPOW (v_iteration0 : 'a -> 'a) 3 v_value0 = v_value0 ==>
             FUNPOW v_iteration0 4 v_value0 =
             FUNPOW v_iteration0 (4 MOD 3) v_value0``
         val (premise, _) = boolSyntax.dest_imp target
         val instantiated =
           Q.SPECL [`v_iteration0 : 'a -> 'a`, `3`, `v_value0`, `4`]
             parityTranslationTheory.source_funpow_mod_periodic
         val theorem =
           DISCH premise (MP instantiated (ASSUME premise))
       in
         Term.aconv (Thm.concl theorem) target
       end)

val bool_negation_period =
  Tactical.prove
    (``FUNPOW (\value : bool. ~value) 2 T = T``,
     bossLib.simp[arithmeticTheory.FUNPOW_2])

val funpow_mod_zero_normalize =
  parityTranslationTheory.source_funpow_mod_zero_imp_normalize

val _ =
  check
    ("period-zero implication normalization is operation-generic",
     fn () =>
       recipe_solves
         (benchLib.Invoke
           (benchLib.Simp,
            [benchLib.RewriteAdd
               {name = "unit$source_funpow_mod_zero_imp_normalize",
                theorem = funpow_mod_zero_normalize},
             benchLib.RewriteAdd
               {name = "unit$bool_negation_period",
                theorem = bool_negation_period}]))
         ``!count.
             count MOD 2 = 0 ==>
             FUNPOW (\value : bool. ~value) count T = T``)

(* The generalization tests that used to sit here ran a corpus
   entry's recipe against a statement the corpus does not contain, so
   a tactic that recognised the corpus statement would fail them.
   Each took its recipe from a corpus entry that is now a registered
   shortfall -- the recipes they supplied were built from lemmas the
   Isabelle method never names, and a test whose base goal does not
   solve says nothing about recognition, so the test goes with the
   entry.  The entries were [list_L5409_nths_drop],
   [list_L6384_sorted_insort_insert_key], [list_L6453_sorted_transpose],
   [list_L6847_sorted_list_of_set_nonempty],
   [list_L6873_nth_sorted_list_of_set_greaterThanAtMost],
   [list_L3381_anon_L3381], [list_L5527_Nil_in_shufflesI],
   [list_L5470_subset_subseqs], [list_L8673_these_set_code],
   [list_L7922_wf_listrel1_iff], [list_L7771_wf_measures],
   [list_L7508_lexord_trans] and [list_L7954_listrel_iff_nth].
   Closing any of those shortfalls means restoring its generalization
   test in the same commit. *)

fun retarget_goal id goal (base : benchLib.corpus_goal) =
  {id = id, goal = goal, source_method = #source_method base,
   recipe = #recipe base, excl = #excl base,
   provenance = #provenance base, representative = true}

val promoted_recovered_schema_goals =
  [retarget_goal "schema-abort-empty-card"
     ``parityTranslation$source_abort_empty_set
         (\domain : num set. CARD domain) = 0``
     (goal_named "list_L3349_anon_L3349" benchListMap.goals),
   retarget_goal "schema-lists-membership-mono"
     ``[1; 1] IN parityTranslation$source_lists ({1} : num set) ==>
       [1; 1] IN parityTranslation$source_lists ({1; 2} : num set)``
     (goal_named "list_L6972_mono_lists" benchListMap.goals),
   retarget_goal "schema-wf-finite-single-edge"
     ``relation$WF
         (set_relation$reln_to_rel
           (LIST_TO_SET [((1 : num), 2)])) <=>
       set_relation$acyclic (LIST_TO_SET [((1 : num), 2)])``
     (goal_named "list_L8709_wf_set" benchListMap.goals)]

val _ =
  check
    ("recovered dependency schemas generalize beyond corpus statements",
     fn () =>
       List.all
         (fn goal =>
           case benchLib.run_goal (Time.fromSeconds 5)
                  (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         promoted_recovered_schema_goals)

val literal_constructor_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "parityTranslation$source_Literal_def",
         theorem = parityTranslationTheory.source_Literal_def},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_abs_11",
         theorem = parityTranslationTheory.source_literal_abs_11},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_Literal_valid",
         theorem = parityTranslationTheory.source_Literal_valid},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_Char_ascii_eq_iff",
         theorem = parityTranslationTheory.source_Char_ascii_eq_iff},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_explode_11",
         theorem = parityTranslationTheory.source_literal_explode_11},
      benchLib.RewriteAdd
        {name = "bool$CONJ_ASSOC",
         theorem = boolTheory.CONJ_ASSOC}])

val literal_empty_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "parityTranslation$source_literal_empty_def",
         theorem = parityTranslationTheory.source_literal_empty_def},
      benchLib.DefinitionAdd
        {name = "parityTranslation$source_Literal_def",
         theorem = parityTranslationTheory.source_Literal_def},
      benchLib.DefinitionAdd
        {name = "parityTranslation$source_literal_valid_def",
         theorem = parityTranslationTheory.source_literal_valid_def},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_eq_iff_explode",
         theorem =
           parityTranslationTheory.source_literal_eq_iff_explode},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_explode_abs",
         theorem = parityTranslationTheory.source_literal_explode_abs},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_Literal_valid",
         theorem = parityTranslationTheory.source_Literal_valid}])

val _ =
  check
    ("literal constructors are faithful to the subtype representation",
     fn () =>
       recipe_solves literal_constructor_recipe
         (Thm.concl parityTranslationTheory.source_Literal_eq_iff) andalso
       recipe_solves literal_empty_recipe
         (Thm.concl
            parityTranslationTheory.source_literal_empty_neq_Literal) andalso
       recipe_solves literal_empty_recipe
         (Thm.concl parityTranslationTheory.source_Literal_neq_empty))

val literal_implode_explode_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "parityTranslation$source_literal_implode_def",
         theorem = parityTranslationTheory.source_literal_implode_def},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_ascii_map_id",
         theorem = parityTranslationTheory.source_ascii_map_id},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_explode_valid",
         theorem = parityTranslationTheory.source_literal_explode_valid},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_abs_explode",
         theorem = parityTranslationTheory.source_literal_abs_explode}])

val literal_explode_implode_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "parityTranslation$source_literal_implode_def",
         theorem = parityTranslationTheory.source_literal_implode_def},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_explode_abs",
         theorem = parityTranslationTheory.source_literal_explode_abs},
      benchLib.RewriteAdd
        {name = "parityTranslation$source_literal_implode_valid",
         theorem = parityTranslationTheory.source_literal_implode_valid}])

val _ =
  check
    ("literal implode and explode round-trip in both directions",
     fn () =>
       recipe_solves literal_implode_explode_recipe
         (Thm.concl
            parityTranslationTheory.source_literal_implode_explode) andalso
       recipe_solves literal_explode_implode_recipe
         (Thm.concl
            parityTranslationTheory.source_literal_explode_implode))

val ball_congruence_goal =
  ``parityTranslation$source_ball (carrier_domain : 'a set)
      (\x. x IN carrier_domain /\ predicate x) <=>
    parityTranslation$source_ball carrier_domain predicate``
val bex_congruence_goal =
  ``parityTranslation$source_bex (carrier_domain : 'a set)
      (\x. x IN carrier_domain /\ predicate x) <=>
    parityTranslation$source_bex carrier_domain predicate``
val image_congruence_goal =
  ``parityTranslation$source_image
      (\x. if x IN (carrier_domain : 'a set)
           then mapper x else other_mapper x)
      carrier_domain =
    parityTranslation$source_image (mapper : 'a -> 'b) carrier_domain``

fun congruence_recipe name theorem =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.CongruenceAdd {name = name, theorem = theorem}])

val _ =
  check
    ("local ball congruence simplifies under bounded membership",
     fn () =>
       recipe_solves
         (congruence_recipe "parityTranslation$source_ball_cong_simp"
            parityTranslationTheory.source_ball_cong_simp)
         ball_congruence_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            ball_congruence_goal))

val _ =
  check
    ("local bex congruence simplifies under bounded membership",
     fn () =>
       recipe_solves
         (congruence_recipe "parityTranslation$source_bex_cong_simp"
            parityTranslationTheory.source_bex_cong_simp)
         bex_congruence_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            bex_congruence_goal))

val _ =
  check
    ("local image congruence simplifies under domain membership",
     fn () =>
       recipe_solves
         (congruence_recipe "parityTranslation$source_image_cong_simp"
            parityTranslationTheory.source_image_cong_simp)
         image_congruence_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            image_congruence_goal))

val integer_ideal_goal = goal_named "groebner_L113" benchAlgebra.goals

val _ =
  check
    ("integer ring normalization alone leaves the witness goal",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 30)
              (benchLib.Invoke (benchLib.IntRing, []))
              integer_ideal_goal)))

val integer_algebra_goals =
  map Thm.concl
    [parityAlgebraTranslationTheory.source_idom_simultaneous_squares_int,
     parityAlgebraTranslationTheory.source_idom_four_square_int,
     parityAlgebraTranslationTheory.source_idom_eight_square_int]

val _ =
  check
    ("integral-domain identities specialize to HOL4 integers",
     fn () =>
       List.all
         (fn goal =>
           let val (variables, _) = boolSyntax.strip_forall goal
           in
             not (null variables) andalso
             List.all
               (fn variable => type_of variable = intSyntax.int_ty)
               variables
           end)
         integer_algebra_goals)

fun remove_first predicate items =
  case items of
      [] => []
    | item :: rest =>
        if predicate item then rest
        else item :: remove_first predicate rest

fun weaken_antecedent predicate goal =
  let
    val (variables, body) = boolSyntax.strip_forall goal
    val (antecedent, conclusion) = boolSyntax.dest_imp body
    val clauses = boolSyntax.strip_conj antecedent
    val weakened = boolSyntax.list_mk_conj
      (remove_first predicate clauses)
  in
    boolSyntax.list_mk_forall
      (variables, boolSyntax.mk_imp (weakened, conclusion))
  end

fun headed_by wanted term =
  let val (head, _) = strip_comb term
  in same_const head wanted end
  handle HOL_ERR _ => false

fun is_membership term =
  pred_setSyntax.is_in term
  handle HOL_ERR _ => false

val four_square_goal = goal_named "groebner_L72" benchAlgebra.goals
val without_integral_domain =
  weaken_antecedent
    (headed_by ``ring$IntegralDomain``) (#goal four_square_goal)
val without_carrier_membership =
  weaken_antecedent is_membership (#goal four_square_goal)

val _ =
  check
    ("explicit ring normalization rejects a missing domain assumption",
     fn () =>
       not (recipe_solves (#recipe four_square_goal)
              without_integral_domain))

val _ =
  check
    ("explicit ring normalization rejects missing carrier membership",
     fn () =>
       not (recipe_solves (#recipe four_square_goal)
              without_carrier_membership))

val corrupted_ring_certificate_goal =
  ``!x : 'a.
      ringLib$ring_mul (r : 'a ringLib$Ring) x x =
        ringLib$ring_0 r ==>
      ringLib$ring_mul r x x = ringLib$ring_0 r``

val _ =
  check
    ("ring replay rejects a deliberately corrupted cofactor",
     fn () =>
       ((ringLib.RING_REPLAY_COFACTORS corrupted_ring_certificate_goal
           [``ringLib$ring_0 (r : 'a ringLib$Ring)``];
         false)
        handle HOL_ERR _ => true))

fun family_ok expected run =
  let
    val result : benchLib.family_result =
      run (benchLib.selftest_level ())
  in
    length (#gated result) =
      (case OS.Process.getEnv "HOLBENCHGOAL" of
           NONE => expected
         | SOME ids => length (String.tokens (equal #",") ids))
  end

fun family_selected name =
  case OS.Process.getEnv "HOLBENCHFAMILY" of
      NONE => true
    | SOME selected => selected = name

fun count_cause cause shortfalls =
  length
    (List.filter
      (fn ({cause = item, ...} : benchLib.shortfall) => item = cause)
      shortfalls)

val _ =
  check
    ("exhaustive pinned-source accounting is exact",
     fn () =>
       let
         val source_outcomes =
           length benchClassical.goals + length benchSets.goals +
           length benchListMap.goals + length benchLinarith.goals +
           (length benchPresburger.goals - 11) +
           length benchAlgebra.goals +
           count_cause benchLib.TranslationGap benchSets.shortfalls +
           count_cause benchLib.TranslationGap benchListMap.shortfalls +
           count_cause benchLib.TranslationGap benchAlgebra.shortfalls
       in
         source_outcomes = 1061 andalso source_outcomes + 11 = 1072
       end)

val all_shortfalls =
  benchClassical.shortfalls @ benchSets.shortfalls @
  benchListMap.shortfalls @ benchLinarith.shortfalls @
  benchPresburger.shortfalls @ benchAlgebra.shortfalls

(* The registers are not empty and are not meant to be: they carry the
   measured non-solutions.  What has to hold is that every record says
   something.  [UnderIteration] is a working marker, not a diagnosis,
   so no committed record may carry it; and a record with no date or no
   note is not a diagnosis either.

   A [TranslationGap] is the one classification that takes a source
   result out of the measurement, so the set is pinned by identifier
   rather than counted: declaring a new one is a failing test until it
   is signed here.  That such a record carries no executable goal is
   [benchLib.validate_corpus]'s check, not this one. *)
val translation_gaps =
  ["list_L8259_anon_L8259", "list_L8273_anon_L8273"]

fun translation_gap_ids shortfalls =
  map (#id : benchLib.shortfall -> string)
    (List.filter
      (fn ({cause, ...} : benchLib.shortfall) =>
        cause = benchLib.TranslationGap)
      shortfalls)

fun same_identifiers left right =
  length left = length right andalso
  List.all (fn id => List.exists (fn other => other = id) right) left

fun dated_and_explained (shortfall : benchLib.shortfall) =
  size (#date shortfall) = size "2026-08-20" andalso
  String.isPrefix "20" (#date shortfall) andalso
  size (#note shortfall) >= 20

val _ =
  check
    ("every shortfall record names a cause, a date and a reason",
     fn () =>
       count_cause benchLib.UnderIteration all_shortfalls = 0 andalso
       same_identifiers (translation_gap_ids all_shortfalls)
         translation_gaps andalso
       List.all dated_and_explained all_shortfalls)

val _ =
  check
    ("classical mined-corpus representative slice is exact",
     fn () =>
       not (family_selected "classical") orelse family_ok
         (if benchLib.selftest_level () >= 2 then 25 else 4)
         benchClassical.run)

val _ =
  check
    ("set mined-corpus representative slice is exact",
     fn () =>
       not (family_selected "sets") orelse
       family_ok
         (if benchLib.selftest_level () >= 2 then 353 else 4)
         benchSets.run)

val _ =
  check
    ("list/map mined-corpus representative slice is exact",
     fn () =>
       not (family_selected "listmap") orelse
       family_ok
         (if benchLib.selftest_level () >= 2 then 602 else 5)
         benchListMap.run)

val _ =
  check
    ("linear-arithmetic representative slice is exact",
     fn () =>
       not (family_selected "linarith") orelse family_ok
         (if benchLib.selftest_level () >= 2 then 46 else 4)
         benchLinarith.run)

val _ =
  check
    ("Presburger representative slice is exact",
     fn () =>
       not (family_selected "presburger") orelse family_ok
         (if benchLib.selftest_level () >= 2 then 34 else 8)
         benchPresburger.run)

val _ =
  check
    ("algebra representative slice and accepted gaps are exact",
     fn () =>
       not (family_selected "algebra") orelse family_ok
         (if benchLib.selftest_level () >= 2 then 10 else 3)
         benchAlgebra.run)

(* A6.  Goal statements are owner-signed: a changed hash means a goal
   statement moved, which needs an explicit decision rather than an
   updated pin. *)
val goal_term_pins =
  [("Classical", "49F818B8"), ("Sets", "7641FC9E"),
   ("List/map", "5BCE22FA"), ("Linarith", "E9DDA580"),
   ("Presburger", "5A7FD8D5"), ("Algebra", "4C63E77A")]

val _ =
  check
    ("A6 goal-term hashes match their pins",
     fn () =>
       length goal_term_pins = length parityLib.families andalso
       List.all
         (fn ({name, goals, ...} : parityLib.family) =>
           case List.find (fn (family, _) => family = name)
                  goal_term_pins of
               NONE => false
             | SOME (_, pin) => benchGuards.family_hash goals = pin)
         parityLib.families)

fun read_all path =
  let
    val stream = TextIO.openIn path
    val text = TextIO.inputAll stream
    val _ = TextIO.closeIn stream
  in
    text
  end

val _ =
  check
    ("level-2 generated parity report matches the committed file \
      \outside its timings",
     fn () =>
       Option.isSome (OS.Process.getEnv "HOLBENCHFAMILY") orelse
       OS.Process.getEnv "HOLBENCHNOBATTERY" = SOME "1" orelse
       benchLib.selftest_level () < 2 orelse
       parityLib.without_costs (read_all "../PARITY.md") =
       parityLib.without_costs (parityLib.render ()))
