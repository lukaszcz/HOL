open HolKernel testutils

fun check (name, predicate) =
  (tprint name;
   if predicate () then OK () else die "failed")

fun raises thunk =
  ((thunk (); false)
   handle Portable.Interrupt => raise Portable.Interrupt
        | HOL_ERR _ => true)

val provenance =
  {file = "src/HOL/HOL.thy", line = 1, commit = "f7e02b7e"}

val p = mk_var ("bench_unit_p", bool)
val q = mk_var ("bench_unit_q", bool)

val solved_goal : benchLib.corpus_goal =
  {id = "unit-solved", goal = boolSyntax.T,
   source_method = "simp", recipe = benchLib.Invoke (benchLib.Simp, []),
   excl = [],
   provenance = provenance, representative = true}

val failed_goal : benchLib.corpus_goal =
  {id = "unit-failed", goal = p,
   source_method = "simp", recipe = benchLib.Invoke (benchLib.Simp, []),
   excl = [],
   provenance = provenance, representative = true}

val duplicate_solved_goal : benchLib.corpus_goal =
  {id = "unit-solved-duplicate", goal = boolSyntax.T,
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
             {family = "unit", goals = [solved_goal, failed_goal],
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
             {family = "unit-battery", goals = [solved_goal],
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
  let val entry = recipe_goal "unit-recipe" recipe goal
  in
    benchLib.outcome_solved
      (benchLib.run_goal (Time.fromSeconds 5) recipe entry)
  end

val conjunction_commute = boolTheory.CONJ_COMM
val disjunction_commute = boolTheory.DISJ_COMM

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

val _ =
  check
    ("recipe-local rewrite closes a goal that bare simp leaves",
     fn () =>
       recipe_solves rewrite_recipe (Thm.concl conjunction_commute) andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            (Thm.concl conjunction_commute)))

val _ =
  check
    ("recipe-local definition closes a goal that bare simp leaves",
     fn () =>
       recipe_solves definition_recipe (Thm.concl disjunction_commute) andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            (Thm.concl disjunction_commute)))

val length_reverse =
  {name = "list$LENGTH_REVERSE", theorem = listTheory.LENGTH_REVERSE}
val length_reverse_goal = Thm.concl listTheory.LENGTH_REVERSE
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
          "cong(list$LENGTH_REVERSE)"])

fun goal_named id goals =
  case List.filter
         (fn ({id = candidate, ...} : benchLib.corpus_goal) =>
           candidate = id) goals of
      [goal] => goal
    | _ => raise mk_HOL_ERR "selftest" "goal_named" id

val absolute_recurrence_goal =
  goal_named "presburger_L102" benchPresburger.goals

val _ =
  check
    ("absolute recurrence uses the deterministic pruned split tree",
     fn () =>
       let
         val outcome =
           benchLib.run_goal (Time.fromSeconds 5)
             (#recipe absolute_recurrence_goal) absolute_recurrence_goal
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

val direct_blast_classical_goals =
  map
    (fn id => goal_named id benchClassical.goals)
    ["classical_L375", "classical_L803"]

val _ =
  check
    ("argument-free BLAST skips divergent simplifier preprocessing",
     fn () =>
       List.all
         (fn goal =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         direct_blast_classical_goals)

val unit_order_goal =
  goal_named "product_type_L140_less_eq_unit" benchProductCorpus.goals

val _ =
  check
    ("translated unit order uses its local source-definition recipe",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe unit_order_goal) unit_order_goal) andalso
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
              (benchLib.Invoke (benchLib.Simp, [])) unit_order_goal)))

val strict_unit_order_goal =
  ``!u v : unit. ~parityTranslation$source_unit_lt u v``
val strict_unit_order_recipe =
  benchLib.Invoke
    (benchLib.Simp,
     [benchLib.DefinitionAdd
        {name = "parityTranslation$source_unit_lt_def",
         theorem = parityTranslationTheory.source_unit_lt_def}])

val _ =
  check
    ("translated strict unit order has the same local boundary",
     fn () =>
       recipe_solves strict_unit_order_recipe strict_unit_order_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            strict_unit_order_goal))

val translated_set_goals =
  map
    (fn id => goal_named id benchSets.goals)
    ["set_L461_ball_cong_simp", "set_L471_bex_cong_simp",
     "set_L972_image_cong_simp"]

val translated_ordered_image_goal =
  goal_named "set_L968_image_cong" benchSets.goals

val _ =
  check
    ("translated image definition executes with source witness order",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_ordered_image_goal)
            translated_ordered_image_goal))

val _ =
  check
    ("source image-definition context is essential to simp",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
              (benchLib.Invoke (benchLib.Simp, []))
              translated_ordered_image_goal)))

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

val translated_bigunion_image_goal =
  goal_named "set_theory_L36" benchSets.goals

val _ =
  check
    ("mapped BLAST distributes BIGUNION over pointwise union",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_bigunion_image_goal)
            translated_bigunion_image_goal))

val _ =
  check
    ("indexed-union membership is essential to mapped BLAST",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              (benchLib.Invoke (benchLib.Blast, []))
              translated_bigunion_image_goal)))

fun without_rewrite target arguments =
  List.filter
    (fn benchLib.RewriteAdd {name, ...} => name <> target
      | _ => true)
    arguments

val translated_fixed_point_goal =
  goal_named "set_theory_L79" benchSets.goals

val fixed_point_without_bridge =
  case #recipe translated_fixed_point_goal of
      benchLib.AllGoals
        (benchLib.Invoke (benchLib.Simp, arguments), _) =>
        benchLib.Invoke
          (benchLib.Simp,
           without_rewrite
             "paritySetTranslation$source_compl_image_fixedpoint_iff"
             arguments)
    | _ => raise Fail "unexpected fixed-point recipe"

val _ =
  check
    ("translated complement-image fixed point executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_fixed_point_goal)
            translated_fixed_point_goal))

val _ =
  check
    ("complement-image fixed point needs its source bridge",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 1)
              fixed_point_without_bridge
              translated_fixed_point_goal)))

val translated_num_set_induction_goal =
  goal_named "set_theory_L199" benchSets.goals

val num_set_induction_without_bridge =
  case #recipe translated_num_set_induction_goal of
      benchLib.AllGoals
        (benchLib.Invoke (benchLib.Simp, arguments), _) =>
        benchLib.Invoke
          (benchLib.Simp,
           without_rewrite
             "parityTranslation$source_num_set_induction_iff"
             arguments)
    | _ => raise Fail "unexpected number-set induction recipe"

val _ =
  check
    ("translated number-set induction executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_num_set_induction_goal)
            translated_num_set_induction_goal))

val _ =
  check
    ("number-set induction needs its source bridge",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 1)
              num_set_induction_without_bridge
              translated_num_set_induction_goal)))

val promoted_set_bridge_goals =
  [(goal_named "set_L869_doubleton_eq_iff" benchSets.goals,
    "parityTranslation$source_doubleton_eq_iff"),
   (goal_named "set_L928_subset_image_iff" benchSets.goals,
    "parityTranslation$source_subset_image_iff"),
   (goal_named "set_L1125_image_Pow_surj" benchSets.goals,
    "parityTranslation$source_image_pow_surj_iff"),
   (goal_named "set_L1604_Pow_singleton_iff" benchSets.goals,
    "parityTranslation$source_pow_singleton_iff"),
   (goal_named "set_L1607_Pow_insert" benchSets.goals,
    "parityTranslation$source_pow_insert_image_case_iff"),
   (goal_named "set_L1610_Pow_Compl" benchSets.goals,
    "parityTranslation$source_pow_compl_iff"),
   (goal_named "set_L1967_pairwise_image" benchSets.goals,
    "parityTranslation$source_pairwise_image")]

val _ =
  check
    ("promoted translated set goals execute exactly",
     fn () =>
       List.all
         (fn (goal, _) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         promoted_set_bridge_goals)

val _ =
  check
    ("promoted translated set goals need their source bridges",
     fn () =>
       List.all
         (fn (goal, bridge) =>
           case #recipe goal of
               benchLib.AllGoals
                 (benchLib.Invoke (benchLib.Simp, arguments), _) =>
                 not
                   (benchLib.outcome_solved
                     (benchLib.run_goal (Time.fromSeconds 1)
                        (benchLib.Invoke
                           (benchLib.Simp,
                            without_rewrite bridge arguments))
                        goal))
             | _ => raise Fail "unexpected promoted set recipe")
         promoted_set_bridge_goals)

val translated_psubset_trans_goal =
  goal_named "set_L1101_psubset_trans" benchSets.goals

val psubset_trans_without_safe =
  case #recipe translated_psubset_trans_goal of
      benchLib.AllGoals
        (simplify,
         benchLib.AllGoals
           (benchLib.Invoke (benchLib.Safe, _), automatic)) =>
        benchLib.AllGoals (simplify, automatic)
    | _ => raise Fail "unexpected proper-subset transitivity recipe"

val _ =
  check
    ("translated proper-subset transitivity executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_psubset_trans_goal)
            translated_psubset_trans_goal))

val _ =
  check
    ("proper-subset transitivity needs safe saturation before auto",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 1)
              psubset_trans_without_safe
              translated_psubset_trans_goal)))

val translated_predicate_witness_goal =
  goal_named "set_theory_L172" benchSets.goals

val _ =
  check
    ("translated predicate-set witness executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_predicate_witness_goal)
            translated_predicate_witness_goal))

val _ =
  check
    ("predicate-set witness needs its source construction bridge",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              (benchLib.Invoke
                 (benchLib.Force,
                  [benchLib.RewriteAdd
                     {name =
                        "parityTranslation$source_mem_bigunion_image",
                      theorem =
                        parityTranslationTheory.source_mem_bigunion_image}]))
              translated_predicate_witness_goal)))

val translated_nonempty_predicate_goal =
  goal_named "set_theory_L164" benchSets.goals

val _ =
  check
    ("translated nonempty predicate set executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_nonempty_predicate_goal)
            translated_nonempty_predicate_goal))

val _ =
  check
    ("nonempty predicate set needs its source normalization",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              (benchLib.Invoke
                 (benchLib.Simp,
                  [benchLib.RewriteAdd
                     {name =
                        "parityTranslation$source_mem_bigunion_image",
                      theorem =
                        parityTranslationTheory.source_mem_bigunion_image},
                   benchLib.FactAdd
                     {name =
                        "parityTranslation$source_predicate_set_witness",
                      theorem =
                        parityTranslationTheory.source_predicate_set_witness}]))
              translated_nonempty_predicate_goal)))

val translated_set_separation_goal =
  goal_named "set_theory_L184" benchSets.goals

val _ =
  check
    ("translated set separation executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_set_separation_goal)
            translated_set_separation_goal))

val _ =
  check
    ("set separation needs its source existential normalization",
     fn () =>
       not
         (recipe_solves
            (benchLib.Invoke
               (benchLib.Simp,
                [benchLib.RewriteAdd
                   {name =
                      "parityTranslation$source_nonnegative_neq_negative",
                    theorem =
                      parityTranslationTheory.source_nonnegative_neq_negative}]))
            (#goal translated_set_separation_goal)))

val _ =
  check
    ("set separation needs nonnegative order normalization",
     fn () =>
       not
         (recipe_solves
            (benchLib.Invoke
               (benchLib.Simp,
                [benchLib.RewriteAdd
                   {name = "parityTranslation$source_set_separates_image",
                    theorem =
                      parityTranslationTheory.source_set_separates_image}]))
            (#goal translated_set_separation_goal)))

val translated_two_point_separation_goal =
  goal_named "set_theory_L168" benchSets.goals

val _ =
  check
    ("translated two-point set separation executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_two_point_separation_goal)
            translated_two_point_separation_goal))

val _ =
  check
    ("two-point set separation needs its witness normalization",
     fn () =>
       not
         (recipe_solves
            (benchLib.Invoke (benchLib.Simp, []))
            (#goal translated_two_point_separation_goal)))

val translated_omitting_set_goal =
  goal_named "set_theory_L180" benchSets.goals

val _ =
  check
    ("translated omitting-set witness executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_omitting_set_goal)
            translated_omitting_set_goal))

val _ =
  check
    ("omitting-set witness needs its existential normalization",
     fn () =>
       not
         (recipe_solves
            (benchLib.Invoke (benchLib.Simp, []))
            (#goal translated_omitting_set_goal)))

val translated_singleton_superset_goals =
  map (fn id => goal_named id benchSets.goals)
    ["set_theory_L44", "set_theory_L48"]

val _ =
  check
    ("translated singleton supersets execute exactly",
     fn () =>
       List.all
         (fn goal =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         translated_singleton_superset_goals)

val _ =
  check
    ("singleton supersets need their at-most-one normalization",
     fn () =>
       List.all
         (fn goal =>
           not
             (recipe_solves
                (benchLib.Invoke (benchLib.Simp, []))
                (#goal goal)))
         translated_singleton_superset_goals)

val translated_forall_iff_set_goals =
  map (fn id => goal_named id benchSets.goals)
    ["set_L796_insert_ident", "set_L872_Un_singleton_iff",
     "set_L875_singleton_Un_iff"]

fun set_auto_without_forall_iff (goal : benchLib.corpus_goal) =
  let
    val arguments = benchSetCorpus.method_args (#source_method goal)
  in
    benchLib.AllGoals
      (benchLib.Invoke (benchLib.Simp, arguments),
       benchLib.Invoke (benchLib.Auto, arguments))
  end

val _ =
  check
    ("translated quantified set equalities execute exactly",
     fn () =>
       List.all
         (fn goal =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         translated_forall_iff_set_goals)

val _ =
  check
    ("quantified set equalities need their destruction rules",
     fn () =>
       List.all
         (fn goal =>
           not
             (benchLib.outcome_solved
               (benchLib.run_goal (Time.fromSeconds 2)
                  (set_auto_without_forall_iff goal) goal)))
         translated_forall_iff_set_goals)

val translated_unique_member_goal =
  goal_named "set_L2012_pairwise_disjnt_iff" benchSets.goals

val _ =
  check
    ("translated pairwise-disjoint uniqueness executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_unique_member_goal)
            translated_unique_member_goal))

val _ =
  check
    ("pairwise-disjoint uniqueness needs its source transfer fact",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
            (benchLib.Invoke
               (benchLib.Auto,
                benchSetCorpus.method_args
                  (#source_method translated_unique_member_goal)))
            translated_unique_member_goal)))

val _ =
  check
    ("translated simp-implies results require their recorded recipes",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5) (#recipe goal) goal) andalso
           not
             (benchLib.outcome_solved
               (benchLib.run_goal (Time.fromSeconds 5)
                  (benchLib.Invoke (benchLib.Simp, [])) goal)))
         translated_set_goals)

val additive_image_goal =
  goal_named "set_L994_image_add_0" benchSets.goals

val _ =
  check
    ("polymorphic additive image requires its explicit-carrier recipe",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe additive_image_goal) additive_image_goal) andalso
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
              (benchLib.Invoke (benchLib.Auto, []))
              additive_image_goal)))

val translated_sorted_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L412_sorted_simps_1", "list_L412_sorted_simps_2",
     "list_L415_strict_sorted_simps_1",
     "list_L415_strict_sorted_simps_2",
     "list_L441_strict_sorted_imp_sorted",
     "list_L5911_sorted_wrt1",
     "list_L5946_sorted_wrt_dropWhile",
     "list_L5964_sorted_wrt01",
     "list_L5971_sorted_wrt_nth_less",
     "list_L6208_sorted_upt"]

val _ =
  check
    ("polymorphic sorted translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_sorted_goals)

val _ =
  check
    ("translated sorted suffix rule is essential to AUTO",
     fn () =>
       let
         val goal =
           goal_named "list_L5946_sorted_wrt_dropWhile"
             benchListMap.goals
         val budget = Time.fromSeconds 5
       in
         benchLib.outcome_solved
           (benchLib.run_goal budget (#recipe goal) goal) andalso
         not
           (benchLib.outcome_solved
             (benchLib.run_goal budget
               (benchLib.Invoke (benchLib.Auto, [])) goal))
       end)

val _ =
  check
    ("translated sorted interval argument is essential to simp",
     fn () =>
       let
         val goal =
           goal_named "list_L6208_sorted_upt" benchListMap.goals
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
               (benchLib.Invoke (benchLib.Simp, [])) goal))
       end)

val _ =
  check
    ("translated all-pairs sortedness argument is essential to AUTO",
     fn () =>
       let
         val goal =
           goal_named "list_L5971_sorted_wrt_nth_less"
             benchListMap.goals
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
               (benchLib.Invoke (benchLib.Auto, [])) goal))
       end)

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

val translated_fold_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L3286_rev_conv_fold",
     "list_L3400_foldr_conv_foldl",
     "list_L3404_foldl_conv_foldr",
     "list_L3413_foldr_cong",
     "list_L3417_foldl_cong",
     "list_L3421_foldr_append",
     "list_L3424_foldl_append",
     "list_L3427_foldr_map",
     "list_L3430_foldr_filter",
     "list_L3434_foldl_map",
     "list_L3438_concat_conv_foldr"]

val _ =
  check
    ("translated fold methods execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         translated_fold_list_goals)

val essential_fold_list_goals =
  [("list_L3286_rev_conv_fold", benchLib.Simp),
   ("list_L3400_foldr_conv_foldl", benchLib.Simp),
   ("list_L3413_foldr_cong", benchLib.Auto),
   ("list_L3421_foldr_append", benchLib.Simp),
   ("list_L3427_foldr_map", benchLib.Simp),
   ("list_L3430_foldr_filter", benchLib.Simp),
   ("list_L3438_concat_conv_foldr", benchLib.Simp)]

val _ =
  check
    ("translated fold method arguments are essential",
     fn () =>
       List.all
         (fn (id, tactic_id) =>
           let
             val goal = goal_named id benchListMap.goals
           in
             not
               (benchLib.outcome_solved
                 (benchLib.run_goal (Time.fromSeconds 5)
                    (benchLib.Invoke (tactic_id, [])) goal))
           end)
         essential_fold_list_goals)

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

val translated_list_relation_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L3168_list_eq_iff_zip_eq",
     "list_L3569_list_all2_antisym"]

val _ =
  check
    ("translated list-relation methods execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         translated_list_relation_goals)

val _ =
  check
    ("translated list-relation arguments are essential",
     fn () =>
       let
         val zip_goal =
           goal_named "list_L3168_list_eq_iff_zip_eq"
             benchListMap.goals
         val antisym_goal =
           goal_named "list_L3569_list_all2_antisym"
             benchListMap.goals
         val budget = Time.fromSeconds 5
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal budget
                (benchLib.Invoke (benchLib.Auto, [])) zip_goal)) andalso
         not
           (benchLib.outcome_solved
             (benchLib.run_goal budget
                (benchLib.Invoke (benchLib.Simp, [])) antisym_goal))
       end)

val translated_list_all_transfer_goal =
  goal_named "list_L9013_list_all_transfer" benchListMap.goals

fun not_list_rel_all_mem argument =
  case argument of
      benchLib.DestAdd
        (_, {name = "parityTranslation$source_list_rel_all_mem", ...}) =>
        false
    | _ => true

val list_all_transfer_without_bridge =
  case #recipe translated_list_all_transfer_goal of
      benchLib.Invoke (benchLib.Blast, arguments) =>
        benchLib.Invoke
          (benchLib.Blast,
           List.filter not_list_rel_all_mem arguments)
    | _ => raise Fail "unexpected list-all transfer recipe"

val _ =
  check
    ("translated list-all transfer executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_list_all_transfer_goal)
            translated_list_all_transfer_goal))

val _ =
  check
    ("list-all transfer needs normalized LIST_REL destruction",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              list_all_transfer_without_bridge
              translated_list_all_transfer_goal)))

val translated_split_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L1460_split_list_propE",
     "list_L1484_split_list_first_propE",
     "list_L1511_split_list_last_propE"]

val _ =
  check
    ("translated split-list using clauses execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         translated_split_list_goals)

val _ =
  check
    ("translated split-list dependency is essential to BLAST",
     fn () =>
       let
         val goal =
           goal_named "list_L1460_split_list_propE"
             benchListMap.goals
       in
         not
           (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 1)
                (benchLib.Invoke (benchLib.Blast, [])) goal))
       end)

val translated_split_list_goal =
  goal_named "list_L1415_in_set_conv_decomp" benchListMap.goals

val _ =
  check
    ("translated split-list decomposition executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_split_list_goal)
            translated_split_list_goal))

val _ =
  check
    ("translated split-list decomposition dependency is essential",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 1)
              (benchLib.Invoke (benchLib.Auto, []))
              translated_split_list_goal)))

val translated_concat_injective_goal =
  goal_named "list_L1569_concat_injective" benchListMap.goals

val _ =
  check
    ("translated concat injectivity executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_concat_injective_goal)
            translated_concat_injective_goal))

val _ =
  check
    ("translated concat injectivity dependency is essential",
     fn () =>
       let
         val bare_simp = benchLib.Invoke (benchLib.Simp, [])
         val contextual_bare =
           benchLib.AllGoals
             (bare_simp,
              benchLib.AllGoals
                (benchLib.Invoke (benchLib.Safe, []), bare_simp))
       in
         not
           (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 1)
                contextual_bare translated_concat_injective_goal))
       end)

val translated_concat_append_goal =
  goal_named "list_L1590_concat_eq_append_conv" benchListMap.goals

val _ =
  check
    ("translated concat append decomposition executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_concat_append_goal)
            translated_concat_append_goal))

val _ =
  check
    ("translated concat append dependency is essential",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 1)
              (benchLib.Invoke (benchLib.Auto, []))
              translated_concat_append_goal)))

val translated_filter_cons_goal =
  goal_named "list_L1789_filter_eq_Cons_iff" benchListMap.goals

val filter_cons_args_without_intro =
  List.filter
    (fn benchLib.IntroAdd
          (_, {name = "parityTranslation$source_filter_eq_ConsI", ...}) =>
          false
      | _ => true)
    (benchListCorpus.method_args
       (#source_method translated_filter_cons_goal)
       (#goal translated_filter_cons_goal))

val _ =
  check
    ("translated filter-cons decomposition executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_filter_cons_goal)
            translated_filter_cons_goal))

val _ =
  check
    ("filter-cons decomposition needs its constructor direction",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 3)
              (benchLib.Invoke
                 (benchLib.Auto, filter_cons_args_without_intro))
              translated_filter_cons_goal)))

val translated_take_drop_append_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L2545_takeWhile_append",
     "list_L2585_dropWhile_append"]

val _ =
  check
    ("translated take/drop append using clauses execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         translated_take_drop_append_goals)

val _ =
  check
    ("translated take/drop append dependencies are essential to AUTO",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           not
             (benchLib.outcome_solved
               (benchLib.run_goal (Time.fromSeconds 1)
                  (benchLib.Invoke (benchLib.Auto, [])) goal)))
         translated_take_drop_append_goals)

val translated_take_drop_disjoint_goal =
  goal_named "list_L4065_set_take_disj_set_drop_if_distinct"
    benchListMap.goals

fun not_take_drop_normalization argument =
  case argument of
      benchLib.RewriteAdd {name, ...} =>
        not
          (List.exists (equal name)
             ["list$LENGTH_TAKE", "list$LENGTH_DROP",
              "list$EL_TAKE", "list$EL_DROP",
              "parityTranslation$source_lt_length_take",
              "parityTranslation$source_lt_length_drop"])
    | _ => true

val take_drop_disjoint_without_normalization =
  case #recipe translated_take_drop_disjoint_goal of
      benchLib.Invoke (benchLib.Auto, arguments) =>
        benchLib.Invoke
          (benchLib.Auto,
           List.filter not_take_drop_normalization arguments)
    | _ => raise Fail "unexpected take/drop disjointness recipe"

val _ =
  check
    ("translated take/drop disjointness executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_take_drop_disjoint_goal)
            translated_take_drop_disjoint_goal))

val _ =
  check
    ("take/drop disjointness needs index normalization",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              take_drop_disjoint_without_normalization
              translated_take_drop_disjoint_goal)))

val translated_dropwhile_id_goal =
  goal_named "list_L2576_dropWhile_id" benchListMap.goals

val dropwhile_id_args_without_head_mem =
  [benchLib.FactAdd
     {name = "parityTranslation$source_takeWhile_dropWhile_id",
      theorem =
        Drule.ISPECL
          [``v_P0 : 'a -> bool``, ``v_xs0 : 'a list``]
          parityTranslationTheory.source_takeWhile_dropWhile_id},
   benchLib.FactAdd
     {name = "parityTranslation$source_takeWhile_eq_nil_iff",
      theorem =
        Drule.ISPECL
          [``v_P0 : 'a -> bool``, ``v_xs0 : 'a list``]
          parityTranslationTheory.source_takeWhile_eq_nil_iff}]

val _ =
  check
    ("translated dropWhile identity executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_dropwhile_id_goal)
            translated_dropwhile_id_goal))

val _ =
  check
    ("dropWhile identity needs nonempty-head membership",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              (benchLib.Invoke
                 (benchLib.Fastforce,
                  dropwhile_id_args_without_head_mem))
              translated_dropwhile_id_goal)))

val translated_dropwhile_replicate_goal =
  goal_named "list_L5048_dropWhile_replicate" benchListMap.goals

fun not_hd_replicate argument =
  case argument of
      benchLib.RewriteAdd
        {name = "parityTranslation$source_hd_replicate", ...} => false
    | _ => true

val dropwhile_replicate_without_hd =
  case #recipe translated_dropwhile_replicate_goal of
      benchLib.Invoke (benchLib.Fastforce, arguments) =>
        benchLib.Invoke
          (benchLib.Fastforce, List.filter not_hd_replicate arguments)
    | _ => raise Fail "unexpected dropWhile replicate recipe"

val _ =
  check
    ("translated dropWhile replicate executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_dropwhile_replicate_goal)
            translated_dropwhile_replicate_goal))

val _ =
  check
    ("dropWhile replicate needs source-head normalization",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              dropwhile_replicate_without_hd
              translated_dropwhile_replicate_goal)))

val _ =
  check
    ("translated disjoint append arguments are essential to AUTO",
     fn () =>
       let
         val goal =
           goal_named "list_L1367_append_eq_append_conv_if_disj"
             benchListMap.goals
         val append_only =
           benchLib.Invoke
             (benchLib.Auto,
              [benchLib.RewriteAdd
                 {name = "list$APPEND_EQ_APPEND",
                  theorem = listTheory.APPEND_EQ_APPEND}])
         val empty_only =
           benchLib.Invoke
             (benchLib.Auto,
              [benchLib.RewriteAdd
                 {name = "rich_list$NIL_NO_MEM",
                  theorem = rich_listTheory.NIL_NO_MEM}])
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 1) append_only goal)) andalso
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 1) empty_only goal))
       end)

val _ =
  check
    ("translated append constructor arguments are essential to AUTO",
     fn () =>
       let
         val goal = goal_named "list_L1532_append_Cons_eq_iff"
           benchListMap.goals
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 1)
               (benchLib.Invoke (benchLib.Auto, [])) goal))
       end)

val _ =
  check
    ("translated snoc decomposition arguments are essential to fastforce",
     fn () =>
       let
         val goal = goal_named "list_L2178_snoc_eq_iff_butlast"
           benchListMap.goals
         val normalize_only =
           benchLib.Invoke
             (benchLib.Fastforce,
              [benchLib.RewriteAdd
                 {name = "list$SNOC_APPEND[symmetric]",
                  theorem = Conv.GSYM listTheory.SNOC_APPEND}])
         val decompose_only =
           benchLib.Invoke
             (benchLib.Fastforce,
              [benchLib.RewriteAdd
                 {name = "list$SNOC_LAST_FRONT",
                  theorem = listTheory.SNOC_LAST_FRONT}])
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal
                (Time.fromSeconds 1) normalize_only goal)) andalso
         not
           (benchLib.outcome_solved
             (benchLib.run_goal
                (Time.fromSeconds 1) decompose_only goal))
       end)

val translated_numeric_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L3481_upt_Suc_append", "list_L3485_upt_conv_Cons",
     "list_L3506_hd_upt", "list_L3509_tl_upt",
     "list_L3589_take_Cons_numeral",
     "list_L3593_drop_Cons_numeral",
     "list_L3597_nth_Cons_numeral",
     "list_L3635_upto_empty", "list_L3638_upto_single",
     "list_L3641_upto_Nil", "list_L3646_upto_rec1",
     "list_L3683_upto_split2", "list_L3687_upto_split3",
     "list_L3695_upto_aux_rec", "list_L3699_upto_code"]

val _ =
  check
    ("numeric and inclusive-range translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_numeric_list_goals)

val _ =
  check
    ("translated upt recurrence and TL boundary are essential to simp",
     fn () =>
       let
         val recurrence_goal =
           goal_named "list_L3485_upt_conv_Cons" benchListMap.goals
         val tl_goal =
           goal_named "list_L3509_tl_upt" benchListMap.goals
         val bare = benchLib.Invoke (benchLib.Simp, [])
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
               bare recurrence_goal)) andalso
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5) bare tl_goal))
       end)

val _ =
  check
    ("translated length successor conversion is essential to AUTO",
     fn () =>
       let
         val goal =
           goal_named "list_L5788_lists_length_Suc_eq"
             benchListMap.goals
         val budget = Time.fromSeconds 5
       in
         benchLib.outcome_solved
           (benchLib.run_goal budget (#recipe goal) goal) andalso
         not
           (benchLib.outcome_solved
             (benchLib.run_goal budget
               (benchLib.Invoke (benchLib.Auto, [])) goal))
       end)

val _ =
  check
    ("translated length-at-most-one conversion is essential to AUTO",
     fn () =>
       let
         val goal =
           goal_named "list_L5964_sorted_wrt01" benchListMap.goals
         val budget = Time.fromSeconds 5
       in
         benchLib.outcome_solved
           (benchLib.run_goal budget (#recipe goal) goal) andalso
         not
           (benchLib.outcome_solved
             (benchLib.run_goal budget
               (benchLib.Invoke (benchLib.Auto, [])) goal))
       end)

val translated_adjacent_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L4319_successively_nth",
     "list_L4322_distinct_adj_conv_nth",
     "list_L4326_distinct_adj_nth",
     "list_L4406_distinct_adj_Nil",
     "list_L4406_distinct_adj_singleton",
     "list_L4406_distinct_adj_Cons_Cons",
     "list_L4431_distinct_adj_rev",
     "list_L4434_distinct_adj_append_iff",
     "list_L4439_distinct_adj_appendD1",
     "list_L4439_distinct_adj_appendD2",
     "list_L4450_distinct_adj_map_iff"]

val _ =
  check
    ("adjacent-distinctness translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_adjacent_list_goals)

val translated_removal_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L4628_extract_None_iff",
     "list_L4632_extract_SomeE",
     "list_L4637_extract_Some_iff",
     "list_L4642_extract_Nil_code",
     "list_L4645_extract_Cons_code",
     "list_L4707_foldr_fold_remove1",
     "list_L4742_distinct_removeAll",
     "list_L4758_length_removeAll_less_eq",
     "list_L4762_length_removeAll_less",
     "list_L4781_foldr_fold_removeAll",
     "list_L4793_minus_list_mset_Nil2",
     "list_L4796_minus_list_mset_Cons2",
     "list_L4857_minus_list_set_Cons2"]

val _ =
  check
    ("removal and list-subtraction translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_removal_list_goals)

val translated_indexed_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L2786_zip_append",
     "list_L5136_length_indexed_from",
     "list_L5140_map_fst_indexed_from",
     "list_L5144_map_snd_indexed_from",
     "list_L5163_nth_indexed_from_eq",
     "list_L5176_distinct_indexed_from",
     "list_L5180_indexed_from_append_eq"]

val _ =
  check
    ("indexed-list translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_indexed_list_goals)

val _ =
  check
    ("translated zip prefix append is essential to its simp recipe",
     fn () =>
       let
         val goal = goal_named "list_L2786_zip_append" benchListMap.goals
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
               (benchLib.Invoke (benchLib.Simp, [])) goal))
       end)

val translated_rotate_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L5191_rotate0", "list_L5194_rotate_Suc",
     "list_L5197_rotate_add", "list_L5201_rotate_rotate",
     "list_L5207_rotate1_rotate_swap", "list_L5259_rotate_map",
     "list_L5301_nth_rotate1", "list_L5325_bij_rotate1"]

val _ =
  check
    ("rotation translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_rotate_list_goals)

val translated_nths_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L1856_nth_Cons_pos",
     "list_L1867_nth_append_left",
     "list_L1870_nth_append_right",
     "list_L1903_map_equality_iff",
     "list_L5334_nths_empty", "list_L5337_nths_nil",
     "list_L5344_length_nths", "list_L5385_set_nths_subset",
     "list_L5388_notin_set_nthsI", "list_L5391_in_set_nthsD",
     "list_L5394_nths_singleton"]

val _ =
  check
    ("indexed-selection translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_nths_list_goals)

val _ =
  check
    ("translated positive-index rule is essential to AUTO",
     fn () =>
       let
         val goal = goal_named "list_L1856_nth_Cons_pos"
           benchListMap.goals
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
               (benchLib.Invoke (benchLib.Auto, [])) goal))
       end)

val _ =
  check
    ("translated nth-append rules are essential to AUTO",
     fn () =>
       let
         val goal = goal_named "list_L1867_nth_append_left"
           benchListMap.goals
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
               (benchLib.Invoke (benchLib.Auto, [])) goal))
       end)

val translated_map_injection_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L1193_inj_on_map_eq_map", "list_L1213_inj_on_mapI"]

val _ =
  check
    ("translated map-injection premise order executes exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         translated_map_injection_goals andalso
       let
         val goal = List.hd translated_map_injection_goals
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (benchLib.Invoke (benchLib.Blast, [])) goal))
       end)

val _ =
  check
    ("translated mapped-list equality rules are essential to fastforce",
     fn () =>
       let
         val goal = goal_named "list_L1903_map_equality_iff"
           benchListMap.goals
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
               (benchLib.Invoke (benchLib.Fastforce, [])) goal))
       end)

val _ =
  check
    ("translated map congruence argument is essential to simp",
     fn () =>
       let
         val goal = goal_named "list_L1119_map_cong"
           benchListMap.goals
       in
         not
           (benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 1)
               (benchLib.Invoke (benchLib.Simp, [])) goal))
       end)

val translated_ran_zip_goal =
  goal_named "map_L776_ran_map_of_zip" benchListMap.goals

val _ =
  check
    ("translated association-list range executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_ran_zip_goal)
            translated_ran_zip_goal))

val _ =
  check
    ("translated ZIP range fact is essential to simp",
     fn () =>
       case #recipe translated_ran_zip_goal of
           benchLib.Invoke (benchLib.Simp, arguments) =>
             let
               fun keep (benchLib.FactAdd {name, ...}) =
                     name <> "finite_mapAutoSeed$MEM_SND_ZIP_AUTO"
                 | keep _ = true
               val recipe =
                 benchLib.Invoke
                   (benchLib.Simp, List.filter keep arguments)
             in
               not
                 (benchLib.outcome_solved
                   (benchLib.run_goal (Time.fromSeconds 5)
                      recipe translated_ran_zip_goal))
             end
         | _ => false)

val translated_range_update_goal =
  goal_named "map_L723_ran_map_upd" benchListMap.goals

val _ =
  check
    ("translated range update executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_range_update_goal)
            translated_range_update_goal))

val _ =
  check
    ("range update needs its source membership bridge",
     fn () =>
       case #recipe translated_range_update_goal of
           benchLib.Invoke (backend, arguments) =>
             let
               fun keep (benchLib.RewriteAdd {name, ...}) =
                     name <>
                       "parityTranslation$source_range_update_none"
                 | keep _ = true
             in
               not
                 (benchLib.outcome_solved
                   (benchLib.run_goal (Time.fromSeconds 1)
                      (benchLib.Invoke
                         (backend, List.filter keep arguments))
                      translated_range_update_goal))
             end
         | _ => false)

val translated_pre_simplified_fastforce_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["map_L860_map_le_upd", "map_L887_map_le_map_add",
     "map_L893_map_add_le_mapE"]

val _ =
  check
    ("translated map-order simplification phases execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal))
         translated_pre_simplified_fastforce_goals)

val _ =
  check
    ("map-order fastforce needs its source simplification phase",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case #recipe goal of
               benchLib.AllGoals
                 (benchLib.Invoke (benchLib.Simp, arguments), _) =>
                 not
                   (benchLib.outcome_solved
                     (benchLib.run_goal (Time.fromSeconds 5)
                        (benchLib.Invoke
                          (benchLib.Fastforce, arguments)) goal))
             | _ => false)
         translated_pre_simplified_fastforce_goals)

val translated_map_add_subsumed_goal =
  goal_named "map_L899_map_add_subsumed1" benchListMap.goals

val _ =
  check
    ("translated map-add subsumption executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_map_add_subsumed_goal)
            translated_map_add_subsumed_goal))

val _ =
  check
    ("translated map-add subsumption dependency is essential",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 1)
              (benchLib.Invoke (benchLib.Simp, []))
              translated_map_add_subsumed_goal)))

val translated_map_upds_twist_goal =
  goal_named "map_L519_map_upds_twist" benchListMap.goals

val _ =
  check
    ("translated map-update twist executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_map_upds_twist_goal)
            translated_map_upds_twist_goal))

val _ =
  check
    ("map-update twist needs its full-list bridge",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 1)
              (benchLib.Invoke (benchLib.Simp, []))
              translated_map_upds_twist_goal)))

val translated_map_add_commute_goal =
  goal_named "map_L890_map_le_iff_map_add_commute"
    benchListMap.goals

val map_add_commute_without_split =
  case #recipe translated_map_add_commute_goal of
      benchLib.Invoke (benchLib.Fastforce, arguments) =>
        benchLib.Invoke
          (benchLib.Simp,
           List.filter
             (fn benchLib.SplitAdd _ => false | _ => true)
             arguments)
    | _ => raise Fail "unexpected map-add commute recipe"

val _ =
  check
    ("translated map-add commutation executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_map_add_commute_goal)
            translated_map_add_commute_goal))

val _ =
  check
    ("map-add commutation exceeds simplification without its option split",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              map_add_commute_without_split
              translated_map_add_commute_goal)))

val translated_injective_range_update_goal =
  goal_named "map_L730_ran_map_upd_Some" benchListMap.goals

val range_update_without_pointwise_bridge =
  case #recipe translated_injective_range_update_goal of
      benchLib.AllGoals (source_simplification, _) =>
        source_simplification
    | _ => raise Fail "unexpected injective range-update recipe"

val _ =
  check
    ("translated injective range update executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_injective_range_update_goal)
            translated_injective_range_update_goal))

val _ =
  check
    ("injective range update needs its pointwise bridge",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              range_update_without_pointwise_bridge
              translated_injective_range_update_goal)))

val translated_finite_graph_goal =
  goal_named "map_L828_finite_graph_map_of" benchListMap.goals

fun not_finite_graph_bridge argument =
  case argument of
      benchLib.IntroAdd
        (_, {name = "parityTranslation$source_finite_graph_alookup", ...}) =>
        false
    | _ => true

val finite_graph_without_bridge =
  case #recipe translated_finite_graph_goal of
      benchLib.Invoke (benchLib.Blast, arguments) =>
        benchLib.Invoke
          (benchLib.Blast,
           List.filter not_finite_graph_bridge arguments)
    | _ => raise Fail "unexpected finite-graph recipe"

val _ =
  check
    ("translated finite association-list graph executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_finite_graph_goal)
            translated_finite_graph_goal))

val _ =
  check
    ("finite association-list graph needs its subset bridge",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              finite_graph_without_bridge
              translated_finite_graph_goal)))

val translated_auto_map_domain_goal =
  goal_named "map_L874_map_le_implies_dom_le" benchListMap.goals

val _ =
  check
    ("translated map-domain inclusion executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_auto_map_domain_goal)
            translated_auto_map_domain_goal))

val _ =
  check
    ("map-domain goal needs its translated AUTO backend",
     fn () =>
       case #recipe translated_auto_map_domain_goal of
           benchLib.Invoke (benchLib.Auto, arguments) =>
             not
               (benchLib.outcome_solved
                 (benchLib.run_goal (Time.fromSeconds 5)
                    (benchLib.Invoke (benchLib.Fastforce, arguments))
                    translated_auto_map_domain_goal))
         | _ => false)

val translated_update_distinct_goal =
  goal_named "list_L3925_set_update_distinct" benchListMap.goals

val _ =
  check
    ("translated distinct-list update executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_update_distinct_goal)
            translated_update_distinct_goal))

val _ =
  check
    ("distinct-list update needs its residual AESOP phase",
     fn () =>
       case #recipe translated_update_distinct_goal of
           benchLib.AllGoals
             (benchLib.Invoke (benchLib.Auto, arguments),
              benchLib.Invoke (benchLib.Aesop, _)) =>
             not
               (benchLib.outcome_solved
                 (benchLib.run_goal (Time.fromSeconds 5)
                    (benchLib.Invoke (benchLib.Auto, arguments))
                    translated_update_distinct_goal))
         | _ => false)

val translated_product_projection_goal =
  goal_named "product_type_L1220_subset_fst_snd" benchListMap.goals

val _ =
  check
    ("translated product projections execute exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_product_projection_goal)
            translated_product_projection_goal))

val _ =
  check
    ("product projection goal needs its translated AUTO backend",
     fn () =>
       case #recipe translated_product_projection_goal of
           benchLib.Invoke (benchLib.Auto, arguments) =>
             not
               (benchLib.outcome_solved
                 (benchLib.run_goal (Time.fromSeconds 5)
                    (benchLib.Invoke (benchLib.Force, arguments))
                    translated_product_projection_goal))
         | _ => false)

val translated_unique_pair_choice_goal =
  goal_named "product_type_L688_The_split_eq" benchListMap.goals

val _ =
  check
    ("translated unique-pair choice executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_unique_pair_choice_goal)
            translated_unique_pair_choice_goal))

val _ =
  check
    ("unique-pair choice needs its source selection bridge",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
              (benchLib.Invoke (benchLib.Blast, []))
              translated_unique_pair_choice_goal)))

val translated_pair_predicate_mono_goal =
  goal_named
    "product_type_L1100_Collect_split_mono_strong" benchListMap.goals

val _ =
  check
    ("translated pair-predicate monotonicity executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_pair_predicate_mono_goal)
            translated_pair_predicate_mono_goal))

val _ =
  check
    ("pair-predicate monotonicity exceeds translation simplification",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 2)
              (benchLib.Invoke (benchLib.Simp, []))
              translated_pair_predicate_mono_goal)))

val translated_sigma_union_goal =
  goal_named "product_type_L1133_Sigma_Union" benchListMap.goals

val sigma_union_args_without_reassociation =
  List.filter
    (fn benchLib.RewriteAdd {name, ...} =>
          name <> "parityTranslation$source_exists_swapped_conj"
      | _ => true)
    (benchProductCorpus.method_args "by blast")

val _ =
  check
    ("translated dependent union executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_sigma_union_goal)
            translated_sigma_union_goal))

val _ =
  check
    ("dependent union needs existential-conjunction reassociation",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
              (benchLib.Invoke
                 (benchLib.Blast,
                  sigma_union_args_without_reassociation))
              translated_sigma_union_goal)))

val translated_product_bij_goal =
  goal_named "product_type_L1329_bij_betw_map_prod"
    benchListMap.goals

fun not_bij_components argument =
  case argument of
      benchLib.DestAdd
        (_, {name = "parityTranslation$source_bij_components", ...}) =>
        false
    | _ => true

val product_bij_rule_arguments =
  List.filter
    (fn argument =>
      benchProductCorpus.classical_rule_arg argument andalso
      not_bij_components argument)
    (benchProductCorpus.method_args "by auto")

val _ =
  check
    ("translated product bijection executes exactly",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_product_bij_goal)
            translated_product_bij_goal))

val _ =
  check
    ("product bijection needs combined BIJ components",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 3)
              (benchLib.Invoke
                 (benchLib.Auto, product_bij_rule_arguments))
              translated_product_bij_goal)))

val translated_ordered_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L6023_sorted0", "list_L6026_sorted1",
     "list_L6029_sorted2", "list_L6034_sorted_append",
     "list_L6038_sorted_map", "list_L6042_sorted01",
     "list_L6049_sorted_iff_nth_mono_less",
     "list_L6053_sorted_iff_nth_mono",
     "list_L6057_sorted_nth_mono",
     "list_L6061_sorted_iff_nth_Suc"]

val _ =
  check
    ("ordered-list translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_ordered_list_goals)

val translated_recovered_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L3566_map_nth_upt0",
     "product_type_L1061_Sigma_insert",
     "list_L8543_map_filter_map_filter",
     "list_L8603_is_empty_set",
     "list_L8701_trancl_set_ntrancl"]

val _ =
  check
    ("recovered source translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_recovered_goals)

val translated_interval_list_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L8290_forall_less_eq_iff",
     "list_L8294_exists_less_eq_iff",
     "list_L8298_forall_less_iff",
     "list_L8302_exists_less_iff",
     "list_L8306_forall_greater_eq_iff",
     "list_L8310_exists_greater_eq_iff",
     "list_L8314_forall_greater_iff",
     "list_L8318_exists_greater_iff",
     "list_L8454_atLeast_eq_atLeastAtMost_top",
     "list_L8458_greaterThan_eq_greaterThanAtMost_top",
     "list_L8467_atMost_eq_atLeastAtMost_bot",
     "list_L8471_lessThan_eq_atLeastLessThan_bot"]

val _ =
  check
    ("bounded-quantifier translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
         translated_interval_list_goals)

val translated_string_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["string_L34_of_char_Char", "string_L60_char_of_take_bit_eq",
     "string_L68_char_of_comp_of_char", "string_L83_of_char_eqI",
     "string_L87_of_char_eq_iff", "string_L131_char_of_eq_iff",
     "string_L135_char_of_nat", "string_L344_char_of_integer_code",
     "string_L357_integer_of_char_code", "string_L728_anon_L728",
     "string_L919_abort_cong"]

val _ =
  check
    ("all translated String and character results are executable",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5) (#recipe goal) goal))
         translated_string_goals)

val signed_character_goal =
  goal_named "string_L344_char_of_integer_code" benchListMap.goals

val _ =
  check
    ("signed character translation needs its representation bridge",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
              (benchLib.Invoke (benchLib.Simp, []))
              signed_character_goal)))

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
    ("integer ideal recipe constructs the exact corpus witness",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 30)
            (benchLib.Invoke (benchLib.IntIdeal, [])) integer_ideal_goal))

val _ =
  check
    ("integer ring normalization alone leaves the witness goal",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 30)
              (benchLib.Invoke (benchLib.IntRing, []))
              integer_ideal_goal)))

val translated_algebra_goals =
  map
    (fn id => goal_named id benchAlgebra.goals)
    ["groebner_L61", "groebner_L72", "groebner_L82"]

val _ =
  check
    ("abstract integral-domain translations execute exactly",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 10)
                (#recipe goal) goal))
         translated_algebra_goals)

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
         source_outcomes = 1061 andalso source_outcomes + 9 = 1070
       end)

val _ =
  check
    ("exhaustive shortfall registers are exact",
     fn () =>
       count_cause benchLib.EngineLimitation benchSets.shortfalls = 0 andalso
       count_cause benchLib.TranslationGap benchSets.shortfalls = 0 andalso
       count_cause benchLib.EngineLimitation benchListMap.shortfalls = 0 andalso
       count_cause benchLib.TranslationGap benchListMap.shortfalls = 0 andalso
       count_cause benchLib.EngineLimitation
         benchPresburger.shortfalls = 0 andalso
       count_cause benchLib.TranslationGap benchAlgebra.shortfalls = 0)

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
         (if benchLib.selftest_level () >= 2 then 604 else 5)
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
    ("level-2 generated parity report matches the committed file",
     fn () =>
       Option.isSome (OS.Process.getEnv "HOLBENCHFAMILY") orelse
       benchLib.selftest_level () < 2 orelse
       read_all "../PARITY.md" = parityLib.render ())
