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
              goals = map benchLib.prepare_goal [solved_goal, failed_goal],
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
              goals = map benchLib.prepare_goal [solved_goal],
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
             (benchLib.prepare_goal
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
          "cong(list$LENGTH_REVERSE)"])

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
  | argument_theorem (benchLib.SimpFragmentAdd _) = NONE
  | argument_theorem (benchLib.RewriteDelete _) = NONE

fun argument_name (benchLib.RewriteAdd {name, ...}) = SOME name
  | argument_name (benchLib.SplitAdd {name, ...}) = SOME name
  | argument_name (benchLib.IntroAdd (_, {name, ...})) = SOME name
  | argument_name (benchLib.ElimAdd (_, {name, ...})) = SOME name
  | argument_name (benchLib.DestAdd (_, {name, ...})) = SOME name
  | argument_name (benchLib.CongruenceAdd {name, ...}) = SOME name
  | argument_name (benchLib.FactAdd {name, ...}) = SOME name
  | argument_name (benchLib.DefinitionAdd {name, ...}) = SOME name
  | argument_name (benchLib.SimpFragmentAdd (name, _)) = SOME name
  | argument_name (benchLib.RewriteDelete _) = NONE

fun recipe_theorems (benchLib.Invoke (_, arguments)) =
      List.mapPartial argument_theorem arguments
  | recipe_theorems (benchLib.Then (left, right)) =
      recipe_theorems left @ recipe_theorems right
  | recipe_theorems (benchLib.AllGoals (left, right)) =
      recipe_theorems left @ recipe_theorems right

fun recipe_argument_names (benchLib.Invoke (_, arguments)) =
      List.mapPartial argument_name arguments
  | recipe_argument_names (benchLib.Then (left, right)) =
      recipe_argument_names left @ recipe_argument_names right
  | recipe_argument_names (benchLib.AllGoals (left, right)) =
      recipe_argument_names left @ recipe_argument_names right

fun first_recipe_arguments (benchLib.Invoke (_, arguments)) = arguments
  | first_recipe_arguments (benchLib.Then (left, _)) =
      first_recipe_arguments left
  | first_recipe_arguments (benchLib.AllGoals (left, _)) =
      first_recipe_arguments left

fun last_recipe_arguments (benchLib.Invoke (_, arguments)) = arguments
  | last_recipe_arguments (benchLib.Then (_, right)) =
      last_recipe_arguments right
  | last_recipe_arguments (benchLib.AllGoals (_, right)) =
      last_recipe_arguments right

fun without_argument_names names arguments =
  List.filter
    (fn argument =>
      case argument_name argument of
          SOME name => not (List.exists (equal name) names)
        | NONE => true)
    arguments

fun classical_rule_argument argument =
  case argument of
      benchLib.IntroAdd _ => true
    | benchLib.ElimAdd _ => true
    | benchLib.DestAdd _ => true
    | _ => false

val every_corpus_goal =
  benchClassical.goals @ benchSets.goals @ benchListMap.goals @
  benchLinarith.goals @ benchPresburger.goals @ benchAlgebra.goals

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
                          in
                            arguments recipe
                          end))) ^ "]")
                 direct_recipe_goals) ^ "\n");
          false))

fun goal_named id goals =
  case List.filter
         (fn ({id = candidate, ...} : benchLib.corpus_goal) =>
           candidate = id) goals of
      [goal] => goal
    | _ => raise mk_HOL_ERR "selftest" "goal_named" id

val ambient_list_all_goal =
  goal_named "list_L8167_list_all_iff" benchListMap.goals

val _ =
  check
    ("persistent measured-goal rewrites are excluded from simp",
     fn () =>
       not
         (benchLib.outcome_solved
           (benchLib.run_goal (Time.fromSeconds 5)
              (benchLib.Invoke (benchLib.Simp, []))
              ambient_list_all_goal)))

val _ =
  check
    ("invocation-local list predicate normalization closes its assignment",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe ambient_list_all_goal) ambient_list_all_goal))

val list_predicate_recipe = #recipe ambient_list_all_goal

val nested_list_predicate_goal =
  ``(EVERY (\items. EXISTS (predicate : 'a -> bool) items) xss <=>
     !items. MEM items xss ==>
       ?item. MEM item items /\ predicate item)``

val existential_list_predicate_goal =
  ``(EXISTS
       (\item. (pred_left : 'a -> bool) item /\
                (pred_right : 'a -> bool) item) xs <=>
     ?item. MEM item xs /\ pred_left item /\ pred_right item)``

val _ =
  check
    ("list predicate normalization handles existential and nested forms",
     fn () =>
       recipe_solves list_predicate_recipe nested_list_predicate_goal andalso
       recipe_solves
         list_predicate_recipe existential_list_predicate_goal andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            nested_list_predicate_goal) andalso
       not
         (recipe_solves (benchLib.Invoke (benchLib.Simp, []))
            existential_list_predicate_goal))

val _ =
  check
    ("list predicate normalization preserves empty and cons computation",
     fn () =>
       recipe_solves list_predicate_recipe
         ``EVERY (predicate : 'a -> bool) [] <=> T`` andalso
       recipe_solves list_predicate_recipe
         ``EVERY (predicate : 'a -> bool) (item::items) <=>
           predicate item /\ EVERY predicate items`` andalso
       not (recipe_solves list_predicate_recipe p))

val curry_regression_ids =
  ["product_type_L431_case_prod_unfold",
   "product_type_L451_case_prod_Pair",
   "product_type_L454_case_prod_eta",
   "product_type_L785_curry_conv",
   "product_type_L788_curryI",
   "product_type_L791_curryD",
   "product_type_L794_curryE",
   "product_type_L797_curry_case_prod",
   "product_type_L800_case_prod_curry",
   "product_type_L803_curry_K"]

val _ =
  check
    ("CURRY and UNCURRY definition recipes close neighboring schemas",
     fn () =>
       List.all
         (fn id =>
           let val goal = goal_named id benchListMap.goals
           in
             benchLib.outcome_solved
               (benchLib.run_goal (Time.fromSeconds 5) (#recipe goal) goal)
           end)
         curry_regression_ids)

val set_equality_dependency_goal =
  goal_named "set_L869_doubleton_eq_iff" benchSets.goals

val subset_image_dependency_goal =
  goal_named "set_L928_subset_image_iff" benchSets.goals

val powerset_dependency_goal =
  goal_named "set_L1604_Pow_singleton_iff" benchSets.goals

val _ =
  check
    ("set equality elimination handles a three-element insertion",
     fn () =>
       recipe_solves (#recipe set_equality_dependency_goal)
         ``((first : 'a) INSERT
              ((second : 'a) INSERT ((third : 'a) INSERT {})) =
            (fourth : 'a) INSERT
              ((fifth : 'a) INSERT ((sixth : 'a) INSERT {}))) ==>
           (first = fourth \/ first = fifth \/ first = sixth)``)

val _ =
  check
    ("image-subset elimination handles an unrelated codomain predicate",
     fn () =>
       recipe_solves (#recipe subset_image_dependency_goal)
         ``(((v_source0 : 'a set) SUBSET
               IMAGE (v_function0 : 'b -> 'a)
                 (\value. (v_predicate0 : 'b -> bool) value) <=>
             ?v_chosen0.
               v_chosen0 SUBSET
                 (\value. (v_predicate0 : 'b -> bool) value) /\
               v_source0 = IMAGE v_function0 v_chosen0) /\
            v_source0 SUBSET v_source0)``)

val _ =
  check
    ("powerset normalization handles an arbitrary collection",
     fn () =>
       recipe_solves (#recipe powerset_dependency_goal)
         ``(!candidate : 'a set.
              candidate SUBSET (v_universe0 : 'a set) <=>
              candidate IN (v_collection0 : 'a set set)) ==>
           POW v_universe0 = v_collection0``)

val product_witness_dependency_goal =
  goal_named "product_type_L1162_fst_image_times" benchListMap.goals

val _ =
  check
    ("product rules construct an IMAGE witness for an arbitrary fibre",
     fn () =>
       recipe_solves (#recipe product_witness_dependency_goal)
         ``((element : 'b) IN (fibre (source : 'a) : 'b set)) ==>
           source IN
             IMAGE FST
               (\pair : 'a # 'b.
                  FST pair = source /\
                  SND pair IN fibre (FST pair))``)

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

fun recipe_without_rewrite target recipe =
  case recipe of
      benchLib.Invoke (tactic, arguments) =>
        benchLib.Invoke (tactic, without_rewrite target arguments)
    | benchLib.Then (left, right) =>
        benchLib.Then
          (recipe_without_rewrite target left,
           recipe_without_rewrite target right)
    | benchLib.AllGoals (left, right) =>
        benchLib.AllGoals
          (recipe_without_rewrite target left,
           recipe_without_rewrite target right)

val translated_fixed_point_goal =
  goal_named "set_theory_L79" benchSets.goals

val fixed_point_without_variance =
  case #recipe translated_fixed_point_goal of
      benchLib.Invoke (benchLib.Blast, arguments) =>
        benchLib.Invoke
          (benchLib.Blast,
           without_rewrite
             "parityTranslation$source_complement_subset_swap"
             (without_rewrite "pred_set$IMAGE_SUBSET" arguments))
    | _ => raise Fail "unexpected fixed-point recipe"

val _ =
  check
    ("complement-image fixed point executes through lfp monotonicity",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_fixed_point_goal)
            translated_fixed_point_goal))

val _ =
  check
    ("complement-image fixed point uses general compositional variance",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            fixed_point_without_variance
            translated_fixed_point_goal))

val translated_num_set_induction_goal =
  goal_named "set_theory_L199" benchSets.goals

val _ =
  check
    ("number-set induction executes through predicate abstraction",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (#recipe translated_num_set_induction_goal)
            translated_num_set_induction_goal))

val _ =
  check
    ("predicate abstraction handles a non-numeric datatype",
     fn () =>
       recipe_solves (#recipe translated_num_set_induction_goal)
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
       recipe_solves (#recipe translated_num_set_induction_goal)
         ``((!aset : bool option set.
              NONE IN aset /\
              (!value. value IN aset ==> SOME T IN aset) ==>
              SOME T IN aset) /\
            (property : bool option -> bool) NONE /\
            (!value. property value ==> property (SOME T))) ==>
           property (SOME T)``)

val _ =
  check
    ("lfp witness handles a monotone union transformer",
     fn () =>
       recipe_solves (#recipe translated_fixed_point_goal)
         ``?fixed : 'a set.
             fixed = (seed : 'a set) UNION fixed``)

val _ =
  check
    ("lfp witness rejects an antitone complement transformer",
     fn () =>
       not
         (recipe_solves (#recipe translated_fixed_point_goal)
            ``?fixed : bool set. fixed = COMPL fixed``))

val _ =
  check
    ("lfp witness accepts two composed antitone transformers",
     fn () =>
       recipe_solves (#recipe translated_fixed_point_goal)
         ``?fixed : 'a set. fixed = COMPL (COMPL fixed)``)

val _ =
  check
    ("lfp witness handles an unrelated preimage-image transformer",
     fn () =>
       recipe_solves (#recipe translated_fixed_point_goal)
         ``?fixed : 'a set.
             fixed = PREIMAGE (mapping : 'a -> 'a)
                       (IMAGE mapping fixed)``)

val _ =
  check
    ("lfp witness handles variance below a nested predicate lambda",
     fn () =>
       recipe_solves (#recipe translated_fixed_point_goal)
         ``?fixed : 'a set.
             fixed = (\value. guard value \/ fixed value)``)

val _ =
  check
    ("predicate abstraction rejects an unsupported open pattern",
     fn () =>
       not
         (recipe_solves (#recipe translated_num_set_induction_goal)
            ``(!aset : bool set. T IN aset ==> T IN aset) ==>
              (property : bool -> bool) T``))

val _ =
  check
    ("predicate abstraction rejects a scope-escaping candidate",
     fn () =>
       let
         val recipe = #recipe translated_num_set_induction_goal
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
       recipe_solves (#recipe translated_num_set_induction_goal)
         ``((!aset : bool set. T IN aset ==> T IN aset) /\
            (!aset : bool set. T IN aset ==> F IN aset) /\
            (property : bool -> bool) T) ==>
           property F``)

val promoted_set_bridge_goals =
  [(goal_named "set_L1125_image_Pow_surj" benchSets.goals,
    "parityTranslation$source_image_pow_surj_iff"),
   (goal_named "set_L1607_Pow_insert" benchSets.goals,
    "parityTranslation$source_pow_insert_image_case_iff"),
   (goal_named "set_L1610_Pow_Compl" benchSets.goals,
    "parityTranslation$source_pow_compl_iff"),
   (goal_named "set_L1967_pairwise_image" benchSets.goals,
    "parityTranslation$source_pairwise_image")]

val bridge_dependent_set_goals =
  List.filter
    (fn (goal, _) => #id goal = "set_L1607_Pow_insert")
    promoted_set_bridge_goals

fun shortfall_id entries id =
  List.exists (fn ({id = other, ...} : benchLib.shortfall) => id = other)
    entries

val _ =
  check
    ("promoted translated set goals match corrected accounting",
     fn () =>
       List.all
         (fn (goal, _) =>
           benchLib.outcome_solved
             (benchLib.run_goal (Time.fromSeconds 5)
                (#recipe goal) goal) =
           not (shortfall_id benchSets.shortfalls (#id goal)))
         promoted_set_bridge_goals)

val _ =
  check
    ("translated powerset insertion needs its source bridge",
     fn () =>
       List.all
         (fn (goal, bridge) =>
           let
             val solved =
               benchLib.outcome_solved
                 (benchLib.run_goal (Time.fromSeconds 1)
                    (recipe_without_rewrite bridge (#recipe goal)) goal)
             val _ =
               if OS.Process.getEnv "HOLBENCHDEPENDENCYTRACE" = SOME "1"
               then TextIO.print
                      (#id goal ^ " without " ^ bridge ^ ": " ^
                       Bool.toString solved ^ "\n")
               else ()
           in
             not solved
           end)
         bridge_dependent_set_goals)

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
    ("proper-subset transitivity needs safe saturation before AUTO",
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
    ("FORCE constructs the predicate-set witness without a bridge",
     fn () =>
       benchLib.outcome_solved
         (benchLib.run_goal (Time.fromSeconds 5)
            (benchLib.Invoke
               (benchLib.Force,
                [benchLib.RewriteAdd
                   {name = "parityTranslation$source_mem_bigunion_image",
                    theorem =
                      parityTranslationTheory.source_mem_bigunion_image}]))
            translated_predicate_witness_goal))

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
    ("omitting-set witness executes with general witness search",
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
    val arguments =
      without_argument_names
        ["parityTranslation$source_forall_iffD1",
         "parityTranslation$source_forall_iffD2"]
        (first_recipe_arguments (#recipe goal))
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
                without_argument_names
                  ["parityTranslation$source_pairwise_disjnt_unique_transfer"]
                  (first_recipe_arguments
                    (#recipe translated_unique_member_goal))))
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
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ => true
             | benchLib.TIMEOUT =>
                 (print ("\n" ^ #id goal ^ ": timeout\n"); false)
             | benchLib.FAILED message =>
                 (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                  false))
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
    (first_recipe_arguments (#recipe translated_filter_cons_goal))

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
    ("numeric and inclusive-range translations match accounting",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           benchLib.outcome_solved
             (benchLib.run_goal
                (Time.fromSeconds 5) (#recipe goal) goal) =
           not (shortfall_id benchListMap.shortfalls (#id goal)))
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
     "list_L5207_rotate1_rotate_swap", "list_L5241_rotate_conv_mod",
     "list_L5259_rotate_map",
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

val _ =
  check
    ("rotation recipes never consume the final modulo theorem",
     fn () =>
       not
         (List.exists
           (fn ({recipe, ...} : benchLib.corpus_goal) =>
             List.exists
               (equal "parityTranslation$source_rotate_conv_mod")
               (recipe_argument_names recipe))
           every_corpus_goal))

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
     "list_L5394_nths_singleton", "list_L5409_nths_drop"]

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

val nths_drop_dependency_goal =
  goal_named "list_L5409_nths_drop" benchListMap.goals

val _ =
  check
    ("indexed-selection shifting handles a different predicate",
     fn () =>
       recipe_solves (#recipe nths_drop_dependency_goal)
         ``parityTranslation$source_nths
              (DROP v_count0 (v_xs0 : 'a list))
              {index | EVEN index} =
           parityTranslation$source_nths v_xs0
             (IMAGE (\index. v_count0 + index)
               {index | EVEN index})``)

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
    ("translated range update matches corrected accounting",
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
    ("FASTFORCE handles a map-order goal without recipe staging",
     fn () =>
       List.exists
         (fn (goal : benchLib.corpus_goal) =>
           case #recipe goal of
               benchLib.AllGoals
                 (benchLib.Invoke (benchLib.Simp, arguments), _) =>
                 benchLib.outcome_solved
                   (benchLib.run_goal (Time.fromSeconds 5)
                      (benchLib.Invoke
                        (benchLib.Fastforce, arguments)) goal)
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
    ("map-update twist executes with pointwise update normalization",
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
      benchLib.RewriteAdd
        {name =
           "parityTranslation$source_finite_bounded_lookup_graph", ...} =>
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
    ("finite association-list graph executes through bounded support",
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
    ("FASTFORCE also handles translated map-domain inclusion",
     fn () =>
       case #recipe translated_auto_map_domain_goal of
           benchLib.Invoke (benchLib.Auto, arguments) =>
             benchLib.outcome_solved
               (benchLib.run_goal (Time.fromSeconds 5)
                  (benchLib.Invoke (benchLib.Fastforce, arguments))
                  translated_auto_map_domain_goal)
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
    ("FORCE also handles translated product projections",
     fn () =>
       case #recipe translated_product_projection_goal of
           benchLib.Invoke (benchLib.Auto, arguments) =>
             benchLib.outcome_solved
               (benchLib.run_goal (Time.fromSeconds 5)
                  (benchLib.Invoke (benchLib.Force, arguments))
                  translated_product_projection_goal)
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
    (first_recipe_arguments (#recipe translated_sigma_union_goal))

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
      classical_rule_argument argument andalso
      not_bij_components argument)
    (last_recipe_arguments (#recipe translated_product_bij_goal))

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
     "list_L6061_sorted_iff_nth_Suc",
     "list_L6101_sorted_remove1",
     "list_L6104_sorted_butlast",
     "list_L6138_map_sorted_distinct_set_unique",
     "list_L6146_sorted_dropWhile",
     "list_L6211_sorted_upto",
     "list_L6292_sorted_insort",
     "list_L6298_sorted_sort",
     "list_L6312_sorted_sort_id",
     "list_L6315_sort_replicate",
     "list_L6384_sorted_insort_insert_key",
     "list_L6389_sorted_insort_insert",
     "list_L6433_sorted_indexed_from",
     "list_L6444_stable_sort_key_sort_key",
     "list_L6453_sorted_transpose",
     "list_L6487_nth_nth_transpose_sorted",
     "list_L6690_distinct_if_distinct_map",
     "list_L6761_anon_L6761",
     "list_L6770_sorted_key_list_of_set_unique",
     "list_L6835_sorted_list_of_set_lessThan_Suc",
     "list_L6839_sorted_list_of_set_atMost_Suc",
     "list_L6847_sorted_list_of_set_nonempty",
     "list_L6873_nth_sorted_list_of_set_greaterThanAtMost"]

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

fun retarget_goal id goal (base : benchLib.corpus_goal) =
  {id = id, goal = goal, source_method = #source_method base,
   recipe = #recipe base, excl = #excl base,
   provenance = #provenance base, representative = true}

val promoted_order_schema_goals =
   [retarget_goal "schema-sorted-key-insert"
     ``relation$WeakLinearOrder ($<= : num -> num -> bool) ==>
       parityTranslation$source_sorted ($<=)
         (MAP SUC [1; 3]) ==>
       parityTranslation$source_sorted ($<=)
         (MAP SUC
           (parityTranslation$source_insort_insert_key
             ($<=) SUC 2 [1; 3]))``
     (goal_named "list_L6384_sorted_insort_insert_key"
        benchListMap.goals),
   retarget_goal "schema-transpose-rectangular"
     ``parityTranslation$source_sorted ($<=)
         (REVERSE
           (MAP LENGTH
             (parityTranslation$source_transpose
               [[1; 2]; [3; 4]])))``
     (goal_named "list_L6453_sorted_transpose" benchListMap.goals),
   retarget_goal "schema-transpose-ragged"
     ``parityTranslation$source_sorted ($<=)
         (REVERSE
           (MAP LENGTH
             (parityTranslation$source_transpose
               [[1; 2; 3]; [4]; [5; 6]])))``
     (goal_named "list_L6453_sorted_transpose" benchListMap.goals),
   retarget_goal "schema-finite-enumeration"
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !items.
           FINITE items ==>
           items <> EMPTY ==>
           parityTranslation$source_sorted_list_of_set le items <> []``
     (goal_named "list_L6847_sorted_list_of_set_nonempty"
        benchListMap.goals),
   retarget_goal "schema-indexed-finite-interval"
     ``!index lower upper.
         SUC index < upper - lower ==>
         EL (SUC index)
           (parityTranslation$source_sorted_list_of_set ($<=)
             (parityTranslation$source_greaterThanAtMost
               ($<=) ($<) lower upper)) =
         SUC (lower + SUC index)``
     (goal_named
        "list_L6873_nth_sorted_list_of_set_greaterThanAtMost"
        benchListMap.goals)]

val _ =
  check
    ("promoted sorting, transpose, and finite-enumeration schemas generalize",
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
         promoted_order_schema_goals)

val translated_recovered_goals =
  map
    (fn id => goal_named id benchListMap.goals)
    ["list_L3349_anon_L3349",
     "list_L3381_anon_L3381",
     "list_L3385_anon_L3385",
     "list_L3566_map_nth_upt0",
     "list_L5441_distinct_set_subseqs",
     "list_L5470_subset_subseqs",
     "list_L5527_Nil_in_shufflesI",
     "list_L6972_mono_lists",
     "list_L7054_set_trans_list_step_subset_trancl",
     "list_L7247_lex_conv",
     "list_L7256_lenlex_conv",
     "list_L7387_lexord_same_pref_if_irrefl",
     "list_L7508_lexord_trans",
     "list_L7537_lexord_irrefl",
     "list_L7570_asym_lenlex",
     "list_L7771_wf_measures",
     "list_L7922_wf_listrel1_iff",
     "list_L7954_listrel_iff_nth",
     "list_L7995_equiv_listrel",
     "list_L8673_these_set_code",
     "list_L8701_trancl_set_ntrancl",
     "list_L8709_wf_set",
     "list_L8999_set_Cons_transfer",
     "product_type_L1061_Sigma_insert",
     "list_L8543_map_filter_map_filter",
     "list_L8603_is_empty_set",
     "list_L8701_trancl_set_ntrancl"]

val _ =
  check
    ("recovered source translations match corrected accounting",
     fn () =>
       List.all
         (fn (goal : benchLib.corpus_goal) =>
           case benchLib.run_goal
                  (Time.fromSeconds 5) (#recipe goal) goal of
               benchLib.SOLVED _ =>
                 not (shortfall_id benchListMap.shortfalls (#id goal))
             | benchLib.TIMEOUT =>
                 shortfall_id benchListMap.shortfalls (#id goal)
             | benchLib.FAILED message =>
                 if shortfall_id benchListMap.shortfalls (#id goal) then true
                 else
                   (print ("\n" ^ #id goal ^ ": " ^ message ^ "\n");
                    false))
         translated_recovered_goals)

val promoted_recovered_schema_goals =
  [retarget_goal "schema-abort-empty-card"
     ``parityTranslation$source_abort_empty_set
         (\domain : num set. CARD domain) = 0``
     (goal_named "list_L3349_anon_L3349" benchListMap.goals),
   retarget_goal "schema-fold-image-taken-prefix"
     ``!aggregate operation top function count xs.
         (!ys.
            aggregate (LIST_TO_SET ys) =
            parityTranslation$source_fold operation ys top) ==>
         parityTranslation$source_INF aggregate function
           (LIST_TO_SET (TAKE count xs)) =
         parityTranslation$source_fold
           (\value current. operation (function value) current)
           (TAKE count xs) top``
     (goal_named "list_L3381_anon_L3381" benchListMap.goals),
   retarget_goal "schema-shuffle-two-singletons"
     ``[1; 2] IN
       parityTranslation$source_shuffles ([1] : num list) [2]``
     (goal_named "list_L5527_Nil_in_shufflesI" benchListMap.goals),
   retarget_goal "schema-subseqs-three-elements"
     ``({1; 3} : num set) IN
       IMAGE LIST_TO_SET
         (LIST_TO_SET
           (parityTranslation$source_subseqs [1; 2; 3]))``
     (goal_named "list_L5470_subset_subseqs" benchListMap.goals),
   retarget_goal "schema-lists-membership-mono"
     ``[1; 1] IN parityTranslation$source_lists ({1} : num set) ==>
       [1; 1] IN parityTranslation$source_lists ({1; 2} : num set)``
     (goal_named "list_L6972_mono_lists" benchListMap.goals),
   retarget_goal "schema-these-three-options"
     ``parityTranslation$source_these
         (LIST_TO_SET [NONE; SOME 2; SOME 3]) =
       ({2; 3} : num set)``
     (goal_named "list_L8673_these_set_code" benchListMap.goals),
   retarget_goal "schema-wf-list-lift-forward"
     ``!relation : 'a -> 'a -> bool.
         relation$WF relation ==>
         relation$WF (parityTranslation$source_listrel1 relation)``
     (goal_named "list_L7922_wf_listrel1_iff" benchListMap.goals),
   retarget_goal "schema-wf-two-measures"
     ``relation$WF
         (parityTranslation$source_measures
           [I : num -> num; SUC])``
     (goal_named "list_L7771_wf_measures" benchListMap.goals),
   retarget_goal "schema-lexord-transitive-lift"
     ``!relation : 'a -> 'a -> bool.
         relation$transitive relation ==>
         !left middle right.
           parityTranslation$source_lexord relation [left] [middle] ==>
           parityTranslation$source_lexord relation [middle] [right] ==>
           parityTranslation$source_lexord relation [left] [right]``
     (goal_named "list_L7508_lexord_trans" benchListMap.goals),
   retarget_goal "schema-listrel-concrete-index"
     ``!relation xs ys count.
         (LIST_REL relation (TAKE count xs) (TAKE count ys) <=>
          LENGTH (TAKE count xs) = LENGTH (TAKE count ys) /\
          !index.
            index < LENGTH (TAKE count xs) ==>
            relation
              (EL index (TAKE count xs))
              (EL index (TAKE count ys)))``
     (goal_named "list_L7954_listrel_iff_nth" benchListMap.goals),
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
         source_outcomes = 1061 andalso source_outcomes + 11 = 1072
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
       OS.Process.getEnv "HOLBENCHNOBATTERY" = SOME "1" orelse
       benchLib.selftest_level () < 2 orelse
       read_all "../PARITY.md" = parityLib.render ())
