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
   source_method = "simp", mapped = benchLib.Simp, excl = [],
   provenance = provenance, representative = true}

val failed_goal : benchLib.corpus_goal =
  {id = "unit-failed", goal = p,
   source_method = "simp", mapped = benchLib.Simp, excl = [],
   provenance = provenance, representative = true}

val duplicate_solved_goal : benchLib.corpus_goal =
  {id = "unit-solved-duplicate", goal = boolSyntax.T,
   source_method = "simp", mapped = benchLib.Simp, excl = [],
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
         (benchLib.run_goal (Time.fromSeconds 5) benchLib.Simp solved_goal))

val _ =
  check
    ("benchmark harness enforces a zero time budget",
     fn () =>
       case benchLib.run_goal Time.zeroTime benchLib.Simp solved_goal of
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
   source_method = "blast", mapped = benchLib.Blast,
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
       count_cause benchLib.EngineLimitation benchSets.shortfalls = 123 andalso
       count_cause benchLib.TranslationGap benchSets.shortfalls = 4 andalso
       count_cause benchLib.EngineLimitation benchListMap.shortfalls = 259 andalso
       count_cause benchLib.TranslationGap benchListMap.shortfalls = 191)

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
         (if benchLib.selftest_level () >= 2 then 349 else 4)
         benchSets.run)

val _ =
  check
    ("list/map mined-corpus representative slice is exact",
     fn () =>
       not (family_selected "listmap") orelse
       family_ok
         (if benchLib.selftest_level () >= 2 then 413 else 5)
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
         (if benchLib.selftest_level () >= 2 then 7 else 3)
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
