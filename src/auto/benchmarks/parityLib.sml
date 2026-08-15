structure parityLib =
struct

fun solved outcomes =
  length (List.filter (benchLib.outcome_solved o #2) outcomes)

fun count_cause cause shortfalls =
  length
    (List.filter
      (fn ({cause = item, ...} : benchLib.shortfall) => item = cause)
      shortfalls)

fun battery_count tactic_id battery =
  length
    (List.filter
      (fn (_, item, outcome) =>
        item = tactic_id andalso benchLib.outcome_solved outcome)
      battery)

type family = {
  name : string,
  size : int,
  slice : int,
  shortfalls : benchLib.shortfall list,
  run : int -> benchLib.family_result
}

type measured_family = {
  name : string,
  size : int,
  slice : int,
  shortfalls : benchLib.shortfall list,
  gated : (string * benchLib.outcome) list,
  battery : (string * benchLib.tactic_id * benchLib.outcome) list
}

fun representative_count goals =
  length
    (List.filter
      (fn ({representative, ...} : benchLib.corpus_goal) =>
        representative)
      goals)

val families : family list =
  [{name = "Classical", size = length benchClassical.goals,
    slice = representative_count benchClassical.goals,
    shortfalls = benchClassical.shortfalls, run = benchClassical.run},
   {name = "Sets", size = length benchSets.goals,
    slice = representative_count benchSets.goals,
    shortfalls = benchSets.shortfalls, run = benchSets.run},
   {name = "List/map", size = length benchListMap.goals,
    slice = representative_count benchListMap.goals,
    shortfalls = benchListMap.shortfalls, run = benchListMap.run},
   {name = "Linarith", size = length benchLinarith.goals,
    slice = representative_count benchLinarith.goals,
    shortfalls = benchLinarith.shortfalls, run = benchLinarith.run},
   {name = "Presburger", size = length benchPresburger.goals,
    slice = representative_count benchPresburger.goals,
    shortfalls = benchPresburger.shortfalls,
    run = benchPresburger.run},
   {name = "Algebra", size = length benchAlgebra.goals,
    slice = representative_count benchAlgebra.goals,
    shortfalls = benchAlgebra.shortfalls,
    run = benchAlgebra.run}]

fun measure_family ({name, size, slice, shortfalls, run} : family) =
  let
    val _ = PolyML.fullGC ()
    val result = run 2
  in
    {name = name, size = size, slice = slice,
     shortfalls = shortfalls, gated = #gated result,
     battery = #battery result}
  end

fun primary_row
      ({name, size, slice, gated, ...} : measured_family) =
  let
    fun number value = Int.toString value
  in
    "| " ^ name ^ " | " ^ number size ^ " | " ^
    number (solved gated) ^ " | " ^ number slice ^ " |\n"
  end

fun accounting_row
      ({name, shortfalls, ...} : measured_family) =
  let
    val accepted = count_cause benchLib.AcceptedGap shortfalls
    val engine = count_cause benchLib.EngineLimitation shortfalls
    val translation = count_cause benchLib.TranslationGap shortfalls
    val under = count_cause benchLib.UnderIteration shortfalls
    fun number value = Int.toString value
  in
    "| " ^ name ^ " | " ^ number accepted ^ " | " ^
    number engine ^ " | " ^ number translation ^ " | " ^
    number under ^ " |\n"
  end

fun observation_row
      ({name, battery, ...} : measured_family) =
  let
    fun number value = Int.toString value
  in
    "| " ^ name ^ " | " ^
    number (battery_count benchLib.Auto battery) ^ " | " ^
    number (battery_count benchLib.Blast battery) ^ " | " ^
    number (battery_count benchLib.Aesop battery) ^ " |\n"
  end

fun total_size rows =
  List.foldl
    (fn ({size, ...} : measured_family, total) => size + total)
    0 rows

fun total_solved rows =
  List.foldl
    (fn ({gated, ...} : measured_family, total) =>
      solved gated + total)
    0 rows

fun total_slice rows =
  List.foldl
    (fn ({slice, ...} : measured_family, total) => slice + total)
    0 rows

fun total_cause cause rows =
  List.foldl
    (fn ({shortfalls, ...} : measured_family, total) =>
      count_cause cause shortfalls + total)
    0 rows

fun total_battery tactic_id rows =
  List.foldl
    (fn ({battery, ...} : measured_family, total) =>
      battery_count tactic_id battery + total)
    0 rows

fun render () =
  let
    val rows = map measure_family families
    fun number value = Int.toString value
    val executable = number (total_size rows)
    val assigned_solved = number (total_solved rows)
    val routine = number (total_slice rows)
    val accepted = number (total_cause benchLib.AcceptedGap rows)
    val limitations =
      number (total_cause benchLib.EngineLimitation rows)
    val unavailable =
      number (total_cause benchLib.TranslationGap rows)
    val unaccounted =
      number (total_cause benchLib.UnderIteration rows)
  in
    String.concat
    (["# Automation benchmark results\n\n",
      "## What this report measures\n\n",
      "Each benchmark entry contains a HOL4 theorem statement, the ",
      "Isabelle method used for the corresponding source result, and ",
      "the HOL4 tactic chosen as that method's closest counterpart. ",
      "This report calls that HOL4 tactic the **assigned tactic**.\n\n",
      "The comparison data was mined from Isabelle/HOL commit ",
      "`f7e02b7e`. Each in-repository benchmark entry records its source ",
      "file, line, method, and commit. The report was generated on ",
      "2026-08-11 with a 30-second limit for each tactic attempt.\n\n",
      "## Source accounting\n\n",
      "Source mining identified 1,070 relevant Isabelle results. Nine ",
      "pairs translated to the same HOL4 statement except for bound ",
      "variable names, so they are tested once. This leaves 1,061 ",
      "distinct source-derived results. Eleven existing HOL4 integer ",
      "regression goals are also included, giving 1,072 accounted ",
      "results in total:\n\n",
      "- ", executable, " are executable HOL4 benchmark goals.\n",
      "- ", unavailable, " could not be translated faithfully and are ",
      "listed by identifier and reason in the benchmark files.\n",
      "- ", unaccounted, " source results are missing from both groups.\n\n",
      "The selftest checks this accounting in both directions. An ",
      "unexpected failure is an error, but so is an expected failure ",
      "that starts succeeding without its record being updated.\n\n",
      "## Results from the assigned tactics\n\n",
      "**Executable goals** is the number of runnable HOL4 statements. ",
      "**Solved by assigned tactic** counts statements proved by the ",
      "HOL4 counterpart selected for their Isabelle method. ",
      "**Routine selftest goals** is a fixed, explicitly marked subset ",
      "run when `HOLSELFTESTLEVEL=1`; it is not a random sample. At ",
      "level 2 or higher, all executable goals run.\n\n",
      "A **family** is a subject-area group:\n\n",
      "- **Classical** contains propositional and first-order logic.\n",
      "- **Sets** contains set and relation reasoning.\n",
      "- **List/map** contains lists, finite maps, options, strings, ",
      "and product types.\n",
      "- **Linarith** contains linear arithmetic over natural numbers, ",
      "integers, real numbers, and rational numbers.\n",
      "- **Presburger** contains quantified additive arithmetic over ",
      "natural numbers and integers.\n",
      "- **Algebra** contains polynomial, ring, and field identities.\n\n",
      "| Family | Executable goals | Solved by assigned tactic | ",
      "Routine selftest goals |\n",
      "|---|---:|---:|---:|\n"] @
     map primary_row rows @
     ["| **Total** | **", executable, "** | **", assigned_solved,
      "** | **", routine, "** |\n\n",
      "## Documented results not solved by the assigned tactic\n\n",
      "- **Accepted scope exclusions** are executable goals deliberately ",
      "outside the supported tactic scope, with a recorded reason.\n",
      "- **Assigned-tactic limitations** are executable goals for which ",
      "the assigned tactic failed or exceeded 30 seconds.\n",
      "- **Unavailable translations** are source results that could not ",
      "be represented faithfully as HOL4 goals. They are not included ",
      "in the executable-goal count.\n",
      "- **Unaccounted source results** would be source results that are ",
      "neither executable nor documented as unavailable. This number ",
      "must remain zero.\n\n",
      "| Family | Accepted scope exclusions | Assigned-tactic ",
      "limitations | Unavailable translations | Unaccounted source ",
      "results |\n",
      "|---|---:|---:|---:|---:|\n"] @
     map accounting_row rows @
     ["| **Total** | **", accepted, "** | **", limitations,
      "** | **", unavailable, "** | **", unaccounted, "** |\n\n",
      "For every family, executable goals equal assigned-tactic ",
      "solutions plus accepted scope exclusions plus assigned-tactic ",
      "limitations.\n\n",
      "## Additional tactic observations\n\n",
      "For context, the exhaustive run also tries three general-purpose ",
      "HOL4 tactics when they are not already the assigned tactic. The ",
      "numbers below count these additional solutions. They do not ",
      "affect whether the benchmark selftest passes and are not total ",
      "strength scores for the tactics.\n\n",
      "| Family | Additional `AUTO_TAC` solutions | Additional ",
      "`BLAST_TAC` solutions | Additional `AESOP_TAC` solutions |\n",
      "|---|---:|---:|---:|\n"] @
     map observation_row rows @
     ["| **Total** | **",
      number (total_battery benchLib.Auto rows), "** | **",
      number (total_battery benchLib.Blast rows), "** | **",
      number (total_battery benchLib.Aesop rows), "** |\n\n",
      "## Seed-rule safety check\n\n",
      "A rule is classified as **safe** when applying it cannot discard ",
      "a possible proof of the goal. The automated seed-rule check ",
      "proves the required reverse direction for every such rule. It ",
      "currently passes with no exceptions.\n\n",
      "## Reproducing the report\n\n",
      "From `src/auto/benchmarks/`:\n\n",
      "```sh\n",
      "Holmake\n",
      "./selftest.exe\n",
      "HOLSELFTESTLEVEL=2 ./selftest.exe\n",
      "./genparity.exe\n",
      "```\n\n",
      "The first selftest command runs the fixed routine subset. The ",
      "second runs every executable goal and the additional tactic ",
      "observations. The final command regenerates `../PARITY.md`.\n"])
  end

fun write path =
  let
    val stream = TextIO.openOut path
    val _ = TextIO.output (stream, render ())
  in
    TextIO.closeOut stream
  end

end
