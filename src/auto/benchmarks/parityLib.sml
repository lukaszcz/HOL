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

fun representative_count goals =
  length
    (List.filter
      (fn ({representative, ...} : benchLib.corpus_goal) =>
        representative)
      goals)

fun total_size families =
  List.foldl
    (fn ({size, ...} : family, total) => size + total)
    0 families

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

fun family_row ({name, size, slice, shortfalls, run} : family) =
  let
    val result = run 2
    val gated = #gated result
    val battery = #battery result
    val accepted = count_cause benchLib.AcceptedGap shortfalls
    val engine = count_cause benchLib.EngineLimitation shortfalls
    val translation = count_cause benchLib.TranslationGap shortfalls
    val under = count_cause benchLib.UnderIteration shortfalls
    fun number value = Int.toString value
  in
    "| " ^ name ^ " | " ^ number size ^ " | " ^
    number (solved gated) ^ " | " ^ number slice ^ " | " ^
    number accepted ^ "/" ^ number engine ^ "/" ^
    number translation ^ "/" ^ number under ^ " | " ^
    number (battery_count benchLib.Auto battery) ^ " | " ^
    number (battery_count benchLib.Blast battery) ^ " | " ^
    number (battery_count benchLib.Aesop battery) ^ " |\n"
  end

fun render () =
  let
    val total = Int.toString (total_size families)
  in
    String.concat
    (["# Isabelle-method parity\n\n",
      "Generated deterministically from the Phase-8 benchmark modules. ",
      "The pinned Isabelle mirror is `f7e02b7e`; the per-goal budget is ",
      "30 seconds and the measurement date is 2026-08-11.\n\n",
      "This report covers the exhaustive ", total,
      "-goal executable corpus. The pinned source contributes 1,061 ",
      "accounted outcomes after nine documented HOL4 `aconv` collapses; ",
      "eleven additional goals come from HOL4's integer regression ",
      "suite. Translation gaps remain explicit shortfalls.\n\n",
      "The shortfall column is ",
      "`accepted/engine/translation/under-iteration`. Battery columns ",
      "are recorded observations and do not gate the build.\n\n",
      "| Family | Goals | Gated solved | L1 slice | Shortfalls | ",
      "AUTO | BLAST | AESOP |\n",
      "|---|---:|---:|---:|---:|---:|---:|---:|\n"] @
     map family_row families @
     ["\nThe seed inversion audit currently requires no waivers. ",
      "Corpus provenance is carried by each benchmark entry and points ",
      "to the pinned files under `src/HOL/`.\n"])
  end

fun write path =
  let
    val stream = TextIO.openOut path
    val _ = TextIO.output (stream, render ())
  in
    TextIO.closeOut stream
  end

end
