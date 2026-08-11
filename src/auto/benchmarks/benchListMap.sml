structure benchListMap =
struct

val goals =
  benchListCorpus.goals @ benchMapCorpus.goals @
  benchOptionCorpus.goals @
  benchStringCorpus.goals @
  benchProductCorpus.goals

val shortfalls : benchLib.shortfall list =
  benchLibraryShortfalls.translation @ benchLibraryShortfalls.execution

fun run level =
  benchLib.run_family
    {family = "listmap", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Auto, benchLib.Aesop], level = level}

end
