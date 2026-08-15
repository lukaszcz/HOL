structure benchListMap =
struct

val goals =
  map benchLib.sanitize_goal
    (benchListCorpus.goals @ benchListSorted.goals @
     benchListNumeric.goals @
     benchListAdjacent.goals @
     benchListRemoval.goals @
     benchListIndexed.goals @
     benchListRotate.goals @
     benchListNths.goals @
     benchListOrder.goals @
     benchRecovered.goals @
     benchListIntervals.goals @
     benchListCode.goals @
     benchListRel1.goals @
     benchMeasures.goals @
     benchListLex.goals @
     benchListRelations.goals @
     benchMapCorpus.goals @
     benchOptionCorpus.goals @
     benchStringCorpus.goals @
     benchProductCorpus.goals)

val shortfalls : benchLib.shortfall list =
  benchLibraryShortfalls.translation @ benchLibraryShortfalls.execution

fun run level =
  benchLib.run_family
    {family = "listmap", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Auto, benchLib.Aesop], level = level}

end
