structure benchStringCorpus =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun entry id line method mapped representative excl goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method, mapped = mapped,
   excl = List.filter (fn {theorem, ...} =>
     benchLib.theorem_is_goal goal theorem) excl, provenance =
     {file = "src/HOL/String.thy", line = line, commit = commit},
   representative = representative}

val goals =
  [
   entry "string_L178_card_UNIV_char" 178 "by (auto simp add: UNIV_char_of_nat card_image)" benchLib.Auto true []
     ``((CARD UNIV) = 256)``
  ]

end
