structure benchListAdjacent =
struct

open HolKernel

val commit = "f7e02b7e"

fun named name theorem : benchLib.named_thm =
  {name = name, theorem = theorem}

fun entry id line method recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = recipe, excl = [], provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = false}

val successively_nth_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_successively_conv_nth"
        parityTranslationTheory.source_successively_conv_nth)]

val distinct_nth_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_distinct_adj_def"
        parityTranslationTheory.source_distinct_adj_def),
   benchLib.RewriteAdd
     (named "parityTranslation$source_successively_conv_nth"
        parityTranslationTheory.source_successively_conv_nth)]

val distinct_rec_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_distinct_adj_def"
        parityTranslationTheory.source_distinct_adj_def),
   benchLib.RewriteAdd
     (named "parityTranslation$source_successively_nil"
        parityTranslationTheory.source_successively_nil),
   benchLib.RewriteAdd
     (named "parityTranslation$source_successively_singleton"
        parityTranslationTheory.source_successively_singleton),
   benchLib.RewriteAdd
     (named "parityTranslation$source_successively_cons_cons"
        parityTranslationTheory.source_successively_cons_cons)]

val append_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_distinct_adj_def"
        parityTranslationTheory.source_distinct_adj_def),
   benchLib.RewriteAdd
     (named "parityTranslation$source_successively_append_iff"
        parityTranslationTheory.source_successively_append_iff)]

val append_dest_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_distinct_adj_append_iff"
        parityTranslationTheory.source_distinct_adj_append_iff)]

val map_context =
  [benchLib.FactAdd
     (named "parityTranslation$source_distinct_adj_mapI"
        parityTranslationTheory.source_distinct_adj_mapI),
   benchLib.FactAdd
     (named "parityTranslation$source_distinct_adj_mapD"
        parityTranslationTheory.source_distinct_adj_mapD)]

val goals =
  [entry "list_L4319_successively_nth" 4319 "by blast"
     (benchLib.AllGoals
       (benchLib.Invoke (benchLib.Simp, successively_nth_context),
        benchLib.Invoke (benchLib.Blast, [])))
     ``!relation xs i.
         parityTranslation$source_successively relation xs ==>
         i + 1 < LENGTH xs ==>
         relation (EL i xs) (EL (i + 1) xs)``,
   entry "list_L4322_distinct_adj_conv_nth" 4322
     "by (simp add: distinct_adj_def successively_conv_nth)"
     (benchLib.Invoke (benchLib.Simp, distinct_nth_context))
     ``!xs.
         parityTranslation$source_distinct_adj xs <=>
         !i. i + 1 < LENGTH xs ==> EL i xs <> EL (i + 1) xs``,
   entry "list_L4326_distinct_adj_nth" 4326 "by blast"
     (benchLib.AllGoals
       (benchLib.Invoke
         (benchLib.Simp,
          [benchLib.RewriteAdd
             (named "parityTranslation$source_distinct_adj_conv_nth"
                parityTranslationTheory.source_distinct_adj_conv_nth)]),
        benchLib.Invoke (benchLib.Blast, [])))
     ``!xs i.
         parityTranslation$source_distinct_adj xs ==>
         i + 1 < LENGTH xs ==> EL i xs <> EL (i + 1) xs``,
   entry "list_L4406_distinct_adj_Nil" 4406
     "by (auto simp: distinct_adj_def)"
     (benchLib.Invoke (benchLib.Auto, distinct_rec_context))
     ``parityTranslation$source_distinct_adj ([] : 'a list)``,
   entry "list_L4406_distinct_adj_singleton" 4406
     "by (auto simp: distinct_adj_def)"
     (benchLib.Invoke (benchLib.Auto, distinct_rec_context))
     ``!x. parityTranslation$source_distinct_adj [x]``,
   entry "list_L4406_distinct_adj_Cons_Cons" 4406
     "by (auto simp: distinct_adj_def)"
     (benchLib.Invoke (benchLib.Auto, distinct_rec_context))
     ``!x y xs.
         parityTranslation$source_distinct_adj (x::y::xs) <=>
         x <> y /\
         parityTranslation$source_distinct_adj (y::xs)``,
   entry "list_L4431_distinct_adj_rev" 4431
     "by (simp add: distinct_adj_def eq_commute)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_distinct_adj_def"
              parityTranslationTheory.source_distinct_adj_def),
         benchLib.DefinitionAdd
           (named "parityTranslation$source_successively_def"
              parityTranslationTheory.source_successively_def),
         benchLib.RewriteAdd
           (named "list$adjacent_REVERSE"
              listTheory.adjacent_REVERSE)]))
     ``!xs.
         parityTranslation$source_distinct_adj (REVERSE xs) <=>
         parityTranslation$source_distinct_adj xs``,
   entry "list_L4434_distinct_adj_append_iff" 4434
     "by (auto simp: distinct_adj_def successively_append_iff)"
     (benchLib.Invoke (benchLib.Auto, append_context))
     ``!xs ys.
         parityTranslation$source_distinct_adj (xs ++ ys) <=>
         parityTranslation$source_distinct_adj xs /\
         parityTranslation$source_distinct_adj ys /\
         (xs = [] \/ ys = [] \/ LAST xs <> HD ys)``,
   entry "list_L4439_distinct_adj_appendD1" 4439
     "by (auto simp: distinct_adj_append_iff)"
     (benchLib.Invoke (benchLib.Auto, append_dest_context))
     ``!xs ys.
         parityTranslation$source_distinct_adj (xs ++ ys) ==>
         parityTranslation$source_distinct_adj xs``,
   entry "list_L4439_distinct_adj_appendD2" 4439
     "by (auto simp: distinct_adj_append_iff)"
     (benchLib.Invoke (benchLib.Auto, append_dest_context))
     ``!xs ys.
         parityTranslation$source_distinct_adj (xs ++ ys) ==>
         parityTranslation$source_distinct_adj ys``,
   entry "list_L4450_distinct_adj_map_iff" 4450 "by blast"
     (benchLib.Invoke (benchLib.Blast, map_context))
     ``!function xs.
         parityTranslation$source_inj_on
           function (LIST_TO_SET xs) ==>
         (parityTranslation$source_distinct_adj
            (MAP function xs) <=>
          parityTranslation$source_distinct_adj xs)``]

val shortfalls : benchLib.shortfall list = []

end
