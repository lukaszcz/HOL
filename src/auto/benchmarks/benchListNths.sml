structure benchListNths =
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

val definition_context =
  [benchLib.DefinitionAdd
     (named "parityTranslation$source_nths_def"
        parityTranslationTheory.source_nths_def)]

val representation_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_nths_filter_bridge"
        parityTranslationTheory.source_nths_filter_bridge)]

val membership_context =
  representation_context @
  [benchLib.IntroAdd
     (benchLib.SafeRule,
      named "parityTranslation$source_map_el_filter_count_mem"
        parityTranslationTheory.source_map_el_filter_count_mem)]

val goals =
  [entry "list_L5334_nths_empty" 5334
     "by (auto simp add: nths_def)"
     (benchLib.Invoke (benchLib.Simp, representation_context))
     ``!xs. parityTranslation$source_nths xs EMPTY = []``,
   entry "list_L5337_nths_nil" 5337
     "by (auto simp add: nths_def)"
     (benchLib.Invoke (benchLib.Simp, definition_context))
     ``!indices. parityTranslation$source_nths [] indices = []``,
   entry "list_L5344_length_nths" 5344
     "by(simp add: nths_def length_filter_conv_card cong:conj_cong)"
     (benchLib.Invoke
       (benchLib.Simp,
        representation_context @
        [benchLib.RewriteAdd
           (named "parityTranslation$source_length_filter_count"
              parityTranslationTheory.source_length_filter_count)]))
     ``!xs indices.
         LENGTH (parityTranslation$source_nths xs indices) =
         CARD {index | index < LENGTH xs /\ index IN indices}``,
   entry "list_L5385_set_nths_subset" 5385
     "by(auto simp add:set_nths)"
     (benchLib.Invoke (benchLib.Auto, membership_context))
     ``!xs indices.
         LIST_TO_SET (parityTranslation$source_nths xs indices)
           SUBSET LIST_TO_SET xs``,
   entry "list_L5388_notin_set_nthsI" 5388
     "by(auto simp add:set_nths)"
     (benchLib.Invoke (benchLib.Auto, membership_context))
     ``!value xs indices.
         ~MEM value xs ==>
         ~MEM value (parityTranslation$source_nths xs indices)``,
   entry "list_L5391_in_set_nthsD" 5391
     "by(auto simp add:set_nths)"
     (benchLib.Invoke (benchLib.Auto, membership_context))
     ``!value xs indices.
         MEM value (parityTranslation$source_nths xs indices) ==>
         MEM value xs``,
   entry "list_L5394_nths_singleton" 5394
     "by (simp add: nths_Cons)"
     (benchLib.Invoke (benchLib.Simp, definition_context))
     ``!value indices.
         parityTranslation$source_nths [value] indices =
         if 0 IN indices then [value] else []``,
   entry "list_L5409_nths_drop" 5409
     "by force"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_nths_drop"
              parityTranslationTheory.source_nths_drop)]))
     ``!count xs indices.
         parityTranslation$source_nths (DROP count xs) indices =
         parityTranslation$source_nths xs
           (IMAGE (\index. count + index) indices)``]

val shortfalls : benchLib.shortfall list = []

end
