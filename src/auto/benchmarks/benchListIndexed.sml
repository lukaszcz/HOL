structure benchListIndexed =
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

val bridge =
  benchLib.RewriteAdd
    (named "parityTranslation$source_indexed_from_bridge"
       parityTranslationTheory.source_indexed_from_bridge)

val map_context =
  [bridge,
   benchLib.RewriteAdd
     (named "list$MAP_ZIP" listTheory.MAP_ZIP)]

val nth_context =
  [bridge,
   benchLib.RewriteAdd
     (named "list$EL_ZIP" listTheory.EL_ZIP),
   benchLib.RewriteAdd
     (named "list$EL_GENLIST" listTheory.EL_GENLIST)]

val distinct_context =
  [bridge,
   benchLib.RewriteAdd
     (named "parityTranslation$source_num_genlist_zip_distinct"
        parityTranslationTheory.source_num_genlist_zip_distinct)]

val append_context =
  [bridge,
   benchLib.RewriteAdd
     (named "parityTranslation$source_num_genlist_append"
        parityTranslationTheory.source_num_genlist_append),
   benchLib.RewriteAdd
     (named "rich_list$ZIP_APPEND" rich_listTheory.ZIP_APPEND)]

val goals =
  [entry "list_L5136_length_indexed_from" 5136
     "by (simp add: indexed_from_eq_zip)"
     (benchLib.Invoke (benchLib.Simp, [bridge]))
     ``!start xs.
         LENGTH (parityTranslation$source_indexed_from start xs) =
         LENGTH xs``,
   entry "list_L5140_map_fst_indexed_from" 5140
     "by (simp add: indexed_from_eq_zip)"
     (benchLib.Invoke (benchLib.Simp, map_context))
     ``!start xs.
         MAP FST (parityTranslation$source_indexed_from start xs) =
         GENLIST (\offset. start + offset) (LENGTH xs)``,
   entry "list_L5144_map_snd_indexed_from" 5144
     "by (simp add: indexed_from_eq_zip)"
     (benchLib.Invoke (benchLib.Simp, map_context))
     ``!start xs.
         MAP SND (parityTranslation$source_indexed_from start xs) = xs``,
   entry "list_L5163_nth_indexed_from_eq" 5163
     "by (simp add: indexed_from_eq_zip)"
     (benchLib.Invoke (benchLib.Simp, nth_context))
     ``!start xs index.
         index < LENGTH xs ==>
         EL index
           (parityTranslation$source_indexed_from start xs) =
         (start + index, EL index xs)``,
   entry "list_L5176_distinct_indexed_from" 5176
     "by (simp add: indexed_from_eq_zip distinct_zipI1)"
     (benchLib.Invoke (benchLib.Simp, distinct_context))
     ``!start xs.
         ALL_DISTINCT
           (parityTranslation$source_indexed_from start xs)``,
   entry "list_L5180_indexed_from_append_eq" 5180
     "by (simp add: indexed_from_eq_zip add.assoc zip_append2)"
     (benchLib.Invoke (benchLib.Simp, append_context))
     ``!start xs ys.
         parityTranslation$source_indexed_from start (xs ++ ys) =
         parityTranslation$source_indexed_from start xs ++
         parityTranslation$source_indexed_from
           (start + LENGTH xs) ys``]

val shortfalls : benchLib.shortfall list = []

end
