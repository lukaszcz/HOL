structure benchListCode =
struct

open HolKernel

fun named name theorem : benchLib.named_thm =
  {name = name, theorem = theorem}

fun entry id line method recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = recipe, excl = [], provenance =
     {file = "src/HOL/List.thy", line = line, commit = "f7e02b7e"},
   representative = false}

val can_select_context =
  [benchLib.DefinitionAdd
     (named "parityTranslation$source_can_select_def"
        parityTranslationTheory.source_can_select_def),
   benchLib.DefinitionAdd
     (named "parityTranslation$source_list_ex1_def"
        parityTranslationTheory.source_list_ex1_def)]

val goals =
  [entry "list_L8199_list_ex1_Nil_iff" 8199
     "by (auto simp add: list_ex1_iff)"
     (benchLib.Invoke (benchLib.Auto, can_select_context))
     ``!predicate.
         ~parityTranslation$source_list_ex1 predicate []``,
   entry "list_L8203_list_ex1_Cons_iff" 8203
     "by (auto simp add: list_ex1_iff list_all_iff)"
     (benchLib.Invoke
       (benchLib.Auto,
        can_select_context @
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_list_all_def"
              parityTranslationTheory.source_list_all_def)]))
     ``!predicate value xs.
         (parityTranslation$source_list_ex1 predicate (value::xs) <=>
          if predicate value then
            parityTranslation$source_list_all
              (\other. ~predicate other \/ value = other) xs
          else
            parityTranslation$source_list_ex1 predicate xs)``,
   entry "list_L8673_these_set_code" 8673
     ("by (simp add: Option.these_eq Option.is_none_def set_eq_iff " ^
      "map_filter_def)")
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_these_list_to_set"
              parityTranslationTheory.source_these_list_to_set)]))
     ``!xs.
         parityTranslation$source_these (LIST_TO_SET xs) =
         LIST_TO_SET (parityTranslation$source_map_filter I xs)``,
   entry "list_L8683_can_select_set_list_ex1" 8683
     "by (simp add: list_ex1_iff)"
     (benchLib.Invoke (benchLib.Simp, can_select_context))
     ``!predicate xs.
         (parityTranslation$source_can_select
            predicate (LIST_TO_SET xs) =
          parityTranslation$source_list_ex1 predicate xs)``,
   entry "list_L8691_Id_on_set" 8691
     "by (auto simp add: Id_on_def)"
     (benchLib.Invoke
       (benchLib.Auto,
         [benchLib.DefinitionAdd
           (named "parityTranslation$source_Id_on_def"
              parityTranslationTheory.source_Id_on_def),
         benchLib.DefinitionAdd
           (named "pred_set$EXTENSION" pred_setTheory.EXTENSION),
         benchLib.RewriteAdd
           (named "list$MEM_MAP" listTheory.MEM_MAP)]))
     ``!xs.
         parityTranslation$source_Id_on (LIST_TO_SET xs) =
         LIST_TO_SET (MAP (\value. (value, value)) xs)``,
   entry "list_L8701_trancl_set_ntrancl" 8701
     "by (simp add: finite_trancl_ntranl)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_trancl_set_ntrancl"
              parityTranslationTheory.source_trancl_set_ntrancl)]))
     ``!pairs.
         relation$TC
           (parityTranslation$source_list_relation pairs) =
         parityTranslation$source_ntrancl
           (CARD (LIST_TO_SET pairs) - 1)
           (parityTranslation$source_list_relation pairs)``,
   entry "list_L9009_null_transfer" 9009
     "unfolding rel_fun_def by auto"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.RewriteAdd
           (named "list$NULL_LENGTH" listTheory.NULL_LENGTH),
         benchLib.DestAdd
           (benchLib.SafeRule,
            named "list$LIST_REL_LENGTH"
              listTheory.LIST_REL_LENGTH)]))
     ``!relation xs ys.
         LIST_REL relation xs ys ==> (NULL xs = NULL ys)``]

val shortfalls : benchLib.shortfall list = []

end
