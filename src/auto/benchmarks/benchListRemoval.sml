structure benchListRemoval =
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

val removeAll_filter_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_removeAll_filter"
        parityTranslationTheory.source_removeAll_filter)]

fun fold_context commute_name commute =
  [benchLib.IntroAdd
     (benchLib.SafeRule,
      named "parityTranslation$source_foldr_fold"
        parityTranslationTheory.source_foldr_fold),
   benchLib.FactAdd (named commute_name commute)]

val mset_context =
  [benchLib.DefinitionAdd
     (named "parityTranslation$source_minus_list_mset_def"
        parityTranslationTheory.source_minus_list_mset_def),
   benchLib.DefinitionAdd
     (named "parityTranslation$source_foldr_def"
        parityTranslationTheory.source_foldr_def)]

val set_context =
  [benchLib.DefinitionAdd
     (named "parityTranslation$source_minus_list_set_def"
        parityTranslationTheory.source_minus_list_set_def),
   benchLib.DefinitionAdd
     (named "parityTranslation$source_foldr_def"
        parityTranslationTheory.source_foldr_def)]

val extract_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_extract_none_splitp"
        parityTranslationTheory.source_extract_none_splitp),
   benchLib.RewriteAdd
     (named "parityTranslation$source_extract_some_splitp"
        parityTranslationTheory.source_extract_some_splitp),
   benchLib.RewriteAdd
     (named "parityTranslation$source_splitp_none"
        parityTranslationTheory.source_splitp_none),
   benchLib.RewriteAdd
     (named "parityTranslation$source_splitp_some"
        parityTranslationTheory.source_splitp_some),
   benchLib.RewriteAdd
     (named "combin$o_DEF" combinTheory.o_DEF)]

val goals =
  [entry "list_L4628_extract_None_iff" 4628
     "by (auto simp: extract_def split: list.splits)"
     (benchLib.Invoke (benchLib.Auto, extract_context))
     ``!predicate xs.
         (parityTranslation$source_extract predicate xs = NONE <=>
          ~(?value. MEM value xs /\ predicate value))``,
   entry "list_L4632_extract_SomeE" 4632
     "by (auto simp: extract_def split: list.splits)"
     (benchLib.Invoke (benchLib.Auto, extract_context))
     ``!predicate xs prefix value suffix.
         parityTranslation$source_extract predicate xs =
           SOME (prefix, value, suffix) ==>
         xs = prefix ++ value::suffix /\ predicate value /\
         ~(?item. MEM item prefix /\ predicate item)``,
   entry "list_L4637_extract_Some_iff" 4637
     "by (auto simp: extract_def dest: set_takeWhileD split: list.splits)"
     (benchLib.Invoke (benchLib.Auto, extract_context))
     ``!predicate xs prefix value suffix.
         (parityTranslation$source_extract predicate xs =
            SOME (prefix, value, suffix) <=>
          xs = prefix ++ value::suffix /\ predicate value /\
          ~(?item. MEM item prefix /\ predicate item))``,
   entry "list_L4642_extract_Nil_code" 4642
     "by (simp add: extract_def)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_extract_rec"
              parityTranslationTheory.source_extract_rec)]))
     ``!predicate.
         parityTranslation$source_extract predicate [] = NONE``,
   entry "list_L4645_extract_Cons_code" 4645
     "by (auto simp add: extract_def comp_def split: list.splits)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_extract_rec"
              parityTranslationTheory.source_extract_rec)]))
     ``!predicate head tail.
         parityTranslation$source_extract predicate (head::tail) =
         if predicate head then SOME ([], head, tail)
         else
           case parityTranslation$source_extract predicate tail of
             NONE => NONE
           | SOME (prefix, value, suffix) =>
               SOME (head::prefix, value, suffix)``,
   entry "list_L4707_foldr_fold_remove1" 4707 "by fastforce"
     (benchLib.Invoke
       (benchLib.Fastforce,
        fold_context
          "parityTranslation$source_remove1_commute"
          parityTranslationTheory.source_remove1_commute))
     ``parityTranslation$source_foldr
          parityTranslation$source_remove1 =
        parityTranslation$source_fold
          parityTranslation$source_remove1``,
   entry "list_L4742_distinct_removeAll" 4742
     "by (simp add: removeAll_filter_not_eq)"
     (benchLib.Invoke
       (benchLib.Simp,
        removeAll_filter_context @
        [benchLib.RewriteAdd
           (named "list$FILTER_ALL_DISTINCT"
              listTheory.FILTER_ALL_DISTINCT)]))
     ``!xs value.
         ALL_DISTINCT xs ==>
         ALL_DISTINCT
           (parityTranslation$source_removeAll value xs)``,
   entry "list_L4758_length_removeAll_less_eq" 4758
     "by (simp add: removeAll_filter_not_eq)"
     (benchLib.Invoke
       (benchLib.Simp,
        removeAll_filter_context @
        [benchLib.RewriteAdd
           (named "rich_list$LENGTH_FILTER_LEQ"
              rich_listTheory.LENGTH_FILTER_LEQ)]))
     ``!xs value.
         LENGTH (parityTranslation$source_removeAll value xs) <=
         LENGTH xs``,
   entry "list_L4762_length_removeAll_less" 4762
     "by (auto dest: length_filter_less simp add: removeAll_filter_not_eq)"
     (benchLib.Invoke
       (benchLib.Auto,
        removeAll_filter_context @
        [benchLib.RewriteAdd
           (named "list$EXISTS_MEM" listTheory.EXISTS_MEM),
         benchLib.RewriteAdd
           (named "combin$o_DEF" combinTheory.o_DEF),
         benchLib.IntroAdd
           (benchLib.SafeRule,
            named "rich_list$LENGTH_FILTER_LESS"
              rich_listTheory.LENGTH_FILTER_LESS)]))
     ``!xs value.
         MEM value xs ==>
         LENGTH (parityTranslation$source_removeAll value xs) <
         LENGTH xs``,
   entry "list_L4781_foldr_fold_removeAll" 4781 "by fastforce"
     (benchLib.Invoke
       (benchLib.Fastforce,
        fold_context
          "parityTranslation$source_removeAll_commute"
          parityTranslationTheory.source_removeAll_commute))
     ``parityTranslation$source_foldr
          parityTranslation$source_removeAll =
        parityTranslation$source_fold
          parityTranslation$source_removeAll``,
   entry "list_L4793_minus_list_mset_Nil2" 4793
     "by (simp add: minus_list_mset_def)"
     (benchLib.Invoke (benchLib.Simp, mset_context))
     ``!xs.
         parityTranslation$source_minus_list_mset xs [] = xs``,
   entry "list_L4796_minus_list_mset_Cons2" 4796
     "by (simp add: minus_list_mset_def)"
     (benchLib.Invoke (benchLib.Simp, mset_context))
     ``!xs value ys.
         parityTranslation$source_minus_list_mset
           xs (value::ys) =
         parityTranslation$source_remove1 value
           (parityTranslation$source_minus_list_mset xs ys)``,
   entry "list_L4857_minus_list_set_Cons2" 4857
     "by (simp add: minus_list_set_def)"
     (benchLib.Invoke (benchLib.Simp, set_context))
     ``!xs value ys.
         parityTranslation$source_minus_list_set
           xs (value::ys) =
         parityTranslation$source_removeAll value
           (parityTranslation$source_minus_list_set xs ys)``]

val shortfalls : benchLib.shortfall list = []

end
