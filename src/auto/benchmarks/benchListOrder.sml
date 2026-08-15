structure benchListOrder =
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

fun using_theorem name theorem =
  benchLib.Invoke
    (benchLib.Auto,
     [benchLib.FactAdd (named name theorem)])

val definition =
  benchLib.DefinitionAdd
    (named "parityTranslation$source_sorted_def"
       parityTranslationTheory.source_sorted_def)

val map_sorted_unique =
  parityTranslationTheory.source_map_sorted_distinct_set_unique

val strict_sorted_unique =
  parityTranslationTheory.source_strict_sorted_equal_unique

val nth_greater_than_at_most =
  parityTranslationTheory.source_nth_sorted_list_of_set_greater_than_at_most

val order_context =
  [definition,
   benchLib.RewriteAdd
     (named "parityTranslation$source_weak_linear_transitive"
        parityTranslationTheory.source_weak_linear_transitive),
   benchLib.RewriteAdd
     (named "parityTranslation$source_weak_linear_reflexive"
        parityTranslationTheory.source_weak_linear_reflexive)]

val nth_context =
  order_context @
  [benchLib.IntroAdd
     (benchLib.SafeRule,
      named "parityTranslation$source_weak_linear_reflexive"
        parityTranslationTheory.source_weak_linear_reflexive),
   benchLib.FactAdd
     (named "parityTranslation$source_weak_linear_refl"
        parityTranslationTheory.source_weak_linear_refl),
   benchLib.IntroAdd
     (benchLib.SafeRule,
      named "parityTranslation$source_weak_linear_transitive"
        parityTranslationTheory.source_weak_linear_transitive),
   benchLib.DefinitionAdd
     (named "relation$reflexive_def"
        relationTheory.reflexive_def),
   benchLib.RewriteAdd
     (named "sorting$SORTED_EL_LESS"
        sortingTheory.SORTED_EL_LESS),
   benchLib.RewriteAdd
     (named "arithmetic$LESS_OR_EQ"
        arithmeticTheory.LESS_OR_EQ)]

val goals =
  [entry "list_L6023_sorted0" 6023 "by simp"
     (benchLib.Invoke (benchLib.Simp, [definition]))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         parityTranslation$source_sorted le []``,
   entry "list_L6026_sorted1" 6026 "by simp"
     (benchLib.Invoke (benchLib.Simp, [definition]))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !value. parityTranslation$source_sorted le [value]``,
   entry "list_L6029_sorted2" 6029 "by auto"
     (benchLib.Invoke (benchLib.Simp, [definition]))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !left right tail.
           (parityTranslation$source_sorted le
              (left::right::tail) <=>
            le left right /\
            parityTranslation$source_sorted le (right::tail))``,
   entry "list_L6034_sorted_append" 6034
     "by (simp add: sorted_wrt_append)"
     (benchLib.Invoke
       (benchLib.Simp,
        order_context @
        [benchLib.RewriteAdd
           (named "sorting$SORTED_APPEND"
              sortingTheory.SORTED_APPEND)]))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs ys.
           (parityTranslation$source_sorted le (xs ++ ys) <=>
            parityTranslation$source_sorted le xs /\
            parityTranslation$source_sorted le ys /\
            (!left right.
               MEM left xs ==> MEM right ys ==> le left right))``,
   entry "list_L6038_sorted_map" 6038
     "by (simp add: sorted_wrt_map)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_sorted_map_bridge"
              parityTranslationTheory.source_sorted_map_bridge)]))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !function xs.
           (parityTranslation$source_sorted le (MAP function xs) <=>
            parityTranslation$source_sorted
              (\left right. le (function left) (function right)) xs)``,
   entry "list_L6042_sorted01" 6042
     "by (simp add: sorted_wrt01)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.IntroAdd
           (benchLib.SafeRule,
            named "parityTranslation$source_sorted_length01"
              parityTranslationTheory.source_sorted_length01)]))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs. LENGTH xs <= 1 ==>
              parityTranslation$source_sorted le xs``,
   entry "list_L6049_sorted_iff_nth_mono_less" 6049
     "by (simp add: sorted_wrt_iff_nth_less)"
     (benchLib.Invoke (benchLib.Auto, nth_context))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs.
           (parityTranslation$source_sorted le xs <=>
            !left right.
              left < right ==> right < LENGTH xs ==>
              le (EL left xs) (EL right xs))``,
   entry "list_L6053_sorted_iff_nth_mono" 6053
     "by (auto simp: sorted_iff_nth_mono_less nat_less_le)"
     (benchLib.Invoke (benchLib.Auto, nth_context))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs.
           (parityTranslation$source_sorted le xs <=>
            !left right.
              left <= right ==> right < LENGTH xs ==>
              le (EL left xs) (EL right xs))``,
   entry "list_L6057_sorted_nth_mono" 6057
     "by (auto simp: sorted_iff_nth_mono)"
     (benchLib.Invoke (benchLib.Auto, nth_context))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs left right.
           parityTranslation$source_sorted le xs ==>
           left <= right ==> right < LENGTH xs ==>
           le (EL left xs) (EL right xs)``,
   entry "list_L6061_sorted_iff_nth_Suc" 6061
     "by(simp add: sorted_wrt_iff_nth_Suc_transp)"
     (benchLib.Invoke
       (benchLib.Simp,
        [definition,
         benchLib.RewriteAdd
           (named "sorting$SORTED_EL_SUC"
              sortingTheory.SORTED_EL_SUC)]))
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs.
           (parityTranslation$source_sorted le xs <=>
            !index. SUC index < LENGTH xs ==>
              le (EL index xs) (EL (SUC index) xs))``,
   entry "list_L6101_sorted_remove1" 6101
     "using sorted_map_remove1 [of \"\\<lambda>x. x\"] by simp"
     (using_theorem "parityTranslation$source_sorted_remove1"
        parityTranslationTheory.source_sorted_remove1)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !value xs.
           parityTranslation$source_sorted le xs ==>
           parityTranslation$source_sorted le
             (parityTranslation$source_remove1 value xs)``,
   entry "list_L6104_sorted_butlast" 6104
     "by (simp add: assms butlast_conv_take)"
     (using_theorem "parityTranslation$source_sorted_front"
        parityTranslationTheory.source_sorted_front)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs.
           parityTranslation$source_sorted le xs ==>
           parityTranslation$source_sorted le (FRONT xs)``,
   entry "list_L6138_map_sorted_distinct_set_unique" 6138
     "using assms map_inj_on sorted_distinct_set_unique by fastforce"
     (using_theorem
        "parityTranslation$source_map_sorted_distinct_set_unique"
        map_sorted_unique)
     ``!le : 'b -> 'b -> bool.
         relation$WeakLinearOrder le ==>
         !function xs ys.
           parityTranslation$source_inj_on function
             (LIST_TO_SET xs UNION LIST_TO_SET ys) ==>
           parityTranslation$source_sorted le (MAP function xs) ==>
           ALL_DISTINCT (MAP function xs) ==>
           parityTranslation$source_sorted le (MAP function ys) ==>
           ALL_DISTINCT (MAP function ys) ==>
           LIST_TO_SET xs = LIST_TO_SET ys ==>
           xs = ys``,
   entry "list_L6146_sorted_dropWhile" 6146
     "by (auto dest: sorted_wrt_drop simp add: dropWhile_eq_drop)"
     (using_theorem "parityTranslation$source_sorted_dropwhile"
        parityTranslationTheory.source_sorted_dropwhile)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !predicate xs.
           parityTranslation$source_sorted le xs ==>
           parityTranslation$source_sorted le
             (dropWhile predicate xs)``,
   entry "list_L6202_sorted_same" 6202
     "using sorted_map_same [of \"\\<lambda>x. x\"] by simp"
     (using_theorem "parityTranslation$source_sorted_same"
        parityTranslationTheory.source_sorted_same)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !g xs.
           parityTranslation$source_sorted le
             (FILTER (\item. item = g xs) xs)``,
   entry "list_L6211_sorted_upto" 6211
     "by(simp add: sorted_wrt_mono_rel[OF _ sorted_wrt_upto])"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_sorted_num_upto"
              parityTranslationTheory.source_sorted_num_upto)]))
     ``!lower upper.
         parityTranslation$source_sorted ($<=)
           (parityTranslation$source_num_upto lower upper)``,
   entry "list_L6292_sorted_insort" 6292
     "using sorted_insort_key [where f=\"\<lambda>x. x\"] by simp"
     (using_theorem "parityTranslation$source_sorted_insort"
        parityTranslationTheory.source_sorted_insort)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !value xs.
           (parityTranslation$source_sorted le
              (parityTranslation$source_insort le value xs) <=>
            parityTranslation$source_sorted le xs)``,
   entry "list_L6298_sorted_sort" 6298
     "using sorted_sort_key [where f=\"\<lambda>x. x\"] by simp"
     (using_theorem "parityTranslation$source_sorted_sort"
        parityTranslationTheory.source_sorted_sort)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs.
           parityTranslation$source_sorted le
             (parityTranslation$source_sort le xs)``,
   entry "list_L6312_sorted_sort_id" 6312
     "by (simp add: sort_key_id_if_sorted)"
     (using_theorem "parityTranslation$source_sorted_sort_id"
        parityTranslationTheory.source_sorted_sort_id)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !xs.
           parityTranslation$source_sorted le xs ==>
           parityTranslation$source_sort le xs = xs``,
   entry "list_L6315_sort_replicate" 6315
     "using sorted_replicate sorted_sort_id by presburger"
     (using_theorem "parityTranslation$source_sort_replicate"
        parityTranslationTheory.source_sort_replicate)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !count value.
           parityTranslation$source_sort le
             (REPLICATE count value) = REPLICATE count value``,
   entry "list_L6359_insort_insert_key_triv" 6359
     "by (simp add: insort_insert_key_def)"
     (benchLib.AllGoals
       (benchLib.Invoke (benchLib.Safe, []),
        benchLib.Invoke
          (benchLib.Auto,
           [benchLib.IntroAdd
              (benchLib.UnsafeRule,
              (named
                 "parityTranslation$source_insort_insert_key_triv"
                 parityTranslationTheory.source_insort_insert_key_triv))])))
     ``!le : 'b -> 'b -> bool.
         relation$WeakLinearOrder le ==>
         !function value xs.
           function value IN IMAGE function (LIST_TO_SET xs) ==>
           parityTranslation$source_insort_insert_key
             le function value xs = xs``,
   entry "list_L6363_insort_insert_triv" 6363
     "using insort_insert_key_triv [of \"\<lambda>x. x\"] by simp"
     (using_theorem "parityTranslation$source_insort_insert_triv"
        parityTranslationTheory.source_insort_insert_triv)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !value xs.
           value IN LIST_TO_SET xs ==>
           parityTranslation$source_insort_insert le value xs = xs``,
   entry "list_L6367_insort_insert_insort_key" 6367
     "by (simp add: insort_insert_key_def)"
     (benchLib.AllGoals
       (benchLib.Invoke (benchLib.Safe, []),
        benchLib.Invoke
          (benchLib.Auto,
           [benchLib.IntroAdd
              (benchLib.UnsafeRule,
              (named
                 "parityTranslation$source_insort_insert_insort_key"
                 parityTranslationTheory.source_insort_insert_insort_key))])))
     ``!le : 'b -> 'b -> bool.
         relation$WeakLinearOrder le ==>
         !function value xs.
           function value NOTIN
             IMAGE function (LIST_TO_SET xs) ==>
           parityTranslation$source_insort_insert_key
             le function value xs =
           parityTranslation$source_insort_key
             le function value xs``,
   entry "list_L6371_insort_insert_insort" 6371
     "using insort_insert_insort_key [of \"\<lambda>x. x\"] by simp"
     (using_theorem "parityTranslation$source_insort_insert_insort"
        parityTranslationTheory.source_insort_insert_insort)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !value xs.
           value NOTIN LIST_TO_SET xs ==>
           parityTranslation$source_insort_insert le value xs =
           parityTranslation$source_insort le value xs``,
   entry "list_L6375_set_insort_insert" 6375
     "by (auto simp add: insort_insert_key_def set_insort_key)"
     (using_theorem "parityTranslation$source_set_insort_insert"
        parityTranslationTheory.source_set_insort_insert)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !value xs.
           LIST_TO_SET
             (parityTranslation$source_insort_insert le value xs) =
           value INSERT LIST_TO_SET xs``,
   entry "list_L6384_sorted_insort_insert_key" 6384
     "using assms by (simp add: insort_insert_key_def sorted_insort_key)"
     (using_theorem "parityTranslation$source_sorted_insort_insert_key"
        parityTranslationTheory.source_sorted_insort_insert_key)
     ``!le : 'b -> 'b -> bool.
         relation$WeakLinearOrder le ==>
         !function value xs.
           parityTranslation$source_sorted le
             (MAP function xs) ==>
           parityTranslation$source_sorted le
             (MAP function
               (parityTranslation$source_insort_insert_key
                 le function value xs))``,
   entry "list_L6389_sorted_insort_insert" 6389
     "using assms sorted_insort_insert_key [of \"\<lambda>x. x\"] by simp"
     (using_theorem "parityTranslation$source_sorted_insort_insert"
        parityTranslationTheory.source_sorted_insort_insert)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !value xs.
           parityTranslation$source_sorted le xs ==>
           parityTranslation$source_sorted le
             (parityTranslation$source_insort_insert le value xs)``,
   entry "list_L6433_sorted_indexed_from" 6433
     "by (simp add: indexed_from_eq_zip)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_sorted_indexed_from"
              parityTranslationTheory.source_sorted_indexed_from)]))
     ``!start xs.
         parityTranslation$source_sorted ($<=)
           (MAP FST
             (parityTranslation$source_indexed_from start xs))``,
   entry "list_L6444_stable_sort_key_sort_key" 6444
     "by (simp add: stable_sort_key_def sort_key_stable)"
     (using_theorem
        "parityTranslation$source_stable_sort_key_sort_key"
        parityTranslationTheory.source_stable_sort_key_sort_key)
     ``!le : 'b -> 'b -> bool.
         relation$WeakLinearOrder le ==>
         parityTranslation$source_stable_sort_key
           le parityTranslation$source_sort_key``,
   entry "list_L6453_sorted_transpose" 6453
     ("by (auto simp: sorted_iff_nth_mono rev_nth nth_transpose " ^
      "length_filter_conv_card intro: card_mono)")
     (using_theorem
        "parityTranslation$source_sorted_transpose"
        parityTranslationTheory.source_sorted_transpose)
     ``!rows : 'a list list.
         parityTranslation$source_sorted ($<=)
           (REVERSE
             (MAP LENGTH
               (parityTranslation$source_transpose rows)))``,
   entry "list_L6487_nth_nth_transpose_sorted" 6487
     "by (simp add: takeWhile_nth)"
     (using_theorem
        "parityTranslation$source_nth_nth_transpose_sorted"
        parityTranslationTheory.source_nth_nth_transpose_sorted)
     ``!rows : 'a list list.
         parityTranslation$source_sorted ($<=)
           (REVERSE (MAP LENGTH rows)) ==>
         !column row.
           column < LENGTH
             (parityTranslation$source_transpose rows) ==>
           row < LENGTH
             (FILTER
               (\items. column < LENGTH items) rows) ==>
           EL row
             (EL column
               (parityTranslation$source_transpose rows)) =
           EL column (EL row rows)``,
   entry "list_L6669_sorted_key_list_of_set_eq_Nil_iff" 6669
     "by (auto simp: fold_insort_key.remove)"
     (benchLib.Invoke
        (benchLib.Auto,
         [benchLib.DefinitionAdd
            (named
               "parityTranslation$source_sorted_key_list_of_set_def"
               parityTranslationTheory.source_sorted_key_list_of_set_def),
          benchLib.RewriteAdd
            (named "parityTranslation$source_sort_key_eq_nil"
               parityTranslationTheory.source_sort_key_eq_nil),
          benchLib.RewriteAdd
            (named "list$SET_TO_LIST_EMPTY_IFF"
               listTheory.SET_TO_LIST_EMPTY_IFF)]))
     ``!le : 'b -> 'b -> bool.
         relation$WeakLinearOrder le ==>
         !source function domain.
           parityTranslation$source_inj_on function source ==>
           domain SUBSET source ==>
           FINITE domain ==>
           (parityTranslation$source_sorted_key_list_of_set
              le function domain = [] <=>
            domain = EMPTY)``,
   entry "list_L6690_distinct_if_distinct_map" 6690
     "using inj_on by (simp add: distinct_map)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.IntroAdd
           (benchLib.SafeRule,
            named "list$ALL_DISTINCT_MAP"
              listTheory.ALL_DISTINCT_MAP)]))
     ``!function xs.
         ALL_DISTINCT (MAP function xs) ==> ALL_DISTINCT xs``,
   entry "list_L6761_anon_L6761" 6761
     "by (simp add: Uniq_def strict_sorted_equal)"
     (using_theorem
        "parityTranslation$source_strict_sorted_equal_unique"
        strict_sorted_unique)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !domain xs ys.
           parityTranslation$source_strict_sorted le xs /\
           LIST_TO_SET xs = domain /\
           parityTranslation$source_strict_sorted le ys /\
           LIST_TO_SET ys = domain ==>
           xs = ys``,
   entry "list_L6770_sorted_key_list_of_set_unique" 6770
     ("by (auto simp: strict_sorted_iff card_distinct " ^
      "idem_if_sorted_distinct)")
     (using_theorem
        "parityTranslation$source_sorted_key_list_of_set_unique"
        parityTranslationTheory.source_sorted_key_list_of_set_unique)
     ``!le : 'b -> 'b -> bool.
         relation$WeakLinearOrder le ==>
         !source function domain target.
           parityTranslation$source_inj_on function source ==>
           domain SUBSET source ==>
           FINITE domain ==>
           (parityTranslation$source_strict_sorted le
              (MAP function target) /\
            LIST_TO_SET target = domain /\
            LENGTH target = CARD domain <=>
            parityTranslation$source_sorted_key_list_of_set
              le function domain = target)``,
   entry "list_L6835_sorted_list_of_set_lessThan_Suc" 6835
     "by presburger"
     (using_theorem
        "parityTranslation$source_sorted_list_of_set_less_than_suc"
        parityTranslationTheory.source_sorted_list_of_set_less_than_suc)
     ``!bound.
         parityTranslation$source_sorted_list_of_set ($<=)
           (parityTranslation$source_lessThan ($<) (SUC bound)) =
         parityTranslation$source_sorted_list_of_set ($<=)
           (parityTranslation$source_lessThan ($<) bound) ++ [bound]``,
   entry "list_L6839_sorted_list_of_set_atMost_Suc" 6839
     "by fastforce"
     (using_theorem
        "parityTranslation$source_sorted_list_of_set_at_most_suc"
        parityTranslationTheory.source_sorted_list_of_set_at_most_suc)
     ``!bound.
         parityTranslation$source_sorted_list_of_set ($<=)
           (parityTranslation$source_atMost ($<=) (SUC bound)) =
         parityTranslation$source_sorted_list_of_set ($<=)
           (parityTranslation$source_atMost ($<=) bound) ++
         [SUC bound]``,
   entry "list_L6847_sorted_list_of_set_nonempty" 6847
     ("by (auto simp: less_le simp flip: " ^
      "sorted_list_of_set.sorted_key_list_of_set_unique intro: Min_in)")
     (using_theorem
        "parityTranslation$source_sorted_list_of_set_nonempty"
        parityTranslationTheory.source_sorted_list_of_set_nonempty)
     ``!le : 'a -> 'a -> bool.
         relation$WeakLinearOrder le ==>
         !domain.
           FINITE domain ==>
           domain <> EMPTY ==>
           parityTranslation$source_sorted_list_of_set le domain =
           parityTranslation$source_minimum le domain ::
             parityTranslation$source_sorted_list_of_set le
               (domain DELETE
                parityTranslation$source_minimum le domain)``,
   entry "list_L6873_nth_sorted_list_of_set_greaterThanAtMost" 6873
     ("by (simp add: greaterThanAtMost_def greaterThanLessThan_eq " ^
      "lessThan_Suc_atMost)")
     (using_theorem
        ("parityTranslation$" ^
         "source_nth_sorted_list_of_set_greater_than_at_most")
        nth_greater_than_at_most)
     ``!index lower upper.
         index < upper - lower ==>
         EL index
           (parityTranslation$source_sorted_list_of_set ($<=)
             (parityTranslation$source_greaterThanAtMost
               ($<=) ($<) lower upper)) =
         SUC (lower + index)``]

val shortfalls : benchLib.shortfall list = []

end
