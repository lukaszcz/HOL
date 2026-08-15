structure benchListNumeric =
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

val numeral_context =
  [benchLib.DefinitionAdd
     (named "parityTranslation$source_numeral_def"
        parityTranslationTheory.source_numeral_def)]

val upto_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_upto_closed"
        parityTranslationTheory.source_upto_closed),
   benchLib.RewriteAdd
     (named "parityTranslation$source_num_step"
        parityTranslationTheory.source_num_step),
   benchLib.RewriteAdd
     (named "list$GENLIST_EQ_NIL"
        listTheory.GENLIST_EQ_NIL),
   benchLib.RewriteAdd
     (named "parityTranslation$source_int_genlist_cons"
        parityTranslationTheory.source_int_genlist_cons),
   benchLib.RewriteAdd
     (named "parityTranslation$source_int_lt_add1"
        parityTranslationTheory.source_int_lt_add1),
   benchLib.RewriteAdd
     (named "integer$INT_NOT_LT" integerTheory.INT_NOT_LT),
   benchLib.RewriteAdd
     (named "integer$INT_NOT_LE" integerTheory.INT_NOT_LE),
   benchLib.RewriteAdd
     (named "integer$INT_LE_ANTISYM"
        integerTheory.INT_LE_ANTISYM),
   benchLib.RewriteAdd
     (named "parityTranslation$source_int_le_antisym_imp"
        parityTranslationTheory.source_int_le_antisym_imp)]

val split2_context =
  [benchLib.IntroAdd
     (benchLib.SafeRule,
      named "parityTranslation$source_upto_split_boundary"
        parityTranslationTheory.source_upto_split_boundary),
   benchLib.RewriteAdd
     (named "integer$INT_LE_LT" integerTheory.INT_LE_LT),
   benchLib.RewriteAdd
     (named "parityTranslation$source_int_lt_add1"
        parityTranslationTheory.source_int_lt_add1),
   benchLib.RewriteAdd
     (named "integer$INT_NOT_LT" integerTheory.INT_NOT_LT)]
     @ [benchLib.RewriteAdd
          (named "parityTranslation$source_upto_empty"
             parityTranslationTheory.source_upto_empty)]

val split3_context =
  [benchLib.IntroAdd
     (benchLib.SafeRule,
      named "parityTranslation$source_append_cons_cut"
        parityTranslationTheory.source_append_cons_cut),
   benchLib.IntroAdd
     (benchLib.SafeRule,
      named "parityTranslation$source_upto_split_boundary"
        parityTranslationTheory.source_upto_split_boundary),
   benchLib.IntroAdd
     (benchLib.SafeRule,
      named "parityTranslation$source_upto_rec1"
        parityTranslationTheory.source_upto_rec1)]

val aux_context =
  [benchLib.DefinitionAdd
     (named "parityTranslation$source_upto_aux_def"
        parityTranslationTheory.source_upto_aux_def),
   benchLib.RewriteAdd
     (named "parityTranslation$source_upto_empty"
        parityTranslationTheory.source_upto_empty),
   benchLib.RewriteAdd
     (named "parityTranslation$source_upto_rec2"
        parityTranslationTheory.source_upto_rec2)]

val goals =
  [entry "list_L3589_take_Cons_numeral" 3589
     "by (simp add: take_Cons')"
     (benchLib.Invoke (benchLib.Simp, numeral_context))
     ``!v x xs.
         TAKE (parityTranslation$source_numeral v) (x::xs) =
         x :: TAKE (parityTranslation$source_numeral v - 1) xs``,
   entry "list_L3593_drop_Cons_numeral" 3593
     "by (simp add: drop_Cons')"
     (benchLib.Invoke (benchLib.Simp, numeral_context))
     ``!v x xs.
         DROP (parityTranslation$source_numeral v) (x::xs) =
         DROP (parityTranslation$source_numeral v - 1) xs``,
   entry "list_L3597_nth_Cons_numeral" 3597
     "by (simp add: nth_Cons')"
     (benchLib.Invoke (benchLib.Simp, numeral_context))
     ``!v x xs.
         EL (parityTranslation$source_numeral v) (x::xs) =
         EL (parityTranslation$source_numeral v - 1) xs``,
   entry "list_L3635_upto_empty" 3635
     "by(simp add: upto.simps)"
     (benchLib.Invoke (benchLib.Simp, upto_context))
     ``!i j : int. j < i ==>
         parityTranslation$source_upto i j = []``,
   entry "list_L3638_upto_single" 3638
     "by(simp add: upto.simps)"
     (benchLib.Invoke (benchLib.Simp, upto_context))
     ``!i : int. parityTranslation$source_upto i i = [i]``,
   entry "list_L3641_upto_Nil" 3641
     "by (simp add: upto.simps)"
     (benchLib.Invoke (benchLib.Simp, upto_context))
     ``!i j : int.
         (parityTranslation$source_upto i j = [] <=> j < i)``,
   entry "list_L3646_upto_rec1" 3646
     "by(simp add: upto.simps)"
     (benchLib.Invoke (benchLib.Simp, upto_context))
     ``!i j : int. i <= j ==>
         parityTranslation$source_upto i j =
         i :: parityTranslation$source_upto (i + 1) j``,
   entry "list_L3683_upto_split2" 3683 "by auto"
     (benchLib.Invoke (benchLib.Auto, split2_context))
     ``!i j k : int. i <= j ==> j <= k ==>
         parityTranslation$source_upto i k =
         parityTranslation$source_upto i j ++
         parityTranslation$source_upto (j + 1) k``,
   entry "list_L3687_upto_split3" 3687 "by auto"
     (benchLib.Invoke (benchLib.Auto, split3_context))
     ``!i j k : int. i <= j ==> j <= k ==>
         parityTranslation$source_upto i k =
         parityTranslation$source_upto i (j - 1) ++
         j :: parityTranslation$source_upto (j + 1) k``,
   entry "list_L3695_upto_aux_rec" 3695
     "by (simp add: upto_aux_def upto_rec2)"
     (benchLib.Invoke (benchLib.Simp, aux_context))
     ``!i j : int. !js.
         parityTranslation$source_upto_aux i j js =
         if j < i then js
         else parityTranslation$source_upto_aux
                i (j - 1) (j::js)``,
   entry "list_L3699_upto_code" 3699
     "by(simp add: upto_aux_def)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_upto_aux_def"
              parityTranslationTheory.source_upto_aux_def)]))
     ``!i j : int.
         parityTranslation$source_upto i j =
         parityTranslation$source_upto_aux i j []``]

val shortfalls : benchLib.shortfall list = []

end
