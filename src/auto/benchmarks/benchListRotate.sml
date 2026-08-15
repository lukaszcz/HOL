structure benchListRotate =
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

val rotate_definition =
  benchLib.DefinitionAdd
    (named "parityTranslation$source_rotate_def"
       parityTranslationTheory.source_rotate_def)

val funpow_context =
  [rotate_definition,
   benchLib.RewriteAdd
     (named "arithmetic$FUNPOW_SUC"
        arithmeticTheory.FUNPOW_SUC),
   benchLib.RewriteAdd
     (named "arithmetic$FUNPOW_ADD"
        arithmeticTheory.FUNPOW_ADD),
   benchLib.RewriteAdd
     (named "combin$o_DEF" combinTheory.o_DEF)]

val function_context =
  benchLib.RewriteAdd
    (named "bool$FUN_EQ_THM" boolTheory.FUN_EQ_THM) ::
  funpow_context

val nth_context =
  [benchLib.RewriteAdd
     (named "parityTranslation$source_rotate1_drop_take_bridge"
        parityTranslationTheory.source_rotate1_drop_take_bridge),
   benchLib.RewriteAdd
     (named "parityTranslation$source_drop1_take1_el"
        parityTranslationTheory.source_drop1_take1_el)]

val bij_context =
  [benchLib.DefinitionAdd
     (named "pred_set$BIJ_DEF" pred_setTheory.BIJ_DEF),
   benchLib.DefinitionAdd
     (named "pred_set$INJ_DEF" pred_setTheory.INJ_DEF),
   benchLib.DefinitionAdd
     (named "pred_set$SURJ_DEF" pred_setTheory.SURJ_DEF),
   benchLib.IntroAdd
     (benchLib.SafeRule,
      named "parityTranslation$source_rotate1_inj"
        parityTranslationTheory.source_rotate1_inj),
   benchLib.FactAdd
     (named "parityTranslation$source_rotate1_surj"
        parityTranslationTheory.source_rotate1_surj)]

val goals =
  [entry "list_L5191_rotate0" 5191
     "by(simp add:rotate_def)"
     (benchLib.Invoke (benchLib.Simp, function_context))
     ``parityTranslation$source_rotate 0 = I``,
   entry "list_L5194_rotate_Suc" 5194
     "by(simp add:rotate_def)"
     (benchLib.Invoke (benchLib.Simp, function_context))
     ``!count xs.
         parityTranslation$source_rotate (SUC count) xs =
         parityTranslation$source_rotate1
           (parityTranslation$source_rotate count xs)``,
   entry "list_L5197_rotate_add" 5197
     "by(simp add:rotate_def funpow_add)"
     (benchLib.Invoke (benchLib.Simp, function_context))
     ``!left right.
         parityTranslation$source_rotate (left + right) =
         parityTranslation$source_rotate left o
         parityTranslation$source_rotate right``,
   entry "list_L5201_rotate_rotate" 5201
     "by(simp add:rotate_add)"
     (benchLib.Invoke (benchLib.Simp, funpow_context))
     ``!left right xs.
         parityTranslation$source_rotate left
           (parityTranslation$source_rotate right xs) =
         parityTranslation$source_rotate (left + right) xs``,
   entry "list_L5207_rotate1_rotate_swap" 5207
     "by(simp add:rotate_def funpow_swap1)"
     (benchLib.Invoke
       (benchLib.Simp,
        [rotate_definition,
         benchLib.RewriteAdd
           (named "parityTranslation$source_funpow_rotate1_swap"
              parityTranslationTheory.source_funpow_rotate1_swap)]))
     ``!count xs.
         parityTranslation$source_rotate1
           (parityTranslation$source_rotate count xs) =
         parityTranslation$source_rotate count
           (parityTranslation$source_rotate1 xs)``,
   entry "list_L5241_rotate_conv_mod" 5241
     "by (simp add: rotate_drop_take)"
     (benchLib.Invoke
       (benchLib.Simp,
         [benchLib.RewriteAdd
           (named "parityTranslation$source_rotate_conv_mod"
              (BoundedRewrites.Once
                 parityTranslationTheory.source_rotate_conv_mod))]))
     ``!count xs.
         parityTranslation$source_rotate count xs =
         parityTranslation$source_rotate
           (count MOD LENGTH xs) xs``,
   entry "list_L5244_rotate_id" 5244
     "by (simp add: rotate_drop_take)"
     (benchLib.Invoke
       (benchLib.Simp,
         [benchLib.RewriteAdd
           (named "parityTranslation$source_rotate_conv_mod"
              (BoundedRewrites.Once
                 parityTranslationTheory.source_rotate_conv_mod)),
         rotate_definition]))
     ``!count xs.
         count MOD LENGTH xs = 0 ==>
         parityTranslation$source_rotate count xs = xs``,
   entry "list_L5259_rotate_map" 5259
     "by(simp add:rotate_drop_take take_map drop_map)"
     (benchLib.Invoke
       (benchLib.Simp,
        [rotate_definition,
         benchLib.RewriteAdd
           (named "parityTranslation$source_funpow_rotate1_map"
              parityTranslationTheory.source_funpow_rotate1_map)]))
     ``!count function xs.
         parityTranslation$source_rotate count (MAP function xs) =
         MAP function
           (parityTranslation$source_rotate count xs)``,
   entry "list_L5301_nth_rotate1" 5301
     "using that nth_rotate [of n xs 1] by simp"
     (benchLib.Invoke (benchLib.Auto, nth_context))
     ``!xs index.
         index < LENGTH xs ==>
         EL index (parityTranslation$source_rotate1 xs) =
         EL (SUC index MOD LENGTH xs) xs``,
   entry "list_L5325_bij_rotate1" 5325
     "using bijI inj_rotate1 surj_rotate1 by blast"
     (benchLib.Invoke (benchLib.Auto, bij_context))
     ``BIJ parityTranslation$source_rotate1 UNIV UNIV``]

val shortfalls : benchLib.shortfall list = []

end
