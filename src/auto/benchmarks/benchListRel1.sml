structure benchListRel1 =
struct

open HolKernel

fun named name theorem : benchLib.named_thm =
  {name = name, theorem = theorem}

fun entry id line method recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = recipe, excl = [], provenance =
     {file = "src/HOL/List.thy", line = line, commit = "f7e02b7e"},
   representative = false}

val definition =
  benchLib.DefinitionAdd
    (named "parityTranslation$source_listrel1_def"
       parityTranslationTheory.source_listrel1_def)

val auto = benchLib.Invoke (benchLib.Auto, [definition])

val goals =
  [entry "list_L7795_listrel1I" 7795
     "unfolding listrel1_def by auto" auto
     ``!relation left right xs ys prefix suffix.
         relation left right ==>
         xs = prefix ++ left::suffix ==>
         ys = prefix ++ right::suffix ==>
         parityTranslation$source_listrel1 relation xs ys``,
   entry "list_L7800_listrel1E" 7800
     "unfolding listrel1_def by auto" auto
     ``!relation xs ys conclusion.
         parityTranslation$source_listrel1 relation xs ys ==>
         (!left right prefix suffix.
            relation left right ==>
            xs = prefix ++ left::suffix ==>
            ys = prefix ++ right::suffix ==>
            conclusion) ==>
         conclusion``,
   entry "list_L7806_not_Nil_listrel1" 7806
     "unfolding listrel1_def by blast" auto
     ``!relation xs.
         ~parityTranslation$source_listrel1 relation [] xs``,
   entry "list_L7809_not_listrel1_Nil" 7809
     "unfolding listrel1_def by blast" auto
     ``!relation xs.
         ~parityTranslation$source_listrel1 relation xs []``,
   entry "list_L7823_append_listrel1I" 7823
     "unfolding listrel1_def by auto"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.IntroAdd
           (benchLib.UnsafeRule,
            named "parityTranslation$source_listrel1_append_suffix"
              parityTranslationTheory.source_listrel1_append_suffix),
         benchLib.IntroAdd
           (benchLib.UnsafeRule,
            named "parityTranslation$source_listrel1_append_prefix"
              parityTranslationTheory.source_listrel1_append_prefix)]))
     ``!relation xs ys us vs.
         ((parityTranslation$source_listrel1 relation xs ys /\
           us = vs) \/
          (xs = ys /\
           parityTranslation$source_listrel1 relation us vs)) ==>
         parityTranslation$source_listrel1
           relation (xs ++ us) (ys ++ vs)``,
   entry "list_L7853_listrel1_eq_len" 7853
     "unfolding listrel1_def by auto"
     (benchLib.Invoke
       (benchLib.Auto,
        [definition,
         benchLib.RewriteAdd
           (named "list$LENGTH_APPEND" listTheory.LENGTH_APPEND)]))
     ``!relation xs ys.
         parityTranslation$source_listrel1 relation xs ys ==>
         LENGTH xs = LENGTH ys``,
   entry "list_L7856_listrel1_mono" 7856
     "unfolding listrel1_def by blast"
     (benchLib.Invoke (benchLib.Blast, [definition]))
     ``!left_relation right_relation.
         (!left right.
            left_relation left right ==>
            right_relation left right) ==>
         !xs ys.
           parityTranslation$source_listrel1 left_relation xs ys ==>
           parityTranslation$source_listrel1 right_relation xs ys``,
   entry "list_L7861_listrel1_converse" 7861
     "unfolding listrel1_def by blast"
     (benchLib.Invoke
       (benchLib.Auto,
        [definition,
         benchLib.DefinitionAdd
           (named "bool$FUN_EQ_THM" boolTheory.FUN_EQ_THM)]))
     ``!relation.
         parityTranslation$source_listrel1
           (\left right. relation right left) =
         (\xs ys.
            parityTranslation$source_listrel1 relation ys xs)``,
   entry "list_L7864_in_listrel1_converse" 7864
     "unfolding listrel1_def by blast" auto
     ``!relation xs ys.
         (parityTranslation$source_listrel1
            (\left right. relation right left) xs ys <=>
          parityTranslation$source_listrel1 relation ys xs)``,
   entry "list_L7922_wf_listrel1_iff" 7922
     ("by (auto simp: wf_iff_acc intro: lists_accD " ^
      "lists_accI[THEN Cons_in_lists_iff[THEN iffD1, " ^
      "THEN conjunct1]])")
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.IntroAdd
           (benchLib.SafeRule,
            named "parityTranslation$source_wf_listrel1_iff"
              parityTranslationTheory.source_wf_listrel1_iff)]))
     ``!relation.
         (relation$WF
            (parityTranslation$source_listrel1 relation) <=>
          relation$WF relation)``]

val shortfalls : benchLib.shortfall list = []

end
