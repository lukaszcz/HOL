structure benchListLex =
struct

open HolKernel

fun named name theorem : benchLib.named_thm =
  {name = name, theorem = theorem}

fun entry id line method recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = recipe, excl = [], provenance =
     {file = "src/HOL/List.thy", line = line, commit = "f7e02b7e"},
   representative = false}

val lex_definition =
  benchLib.DefinitionAdd
    (named "parityTranslation$source_lex_def"
       parityTranslationTheory.source_lex_def)

val lenlex_definition =
  benchLib.DefinitionAdd
    (named "parityTranslation$source_lenlex_def"
       parityTranslationTheory.source_lenlex_def)

val lexord_definition =
  benchLib.DefinitionAdd
    (named "parityTranslation$source_lexord_def"
       parityTranslationTheory.source_lexord_def)

val goals =
  [entry "list_L7247_lex_conv" 7247
     "by (force simp add: lex_def lexn_conv)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_lex_conv"
              parityTranslationTheory.source_lex_conv)]))
     ``!relation xs ys.
         (parityTranslation$source_lex relation xs ys <=>
          LENGTH xs = LENGTH ys /\
          ?prefix left right xs' ys'.
            xs = prefix ++ (left::xs') /\
            ys = prefix ++ (right::ys') /\
            relation left right)``,
   entry "list_L7256_lenlex_conv" 7256
     "by (auto simp add: lenlex_def)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_lenlex_conv"
              parityTranslationTheory.source_lenlex_conv)]))
     ``!relation xs ys.
         (parityTranslation$source_lenlex relation xs ys <=>
          LENGTH xs < LENGTH ys \/
          (LENGTH xs = LENGTH ys /\
           parityTranslation$source_lex relation xs ys))``,
   entry "list_L7283_Nil_notin_lex" 7283
     "by (simp add: lex_conv)"
     (benchLib.Invoke (benchLib.Simp, [lex_definition]))
     ``!relation ys.
         ~parityTranslation$source_lex relation [] ys``,
   entry "list_L7286_Nil2_notin_lex" 7286
     "by (simp add: lex_conv)"
     (benchLib.Invoke (benchLib.Simp, [lex_definition]))
     ``!relation xs.
         ~parityTranslation$source_lex relation xs []``,
   entry "list_L7300_Nil_lenlex_iff1" 7300
     "by (auto simp: lenlex_def)"
     (benchLib.Invoke
       (benchLib.Auto,
        [lenlex_definition,
         benchLib.DefinitionAdd
           (named "list$SHORTLEX_def" listTheory.SHORTLEX_def)]))
     ``!relation xs.
         (parityTranslation$source_lenlex relation [] xs <=> xs <> [])``,
   entry "list_L7300_Nil_lenlex_iff2" 7300
     "by (auto simp: lenlex_def)"
     (benchLib.Invoke (benchLib.Simp, [lenlex_definition]))
     ``!relation xs.
         ~parityTranslation$source_lenlex relation xs []``,
   entry "list_L7304_Cons_lenlex_iff" 7304
     "by (auto simp: lenlex_def)"
     (benchLib.AllGoals
       (benchLib.Invoke
         (benchLib.Auto,
          [lenlex_definition,
           benchLib.DefinitionAdd
             (named "list$SHORTLEX_def" listTheory.SHORTLEX_def),
           benchLib.IntroAdd
             (benchLib.SafeRule,
              named
                "parityTranslation$source_shortlex_not_less_equal"
                parityTranslationTheory.source_shortlex_not_less_equal)]),
        benchLib.Invoke
          (benchLib.Simp, [])))
     ``!relation left xs right ys.
         (parityTranslation$source_lenlex
            relation (left::xs) (right::ys) <=>
          LENGTH xs < LENGTH ys \/
          (LENGTH xs = LENGTH ys /\ relation left right) \/
          (left = right /\
           parityTranslation$source_lenlex relation xs ys))``,
   entry "list_L7318_lenlex_length" 7318
     "by (auto simp: lenlex_def)"
     (benchLib.Then
       (benchLib.Invoke (benchLib.Simp, [lenlex_definition]),
        benchLib.Invoke
          (benchLib.Blast,
           [benchLib.FactAdd
              (named "list$SHORTLEX_LENGTH_LE"
                 listTheory.SHORTLEX_LENGTH_LE)])))
     ``!relation xs ys.
         parityTranslation$source_lenlex relation xs ys ==>
         LENGTH xs <= LENGTH ys``,
   entry "list_L7321_lex_append_rightI" 7321
     "by (fastforce simp: lex_def lexn_conv)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.FactAdd
           (named "parityTranslation$source_lex_append_right"
              parityTranslationTheory.source_lex_append_right)]))
     ``!relation xs ys us vs.
         parityTranslation$source_lex relation xs ys ==>
         LENGTH vs = LENGTH us ==>
         parityTranslation$source_lex
           relation (xs ++ us) (ys ++ vs)``,
   entry "list_L7387_lexord_same_pref_if_irrefl" 7387
     "by (simp add: irrefl_def lexord_same_pref_iff)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_lexord_append_prefix_iff"
              parityTranslationTheory.source_lexord_append_prefix_iff)]))
     ``!relation.
         relation$irreflexive relation ==>
         !prefix xs ys.
           (parityTranslation$source_lexord relation
              (prefix ++ xs) (prefix ++ ys) <=>
            parityTranslation$source_lexord relation xs ys)``,
   entry "list_L7394_lexord_append_left_rightI" 7394
     "by (simp add: lexord_same_pref_iff)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.FactAdd
           (named
              "parityTranslation$source_lexord_append_left_rightI"
              parityTranslationTheory.source_lexord_append_left_rightI)]))
     ``!relation left right prefix xs ys.
         relation left right ==>
         parityTranslation$source_lexord relation
           (prefix ++ left::xs) (prefix ++ right::ys)``,
   entry "list_L7398_lexord_append_leftI" 7398
     "by (simp add: lexord_same_pref_iff)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.FactAdd
           (named "parityTranslation$source_lexord_append_leftI"
              parityTranslationTheory.source_lexord_append_leftI)]))
     ``!relation xs ys prefix.
         parityTranslation$source_lexord relation xs ys ==>
         parityTranslation$source_lexord relation
           (prefix ++ xs) (prefix ++ ys)``,
   entry "list_L7401_lexord_append_leftD" 7401
     "by (simp add: lexord_same_pref_iff)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_lexord_append_prefix_iff"
              parityTranslationTheory.source_lexord_append_prefix_iff)]))
     ``!relation prefix xs ys.
         parityTranslation$source_lexord relation
           (prefix ++ xs) (prefix ++ ys) ==>
         relation$irreflexive relation ==>
         parityTranslation$source_lexord relation xs ys``,
   entry "list_L7508_lexord_trans" 7508
     "by (auto simp: trans_def intro: lexord_partial_trans)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.FactAdd
           (named "parityTranslation$source_lexord_partial_trans"
              parityTranslationTheory.source_lexord_partial_trans)]))
     ``!relation xs ys zs.
         parityTranslation$source_lexord relation xs ys ==>
         parityTranslation$source_lexord relation ys zs ==>
         relation$transitive relation ==>
         parityTranslation$source_lexord relation xs zs``,
   entry "list_L7537_lexord_irrefl" 7537
     "by (simp add: irrefl_def lexord_irreflexive)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_lexord_irreflexive"
              parityTranslationTheory.source_lexord_irreflexive),
         benchLib.DefinitionAdd
           (named "relation$irreflexive_def"
              relationTheory.irreflexive_def)]))
     ``!relation.
         relation$irreflexive relation ==>
         relation$irreflexive
           (parityTranslation$source_lexord relation)``,
   entry "list_L7570_asym_lenlex" 7570
     "by (simp add: lenlex_def asym_inv_image asym_less_than asym_lex)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_asym_lenlex"
              parityTranslationTheory.source_asym_lenlex)]))
     ``!relation.
         parityTranslation$source_asym relation ==>
         parityTranslation$source_asym
           (parityTranslation$source_lenlex relation)``,
   entry "list_L7716_lexordp_conv_lexord" 7716
     "by (simp add: lexordp_iff lexord_def)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_lexordp_def"
              parityTranslationTheory.source_lexordp_def)]))
     ``!relation xs ys.
         (parityTranslation$source_lexordp relation xs ys <=>
          parityTranslation$source_lexord relation xs ys)``,
   entry "list_L7752_lexordp_eq_conv_lexord" 7752
     "by (auto simp add: lexordp_conv_lexordp_eq)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_lexordp_eq_def"
              parityTranslationTheory.source_lexordp_eq_def)]))
     ``!relation xs ys.
         (parityTranslation$source_lexordp_eq relation xs ys <=>
          xs = ys \/
          parityTranslation$source_lexordp relation xs ys)``]

val shortfalls : benchLib.shortfall list = []

end
