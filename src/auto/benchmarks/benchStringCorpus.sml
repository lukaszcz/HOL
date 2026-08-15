structure benchStringCorpus =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun named name theorem : benchLib.named_thm =
  {name = name, theorem = theorem}

fun method_args method =
  if String.isSubstring "UNIV_char_of_nat" method andalso
     String.isSubstring "card_image" method then
    [benchLib.RewriteAdd
       (named "string$UNIV_IMAGE_CHR_count_256"
          stringTheory.UNIV_IMAGE_CHR_count_256),
     benchLib.RewriteAdd
       (named "parityTranslation$source_card_image_chr_count"
          parityTranslationTheory.source_card_image_chr_count)]
  else
    []

fun entry id line method mapped representative excl goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = benchLib.Invoke (mapped, method_args method),
   excl = List.filter (fn {theorem, ...} =>
     benchLib.theorem_is_goal goal theorem) excl, provenance =
     {file = "src/HOL/String.thy", line = line, commit = commit},
   representative = representative}

fun translated id line method recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method, recipe = recipe,
   excl = [], provenance =
     {file = "src/HOL/String.thy", line = line, commit = commit},
   representative = false}

fun simp_with arguments =
  benchLib.Invoke (benchLib.Simp, arguments)

val char_definitions =
  [benchLib.DefinitionAdd
     (named "parityTranslation$source_of_char_def"
       parityTranslationTheory.source_of_char_def),
   benchLib.DefinitionAdd
     (named "parityTranslation$source_char_of_def"
       parityTranslationTheory.source_char_of_def),
   benchLib.DefinitionAdd
     (named "parityTranslation$source_take_bit_def"
       parityTranslationTheory.source_take_bit_def)]

val translated_goals =
  [translated "string_L34_of_char_Char" 34
     "by (simp add: of_char_def)"
     (simp_with
       [benchLib.DefinitionAdd
          (named "parityTranslation$source_of_char_def"
            parityTranslationTheory.source_of_char_def),
        benchLib.DefinitionAdd
          (named "parityTranslation$source_Char_def"
            parityTranslationTheory.source_Char_def),
        benchLib.RewriteAdd
          (named "parityTranslation$source_horner8_bound"
            parityTranslationTheory.source_horner8_bound),
        benchLib.RewriteAdd
          (named "string$ORD_CHR_RWT"
            stringTheory.ORD_CHR_RWT)])
     (Thm.concl parityTranslationTheory.source_of_char_Char),
   translated "string_L60_char_of_take_bit_eq" 60
     "by (simp add: char_of_def bit_take_bit_iff)"
     (simp_with
       (char_definitions @
        [benchLib.RewriteAdd
           (named "arithmetic$MOD_MULT_MOD"
             arithmeticTheory.MOD_MULT_MOD),
         benchLib.RewriteAdd
           (named "parityTranslation$source_take_bit_mod_256"
             parityTranslationTheory.source_take_bit_mod_256)]))
     (Thm.concl parityTranslationTheory.source_char_of_take_bit_eq),
   translated "string_L68_char_of_comp_of_char" 68
     "by (simp add: fun_eq_iff)"
     (simp_with
       [benchLib.RewriteAdd
          (named "parityTranslation$source_char_roundtrip"
            parityTranslationTheory.source_char_roundtrip),
        benchLib.DefinitionAdd
          (named "bool$FUN_EQ_THM" boolTheory.FUN_EQ_THM)])
     (Thm.concl parityTranslationTheory.source_char_of_comp_of_char),
   translated "string_L83_of_char_eqI" 83
     "using that inj_of_char by (simp add: inj_eq)"
     (simp_with
       [benchLib.DefinitionAdd
          (named "parityTranslation$source_of_char_def"
            parityTranslationTheory.source_of_char_def),
        benchLib.RewriteAdd
          (named "string$ORD_11" stringTheory.ORD_11)])
     (Thm.concl parityTranslationTheory.source_of_char_eqI),
   translated "string_L87_of_char_eq_iff" 87
     "by (auto intro: of_char_eqI)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.IntroAdd
           (benchLib.SafeRule,
            named "parityTranslation$source_of_char_eqI"
              parityTranslationTheory.source_of_char_eqI)]))
     (Thm.concl parityTranslationTheory.source_of_char_eq_iff),
   translated "string_L131_char_of_eq_iff" 131
     "by (auto intro: of_char_eqI simp add: take_bit_eq_mod)"
     (benchLib.Invoke
       (benchLib.Auto,
        char_definitions @
        [benchLib.IntroAdd
           (benchLib.SafeRule,
            named "parityTranslation$source_of_char_eqI"
              parityTranslationTheory.source_of_char_eqI),
         benchLib.RewriteAdd
           (named "string$CHR_ORD" stringTheory.CHR_ORD),
         benchLib.RewriteAdd
           (named "string$ORD_CHR_RWT"
             stringTheory.ORD_CHR_RWT),
         benchLib.RewriteAdd
           (named "arithmetic$MOD_LESS"
             arithmeticTheory.MOD_LESS)]))
     (Thm.concl parityTranslationTheory.source_char_of_eq_iff),
   translated "string_L135_char_of_nat" 135
     ("by (simp add: char_of_def String.char_of_def " ^
      "drop_bit_of_nat bit_simps possible_bit_def)")
     (simp_with
       [benchLib.DefinitionAdd
          (named "parityTranslation$source_of_nat_def"
            parityTranslationTheory.source_of_nat_def)])
     (Thm.concl parityTranslationTheory.source_char_of_nat),
   translated "string_L344_char_of_integer_code" 344
     ("by (simp add: bit_cut_integer_def char_of_integer_def " ^
      "char_of_def div_mult2_numeral_eq bit_iff_odd_drop_bit " ^
      "drop_bit_eq_div)")
     (simp_with
       [benchLib.DefinitionAdd
          (named "parityTranslation$source_bit_cut_integer_def"
            parityTranslationTheory.source_bit_cut_integer_def),
        benchLib.RewriteAdd
          (named "bool$LET_THM" boolTheory.LET_THM),
        benchLib.RewriteAdd
          (named "parityTranslation$source_char_of_integer_eq_iff"
            parityTranslationTheory.source_char_of_integer_eq_iff),
        benchLib.RewriteAdd
          (named "parityTranslation$source_num_mod_256_horner"
            parityTranslationTheory.source_num_mod_256_horner)])
     (Thm.concl parityTranslationTheory.source_char_of_integer_code),
   translated "string_L357_integer_of_char_code" 357
     "by (simp add: integer_of_char_def of_char_def)"
     (simp_with
       [benchLib.DefinitionAdd
          (named "parityTranslation$source_integer_of_char_def"
            parityTranslationTheory.source_integer_of_char_def),
        benchLib.DefinitionAdd
          (named "parityTranslation$source_Char_def"
            parityTranslationTheory.source_Char_def),
        benchLib.RewriteAdd
          (named "parityTranslation$source_horner8_bound"
            parityTranslationTheory.source_horner8_bound),
        benchLib.RewriteAdd
          (named "string$ORD_CHR_RWT"
            stringTheory.ORD_CHR_RWT)])
     (Thm.concl parityTranslationTheory.source_integer_of_char_code),
   translated "string_L728_anon_L728" 728 "by simp"
     (simp_with
       [benchLib.DefinitionAdd
          (named "parityTranslation$source_Literal_prime_def"
            parityTranslationTheory.source_Literal_prime_def)])
     (Thm.concl
       parityTranslationTheory.source_Literal_code_computation_unfold),
   translated "string_L919_abort_cong" 919 "by simp"
     (simp_with
       [benchLib.DefinitionAdd
          (named "parityTranslation$source_abort_def"
            parityTranslationTheory.source_abort_def)])
     (Thm.concl parityTranslationTheory.source_abort_cong)]

val goals =
  translated_goals @ [
   entry "string_L178_card_UNIV_char" 178 "by (auto simp add: UNIV_char_of_nat card_image)" benchLib.Auto true []
     ``((CARD (UNIV : char set)) = 256)``
  ]

end
