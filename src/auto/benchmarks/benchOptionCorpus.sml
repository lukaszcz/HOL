structure benchOptionCorpus =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun named name theorem = {name = name, theorem = theorem}

fun contains_constant constant goal =
  can (find_term (same_const constant)) goal

fun variable_named wanted goal =
  case List.find
         (fn variable => #1 (dest_var variable) = wanted)
         (free_vars goal) of
      SOME variable => variable
    | NONE => raise Fail ("missing corpus variable " ^ wanted)

fun negated_forall_option goal =
  let
    val predicate = variable_named "v_P0" goal
    val (domain, _) = dom_rng (type_of predicate)
    val value = variant (free_vars goal)
      (mk_var ("option_value", domain))
    val negated = mk_abs
      (value, boolSyntax.mk_neg (mk_comb (predicate, value)))
    val schema = hd (free_vars (concl optionTheory.FORALL_OPTION))
  in
    INST [schema |-> negated] optionTheory.FORALL_OPTION
  end

fun method_args method goal =
  (if String.isSubstring "these_empty_eq" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_these_empty_eq"
           parityTranslationTheory.source_these_empty_eq),
      benchLib.IntroAdd
        (benchLib.SafeRule,
         named "parityTranslation$source_no_some_member_none"
           parityTranslationTheory.source_no_some_member_none)]
   else
     []) @
  (if String.isSubstring "these_empty_eq" method then
     []
   else
     [benchLib.RewriteAdd
        (named "pred_set$SPECIFICATION" pred_setTheory.SPECIFICATION),
      benchLib.DefinitionAdd
        (named "pred_set$EXTENSION" pred_setTheory.EXTENSION)]) @
  (if String.isSubstring "option.induct" method then
     [benchLib.RewriteAdd
        (named "bool$EQ_IMP_THM" boolTheory.EQ_IMP_THM),
      benchLib.FactAdd
        (named "option$option_induction"
           optionTheory.option_induction)]
   else
     []) @
  (if String.isSubstring "option.split" method then
     [benchLib.SplitAdd
        (named "parityTranslation$source_option_split"
           parityTranslationTheory.source_option_split)]
   else
     []) @
  (if String.isSubstring "split_option_all" method then
     [benchLib.FactAdd
        (named "option$FORALL_OPTION[of-not-P]"
           (negated_forall_option goal))]
   else
     []) @
  (if String.isSubstring "map_option_case" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_map_option_case"
           parityTranslationTheory.source_map_option_case)] @
     (if contains_constant ``option$SOME`` goal then
        [benchLib.RewriteAdd
           (named "bool$EQ_SYM_EQ" boolTheory.EQ_SYM_EQ)]
      else
        [])
   else
     []) @
  (if String.isSubstring "rel_option_iff" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_rel_option_iff"
           parityTranslationTheory.source_rel_option_iff)]
   else
     []) @
  (if String.isSubstring "rel_option_unfold" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_rel_option_unfold"
           parityTranslationTheory.source_rel_option_unfold)]
   else
     []) @
  (if String.isSubstring "Option.is_none_def" method then
     [benchLib.DefinitionAdd
        (named "option$IS_NONE_DEF" optionTheory.IS_NONE_DEF)]
   else
     []) @
  (if String.isSubstring "these_def" method then
     [benchLib.RewriteAdd
        (named "option$FORALL_OPTION" optionTheory.FORALL_OPTION)]
   else
     []) @
  (if String.isSubstring "UNIV_option_conv" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_UNIV_option_conv"
           parityTranslationTheory.source_UNIV_option_conv)]
   else
     []) @
  (if String.isSubstring "finite_imageD" method andalso
      String.isSubstring "inj_Some" method then
     [benchLib.RewriteAdd
        (named "pred_set$INJECTIVE_IMAGE_FINITE"
           pred_setTheory.INJECTIVE_IMAGE_FINITE)]
   else
     []) @
  (if contains_constant ``option$OPTION_BIND`` goal andalso
      contains_constant ``option$OPTREL`` goal then
     [benchLib.RewriteAdd
        (named "option$FORALL_OPTION" optionTheory.FORALL_OPTION)]
   else
     [])

fun entry id line method mapped representative excl goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = benchLib.Invoke (mapped, method_args method goal),
   excl = List.filter (fn {theorem, ...} =>
     benchLib.theorem_is_goal goal theorem) excl, provenance =
     {file = "src/HOL/Option.thy", line = line, commit = commit},
   representative = representative}

val goals =
  [
   entry "option_L39_comp_the_Some" 39 "by auto" benchLib.Auto false []
     ``(((combin$o THE) SOME) = I)``,
   entry "option_L56_split_option_all" 56
     "by (auto intro: option.induct)" benchLib.Auto false []
     ``((!b_x : ('a option). ((v_P0 : (('a option) -> bool)) b_x)) = (((v_P0 : (('a option) -> bool)) NONE) /\ (!b_x : 'a. ((v_P0 : (('a option) -> bool)) (SOME b_x)))))``,
   entry "option_L59_split_option_ex" 59
     "using split_option_all[of (\\x. ~ P x)] by blast"
     benchLib.Blast false []
     ``((?b_x : ('a option). ((v_P0 : (('a option) -> bool)) b_x)) = (((v_P0 : (('a option) -> bool)) NONE) \/ (?b_x : 'a. ((v_P0 : (('a option) -> bool)) (SOME b_x)))))``,
   entry "option_L62_UNIV_option_conv" 62 "by (auto intro: classical)" benchLib.Auto false []
     ``(UNIV = (NONE INSERT (IMAGE SOME UNIV)))``,
   entry "option_L91_ospec" 91 "by simp" benchLib.Simp false []
     ``((!b_x : 'a. (b_x IN ((\b_set_option : ('a option). \b_set_item : 'a. b_set_option = SOME b_set_item) (v_A0 : ('a option)))) ==> ((v_P0 : ('a -> bool)) b_x)) ==> (((v_A0 : ('a option)) = (SOME (v_x0 : 'a))) ==> ((v_P0 : ('a -> bool)) (v_x0 : 'a))))``,
   entry "option_L102_map_option_case" 102 "by (auto split: option.split)" benchLib.Auto false []
     ``(((OPTION_MAP (v_f0 : ('b -> 'a))) (v_y0 : ('b option))) = ((((\b_option_none : ('a option). \b_option_some : ('b -> ('a option)). \b_option_value : ('b option). option_CASE b_option_value b_option_none b_option_some) NONE) (\b_x : 'b. (SOME ((v_f0 : ('b -> 'a)) b_x)))) (v_y0 : ('b option))))``,
   entry "option_L105_map_option_is_None" 105 "by (simp add: map_option_case split: option.split)" benchLib.Simp true [{name = "optionAutoSeed$OPTION_MAP_EQ_NONE_AUTO", theorem = optionAutoSeedTheory.OPTION_MAP_EQ_NONE_AUTO}, {name = "option$OPTION_MAP_EQ_NONE", theorem = optionTheory.OPTION_MAP_EQ_NONE}]
     ``((((OPTION_MAP (v_f0 : ('b -> 'a))) (v_opt0 : ('b option))) = NONE) = ((v_opt0 : ('b option)) = NONE))``,
   entry "option_L111_map_option_eq_Some" 111 "by (simp add: map_option_case split: option.split)" benchLib.Simp false []
     ``((((OPTION_MAP (v_f0 : ('b -> 'a))) (v_xo0 : ('b option))) = (SOME (v_y0 : 'a))) = (?b_z : 'b. (((v_xo0 : ('b option)) = (SOME b_z)) /\ (((v_f0 : ('b -> 'a)) b_z) = (v_y0 : 'a)))))``,
   entry "option_L130_None_notin_image_Some" 130 "by auto" benchLib.Auto false []
     ``(~(NONE IN (IMAGE SOME (v_A0 : ('a set)))))``,
   entry "option_L136_rel_option_iff" 136 "by (auto split: prod.split option.split)" benchLib.Auto false []
     ``((((OPTREL (v_R0 : ('a -> ('b -> bool)))) (v_x0 : ('a option))) (v_y0 : ('b option))) = ((UNCURRY (\b_a : ('a option). (\b_b : ('b option). ((((\b_option_none : bool. \b_option_some : ('a -> bool). \b_option_value : ('a option). option_CASE b_option_value b_option_none b_option_some) ((((\b_option_none : bool. \b_option_some : ('b -> bool). \b_option_value : ('b option). option_CASE b_option_value b_option_none b_option_some) T) (\b_a : 'b. F)) b_b)) (\b_x : 'a. ((((\b_option_none : bool. \b_option_some : ('b -> bool). \b_option_value : ('b option). option_CASE b_option_value b_option_none b_option_some) F) (\b_y : 'b. (((v_R0 : ('a -> ('b -> bool))) b_x) b_y))) b_b))) b_a)))) ((v_x0 : ('a option)),(v_y0 : ('b option)))))``,
   entry "option_L163_combine_options_assoc" 163 "by (auto simp: combine_options_def split: option.splits)" benchLib.Auto false []
     ``((!b_x : 'a. (!b_y : 'a. (!b_z : 'a. ((((v_f0 : ('a -> ('a -> 'a))) (((v_f0 : ('a -> ('a -> 'a))) b_x) b_y)) b_z) = (((v_f0 : ('a -> ('a -> 'a))) b_x) (((v_f0 : ('a -> ('a -> 'a))) b_y) b_z)))))) ==> (((((\b_combine : ('a -> ('a -> 'a)). \b_option_left : ('a option). \b_option_right : ('a option). option_CASE b_option_left b_option_right (\b_combine_left. option_CASE b_option_right (SOME b_combine_left) (\b_combine_right. SOME (b_combine b_combine_left b_combine_right)))) (v_f0 : ('a -> ('a -> 'a)))) ((((\b_combine : ('a -> ('a -> 'a)). \b_option_left : ('a option). \b_option_right : ('a option). option_CASE b_option_left b_option_right (\b_combine_left. option_CASE b_option_right (SOME b_combine_left) (\b_combine_right. SOME (b_combine b_combine_left b_combine_right)))) (v_f0 : ('a -> ('a -> 'a)))) (v_x0 : ('a option))) (v_y0 : ('a option)))) (v_z0 : ('a option))) = ((((\b_combine : ('a -> ('a -> 'a)). \b_option_left : ('a option). \b_option_right : ('a option). option_CASE b_option_left b_option_right (\b_combine_left. option_CASE b_option_right (SOME b_combine_left) (\b_combine_right. SOME (b_combine b_combine_left b_combine_right)))) (v_f0 : ('a -> ('a -> 'a)))) (v_x0 : ('a option))) ((((\b_combine : ('a -> ('a -> 'a)). \b_option_left : ('a option). \b_option_right : ('a option). option_CASE b_option_left b_option_right (\b_combine_left. option_CASE b_option_right (SOME b_combine_left) (\b_combine_right. SOME (b_combine b_combine_left b_combine_right)))) (v_f0 : ('a -> ('a -> 'a)))) (v_y0 : ('a option))) (v_z0 : ('a option))))))``,
   entry "option_L169_combine_options_left_commute" 169 "by (auto simp: combine_options_def split: option.splits)" benchLib.Auto false []
     ``((!b_x : 'a. (!b_y : 'a. ((((v_f0 : ('a -> ('a -> 'a))) b_x) b_y) = (((v_f0 : ('a -> ('a -> 'a))) b_y) b_x)))) ==> ((!b_x : 'a. (!b_y : 'a. (!b_z : 'a. ((((v_f0 : ('a -> ('a -> 'a))) (((v_f0 : ('a -> ('a -> 'a))) b_x) b_y)) b_z) = (((v_f0 : ('a -> ('a -> 'a))) b_x) (((v_f0 : ('a -> ('a -> 'a))) b_y) b_z)))))) ==> (((((\b_combine : ('a -> ('a -> 'a)). \b_option_left : ('a option). \b_option_right : ('a option). option_CASE b_option_left b_option_right (\b_combine_left. option_CASE b_option_right (SOME b_combine_left) (\b_combine_right. SOME (b_combine b_combine_left b_combine_right)))) (v_f0 : ('a -> ('a -> 'a)))) (v_y0 : ('a option))) ((((\b_combine : ('a -> ('a -> 'a)). \b_option_left : ('a option). \b_option_right : ('a option). option_CASE b_option_left b_option_right (\b_combine_left. option_CASE b_option_right (SOME b_combine_left) (\b_combine_right. SOME (b_combine b_combine_left b_combine_right)))) (v_f0 : ('a -> ('a -> 'a)))) (v_x0 : ('a option))) (v_z0 : ('a option)))) = ((((\b_combine : ('a -> ('a -> 'a)). \b_option_left : ('a option). \b_option_right : ('a option). option_CASE b_option_left b_option_right (\b_combine_left. option_CASE b_option_right (SOME b_combine_left) (\b_combine_right. SOME (b_combine b_combine_left b_combine_right)))) (v_f0 : ('a -> ('a -> 'a)))) (v_x0 : ('a option))) ((((\b_combine : ('a -> ('a -> 'a)). \b_option_left : ('a option). \b_option_right : ('a option). option_CASE b_option_left b_option_right (\b_combine_left. option_CASE b_option_right (SOME b_combine_left) (\b_combine_right. SOME (b_combine b_combine_left b_combine_right)))) (v_f0 : ('a -> ('a -> 'a)))) (v_y0 : ('a option))) (v_z0 : ('a option)))))))``,
   entry "option_L195_rel_option_unfold" 195 "by (simp add: rel_option_iff split: option.split)" benchLib.Simp false []
     ``((((OPTREL (v_R0 : ('a -> ('b -> bool)))) (v_x0 : ('a option))) (v_y0 : ('b option))) = (((IS_NONE (v_x0 : ('a option))) = (IS_NONE (v_y0 : ('b option)))) /\ ((~(IS_NONE (v_x0 : ('a option)))) ==> ((~(IS_NONE (v_y0 : ('b option)))) ==> (((v_R0 : ('a -> ('b -> bool))) (THE (v_x0 : ('a option)))) (THE (v_y0 : ('b option))))))))``,
   entry "option_L200_rel_optionI" 200 "by (simp add: rel_option_unfold)" benchLib.Simp false []
     ``(((IS_NONE (v_x0 : ('a option))) = (IS_NONE (v_y0 : ('b option)))) ==> (((~(IS_NONE (v_x0 : ('a option)))) ==> ((~(IS_NONE (v_y0 : ('b option)))) ==> (((v_P0 : ('a -> ('b -> bool))) (THE (v_x0 : ('a option)))) (THE (v_y0 : ('b option)))))) ==> (((OPTREL (v_P0 : ('a -> ('b -> bool)))) (v_x0 : ('a option))) (v_y0 : ('b option)))))``,
   entry "option_L205_is_none_map_option" 205 "by (simp add: is_none_def)" benchLib.Simp false []
     ``((IS_NONE ((OPTION_MAP (v_f0 : ('b -> 'a))) (v_x0 : ('b option)))) = (IS_NONE (v_x0 : ('b option))))``,
   entry "option_L208_the_map_option" 208 "by (auto simp add: is_none_def)" benchLib.Auto false []
     ``((~(IS_NONE (v_x0 : ('a option)))) ==> ((THE ((OPTION_MAP (v_f0 : ('a -> 'b))) (v_x0 : ('a option)))) = ((v_f0 : ('a -> 'b)) (THE (v_x0 : ('a option))))))``,
   entry "option_L257_bind_option_cong_code" 257 "by simp" benchLib.Simp false []
     ``(((v_x0 : ('a option)) = (v_y0 : ('a option))) ==> ((OPTION_BIND (v_x0 : ('a option)) (v_f0 : ('a -> ('b option)))) = (OPTION_BIND (v_y0 : ('a option)) (v_f0 : ('a -> ('b option))))))``,
   entry "option_L288_these_empty" 288 "by (simp add: these_def)" benchLib.Simp false []
     ``(((\b_these_source : (('a option) set). \b_these_item : 'a. SOME b_these_item IN b_these_source) {}) = {})``,
   entry "option_L291_these_insert_None" 291 "by (auto simp add: these_def)" benchLib.Auto false []
     ``(((\b_these_source : (('a option) set). \b_these_item : 'a. SOME b_these_item IN b_these_source) (NONE INSERT (v_A0 : (('a option) set)))) = ((\b_these_source : (('a option) set). \b_these_item : 'a. SOME b_these_item IN b_these_source) (v_A0 : (('a option) set))))``,
   entry "option_L311_these_image_Some_eq" 311 "by (auto simp add: these_def intro!: image_eqI)" benchLib.Auto false []
     ``(((\b_these_source : (('a option) set). \b_these_item : 'a. SOME b_these_item IN b_these_source) (IMAGE SOME (v_A0 : ('a set)))) = (v_A0 : ('a set)))``,
   entry "option_L314_Some_image_these_eq" 314 "by (auto simp add: these_def image_image intro!: image_eqI)" benchLib.Auto false []
     ``((IMAGE SOME ((\b_these_source : (('a option) set). \b_these_item : 'a. SOME b_these_item IN b_these_source) (v_A0 : (('a option) set)))) = (\b_x : ('a option). ((b_x IN (v_A0 : (('a option) set))) /\ (~(b_x = NONE)))))``,
   entry "option_L317_these_empty_eq" 317 "by (auto simp add: these_def)" benchLib.Auto false []
     ``((((\b_these_source : (('a option) set). \b_these_item : 'a. SOME b_these_item IN b_these_source) (v_B0 : (('a option) set))) = {}) = (((v_B0 : (('a option) set)) = {}) \/ ((v_B0 : (('a option) set)) = (NONE INSERT {}))))``,
   entry "option_L320_these_not_empty_eq" 320 "by (auto simp add: these_empty_eq)" benchLib.Auto false []
     ``((~(((\b_these_source : (('a option) set). \b_these_item : 'a. SOME b_these_item IN b_these_source) (v_B0 : (('a option) set))) = {})) = ((~((v_B0 : (('a option) set)) = {})) /\ (~((v_B0 : (('a option) set)) = (NONE INSERT {})))))``,
   entry "option_L328_finite_range_Some" 328 "by (auto dest: finite_imageD intro: inj_Some)" benchLib.Auto false []
     ``((FINITE
          (IMAGE (SOME : 'a -> 'a option) (UNIV : 'a set))) =
        (FINITE (UNIV : 'a set)))``,
   entry "option_L337_option_bind_transfer" 337 "by simp" benchLib.Simp false []
     ``(((((\b_rel_left : (('a option) -> (('b option) -> bool)). \b_rel_right : ((('a -> ('c option)) -> ('c option)) -> ((('b -> ('d option)) -> ('d option)) -> bool)). \b_rel_left_function : (('a option) -> (('a -> ('c option)) -> ('c option))). \b_rel_right_function : (('b option) -> (('b -> ('d option)) -> ('d option))). !b_rel_x : ('a option). !b_rel_y : ('b option). b_rel_left b_rel_x b_rel_y ==> b_rel_right (b_rel_left_function b_rel_x) (b_rel_right_function b_rel_y)) (OPTREL (v_A0 : ('a -> ('b -> bool))))) (((\b_rel_left : (('a -> ('c option)) -> (('b -> ('d option)) -> bool)). \b_rel_right : (('c option) -> (('d option) -> bool)). \b_rel_left_function : (('a -> ('c option)) -> ('c option)). \b_rel_right_function : (('b -> ('d option)) -> ('d option)). !b_rel_x : ('a -> ('c option)). !b_rel_y : ('b -> ('d option)). b_rel_left b_rel_x b_rel_y ==> b_rel_right (b_rel_left_function b_rel_x) (b_rel_right_function b_rel_y)) (((\b_rel_left : ('a -> ('b -> bool)). \b_rel_right : (('c option) -> (('d option) -> bool)). \b_rel_left_function : ('a -> ('c option)). \b_rel_right_function : ('b -> ('d option)). !b_rel_x : 'a. !b_rel_y : 'b. b_rel_left b_rel_x b_rel_y ==> b_rel_right (b_rel_left_function b_rel_x) (b_rel_right_function b_rel_y)) (v_A0 : ('a -> ('b -> bool)))) (OPTREL (v_B0 : ('c -> ('d -> bool)))))) (OPTREL (v_B0 : ('c -> ('d -> bool)))))) OPTION_BIND) OPTION_BIND)``,
   entry "option_L351_finite_option_UNIV" 351 "by (auto simp add: UNIV_option_conv elim: finite_imageD intro: inj_Some)" benchLib.Auto false []
     ``((FINITE (UNIV : ('a option) set)) =
        (FINITE (UNIV : 'a set)))``,
   entry "option_L361_equal_None_code_unfold_1" 361 "by (auto simp add: equal Option.is_none_def)" benchLib.Auto false []
     ``((((\b_equal_left : ('a option). \b_equal_right : ('a option). b_equal_left = b_equal_right) (v_x0 : ('a option))) NONE) = (IS_NONE (v_x0 : ('a option))))``,
   entry "option_L361_equal_None_code_unfold_2" 361 "by (auto simp add: equal Option.is_none_def)" benchLib.Auto false []
     ``(((\b_equal_left : ('b option). \b_equal_right : ('b option). b_equal_left = b_equal_right) NONE) = IS_NONE)``
  ]

end
