structure benchSetCorpus =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

(* Isabelle line 1634 is HOL4 aconv-identical to line 505.  Line 994 is
   registered by benchSets as a type-class translation gap. *)

fun named name theorem = {name = name, theorem = theorem}

val common_args =
  [benchLib.RewriteAdd
     (named "pred_set$SPECIFICATION" pred_setTheory.SPECIFICATION),
   benchLib.DefinitionAdd
     (named "pred_set$SUBSET_DEF" pred_setTheory.SUBSET_DEF)]

fun method_args method =
  common_args @
  (if String.isSubstring "Uniq_def" method orelse
      String.isSubstring "elim: equalityE" method orelse
      String.isSubstring "dest: subset_antisym" method then
     [benchLib.RewriteDelete "pred_set.EXTENSION",
      benchLib.RewriteDelete "bool.FUN_EQ_THM"]
   else
     [benchLib.DefinitionAdd
        (named "pred_set$EXTENSION" pred_setTheory.EXTENSION),
      benchLib.RewriteAdd
        (named "bool$FUN_EQ_THM" boolTheory.FUN_EQ_THM)]) @
  (if String.isSubstring "disjnt_iff" method then
     [benchLib.RewriteAdd
        (named "pred_set$DISJOINT_ALT" pred_setTheory.DISJOINT_ALT)]
   else
     [benchLib.DefinitionAdd
        (named "pred_set$DISJOINT_DEF" pred_setTheory.DISJOINT_DEF)]) @
  (if String.isSubstring "Ball_def" method then
     [benchLib.RewriteAdd
        (named "bool$LEFT_FORALL_IMP_THM"
           boolTheory.LEFT_FORALL_IMP_THM)]
   else
     []) @
  (if String.isSubstring "Bex_def" method then
     [benchLib.RewriteAdd
        (named "bool$LEFT_EXISTS_AND_THM"
           boolTheory.LEFT_EXISTS_AND_THM)]
   else
     []) @
  (if String.isSubstring "image_def" method then
     [benchLib.RewriteDelete "pred_set.IN_IMAGE",
      benchLib.DefinitionAdd
        (named "parityTranslation$source_image_expansion"
           parityTranslationTheory.source_image_expansion),
      benchLib.CongruenceAdd
        (named "parityTranslation$source_rev_conj_cong"
           parityTranslationTheory.source_rev_conj_cong)]
   else
     []) @
  (if String.isSubstring "cong: conj_cong" method then
     [benchLib.CongruenceAdd
        (named "parityTranslation$source_conj_cong"
           parityTranslationTheory.source_conj_cong)]
   else
     []) @
  (if String.isSubstring "disjnt_def" method then
     [benchLib.RewriteAdd
        (named "bool$CONJ_COMM" boolTheory.CONJ_COMM)]
   else
     []) @
  (if String.isSubstring "is_singleton_def" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_is_singleton_bridge"
           parityTranslationTheory.source_is_singleton_bridge)] @
     (if String.isSubstring "simp add:" method then
        [benchLib.RewriteAdd
           (named "parityTranslation$source_is_singleton_unique"
              parityTranslationTheory.source_is_singleton_unique)]
      else
        [benchLib.RewriteAdd
           (named "parityTranslation$source_is_singleton_choice"
              parityTranslationTheory.source_is_singleton_choice)])
   else
     []) @
  (if String.isSubstring "subset_imageE" method then
     [benchLib.ElimAdd
        (benchLib.UnsafeRule,
         named "parityTranslation$source_subset_imageE"
           parityTranslationTheory.source_subset_imageE)]
   else
     []) @
  (if String.isSubstring "elim: equalityE" method then
     [benchLib.ElimAdd
        (benchLib.UnsafeRule,
         named "parityTranslation$source_set_equality_elim"
           parityTranslationTheory.source_set_equality_elim)]
   else
     []) @
  (if String.isSubstring "bool_induct" method then
     [benchLib.RewriteAdd
        (named "bool$EQ_IMP_THM" boolTheory.EQ_IMP_THM),
      benchLib.FactAdd
        (named "parityTranslation$source_bool_induct"
           parityTranslationTheory.source_bool_induct)]
   else
     []) @
  (if String.isSubstring "bool_contrapos" method then
     [benchLib.IntroAdd
        (benchLib.UnsafeRule,
         named "parityTranslation$source_bool_contrapos"
           parityTranslationTheory.source_bool_contrapos)]
   else
     []) @
  (if String.isSubstring "dest: subset_antisym" method then
     [benchLib.RewriteDelete "pred_set$SUBSET_ANTISYM",
      benchLib.DestAdd
        (benchLib.UnsafeRule,
         named "parityTranslation$source_subset_sandwich"
           parityTranslationTheory.source_subset_sandwich)]
   else
     []) @
  (if String.isSubstring "intro: sym" method then
     [benchLib.IntroAdd
        (benchLib.UnsafeRule,
         named "bool$EQ_SYM" boolTheory.EQ_SYM)]
   else
     []) @
  (if String.isSubstring
        "image_eqI [where ?x = \"u - {a}\"" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_in_pow_insert"
           parityTranslationTheory.source_in_pow_insert),
      benchLib.RewriteAdd
        (named "parityTranslation$source_pow_insert_image_case_iff"
           parityTranslationTheory.source_pow_insert_image_case_iff),
      benchLib.IntroAdd
        (benchLib.UnsafeRule,
         named "parityTranslation$source_pow_insert_image_witness"
           parityTranslationTheory.source_pow_insert_image_witness),
      benchLib.IntroAdd
        (benchLib.UnsafeRule,
         named "parityTranslation$source_pow_insert_image_case"
           parityTranslationTheory.source_pow_insert_image_case)]
   else
     []) @
  (if String.isSubstring
        "exI [where ?x = \"- u\"" method then
     [benchLib.IntroAdd
        (benchLib.UnsafeRule,
         named "parityTranslation$source_complement_exI"
           parityTranslationTheory.source_complement_exI)]
   else
     [])

fun source_args method =
  (if String.isSubstring "elim: equalityE" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_doubleton_eq_iff"
           parityTranslationTheory.source_doubleton_eq_iff)]
   else
     []) @
  (if String.isSubstring "subset_imageE" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_subset_image_iff"
           parityTranslationTheory.source_subset_image_iff),
      benchLib.RewriteAdd
        (named "parityTranslation$source_image_pow_surj_iff"
           parityTranslationTheory.source_image_pow_surj_iff)]
   else
     []) @
  (if String.isSubstring "somewhat slow" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_pow_singleton_iff"
           parityTranslationTheory.source_pow_singleton_iff)]
   else
     []) @
  (if String.isSubstring "exI [where ?x = \"- u\"" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_pow_compl_iff"
           parityTranslationTheory.source_pow_compl_iff)]
   else
     []) @
  (if method = "by (force simp: pairwise_def)" then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_pairwise_image"
           parityTranslationTheory.source_pairwise_image)]
   else
     [])

fun needs_pre_simplification method =
  List.exists
    (fn marker => String.isSubstring marker method)
    ["elim: equalityE",
     "subset_imageE",
     "somewhat slow",
     "image_eqI [where ?x = \"u - {a}\"",
     "exI [where ?x = \"- u\""] orelse
  method = "by (force simp: pairwise_def)"

fun entry id line method mapped representative excl goal :
    benchLib.corpus_goal =
  let
    val arguments =
      method_args method @ source_args method @
      (if mapped = benchLib.Auto andalso
          not (String.isSubstring "dest: subset_antisym" method) then
         [benchLib.DestAdd
            (benchLib.SafeRule,
             named "parityTranslation$source_forall_iffD1"
               parityTranslationTheory.source_forall_iffD1),
          benchLib.DestAdd
            (benchLib.SafeRule,
             named "parityTranslation$source_forall_iffD2"
               parityTranslationTheory.source_forall_iffD2)]
       else
         [])
    val recipe =
      if String.isSubstring "dest: subset_antisym" method then
        benchLib.AllGoals
          (benchLib.Invoke (benchLib.Simp, arguments),
           benchLib.AllGoals
             (benchLib.Invoke (benchLib.Safe, arguments),
              benchLib.Invoke (benchLib.Auto, arguments)))
      else if needs_pre_simplification method then
        benchLib.AllGoals
          (benchLib.Invoke (benchLib.Simp, arguments),
           benchLib.Invoke (mapped, arguments))
      else if String.isSubstring "Uniq_def" method then
        benchLib.AllGoals
          (benchLib.Invoke (mapped, arguments),
           benchLib.Invoke
             (benchLib.Blast,
              [benchLib.FactAdd
                 (named "parityTranslation$source_unique_member_transfer"
                    parityTranslationTheory.source_unique_member_transfer)]))
      else if mapped = benchLib.Auto then
        benchLib.AllGoals
          (benchLib.Invoke (benchLib.Simp, arguments),
           benchLib.Invoke (benchLib.Auto, arguments))
      else
        benchLib.Invoke (mapped, arguments)
  in
    {id = id, goal = goal, source_method = method, recipe = recipe,
     excl = List.filter (fn {theorem, ...} =>
       benchLib.theorem_is_goal goal theorem) excl,
     provenance =
       {file = "src/HOL/Set.thy", line = line, commit = commit},
     representative = representative}
  end

val goals =
  [
   entry "set_L70_CollectI" 70 "by simp" benchLib.Simp false []
     ``(((v_P0 : ('a -> bool)) (v_a0 : 'a)) ==> ((v_a0 : 'a) IN (\b_x : 'a. ((v_P0 : ('a -> bool)) b_x))))``,
   entry "set_L73_CollectD" 73 "by simp" benchLib.Simp false []
     ``(((v_a0 : 'a) IN (\b_x : 'a. ((v_P0 : ('a -> bool)) b_x))) ==> ((v_P0 : ('a -> bool)) (v_a0 : 'a)))``,
   entry "set_L76_Collect_cong" 76 "by simp" benchLib.Simp false []
     ``((!b_x : 'a. (((v_P0 : ('a -> bool)) b_x) = ((v_Q0 : ('a -> bool)) b_x))) ==> ((\b_x : 'a. ((v_P0 : ('a -> bool)) b_x)) = (\b_x : 'a. ((v_Q0 : ('a -> bool)) b_x))))``,
   entry "set_L105_set_eq_iff" 105 "by (auto intro:set_eqI)" benchLib.Auto false []
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) = (!b_x : 'a. ((b_x IN (v_A0 : ('a set))) = (b_x IN (v_B0 : ('a set))))))``,
   entry "set_L108_Collect_eqI" 108 "by (auto intro: set_eqI)" benchLib.Auto false []
     ``((!b_x : 'a. (((v_P0 : ('a -> bool)) b_x) = ((v_Q0 : ('a -> bool)) b_x))) ==> ((v_P0 : ('a -> bool)) = (v_Q0 : ('a -> bool))))``,
   entry "set_L378_ballI" 378 "by (simp add: Ball_def)" benchLib.Simp false []
     ``((!b_x : 'a. ((b_x IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) b_x))) ==> (!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) b_x)))``,
   entry "set_L383_bspec" 383 "by (simp add: Ball_def)" benchLib.Simp false []
     ``((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) b_x)) ==> (((v_x0 : 'a) IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) (v_x0 : 'a))))``,
   entry "set_L404_ballE" 404 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) b_x)) ==> ((((v_P0 : ('a -> bool)) (v_x0 : 'a)) ==> (v_Q0 : bool)) ==> (((~((v_x0 : 'a) IN (v_A0 : ('a set)))) ==> (v_Q0 : bool)) ==> (v_Q0 : bool))))``,
   entry "set_L407_bexI" 407 "by blast" benchLib.Blast false []
     ``(((v_P0 : ('a -> bool)) (v_x0 : 'a)) ==> (((v_x0 : 'a) IN (v_A0 : ('a set))) ==> (?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x))))``,
   entry "set_L411_rev_bexI" 411 "by blast" benchLib.Blast false []
     ``(((v_x0 : 'a) IN (v_A0 : ('a set))) ==> (((v_P0 : ('a -> bool)) (v_x0 : 'a)) ==> (?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x))))``,
   entry "set_L415_bexCI" 415 "by blast" benchLib.Blast false []
     ``(((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> (~((v_P0 : ('a -> bool)) b_x))) ==> ((v_P0 : ('a -> bool)) (v_a0 : 'a))) ==> (((v_a0 : 'a) IN (v_A0 : ('a set))) ==> (?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x))))``,
   entry "set_L418_bexE" 418 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x)) ==> ((!b_x : 'a. ((b_x IN (v_A0 : ('a set))) ==> (((v_P0 : ('a -> bool)) b_x) ==> (v_Q0 : bool)))) ==> (v_Q0 : bool)))``,
   entry "set_L421_ball_triv" 421 "by (simp add: Ball_def)" benchLib.Simp false []
     ``((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> (v_P0 : bool)) = ((?b_x : 'a. (b_x IN (v_A0 : ('a set)))) ==> (v_P0 : bool)))``,
   entry "set_L425_bex_triv" 425 "by (simp add: Bex_def)" benchLib.Simp false []
     ``((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ (v_P0 : bool)) = ((?b_x : 'a. (b_x IN (v_A0 : ('a set)))) /\ (v_P0 : bool)))``,
   entry "set_L429_bex_triv_one_point1" 429 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ (b_x = (v_a0 : 'a))) = ((v_a0 : 'a) IN (v_A0 : ('a set))))``,
   entry "set_L432_bex_triv_one_point2" 432 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_a0 : 'a) = b_x)) = ((v_a0 : 'a) IN (v_A0 : ('a set))))``,
   entry "set_L435_bex_one_point1" 435 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((b_x = (v_a0 : 'a)) /\ ((v_P0 : ('a -> bool)) b_x))) = (((v_a0 : 'a) IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) (v_a0 : 'a))))``,
   entry "set_L438_bex_one_point2" 438 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ (((v_a0 : 'a) = b_x) /\ ((v_P0 : ('a -> bool)) b_x))) = (((v_a0 : 'a) IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) (v_a0 : 'a))))``,
   entry "set_L441_ball_one_point1" 441 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> ((b_x = (v_a0 : 'a)) ==> ((v_P0 : ('a -> bool)) b_x))) = (((v_a0 : 'a) IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) (v_a0 : 'a))))``,
   entry "set_L444_ball_one_point2" 444 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> (((v_a0 : 'a) = b_x) ==> ((v_P0 : ('a -> bool)) b_x))) = (((v_a0 : 'a) IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) (v_a0 : 'a))))``,
   entry "set_L447_ball_conj_distrib" 447 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> (((v_P0 : ('a -> bool)) b_x) /\ ((v_Q0 : ('a -> bool)) b_x))) = ((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) b_x)) /\ (!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> ((v_Q0 : ('a -> bool)) b_x))))``,
   entry "set_L450_bex_disj_distrib" 450 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ (((v_P0 : ('a -> bool)) b_x) \/ ((v_Q0 : ('a -> bool)) b_x))) = ((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x)) \/ (?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_Q0 : ('a -> bool)) b_x))))``,
   entry "set_L456_ball_cong" 456 "by (simp add: Ball_def)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) ==> ((!b_x : 'a. ((b_x IN (v_B0 : ('a set))) ==> (((v_P0 : ('a -> bool)) b_x) = ((v_Q0 : ('a -> bool)) b_x)))) ==> ((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) b_x)) = (!b_x : 'a. (b_x IN (v_B0 : ('a set))) ==> ((v_Q0 : ('a -> bool)) b_x)))))``,
   entry "set_L466_bex_cong" 466 "by (simp add: Bex_def cong: conj_cong)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) ==> ((!b_x : 'a. ((b_x IN (v_B0 : ('a set))) ==> (((v_P0 : ('a -> bool)) b_x) = ((v_Q0 : ('a -> bool)) b_x)))) ==> ((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x)) = (?b_x : 'a. (b_x IN (v_B0 : ('a set))) /\ ((v_Q0 : ('a -> bool)) b_x)))))``,
   entry "set_L476_bex1_def" 476 "by auto" benchLib.Auto false []
     ``((?!b_x : 'a. ((b_x IN (v_X0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x))) = ((?b_x : 'a. (b_x IN (v_X0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x)) /\ (!b_x : 'a. (b_x IN (v_X0 : ('a set))) ==> (!b_y : 'a. (b_y IN (v_X0 : ('a set))) ==> (((v_P0 : ('a -> bool)) b_x) ==> (((v_P0 : ('a -> bool)) b_y) ==> (b_x = b_y)))))))``,
   entry "set_L484_subsetI" 484 "by (simp add: less_eq_set_def le_fun_def)" benchLib.Simp false []
     ``((!b_x : 'a. ((b_x IN (v_A0 : ('a set))) ==> (b_x IN (v_B0 : ('a set))))) ==> ((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))))``,
   entry "set_L493_subsetD" 493 "by (simp add: less_eq_set_def le_fun_def)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> (((v_c0 : 'a) IN (v_A0 : ('a set))) ==> ((v_c0 : 'a) IN (v_B0 : ('a set)))))``,
   entry "set_L501_subsetCE" 501 "by (auto simp add: less_eq_set_def le_fun_def)" benchLib.Auto false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> (((~((v_c0 : 'a) IN (v_A0 : ('a set)))) ==> (v_P0 : bool)) ==> ((((v_c0 : 'a) IN (v_B0 : ('a set))) ==> (v_P0 : bool)) ==> (v_P0 : bool))))``,
   entry "set_L505_subset_eq" 505 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) = (!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> (b_x IN (v_B0 : ('a set)))))``,
   entry "set_L508_contra_subsetD" 508 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> ((~((v_c0 : 'a) IN (v_B0 : ('a set)))) ==> (~((v_c0 : 'a) IN (v_A0 : ('a set))))))``,
   entry "set_L520_eq_mem_trans" 520 "by simp" benchLib.Simp false []
     ``(((v_a0 : 'a) = (v_b0 : 'a)) ==> (((v_b0 : 'a) IN (v_A0 : ('a set))) ==> ((v_a0 : 'a) IN (v_A0 : ('a set)))))``,
   entry "set_L535_equalityD1" 535 "by simp" benchLib.Simp false []
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) ==> ((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))))``,
   entry "set_L538_equalityD2" 538 "by simp" benchLib.Simp false []
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) ==> ((v_B0 : ('a set)) SUBSET (v_A0 : ('a set))))``,
   entry "set_L548_equalityE" 548 "by simp" benchLib.Simp false []
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) ==> ((((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> (((v_B0 : ('a set)) SUBSET (v_A0 : ('a set))) ==> (v_P0 : bool))) ==> (v_P0 : bool)))``,
   entry "set_L551_equalityCE" 551 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) ==> ((((v_c0 : 'a) IN (v_A0 : ('a set))) ==> (((v_c0 : 'a) IN (v_B0 : ('a set))) ==> (v_P0 : bool))) ==> (((~((v_c0 : 'a) IN (v_A0 : ('a set)))) ==> ((~((v_c0 : 'a) IN (v_B0 : ('a set)))) ==> (v_P0 : bool))) ==> (v_P0 : bool))))``,
   entry "set_L554_eqset_imp_iff" 554 "by simp" benchLib.Simp false []
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) ==> (((v_x0 : 'a) IN (v_A0 : ('a set))) = ((v_x0 : 'a) IN (v_B0 : ('a set)))))``,
   entry "set_L557_eqelem_imp_iff" 557 "by simp" benchLib.Simp false []
     ``(((v_x0 : 'a) = (v_y0 : 'a)) ==> (((v_x0 : 'a) IN (v_A0 : ('a set))) = ((v_y0 : 'a) IN (v_A0 : ('a set)))))``,
   entry "set_L563_empty_def" 563 "by (simp add: bot_set_def bot_fun_def)" benchLib.Simp false [{name = "fixedPoint$empty_def", theorem = fixedPointTheory.empty_def}, {name = "pred_set$EMPTY_DEF", theorem = pred_setTheory.EMPTY_DEF}]
     ``({} = (\b_x : 'a. F))``,
   entry "set_L566_empty_iff" 566 "by (simp add: empty_def)" benchLib.Simp false []
     ``(((v_c0 : 'a) IN {}) = F)``,
   entry "set_L569_emptyE" 569 "by simp" benchLib.Simp false []
     ``(((v_a0 : 'a) IN {}) ==> (v_P0 : bool))``,
   entry "set_L572_empty_subsetI" 572 "by blast" benchLib.Blast true [{name = "pred_setAutoSeed$EMPTY_SUBSET_AUTO", theorem = pred_setAutoSeedTheory.EMPTY_SUBSET_AUTO}, {name = "pred_set$EMPTY_SUBSET", theorem = pred_setTheory.EMPTY_SUBSET}]
     ``({} SUBSET (v_A0 : ('a set)))``,
   entry "set_L576_equals0I" 576 "by blast" benchLib.Blast false []
     ``((!b_y : 'a. ((b_y IN (v_A0 : ('a set))) ==> F)) ==> ((v_A0 : ('a set)) = {}))``,
   entry "set_L579_equals0D" 579 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) = {}) ==> (~((v_a0 : 'a) IN (v_A0 : ('a set)))))``,
   entry "set_L583_ball_empty" 583 "by (simp add: Ball_def)" benchLib.Simp false []
     ``((!b_set : 'a. (b_set IN {}) ==> ((v_P0 : ('a -> bool)) b_set)) = T)``,
   entry "set_L586_bex_empty" 586 "by (simp add: Bex_def)" benchLib.Simp false []
     ``((?b_set : 'a. (b_set IN {}) /\ ((v_P0 : ('a -> bool)) b_set)) = F)``,
   entry "set_L595_UNIV_def" 595 "by (simp add: top_set_def top_fun_def)" benchLib.Simp false [{name = "pred_set$UNIV_DEF", theorem = pred_setTheory.UNIV_DEF}]
     ``(UNIV = (\b_x : 'a. T))``,
   entry "set_L598_UNIV_I" 598 "by (simp add: UNIV_def)" benchLib.Simp false []
     ``((v_x0 : 'a) IN UNIV)``,
   entry "set_L603_UNIV_witness" 603 "by simp" benchLib.Simp false []
     ``(?b_x : 'a. (b_x IN UNIV))``,
   entry "set_L615_ball_UNIV" 615 "by (simp add: Ball_def)" benchLib.Simp false []
     ``((!b_set : 'a. (b_set IN UNIV) ==> ((v_P0 : ('a -> bool)) b_set)) = (!b_pred : 'a. (v_P0 : ('a -> bool)) b_pred))``,
   entry "set_L618_bex_UNIV" 618 "by (simp add: Bex_def)" benchLib.Simp false []
     ``((?b_set : 'a. (b_set IN UNIV) /\ ((v_P0 : ('a -> bool)) b_set)) = (?b_pred : 'a. (v_P0 : ('a -> bool)) b_pred))``,
   entry "set_L621_UNIV_eq_I" 621 "by auto" benchLib.Auto false []
     ``((!b_x : 'a. (b_x IN (v_A0 : ('a set)))) ==> (UNIV = (v_A0 : ('a set))))``,
   entry "set_L624_UNIV_not_empty" 624 "by (blast elim: equalityE)" benchLib.Blast false [{name = "pred_set$UNIV_NOT_EMPTY", theorem = pred_setTheory.UNIV_NOT_EMPTY}]
     ``(~(UNIV = {}))``,
   entry "set_L627_empty_not_UNIV" 627 "by blast" benchLib.Blast false [{name = "pred_set$EMPTY_NOT_UNIV", theorem = pred_setTheory.EMPTY_NOT_UNIV}]
     ``(~({} = UNIV))``,
   entry "set_L636_Pow_iff" 636 "by (simp add: Pow_def)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) IN (POW (v_B0 : ('a set)))) = ((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))))``,
   entry "set_L639_PowI" 639 "by (simp add: Pow_def)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> ((v_A0 : ('a set)) IN (POW (v_B0 : ('a set)))))``,
   entry "set_L642_PowD" 642 "by (simp add: Pow_def)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) IN (POW (v_B0 : ('a set)))) ==> ((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))))``,
   entry "set_L645_Pow_bottom" 645 "by simp" benchLib.Simp false []
     ``({} IN (POW (v_B0 : ('a set))))``,
   entry "set_L648_Pow_top" 648 "by simp" benchLib.Simp false []
     ``((v_A0 : ('a set)) IN (POW (v_A0 : ('a set))))``,
   entry "set_L651_Pow_not_empty" 651 "by blast" benchLib.Blast false []
     ``(~((POW (v_A0 : ('a set))) = {}))``,
   entry "set_L657_Compl_iff" 657 "by (simp add: fun_Compl_def uminus_set_def)" benchLib.Simp false []
     ``(((v_c0 : 'a) IN (COMPL (v_A0 : ('a set)))) = (~((v_c0 : 'a) IN (v_A0 : ('a set)))))``,
   entry "set_L670_ComplD" 670 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN (COMPL (v_A0 : ('a set)))) ==> (~((v_c0 : 'a) IN (v_A0 : ('a set)))))``,
   entry "set_L675_Compl_eq" 675 "by blast" benchLib.Blast false []
     ``((COMPL (v_A0 : ('a set))) = (\b_x : 'a. (~(b_x IN (v_A0 : ('a set))))))``,
   entry "set_L687_Int_def" 687 "by (simp add: inf_set_def inf_fun_def)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) INTER (v_B0 : ('a set))) = (\b_x : 'a. ((b_x IN (v_A0 : ('a set))) /\ (b_x IN (v_B0 : ('a set))))))``,
   entry "set_L690_Int_iff" 690 "by blast" benchLib.Blast true [{name = "pred_setAutoSeed$IN_INTER_AUTO", theorem = pred_setAutoSeedTheory.IN_INTER_AUTO}, {name = "pred_set$IN_INTER", theorem = pred_setTheory.IN_INTER}]
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))) = (((v_c0 : 'a) IN (v_A0 : ('a set))) /\ ((v_c0 : 'a) IN (v_B0 : ('a set)))))``,
   entry "set_L693_IntI" 693 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN (v_A0 : ('a set))) ==> (((v_c0 : 'a) IN (v_B0 : ('a set))) ==> ((v_c0 : 'a) IN ((v_A0 : ('a set)) INTER (v_B0 : ('a set))))))``,
   entry "set_L696_IntD1" 696 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))) ==> ((v_c0 : 'a) IN (v_A0 : ('a set))))``,
   entry "set_L699_IntD2" 699 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))) ==> ((v_c0 : 'a) IN (v_B0 : ('a set))))``,
   entry "set_L702_IntE" 702 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))) ==> ((((v_c0 : 'a) IN (v_A0 : ('a set))) ==> (((v_c0 : 'a) IN (v_B0 : ('a set))) ==> (v_P0 : bool))) ==> (v_P0 : bool)))``,
   entry "set_L714_Un_def" 714 "by (simp add: sup_set_def sup_fun_def)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) UNION (v_B0 : ('a set))) = (\b_x : 'a. ((b_x IN (v_A0 : ('a set))) \/ (b_x IN (v_B0 : ('a set))))))``,
   entry "set_L717_Un_iff" 717 "by blast" benchLib.Blast true [{name = "pred_setAutoSeed$IN_UNION_AUTO", theorem = pred_setAutoSeedTheory.IN_UNION_AUTO}, {name = "pred_set$IN_UNION", theorem = pred_setTheory.IN_UNION}]
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))) = (((v_c0 : 'a) IN (v_A0 : ('a set))) \/ ((v_c0 : 'a) IN (v_B0 : ('a set)))))``,
   entry "set_L720_UnI1" 720 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN (v_A0 : ('a set))) ==> ((v_c0 : 'a) IN ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))))``,
   entry "set_L723_UnI2" 723 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN (v_B0 : ('a set))) ==> ((v_c0 : 'a) IN ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))))``,
   entry "set_L727_UnCI" 727 "by auto" benchLib.Auto false []
     ``(((~((v_c0 : 'a) IN (v_B0 : ('a set)))) ==> ((v_c0 : 'a) IN (v_A0 : ('a set)))) ==> ((v_c0 : 'a) IN ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))))``,
   entry "set_L730_UnE" 730 "by blast" benchLib.Blast false []
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))) ==> ((((v_c0 : 'a) IN (v_A0 : ('a set))) ==> (v_P0 : bool)) ==> ((((v_c0 : 'a) IN (v_B0 : ('a set))) ==> (v_P0 : bool)) ==> (v_P0 : bool))))``,
   entry "set_L733_insert_def" 733 "by (simp add: insert_compr Un_def)" benchLib.Simp false []
     ``(((v_a0 : 'a) INSERT (v_B0 : ('a set))) = ((\b_x : 'a. (b_x = (v_a0 : 'a))) UNION (v_B0 : ('a set))))``,
   entry "set_L743_Diff_iff" 743 "by (simp add: minus_set_def fun_diff_def)" benchLib.Simp true [{name = "pred_setAutoSeed$IN_DIFF_AUTO", theorem = pred_setAutoSeedTheory.IN_DIFF_AUTO}, {name = "pred_set$IN_DIFF", theorem = pred_setTheory.IN_DIFF}]
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))) = (((v_c0 : 'a) IN (v_A0 : ('a set))) /\ (~((v_c0 : 'a) IN (v_B0 : ('a set))))))``,
   entry "set_L746_DiffI" 746 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN (v_A0 : ('a set))) ==> ((~((v_c0 : 'a) IN (v_B0 : ('a set)))) ==> ((v_c0 : 'a) IN ((v_A0 : ('a set)) DIFF (v_B0 : ('a set))))))``,
   entry "set_L749_DiffD1" 749 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))) ==> ((v_c0 : 'a) IN (v_A0 : ('a set))))``,
   entry "set_L752_DiffD2" 752 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))) ==> (((v_c0 : 'a) IN (v_B0 : ('a set))) ==> (v_P0 : bool)))``,
   entry "set_L755_DiffE" 755 "by simp" benchLib.Simp false []
     ``(((v_c0 : 'a) IN ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))) ==> ((((v_c0 : 'a) IN (v_A0 : ('a set))) ==> ((~((v_c0 : 'a) IN (v_B0 : ('a set)))) ==> (v_P0 : bool))) ==> (v_P0 : bool)))``,
   entry "set_L758_set_diff_eq" 758 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) = (\b_x : 'a. ((b_x IN (v_A0 : ('a set))) /\ (~(b_x IN (v_B0 : ('a set)))))))``,
   entry "set_L761_Compl_eq_Diff_UNIV" 761 "by blast" benchLib.Blast false []
     ``((COMPL (v_A0 : ('a set))) = (UNIV DIFF (v_A0 : ('a set))))``,
   entry "set_L769_insert_iff" 769 "by blast" benchLib.Blast false []
     ``(((v_a0 : 'a) IN ((v_b0 : 'a) INSERT (v_A0 : ('a set)))) = (((v_a0 : 'a) = (v_b0 : 'a)) \/ ((v_a0 : 'a) IN (v_A0 : ('a set)))))``,
   entry "set_L772_insertI1" 772 "by simp" benchLib.Simp false []
     ``((v_a0 : 'a) IN ((v_a0 : 'a) INSERT (v_B0 : ('a set))))``,
   entry "set_L775_insertI2" 775 "by simp" benchLib.Simp false []
     ``(((v_a0 : 'a) IN (v_B0 : ('a set))) ==> ((v_a0 : 'a) IN ((v_b0 : 'a) INSERT (v_B0 : ('a set)))))``,
   entry "set_L778_insertE" 778 "by blast" benchLib.Blast false []
     ``(((v_a0 : 'a) IN ((v_b0 : 'a) INSERT (v_A0 : ('a set)))) ==> ((((v_a0 : 'a) = (v_b0 : 'a)) ==> (v_P0 : bool)) ==> ((((v_a0 : 'a) IN (v_A0 : ('a set))) ==> (v_P0 : bool)) ==> (v_P0 : bool))))``,
   entry "set_L781_insertCI" 781 "by auto" benchLib.Auto false []
     ``(((~((v_a0 : 'a) IN (v_B0 : ('a set)))) ==> ((v_a0 : 'a) = (v_b0 : 'a))) ==> ((v_a0 : 'a) IN ((v_b0 : 'a) INSERT (v_B0 : ('a set)))))``,
   entry "set_L785_subset_insert_iff" 785 "by auto" benchLib.Auto false []
     ``(((v_A0 : ('a set)) SUBSET ((v_x0 : 'a) INSERT (v_B0 : ('a set)))) = (if ((v_x0 : 'a) IN (v_A0 : ('a set))) then (((v_A0 : ('a set)) DIFF ((v_x0 : 'a) INSERT {})) SUBSET (v_B0 : ('a set))) else ((v_A0 : ('a set)) SUBSET (v_B0 : ('a set)))))``,
   entry "set_L796_insert_ident" 796 "by auto" benchLib.Auto false []
     ``((~((v_x0 : 'a) IN (v_A0 : ('a set)))) ==> ((~((v_x0 : 'a) IN (v_B0 : ('a set)))) ==> ((((v_x0 : 'a) INSERT (v_A0 : ('a set))) = ((v_x0 : 'a) INSERT (v_B0 : ('a set)))) = ((v_A0 : ('a set)) = (v_B0 : ('a set))))))``,
   entry "set_L821_insert_UNIV" 821 "by auto" benchLib.Auto false [{name = "pred_set$INSERT_UNIV", theorem = pred_setTheory.INSERT_UNIV}]
     ``(((v_x0 : 'a) INSERT UNIV) = UNIV)``,
   entry "set_L831_singletonD" 831 "by blast" benchLib.Blast false []
     ``(((v_b0 : 'a) IN ((v_a0 : 'a) INSERT {})) ==> ((v_b0 : 'a) = (v_a0 : 'a)))``,
   entry "set_L836_singleton_iff" 836 "by blast" benchLib.Blast false []
     ``(((v_b0 : 'a) IN ((v_a0 : 'a) INSERT {})) = ((v_b0 : 'a) = (v_a0 : 'a)))``,
   entry "set_L839_singleton_inject" 839 "by blast" benchLib.Blast false []
     ``((((v_a0 : 'a) INSERT {}) = ((v_b0 : 'a) INSERT {})) ==> ((v_a0 : 'a) = (v_b0 : 'a)))``,
   entry "set_L842_singleton_insert_inj_eq" 842 "by blast" benchLib.Blast false []
     ``((((v_b0 : 'a) INSERT {}) = ((v_a0 : 'a) INSERT (v_A0 : ('a set)))) = (((v_a0 : 'a) = (v_b0 : 'a)) /\ ((v_A0 : ('a set)) SUBSET ((v_b0 : 'a) INSERT {}))))``,
   entry "set_L845_singleton_insert_inj_eq_" 845 "by blast" benchLib.Blast false []
     ``((((v_a0 : 'a) INSERT (v_A0 : ('a set))) = ((v_b0 : 'a) INSERT {})) = (((v_a0 : 'a) = (v_b0 : 'a)) /\ ((v_A0 : ('a set)) SUBSET ((v_b0 : 'a) INSERT {}))))``,
   entry "set_L851_subset_singleton_iff" 851 "by blast" benchLib.Blast false []
     ``(((v_X0 : ('a set)) SUBSET ((v_a0 : 'a) INSERT {})) = (((v_X0 : ('a set)) = {}) \/ ((v_X0 : ('a set)) = ((v_a0 : 'a) INSERT {}))))``,
   entry "set_L854_subset_singleton_iff_Uniq" 854 "by blast" benchLib.Blast false []
     ``((?b_a : 'a. ((v_A0 : ('a set)) SUBSET (b_a INSERT {}))) = (!b_unique_left : 'a. !b_unique_right : 'a. ((\b_x : 'a. (b_x IN (v_A0 : ('a set)))) b_unique_left /\ (\b_x : 'a. (b_x IN (v_A0 : ('a set)))) b_unique_right) ==> b_unique_left = b_unique_right))``,
   entry "set_L857_singleton_conv" 857 "by blast" benchLib.Blast false []
     ``((\b_x : 'a. (b_x = (v_a0 : 'a))) = ((v_a0 : 'a) INSERT {}))``,
   entry "set_L860_singleton_conv2" 860 "by blast" benchLib.Blast false []
     ``((\b_x : 'a. ((v_a0 : 'a) = b_x)) = ((v_a0 : 'a) INSERT {}))``,
   entry "set_L863_Diff_single_insert" 863 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) DIFF ((v_x0 : 'a) INSERT {})) SUBSET (v_B0 : ('a set))) ==> ((v_A0 : ('a set)) SUBSET ((v_x0 : 'a) INSERT (v_B0 : ('a set)))))``,
   entry "set_L866_subset_Diff_insert" 866 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET ((v_B0 : ('a set)) DIFF ((v_x0 : 'a) INSERT (v_C0 : ('a set))))) = (((v_A0 : ('a set)) SUBSET ((v_B0 : ('a set)) DIFF (v_C0 : ('a set)))) /\ (~((v_x0 : 'a) IN (v_A0 : ('a set))))))``,
   entry "set_L869_doubleton_eq_iff" 869 "by (blast elim: equalityE)" benchLib.Blast false []
     ``((((v_a0 : 'a) INSERT ((v_b0 : 'a) INSERT {})) = ((v_c0 : 'a) INSERT ((v_d0 : 'a) INSERT {}))) = ((((v_a0 : 'a) = (v_c0 : 'a)) /\ ((v_b0 : 'a) = (v_d0 : 'a))) \/ (((v_a0 : 'a) = (v_d0 : 'a)) /\ ((v_b0 : 'a) = (v_c0 : 'a)))))``,
   entry "set_L872_Un_singleton_iff" 872 "by auto" benchLib.Auto false []
     ``((((v_A0 : ('a set)) UNION (v_B0 : ('a set))) = ((v_x0 : 'a) INSERT {})) = ((((v_A0 : ('a set)) = {}) /\ ((v_B0 : ('a set)) = ((v_x0 : 'a) INSERT {}))) \/ ((((v_A0 : ('a set)) = ((v_x0 : 'a) INSERT {})) /\ ((v_B0 : ('a set)) = {})) \/ (((v_A0 : ('a set)) = ((v_x0 : 'a) INSERT {})) /\ ((v_B0 : ('a set)) = ((v_x0 : 'a) INSERT {}))))))``,
   entry "set_L875_singleton_Un_iff" 875 "by auto" benchLib.Auto false []
     ``((((v_x0 : 'a) INSERT {}) = ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))) = ((((v_A0 : ('a set)) = {}) /\ ((v_B0 : ('a set)) = ((v_x0 : 'a) INSERT {}))) \/ ((((v_A0 : ('a set)) = ((v_x0 : 'a) INSERT {})) /\ ((v_B0 : ('a set)) = {})) \/ (((v_A0 : ('a set)) = ((v_x0 : 'a) INSERT {})) /\ ((v_B0 : ('a set)) = ((v_x0 : 'a) INSERT {}))))))``,
   entry "set_L886_image_eqI" 886 "by blast" benchLib.Blast false []
     ``(((v_b0 : 'a) = ((v_f0 : ('b -> 'a)) (v_x0 : 'b))) ==> (((v_x0 : 'b) IN (v_A0 : ('b set))) ==> ((v_b0 : 'a) IN (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))))))``,
   entry "set_L896_imageE" 896 "by blast" benchLib.Blast false []
     ``(((v_b0 : 'a) IN (IMAGE (\b_x : 'b. ((v_f0 : ('b -> 'a)) b_x)) (v_A0 : ('b set)))) ==> ((!b_x : 'b. (((v_b0 : 'a) = ((v_f0 : ('b -> 'a)) b_x)) ==> ((b_x IN (v_A0 : ('b set))) ==> (v_thesis0 : bool)))) ==> (v_thesis0 : bool)))``,
   entry "set_L901_Compr_image_eq" 901 "by auto" benchLib.Auto false []
     ``((\b_x : 'a. ((b_x IN (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set)))) /\ ((v_P0 : ('a -> bool)) b_x))) = (IMAGE (v_f0 : ('b -> 'a)) (\b_x : 'b. ((b_x IN (v_A0 : ('b set))) /\ ((v_P0 : ('a -> bool)) ((v_f0 : ('b -> 'a)) b_x))))))``,
   entry "set_L904_image_Un" 904 "by blast" benchLib.Blast false []
     ``((IMAGE (v_f0 : ('b -> 'a)) ((v_A0 : ('b set)) UNION (v_B0 : ('b set)))) = ((IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))) UNION (IMAGE (v_f0 : ('b -> 'a)) (v_B0 : ('b set)))))``,
   entry "set_L907_image_iff" 907 "by blast" benchLib.Blast false []
     ``(((v_z0 : 'a) IN (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set)))) = (?b_x : 'b. (b_x IN (v_A0 : ('b set))) /\ ((v_z0 : 'a) = ((v_f0 : ('b -> 'a)) b_x))))``,
   entry "set_L910_image_subsetI" 910 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. ((b_x IN (v_A0 : ('a set))) ==> (((v_f0 : ('a -> 'b)) b_x) IN (v_B0 : ('b set))))) ==> ((IMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('a set))) SUBSET (v_B0 : ('b set))))``,
   entry "set_L915_image_subset_iff" 915 "by blast" benchLib.Blast false []
     ``(((IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))) SUBSET (v_B0 : ('a set))) = (!b_x : 'b. (b_x IN (v_A0 : ('b set))) ==> (((v_f0 : ('b -> 'a)) b_x) IN (v_B0 : ('a set)))))``,
   entry "set_L928_subset_image_iff" 928 "by (blast elim: subset_imageE)" benchLib.Blast false []
     ``(((v_B0 : ('a set)) SUBSET (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set)))) = (?b_AA : ('b set). ((b_AA SUBSET (v_A0 : ('b set))) /\ ((v_B0 : ('a set)) = (IMAGE (v_f0 : ('b -> 'a)) b_AA)))))``,
   entry "set_L931_image_ident" 931 "by blast" benchLib.Blast false []
     ``((IMAGE (\b_x : 'a. b_x) (v_Y0 : ('a set))) = (v_Y0 : ('a set)))``,
   entry "set_L934_image_empty" 934 "by blast" benchLib.Blast false [{name = "pred_set$IMAGE_EMPTY", theorem = pred_setTheory.IMAGE_EMPTY}]
     ``((IMAGE (v_f0 : ('b -> 'a)) {}) = {})``,
   entry "set_L937_image_insert" 937 "by blast" benchLib.Blast false [{name = "pred_set$IMAGE_INSERT", theorem = pred_setTheory.IMAGE_INSERT}]
     ``((IMAGE (v_f0 : ('b -> 'a)) ((v_a0 : 'b) INSERT (v_B0 : ('b set)))) = (((v_f0 : ('b -> 'a)) (v_a0 : 'b)) INSERT (IMAGE (v_f0 : ('b -> 'a)) (v_B0 : ('b set)))))``,
   entry "set_L940_image_constant" 940 "by auto" benchLib.Auto false []
     ``(((v_x0 : 'a) IN (v_A0 : ('a set))) ==> ((IMAGE (\b_x : 'a. (v_c0 : 'b)) (v_A0 : ('a set))) = ((v_c0 : 'b) INSERT {})))``,
   entry "set_L943_image_constant_conv" 943 "by auto" benchLib.Auto false []
     ``((IMAGE (\b_x : 'b. (v_c0 : 'a)) (v_A0 : ('b set))) = (if ((v_A0 : ('b set)) = {}) then {} else ((v_c0 : 'a) INSERT {})))``,
   entry "set_L946_image_image" 946 "by blast" benchLib.Blast false [{name = "pred_set$IMAGE_IMAGE", theorem = pred_setTheory.IMAGE_IMAGE}]
     ``((IMAGE (v_f0 : ('b -> 'a)) (IMAGE (v_g0 : ('c -> 'b)) (v_A0 : ('c set)))) = (IMAGE (\b_x : 'c. ((v_f0 : ('b -> 'a)) ((v_g0 : ('c -> 'b)) b_x))) (v_A0 : ('c set))))``,
   entry "set_L949_insert_image" 949 "by blast" benchLib.Blast false []
     ``(((v_x0 : 'a) IN (v_A0 : ('a set))) ==> ((((v_f0 : ('a -> 'b)) (v_x0 : 'a)) INSERT (IMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('a set)))) = (IMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('a set)))))``,
   entry "set_L952_image_is_empty" 952 "by blast" benchLib.Blast false []
     ``(((IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))) = {}) = ((v_A0 : ('b set)) = {}))``,
   entry "set_L955_empty_is_image" 955 "by blast" benchLib.Blast false []
     ``(({} = (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set)))) = ((v_A0 : ('b set)) = {}))``,
   entry "set_L958_image_Collect" 958 "by blast" benchLib.Blast false []
     ``((IMAGE (v_f0 : ('b -> 'a)) (\b_x : 'b. ((v_P0 : ('b -> bool)) b_x))) = (\b_uu_ : 'a. (?b_x : 'b. ((b_uu_ = ((v_f0 : ('b -> 'a)) b_x)) /\ ((v_P0 : ('b -> bool)) b_x)))))``,
   entry "set_L964_if_image_distrib" 964 "by auto" benchLib.Auto false []
     ``((IMAGE (\b_x : 'b. (if ((v_P0 : ('b -> bool)) b_x) then ((v_f0 : ('b -> 'a)) b_x) else ((v_g0 : ('b -> 'a)) b_x))) (v_S0 : ('b set))) = ((IMAGE (v_f0 : ('b -> 'a)) ((v_S0 : ('b set)) INTER (\b_x : 'b. ((v_P0 : ('b -> bool)) b_x)))) UNION (IMAGE (v_g0 : ('b -> 'a)) ((v_S0 : ('b set)) INTER (\b_x : 'b. (~((v_P0 : ('b -> bool)) b_x)))))))``,
   entry "set_L968_image_cong" 968 "by (simp add: image_def)" benchLib.Simp false [{name = "pred_set$IMAGE_CONG", theorem = pred_setTheory.IMAGE_CONG}]
     ``(((v_M0 : ('a set)) = (v_N0 : ('a set))) ==> ((!b_x : 'a. ((b_x IN (v_N0 : ('a set))) ==> (((v_f0 : ('a -> 'b)) b_x) = ((v_g0 : ('a -> 'b)) b_x)))) ==> ((IMAGE (v_f0 : ('a -> 'b)) (v_M0 : ('a set))) = (IMAGE (v_g0 : ('a -> 'b)) (v_N0 : ('a set))))))``,
   entry "set_L976_image_Int_subset" 976 "by blast" benchLib.Blast false []
     ``((IMAGE (v_f0 : ('b -> 'a)) ((v_A0 : ('b set)) INTER (v_B0 : ('b set)))) SUBSET ((IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))) INTER (IMAGE (v_f0 : ('b -> 'a)) (v_B0 : ('b set)))))``,
   entry "set_L979_image_diff_subset" 979 "by blast" benchLib.Blast false []
     ``(((IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))) DIFF (IMAGE (v_f0 : ('b -> 'a)) (v_B0 : ('b set)))) SUBSET (IMAGE (v_f0 : ('b -> 'a)) ((v_A0 : ('b set)) DIFF (v_B0 : ('b set)))))``,
   entry "set_L982_Setcompr_eq_image" 982 "by blast" benchLib.Blast false []
     ``((\b_uu_ : 'a. (?b_x : 'b. ((b_uu_ = ((v_f0 : ('b -> 'a)) b_x)) /\ (b_x IN (v_A0 : ('b set)))))) = (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))))``,
   entry "set_L985_setcompr_eq_image" 985 "by auto" benchLib.Auto false []
     ``((\b_uu_ : 'a. (?b_x : 'b. ((b_uu_ = ((v_f0 : ('b -> 'a)) b_x)) /\ ((v_P0 : ('b -> bool)) b_x)))) = (IMAGE (v_f0 : ('b -> 'a)) (\b_x : 'b. ((v_P0 : ('b -> bool)) b_x))))``,
   entry "set_L988_ball_imageD" 988 "by simp" benchLib.Simp false []
     ``((!b_x : 'a. (b_x IN (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set)))) ==> ((v_P0 : ('a -> bool)) b_x)) ==> (!b_x : 'b. (b_x IN (v_A0 : ('b set))) ==> ((v_P0 : ('a -> bool)) ((v_f0 : ('b -> 'a)) b_x))))``,
   entry "set_L991_bex_imageD" 991 "by auto" benchLib.Auto false []
     ``((?b_x : 'a. (b_x IN (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set)))) /\ ((v_P0 : ('a -> bool)) b_x)) ==> (?b_x : 'b. (b_x IN (v_A0 : ('b set))) /\ ((v_P0 : ('a -> bool)) ((v_f0 : ('b -> 'a)) b_x))))``,
   entry "set_L1013_range_eqI" 1013 "by simp" benchLib.Simp false []
     ``(((v_b0 : 'a) = ((v_f0 : ('b -> 'a)) (v_x0 : 'b))) ==> ((v_b0 : 'a) IN (IMAGE (v_f0 : ('b -> 'a)) UNIV)))``,
   entry "set_L1016_rangeI" 1016 "by simp" benchLib.Simp false []
     ``(((v_f0 : ('b -> 'a)) (v_x0 : 'b)) IN (IMAGE (v_f0 : ('b -> 'a)) UNIV))``,
   entry "set_L1022_range_subsetD" 1022 "by blast" benchLib.Blast false []
     ``(((IMAGE (v_f0 : ('b -> 'a)) UNIV) SUBSET (v_B0 : ('a set))) ==> (((v_f0 : ('b -> 'a)) (v_i0 : 'b)) IN (v_B0 : ('a set))))``,
   entry "set_L1025_full_SetCompr_eq" 1025 "by auto" benchLib.Auto false []
     ``((\b_u : 'a. (?b_x : 'b. (b_u = ((v_f0 : ('b -> 'a)) b_x)))) = (IMAGE (v_f0 : ('b -> 'a)) UNIV))``,
   entry "set_L1028_range_composition" 1028 "by auto" benchLib.Auto false []
     ``((IMAGE (\b_x : 'b. ((v_f0 : ('c -> 'a)) ((v_g0 : ('b -> 'c)) b_x))) UNIV) = (IMAGE (v_f0 : ('c -> 'a)) (IMAGE (v_g0 : ('b -> 'c)) UNIV)))``,
   entry "set_L1031_range_constant" 1031 "by (simp add: image_constant)" benchLib.Simp false []
     ``((IMAGE (\b_uu_ : 'b. (v_x0 : 'a)) UNIV) = ((v_x0 : 'a) INSERT {}))``,
   entry "set_L1034_range_eq_singletonD" 1034 "by auto" benchLib.Auto false []
     ``(((IMAGE (v_f0 : ('b -> 'a)) UNIV) = ((v_a0 : 'a) INSERT {})) ==> (((v_f0 : ('b -> 'a)) (v_x0 : 'b)) = (v_a0 : 'a)))``,
   entry "set_L1042_Collect_conv_if" 1042 "by auto" benchLib.Auto false []
     ``((\b_x : 'a. ((b_x = (v_a0 : 'a)) /\ ((v_P0 : ('a -> bool)) b_x))) = (if ((v_P0 : ('a -> bool)) (v_a0 : 'a)) then ((v_a0 : 'a) INSERT {}) else {}))``,
   entry "set_L1045_Collect_conv_if2" 1045 "by auto" benchLib.Auto false []
     ``((\b_x : 'a. (((v_a0 : 'a) = b_x) /\ ((v_P0 : ('a -> bool)) b_x))) = (if ((v_P0 : ('a -> bool)) (v_a0 : 'a)) then ((v_a0 : 'a) INSERT {}) else {}))``,
   entry "set_L1085_psubsetI" 1085 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> ((~((v_A0 : ('a set)) = (v_B0 : ('a set)))) ==> ((v_A0 : ('a set)) PSUBSET (v_B0 : ('a set)))))``,
   entry "set_L1088_psubsetE" 1088 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) PSUBSET (v_B0 : ('a set))) ==> ((((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> ((~((v_B0 : ('a set)) SUBSET (v_A0 : ('a set)))) ==> (v_R0 : bool))) ==> (v_R0 : bool)))``,
   entry "set_L1091_psubset_insert_iff" 1091 "by (auto simp add: less_le subset_insert_iff)" benchLib.Auto false []
     ``(((v_A0 : ('a set)) PSUBSET ((v_x0 : 'a) INSERT (v_B0 : ('a set)))) = (if ((v_x0 : 'a) IN (v_B0 : ('a set))) then ((v_A0 : ('a set)) PSUBSET (v_B0 : ('a set))) else (if ((v_x0 : 'a) IN (v_A0 : ('a set))) then (((v_A0 : ('a set)) DIFF ((v_x0 : 'a) INSERT {})) PSUBSET (v_B0 : ('a set))) else ((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))))))``,
   entry "set_L1098_psubset_imp_subset" 1098 "by (simp add: psubset_eq)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) PSUBSET (v_B0 : ('a set))) ==> ((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))))``,
   entry "set_L1101_psubset_trans" 1101 "by (auto dest: subset_antisym)" benchLib.Auto false [{name = "pred_set$PSUBSET_TRANS", theorem = pred_setTheory.PSUBSET_TRANS}]
     ``(((v_A0 : ('a set)) PSUBSET (v_B0 : ('a set))) ==> (((v_B0 : ('a set)) PSUBSET (v_C0 : ('a set))) ==> ((v_A0 : ('a set)) PSUBSET (v_C0 : ('a set)))))``,
   entry "set_L1104_psubsetD" 1104 "by (auto dest: subsetD)" benchLib.Auto false []
     ``(((v_A0 : ('a set)) PSUBSET (v_B0 : ('a set))) ==> (((v_c0 : 'a) IN (v_A0 : ('a set))) ==> ((v_c0 : 'a) IN (v_B0 : ('a set)))))``,
   entry "set_L1107_psubset_subset_trans" 1107 "by (auto simp add: psubset_eq)" benchLib.Auto false [{name = "pred_set$PSUBSET_SUBSET_TRANS", theorem = pred_setTheory.PSUBSET_SUBSET_TRANS}]
     ``(((v_A0 : ('a set)) PSUBSET (v_B0 : ('a set))) ==> (((v_B0 : ('a set)) SUBSET (v_C0 : ('a set))) ==> ((v_A0 : ('a set)) PSUBSET (v_C0 : ('a set)))))``,
   entry "set_L1110_subset_psubset_trans" 1110 "by (auto simp add: psubset_eq)" benchLib.Auto false [{name = "pred_set$SUBSET_PSUBSET_TRANS", theorem = pred_setTheory.SUBSET_PSUBSET_TRANS}]
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> (((v_B0 : ('a set)) PSUBSET (v_C0 : ('a set))) ==> ((v_A0 : ('a set)) PSUBSET (v_C0 : ('a set)))))``,
   entry "set_L1113_psubset_imp_ex_mem" 1113 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) PSUBSET (v_B0 : ('a set))) ==> (?b_b : 'a. (b_b IN ((v_B0 : ('a set)) DIFF (v_A0 : ('a set))))))``,
   entry "set_L1122_image_Pow_mono" 1122 "by blast" benchLib.Blast false []
     ``(((IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))) SUBSET (v_B0 : ('a set))) ==> ((IMAGE (IMAGE (v_f0 : ('b -> 'a))) (POW (v_A0 : ('b set)))) SUBSET (POW (v_B0 : ('a set)))))``,
   entry "set_L1125_image_Pow_surj" 1125 "by (blast elim: subset_imageE)" benchLib.Blast false []
     ``(((IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))) = (v_B0 : ('a set))) ==> ((IMAGE (IMAGE (v_f0 : ('b -> 'a))) (POW (v_A0 : ('b set)))) = (POW (v_B0 : ('a set)))))``,
   entry "set_L1136_subset_insertI2" 1136 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> ((v_A0 : ('a set)) SUBSET ((v_b0 : 'a) INSERT (v_B0 : ('a set)))))``,
   entry "set_L1139_subset_insert" 1139 "by blast" benchLib.Blast false [{name = "pred_set$SUBSET_INSERT", theorem = pred_setTheory.SUBSET_INSERT}]
     ``((~((v_x0 : 'a) IN (v_A0 : ('a set)))) ==> (((v_A0 : ('a set)) SUBSET ((v_x0 : 'a) INSERT (v_B0 : ('a set)))) = ((v_A0 : ('a set)) SUBSET (v_B0 : ('a set)))))``,
   entry "set_L1169_Diff_subset" 1169 "by blast" benchLib.Blast false [{name = "pred_set$DIFF_SUBSET", theorem = pred_setTheory.DIFF_SUBSET}]
     ``(((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) SUBSET (v_A0 : ('a set)))``,
   entry "set_L1172_Diff_subset_conv" 1172 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) SUBSET (v_C0 : ('a set))) = ((v_A0 : ('a set)) SUBSET ((v_B0 : ('a set)) UNION (v_C0 : ('a set)))))``,
   entry "set_L1180_Collect_const" 1180 "by auto" benchLib.Auto false []
     ``((\b_s : 'a. (v_P0 : bool)) = (if (v_P0 : bool) then UNIV else {}))``,
   entry "set_L1190_Collect_subset" 1190 "by auto" benchLib.Auto false []
     ``((\b_x : 'a. ((b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x))) SUBSET (v_A0 : ('a set)))``,
   entry "set_L1192_Collect_empty_eq" 1192 "by blast" benchLib.Blast false []
     ``(((v_P0 : ('a -> bool)) = {}) = (!b_x : 'a. (~((v_P0 : ('a -> bool)) b_x))))``,
   entry "set_L1195_empty_Collect_eq" 1195 "by blast" benchLib.Blast false []
     ``(({} = (v_P0 : ('a -> bool))) = (!b_x : 'a. (~((v_P0 : ('a -> bool)) b_x))))``,
   entry "set_L1198_Collect_neg_eq" 1198 "by blast" benchLib.Blast false []
     ``((\b_x : 'a. (~((v_P0 : ('a -> bool)) b_x))) = (COMPL (\b_x : 'a. ((v_P0 : ('a -> bool)) b_x))))``,
   entry "set_L1201_Collect_disj_eq" 1201 "by blast" benchLib.Blast false []
     ``((\b_x : 'a. (((v_P0 : ('a -> bool)) b_x) \/ ((v_Q0 : ('a -> bool)) b_x))) = ((\b_x : 'a. ((v_P0 : ('a -> bool)) b_x)) UNION (\b_x : 'a. ((v_Q0 : ('a -> bool)) b_x))))``,
   entry "set_L1204_Collect_imp_eq" 1204 "by blast" benchLib.Blast false []
     ``((\b_x : 'a. (((v_P0 : ('a -> bool)) b_x) ==> ((v_Q0 : ('a -> bool)) b_x))) = ((COMPL (\b_x : 'a. ((v_P0 : ('a -> bool)) b_x))) UNION (\b_x : 'a. ((v_Q0 : ('a -> bool)) b_x))))``,
   entry "set_L1207_Collect_conj_eq" 1207 "by blast" benchLib.Blast false []
     ``((\b_x : 'a. (((v_P0 : ('a -> bool)) b_x) /\ ((v_Q0 : ('a -> bool)) b_x))) = ((\b_x : 'a. ((v_P0 : ('a -> bool)) b_x)) INTER (\b_x : 'a. ((v_Q0 : ('a -> bool)) b_x))))``,
   entry "set_L1210_Collect_conj_eq2" 1210 "by blast" benchLib.Blast false []
     ``((\b_x : 'a. ((b_x IN (v_A0 : ('a set))) /\ (((v_P0 : ('a -> bool)) b_x) /\ ((v_Q0 : ('a -> bool)) b_x)))) = ((\b_x : 'a. ((b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x))) INTER (\b_x : 'a. ((b_x IN (v_A0 : ('a set))) /\ ((v_Q0 : ('a -> bool)) b_x)))))``,
   entry "set_L1213_Collect_mono_iff" 1213 "by blast" benchLib.Blast false []
     ``(((v_P0 : ('a -> bool)) SUBSET (v_Q0 : ('a -> bool))) = (!b_x : 'a. (((v_P0 : ('a -> bool)) b_x) ==> ((v_Q0 : ('a -> bool)) b_x))))``,
   entry "set_L1219_insert_is_Un" 1219 "by blast" benchLib.Blast false []
     ``(((v_a0 : 'a) INSERT (v_A0 : ('a set))) = (((v_a0 : 'a) INSERT {}) UNION (v_A0 : ('a set))))``,
   entry "set_L1227_insert_absorb" 1227 "by blast" benchLib.Blast false []
     ``(((v_a0 : 'a) IN (v_A0 : ('a set))) ==> (((v_a0 : 'a) INSERT (v_A0 : ('a set))) = (v_A0 : ('a set))))``,
   entry "set_L1232_insert_absorb2" 1232 "by blast" benchLib.Blast false []
     ``(((v_x0 : 'a) INSERT ((v_x0 : 'a) INSERT (v_A0 : ('a set)))) = ((v_x0 : 'a) INSERT (v_A0 : ('a set))))``,
   entry "set_L1235_insert_commute" 1235 "by blast" benchLib.Blast false []
     ``(((v_x0 : 'a) INSERT ((v_y0 : 'a) INSERT (v_A0 : ('a set)))) = ((v_y0 : 'a) INSERT ((v_x0 : 'a) INSERT (v_A0 : ('a set)))))``,
   entry "set_L1238_insert_subset" 1238 "by blast" benchLib.Blast false [{name = "pred_set$INSERT_SUBSET", theorem = pred_setTheory.INSERT_SUBSET}]
     ``((((v_x0 : 'a) INSERT (v_A0 : ('a set))) SUBSET (v_B0 : ('a set))) = (((v_x0 : 'a) IN (v_B0 : ('a set))) /\ ((v_A0 : ('a set)) SUBSET (v_B0 : ('a set)))))``,
   entry "set_L1245_insert_Collect" 1245 "by auto" benchLib.Auto false []
     ``(((v_a0 : 'a) INSERT (v_P0 : ('a -> bool))) = (\b_u : 'a. ((~(b_u = (v_a0 : 'a))) ==> ((v_P0 : ('a -> bool)) b_u))))``,
   entry "set_L1248_insert_inter_insert" 1248 "by blast" benchLib.Blast false []
     ``((((v_a0 : 'a) INSERT (v_A0 : ('a set))) INTER ((v_a0 : 'a) INSERT (v_B0 : ('a set)))) = ((v_a0 : 'a) INSERT ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))))``,
   entry "set_L1251_insert_disjoint_1" 1251 "by auto" benchLib.Auto false []
     ``(((((v_a0 : 'a) INSERT (v_A0 : ('a set))) INTER (v_B0 : ('a set))) = {}) = ((~((v_a0 : 'a) IN (v_B0 : ('a set)))) /\ (((v_A0 : ('a set)) INTER (v_B0 : ('a set))) = {})))``,
   entry "set_L1251_insert_disjoint_2" 1251 "by auto" benchLib.Auto false []
     ``(({} = (((v_a0 : 'a) INSERT (v_A0 : ('a set))) INTER (v_B0 : ('a set)))) = ((~((v_a0 : 'a) IN (v_B0 : ('a set)))) /\ ({} = ((v_A0 : ('a set)) INTER (v_B0 : ('a set))))))``,
   entry "set_L1256_disjoint_insert_1" 1256 "by auto" benchLib.Auto false [{name = "pred_set$DISJOINT_INSERT", theorem = pred_setTheory.DISJOINT_INSERT}, {name = "pred_set$disjoint_insert", theorem = pred_setTheory.disjoint_insert}]
     ``((((v_B0 : ('a set)) INTER ((v_a0 : 'a) INSERT (v_A0 : ('a set)))) = {}) = ((~((v_a0 : 'a) IN (v_B0 : ('a set)))) /\ (((v_B0 : ('a set)) INTER (v_A0 : ('a set))) = {})))``,
   entry "set_L1256_disjoint_insert_2" 1256 "by auto" benchLib.Auto false [{name = "pred_set$DISJOINT_INSERT", theorem = pred_setTheory.DISJOINT_INSERT}, {name = "pred_set$disjoint_insert", theorem = pred_setTheory.disjoint_insert}]
     ``(({} = ((v_A0 : ('a set)) INTER ((v_b0 : 'a) INSERT (v_B0 : ('a set))))) = ((~((v_b0 : 'a) IN (v_A0 : ('a set)))) /\ ({} = ((v_A0 : ('a set)) INTER (v_B0 : ('a set))))))``,
   entry "set_L1294_disjoint_eq_subset_Compl" 1294 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) INTER (v_B0 : ('a set))) = {}) = ((v_A0 : ('a set)) SUBSET (COMPL (v_B0 : ('a set)))))``,
   entry "set_L1297_disjoint_iff" 1297 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) INTER (v_B0 : ('a set))) = {}) = (!b_x : 'a. ((b_x IN (v_A0 : ('a set))) ==> (~(b_x IN (v_B0 : ('a set)))))))``,
   entry "set_L1300_disjoint_iff_not_equal" 1300 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) INTER (v_B0 : ('a set))) = {}) = (!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> (!b_y : 'a. (b_y IN (v_B0 : ('a set))) ==> (~(b_x = b_y)))))``,
   entry "set_L1321_Int_Collect" 1321 "by blast" benchLib.Blast false []
     ``(((v_x0 : 'a) IN ((v_A0 : ('a set)) INTER (\b_x : 'a. ((v_P0 : ('a -> bool)) b_x)))) = (((v_x0 : 'a) IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) (v_x0 : 'a))))``,
   entry "set_L1363_Un_insert_left" 1363 "by blast" benchLib.Blast false []
     ``((((v_a0 : 'a) INSERT (v_B0 : ('a set))) UNION (v_C0 : ('a set))) = ((v_a0 : 'a) INSERT ((v_B0 : ('a set)) UNION (v_C0 : ('a set)))))``,
   entry "set_L1366_Un_insert_right" 1366 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) UNION ((v_a0 : 'a) INSERT (v_B0 : ('a set)))) = ((v_a0 : 'a) INSERT ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))))``,
   entry "set_L1369_Int_insert_left" 1369 "by auto" benchLib.Auto false []
     ``((((v_a0 : 'a) INSERT (v_B0 : ('a set))) INTER (v_C0 : ('a set))) = (if ((v_a0 : 'a) IN (v_C0 : ('a set))) then ((v_a0 : 'a) INSERT ((v_B0 : ('a set)) INTER (v_C0 : ('a set)))) else ((v_B0 : ('a set)) INTER (v_C0 : ('a set)))))``,
   entry "set_L1372_Int_insert_left_if0" 1372 "by auto" benchLib.Auto false []
     ``((~((v_a0 : 'a) IN (v_C0 : ('a set)))) ==> ((((v_a0 : 'a) INSERT (v_B0 : ('a set))) INTER (v_C0 : ('a set))) = ((v_B0 : ('a set)) INTER (v_C0 : ('a set)))))``,
   entry "set_L1375_Int_insert_left_if1" 1375 "by auto" benchLib.Auto false []
     ``(((v_a0 : 'a) IN (v_C0 : ('a set))) ==> ((((v_a0 : 'a) INSERT (v_B0 : ('a set))) INTER (v_C0 : ('a set))) = ((v_a0 : 'a) INSERT ((v_B0 : ('a set)) INTER (v_C0 : ('a set))))))``,
   entry "set_L1378_Int_insert_right" 1378 "by auto" benchLib.Auto false []
     ``(((v_A0 : ('a set)) INTER ((v_a0 : 'a) INSERT (v_B0 : ('a set)))) = (if ((v_a0 : 'a) IN (v_A0 : ('a set))) then ((v_a0 : 'a) INSERT ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))) else ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))))``,
   entry "set_L1381_Int_insert_right_if0" 1381 "by auto" benchLib.Auto false []
     ``((~((v_a0 : 'a) IN (v_A0 : ('a set)))) ==> (((v_A0 : ('a set)) INTER ((v_a0 : 'a) INSERT (v_B0 : ('a set)))) = ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))))``,
   entry "set_L1384_Int_insert_right_if1" 1384 "by auto" benchLib.Auto false []
     ``(((v_a0 : 'a) IN (v_A0 : ('a set))) ==> (((v_A0 : ('a set)) INTER ((v_a0 : 'a) INSERT (v_B0 : ('a set)))) = ((v_a0 : 'a) INSERT ((v_A0 : ('a set)) INTER (v_B0 : ('a set))))))``,
   entry "set_L1393_Un_Int_crazy" 1393 "by blast" benchLib.Blast false []
     ``(((((v_A0 : ('a set)) INTER (v_B0 : ('a set))) UNION ((v_B0 : ('a set)) INTER (v_C0 : ('a set)))) UNION ((v_C0 : ('a set)) INTER (v_A0 : ('a set)))) = ((((v_A0 : ('a set)) UNION (v_B0 : ('a set))) INTER ((v_B0 : ('a set)) UNION (v_C0 : ('a set)))) INTER ((v_C0 : ('a set)) UNION (v_A0 : ('a set)))))``,
   entry "set_L1405_Un_Diff_Int" 1405 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) UNION ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))) = (v_A0 : ('a set)))``,
   entry "set_L1408_Diff_Int2" 1408 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) INTER (v_C0 : ('a set))) DIFF ((v_B0 : ('a set)) INTER (v_C0 : ('a set)))) = (((v_A0 : ('a set)) INTER (v_C0 : ('a set))) DIFF (v_B0 : ('a set))))``,
   entry "set_L1419_Un_Int_eq_1" 1419 "by auto" benchLib.Auto false []
     ``((((v_S0 : ('a set)) UNION (v_T0 : ('a set))) INTER (v_S0 : ('a set))) = (v_S0 : ('a set)))``,
   entry "set_L1419_Un_Int_eq_2" 1419 "by auto" benchLib.Auto false []
     ``((((v_S0 : ('a set)) UNION (v_T0 : ('a set))) INTER (v_T0 : ('a set))) = (v_T0 : ('a set)))``,
   entry "set_L1419_Un_Int_eq_3" 1419 "by auto" benchLib.Auto false []
     ``(((v_S0 : ('a set)) INTER ((v_S0 : ('a set)) UNION (v_T0 : ('a set)))) = (v_S0 : ('a set)))``,
   entry "set_L1419_Un_Int_eq_4" 1419 "by auto" benchLib.Auto false []
     ``(((v_T0 : ('a set)) INTER ((v_S0 : ('a set)) UNION (v_T0 : ('a set)))) = (v_T0 : ('a set)))``,
   entry "set_L1422_Int_Un_eq_1" 1422 "by auto" benchLib.Auto false []
     ``((((v_S0 : ('a set)) INTER (v_T0 : ('a set))) UNION (v_S0 : ('a set))) = (v_S0 : ('a set)))``,
   entry "set_L1422_Int_Un_eq_2" 1422 "by auto" benchLib.Auto false []
     ``((((v_S0 : ('a set)) INTER (v_T0 : ('a set))) UNION (v_T0 : ('a set))) = (v_T0 : ('a set)))``,
   entry "set_L1422_Int_Un_eq_3" 1422 "by auto" benchLib.Auto false []
     ``(((v_S0 : ('a set)) UNION ((v_S0 : ('a set)) INTER (v_T0 : ('a set)))) = (v_S0 : ('a set)))``,
   entry "set_L1422_Int_Un_eq_4" 1422 "by auto" benchLib.Auto false []
     ``(((v_T0 : ('a set)) UNION ((v_S0 : ('a set)) INTER (v_T0 : ('a set)))) = (v_T0 : ('a set)))``,
   entry "set_L1448_subset_Compl_self_eq" 1448 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (COMPL (v_A0 : ('a set)))) = ((v_A0 : ('a set)) = {}))``,
   entry "set_L1451_Un_Int_assoc_eq" 1451 "by blast" benchLib.Blast false []
     ``(((((v_A0 : ('a set)) INTER (v_B0 : ('a set))) UNION (v_C0 : ('a set))) = ((v_A0 : ('a set)) INTER ((v_B0 : ('a set)) UNION (v_C0 : ('a set))))) = ((v_C0 : ('a set)) SUBSET (v_A0 : ('a set))))``,
   entry "set_L1468_Compl_insert" 1468 "by blast" benchLib.Blast false [{name = "pred_set$compl_insert", theorem = pred_setTheory.compl_insert}]
     ``((COMPL ((v_x0 : 'a) INSERT (v_A0 : ('a set)))) = ((COMPL (v_A0 : ('a set))) DIFF ((v_x0 : 'a) INSERT {})))``,
   entry "set_L1477_ball_Un" 1477 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. (b_x IN ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))) ==> ((v_P0 : ('a -> bool)) b_x)) = ((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) b_x)) /\ (!b_x : 'a. (b_x IN (v_B0 : ('a set))) ==> ((v_P0 : ('a -> bool)) b_x))))``,
   entry "set_L1480_bex_Un" 1480 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))) /\ ((v_P0 : ('a -> bool)) b_x)) = ((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x)) \/ (?b_x : 'a. (b_x IN (v_B0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x))))``,
   entry "set_L1492_Diff_cancel" 1492 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) DIFF (v_A0 : ('a set))) = {})``,
   entry "set_L1495_Diff_idemp" 1495 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) DIFF (v_B0 : ('a set))) = ((v_A0 : ('a set)) DIFF (v_B0 : ('a set))))``,
   entry "set_L1499_Diff_triv" 1499 "by (blast elim: equalityE)" benchLib.Blast false []
     ``((((v_A0 : ('a set)) INTER (v_B0 : ('a set))) = {}) ==> (((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) = (v_A0 : ('a set))))``,
   entry "set_L1502_empty_Diff" 1502 "by blast" benchLib.Blast false [{name = "pred_set$EMPTY_DIFF", theorem = pred_setTheory.EMPTY_DIFF}]
     ``(({} DIFF (v_A0 : ('a set))) = {})``,
   entry "set_L1505_Diff_empty" 1505 "by blast" benchLib.Blast false [{name = "pred_set$DIFF_EMPTY", theorem = pred_setTheory.DIFF_EMPTY}]
     ``(((v_A0 : ('a set)) DIFF {}) = (v_A0 : ('a set)))``,
   entry "set_L1508_Diff_UNIV" 1508 "by blast" benchLib.Blast false [{name = "pred_set$DIFF_UNIV", theorem = pred_setTheory.DIFF_UNIV}]
     ``(((v_A0 : ('a set)) DIFF UNIV) = {})``,
   entry "set_L1511_Diff_insert0" 1511 "by blast" benchLib.Blast false []
     ``((~((v_x0 : 'a) IN (v_A0 : ('a set)))) ==> (((v_A0 : ('a set)) DIFF ((v_x0 : 'a) INSERT (v_B0 : ('a set)))) = ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))))``,
   entry "set_L1514_Diff_insert" 1514 "by blast" benchLib.Blast false [{name = "pred_set$DIFF_INSERT", theorem = pred_setTheory.DIFF_INSERT}]
     ``(((v_A0 : ('a set)) DIFF ((v_a0 : 'a) INSERT (v_B0 : ('a set)))) = (((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) DIFF ((v_a0 : 'a) INSERT {})))``,
   entry "set_L1518_Diff_insert2" 1518 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) DIFF ((v_a0 : 'a) INSERT (v_B0 : ('a set)))) = (((v_A0 : ('a set)) DIFF ((v_a0 : 'a) INSERT {})) DIFF (v_B0 : ('a set))))``,
   entry "set_L1522_insert_Diff_if" 1522 "by auto" benchLib.Auto false []
     ``((((v_x0 : 'a) INSERT (v_A0 : ('a set))) DIFF (v_B0 : ('a set))) = (if ((v_x0 : 'a) IN (v_B0 : ('a set))) then ((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) else ((v_x0 : 'a) INSERT ((v_A0 : ('a set)) DIFF (v_B0 : ('a set))))))``,
   entry "set_L1525_insert_Diff1" 1525 "by blast" benchLib.Blast false []
     ``(((v_x0 : 'a) IN (v_B0 : ('a set))) ==> ((((v_x0 : 'a) INSERT (v_A0 : ('a set))) DIFF (v_B0 : ('a set))) = ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))))``,
   entry "set_L1528_insert_Diff_single" 1528 "by blast" benchLib.Blast false []
     ``(((v_a0 : 'a) INSERT ((v_A0 : ('a set)) DIFF ((v_a0 : 'a) INSERT {}))) = ((v_a0 : 'a) INSERT (v_A0 : ('a set))))``,
   entry "set_L1531_insert_Diff" 1531 "by blast" benchLib.Blast false [{name = "pred_set$INSERT_DIFF", theorem = pred_setTheory.INSERT_DIFF}]
     ``(((v_a0 : 'a) IN (v_A0 : ('a set))) ==> (((v_a0 : 'a) INSERT ((v_A0 : ('a set)) DIFF ((v_a0 : 'a) INSERT {}))) = (v_A0 : ('a set))))``,
   entry "set_L1534_Diff_insert_absorb" 1534 "by auto" benchLib.Auto false []
     ``((~((v_x0 : 'a) IN (v_A0 : ('a set)))) ==> ((((v_x0 : 'a) INSERT (v_A0 : ('a set))) DIFF ((v_x0 : 'a) INSERT {})) = (v_A0 : ('a set))))``,
   entry "set_L1537_Diff_disjoint" 1537 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) INTER ((v_B0 : ('a set)) DIFF (v_A0 : ('a set)))) = {})``,
   entry "set_L1540_Diff_partition" 1540 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> (((v_A0 : ('a set)) UNION ((v_B0 : ('a set)) DIFF (v_A0 : ('a set)))) = (v_B0 : ('a set))))``,
   entry "set_L1543_double_diff" 1543 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> (((v_B0 : ('a set)) SUBSET (v_C0 : ('a set))) ==> (((v_B0 : ('a set)) DIFF ((v_C0 : ('a set)) DIFF (v_A0 : ('a set)))) = (v_A0 : ('a set)))))``,
   entry "set_L1546_Un_Diff_cancel" 1546 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) UNION ((v_B0 : ('a set)) DIFF (v_A0 : ('a set)))) = ((v_A0 : ('a set)) UNION (v_B0 : ('a set))))``,
   entry "set_L1549_Un_Diff_cancel2" 1549 "by blast" benchLib.Blast false []
     ``((((v_B0 : ('a set)) DIFF (v_A0 : ('a set))) UNION (v_A0 : ('a set))) = ((v_B0 : ('a set)) UNION (v_A0 : ('a set))))``,
   entry "set_L1552_Diff_Un" 1552 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) DIFF ((v_B0 : ('a set)) UNION (v_C0 : ('a set)))) = (((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) INTER ((v_A0 : ('a set)) DIFF (v_C0 : ('a set)))))``,
   entry "set_L1555_Diff_Int" 1555 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) DIFF ((v_B0 : ('a set)) INTER (v_C0 : ('a set)))) = (((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) UNION ((v_A0 : ('a set)) DIFF (v_C0 : ('a set)))))``,
   entry "set_L1558_Diff_Diff_Int" 1558 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) DIFF ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))) = ((v_A0 : ('a set)) INTER (v_B0 : ('a set))))``,
   entry "set_L1561_Un_Diff" 1561 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) UNION (v_B0 : ('a set))) DIFF (v_C0 : ('a set))) = (((v_A0 : ('a set)) DIFF (v_C0 : ('a set))) UNION ((v_B0 : ('a set)) DIFF (v_C0 : ('a set)))))``,
   entry "set_L1564_Int_Diff" 1564 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) INTER (v_B0 : ('a set))) DIFF (v_C0 : ('a set))) = ((v_A0 : ('a set)) INTER ((v_B0 : ('a set)) DIFF (v_C0 : ('a set)))))``,
   entry "set_L1567_Diff_Int_distrib" 1567 "by blast" benchLib.Blast false []
     ``(((v_C0 : ('a set)) INTER ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))) = (((v_C0 : ('a set)) INTER (v_A0 : ('a set))) DIFF ((v_C0 : ('a set)) INTER (v_B0 : ('a set)))))``,
   entry "set_L1570_Diff_Int_distrib2" 1570 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) INTER (v_C0 : ('a set))) = (((v_A0 : ('a set)) INTER (v_C0 : ('a set))) DIFF ((v_B0 : ('a set)) INTER (v_C0 : ('a set)))))``,
   entry "set_L1573_Diff_Compl" 1573 "by auto" benchLib.Auto false []
     ``(((v_A0 : ('a set)) DIFF (COMPL (v_B0 : ('a set)))) = ((v_A0 : ('a set)) INTER (v_B0 : ('a set))))``,
   entry "set_L1576_Compl_Diff_eq" 1576 "by blast" benchLib.Blast false []
     ``((COMPL ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))) = ((COMPL (v_A0 : ('a set))) UNION (v_B0 : ('a set))))``,
   entry "set_L1579_subset_Compl_singleton" 1579 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (COMPL ((v_b0 : 'a) INSERT {}))) = (~((v_b0 : 'a) IN (v_A0 : ('a set)))))``,
   entry "set_L1587_all_bool_eq" 1587 "by (auto intro: bool_induct)" benchLib.Auto false []
     ``((!b_b : bool. ((v_P0 : (bool -> bool)) b_b)) = (((v_P0 : (bool -> bool)) T) /\ ((v_P0 : (bool -> bool)) F)))``,
   entry "set_L1593_ex_bool_eq" 1593 "by (auto intro: bool_contrapos)" benchLib.Auto false []
     ``((?b_b : bool. ((v_P0 : (bool -> bool)) b_b)) = (((v_P0 : (bool -> bool)) T) \/ ((v_P0 : (bool -> bool)) F)))``,
   entry "set_L1596_UNIV_bool" 1596 "by (auto intro: bool_induct)" benchLib.Auto false [{name = "pred_set$UNIV_BOOL", theorem = pred_setTheory.UNIV_BOOL}]
     ``(UNIV = (F INSERT (T INSERT {})))``,
   entry "set_L1601_Pow_empty" 1601 "by (auto simp add: Pow_def)" benchLib.Auto false [{name = "pred_set$POW_EMPTY", theorem = pred_setTheory.POW_EMPTY}]
     ``((POW {}) = ({} INSERT {}))``,
   entry "set_L1604_Pow_singleton_iff" 1604 "by blast (* somewhat slow *)" benchLib.Blast false []
     ``(((POW (v_X0 : ('a set))) = ((v_Y0 : ('a set)) INSERT {})) = (((v_X0 : ('a set)) = {}) /\ ((v_Y0 : ('a set)) = {})))``,
   entry "set_L1607_Pow_insert" 1607 "by (blast intro: image_eqI [where ?x = \"u - {a}\" for u])" benchLib.Blast false [{name = "pred_set$POW_INSERT", theorem = pred_setTheory.POW_INSERT}]
     ``((POW ((v_a0 : 'a) INSERT (v_A0 : ('a set)))) =
        ((POW (v_A0 : ('a set))) UNION
         (IMAGE (\b_insert_set : 'a set.
                   (v_a0 : 'a) INSERT b_insert_set)
            (POW (v_A0 : ('a set))))))``,
   entry "set_L1610_Pow_Compl" 1610 "by (blast intro: exI [where ?x = \"- u\" for u])" benchLib.Blast false []
     ``((POW (COMPL (v_A0 : ('a set)))) = (\b_uu_ : ('a set). (?b_B : ('a set). ((b_uu_ = (COMPL b_B)) /\ ((v_A0 : ('a set)) IN (POW b_B))))))``,
   entry "set_L1613_Pow_UNIV" 1613 "by blast" benchLib.Blast false []
     ``((POW UNIV) = UNIV)``,
   entry "set_L1616_Un_Pow_subset" 1616 "by blast" benchLib.Blast false []
     ``(((POW (v_A0 : ('a set))) UNION (POW (v_B0 : ('a set)))) SUBSET (POW ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))))``,
   entry "set_L1619_Pow_Int_eq" 1619 "by blast" benchLib.Blast false []
     ``((POW ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))) = ((POW (v_A0 : ('a set))) INTER (POW (v_B0 : ('a set)))))``,
   entry "set_L1625_Int_Diff_disjoint" 1625 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) INTER (v_B0 : ('a set))) INTER ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))) = {})``,
   entry "set_L1628_Int_Diff_Un" 1628 "by blast" benchLib.Blast false []
     ``((((v_A0 : ('a set)) INTER (v_B0 : ('a set))) UNION ((v_A0 : ('a set)) DIFF (v_B0 : ('a set)))) = (v_A0 : ('a set)))``,
   entry "set_L1631_set_eq_subset" 1631 "by blast" benchLib.Blast false [{name = "pred_set$SET_EQ_SUBSET", theorem = pred_setTheory.SET_EQ_SUBSET}]
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) = (((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) /\ ((v_B0 : ('a set)) SUBSET (v_A0 : ('a set)))))``,
   entry "set_L1637_subset_iff_psubset_eq" 1637 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) = (((v_A0 : ('a set)) PSUBSET (v_B0 : ('a set))) \/ ((v_A0 : ('a set)) = (v_B0 : ('a set)))))``,
   entry "set_L1640_all_not_in_conv" 1640 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. (~(b_x IN (v_A0 : ('a set))))) = ((v_A0 : ('a set)) = {}))``,
   entry "set_L1643_ex_in_conv" 1643 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (v_A0 : ('a set)))) = (~((v_A0 : ('a set)) = {})))``,
   entry "set_L1646_ball_simps_1" 1646 "by auto" benchLib.Auto false []
     ``((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> (((v_P0 : ('a -> bool)) b_x) \/ (v_Q0 : bool))) = ((!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> ((v_P0 : ('a -> bool)) b_x)) \/ (v_Q0 : bool)))``,
   entry "set_L1646_ball_simps_2" 1646 "by auto" benchLib.Auto false []
     ``((!b_x : 'b. (b_x IN (v_A0 : ('b set))) ==> ((v_P0 : bool) \/ ((v_Q0 : ('b -> bool)) b_x))) = ((v_P0 : bool) \/ (!b_x : 'b. (b_x IN (v_A0 : ('b set))) ==> ((v_Q0 : ('b -> bool)) b_x))))``,
   entry "set_L1646_ball_simps_3" 1646 "by auto" benchLib.Auto false []
     ``((!b_x : 'c. (b_x IN (v_A0 : ('c set))) ==> ((v_P0 : bool) ==> ((v_Q0 : ('c -> bool)) b_x))) = ((v_P0 : bool) ==> (!b_x : 'c. (b_x IN (v_A0 : ('c set))) ==> ((v_Q0 : ('c -> bool)) b_x))))``,
   entry "set_L1646_ball_simps_4" 1646 "by auto" benchLib.Auto false []
     ``((!b_x : 'd. (b_x IN (v_A0 : ('d set))) ==> (((v_P0 : ('d -> bool)) b_x) ==> (v_Q0 : bool))) = ((?b_x : 'd. (b_x IN (v_A0 : ('d set))) /\ ((v_P0 : ('d -> bool)) b_x)) ==> (v_Q0 : bool)))``,
   entry "set_L1646_ball_simps_5" 1646 "by auto" benchLib.Auto false []
     ``((!b_x : 'e. (b_x IN {}) ==> ((v_P0 : ('e -> bool)) b_x)) = T)``,
   entry "set_L1646_ball_simps_6" 1646 "by auto" benchLib.Auto false []
     ``((!b_x : 'f. (b_x IN UNIV) ==> ((v_P0 : ('f -> bool)) b_x)) = (!b_x : 'f. ((v_P0 : ('f -> bool)) b_x)))``,
   entry "set_L1646_ball_simps_7" 1646 "by auto" benchLib.Auto false []
     ``((!b_x : 'g. (b_x IN ((v_a0 : 'g) INSERT (v_B0 : ('g set)))) ==> ((v_P0 : ('g -> bool)) b_x)) = (((v_P0 : ('g -> bool)) (v_a0 : 'g)) /\ (!b_x : 'g. (b_x IN (v_B0 : ('g set))) ==> ((v_P0 : ('g -> bool)) b_x))))``,
   entry "set_L1646_ball_simps_8" 1646 "by auto" benchLib.Auto false []
     ``((!b_x : 'h. (b_x IN (v_Q0 : ('h -> bool))) ==> ((v_P0 : ('h -> bool)) b_x)) = (!b_x : 'h. (((v_Q0 : ('h -> bool)) b_x) ==> ((v_P0 : ('h -> bool)) b_x))))``,
   entry "set_L1646_ball_simps_9" 1646 "by auto" benchLib.Auto false []
     ``((!b_x : 'j. (b_x IN (IMAGE (v_f0 : ('i -> 'j)) (v_A0 : ('i set)))) ==> ((v_P0 : ('j -> bool)) b_x)) = (!b_x : 'i. (b_x IN (v_A0 : ('i set))) ==> ((v_P0 : ('j -> bool)) ((v_f0 : ('i -> 'j)) b_x))))``,
   entry "set_L1646_ball_simps_10" 1646 "by auto" benchLib.Auto false []
     ``((~(!b_x : 'k. (b_x IN (v_A0 : ('k set))) ==> ((v_P0 : ('k -> bool)) b_x))) = (?b_x : 'k. (b_x IN (v_A0 : ('k set))) /\ (~((v_P0 : ('k -> bool)) b_x))))``,
   entry "set_L1659_bex_simps_1" 1659 "by auto" benchLib.Auto false []
     ``((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ (((v_P0 : ('a -> bool)) b_x) /\ (v_Q0 : bool))) = ((?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ ((v_P0 : ('a -> bool)) b_x)) /\ (v_Q0 : bool)))``,
   entry "set_L1659_bex_simps_2" 1659 "by auto" benchLib.Auto false []
     ``((?b_x : 'b. (b_x IN (v_A0 : ('b set))) /\ ((v_P0 : bool) /\ ((v_Q0 : ('b -> bool)) b_x))) = ((v_P0 : bool) /\ (?b_x : 'b. (b_x IN (v_A0 : ('b set))) /\ ((v_Q0 : ('b -> bool)) b_x))))``,
   entry "set_L1659_bex_simps_3" 1659 "by auto" benchLib.Auto false []
     ``((?b_x : 'c. (b_x IN {}) /\ ((v_P0 : ('c -> bool)) b_x)) = F)``,
   entry "set_L1659_bex_simps_4" 1659 "by auto" benchLib.Auto false []
     ``((?b_x : 'd. (b_x IN UNIV) /\ ((v_P0 : ('d -> bool)) b_x)) = (?b_x : 'd. ((v_P0 : ('d -> bool)) b_x)))``,
   entry "set_L1659_bex_simps_5" 1659 "by auto" benchLib.Auto false []
     ``((?b_x : 'e. (b_x IN ((v_a0 : 'e) INSERT (v_B0 : ('e set)))) /\ ((v_P0 : ('e -> bool)) b_x)) = (((v_P0 : ('e -> bool)) (v_a0 : 'e)) \/ (?b_x : 'e. (b_x IN (v_B0 : ('e set))) /\ ((v_P0 : ('e -> bool)) b_x))))``,
   entry "set_L1659_bex_simps_6" 1659 "by auto" benchLib.Auto false []
     ``((?b_x : 'f. (b_x IN (v_Q0 : ('f -> bool))) /\ ((v_P0 : ('f -> bool)) b_x)) = (?b_x : 'f. (((v_Q0 : ('f -> bool)) b_x) /\ ((v_P0 : ('f -> bool)) b_x))))``,
   entry "set_L1659_bex_simps_7" 1659 "by auto" benchLib.Auto false []
     ``((?b_x : 'h. (b_x IN (IMAGE (v_f0 : ('g -> 'h)) (v_A0 : ('g set)))) /\ ((v_P0 : ('h -> bool)) b_x)) = (?b_x : 'g. (b_x IN (v_A0 : ('g set))) /\ ((v_P0 : ('h -> bool)) ((v_f0 : ('g -> 'h)) b_x))))``,
   entry "set_L1659_bex_simps_8" 1659 "by auto" benchLib.Auto false []
     ``((~(?b_x : 'i. (b_x IN (v_A0 : ('i set))) /\ ((v_P0 : ('i -> bool)) b_x))) = (!b_x : 'i. (b_x IN (v_A0 : ('i set))) ==> (~((v_P0 : ('i -> bool)) b_x))))``,
   entry "set_L1670_ex_image_cong_iff_1" 1670 "by auto" benchLib.Auto false []
     ``((?b_x : 'a. (b_x IN (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))))) = (~((v_A0 : ('b set)) = {})))``,
   entry "set_L1670_ex_image_cong_iff_2" 1670 "by auto" benchLib.Auto false []
     ``((?b_x : 'a. ((b_x IN (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set)))) /\ ((v_P0 : ('a -> bool)) b_x))) = (?b_x : 'b. (b_x IN (v_A0 : ('b set))) /\ ((v_P0 : ('a -> bool)) ((v_f0 : ('b -> 'a)) b_x))))``,
   entry "set_L1676_image_mono" 1676 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> ((IMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('a set))) SUBSET (IMAGE (v_f0 : ('a -> 'b)) (v_B0 : ('a set)))))``,
   entry "set_L1679_Pow_mono" 1679 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> ((POW (v_A0 : ('a set))) SUBSET (POW (v_B0 : ('a set)))))``,
   entry "set_L1682_insert_mono" 1682 "by blast" benchLib.Blast false []
     ``(((v_C0 : ('a set)) SUBSET (v_D0 : ('a set))) ==> (((v_a0 : 'a) INSERT (v_C0 : ('a set))) SUBSET ((v_a0 : 'a) INSERT (v_D0 : ('a set)))))``,
   entry "set_L1691_Diff_mono" 1691 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_C0 : ('a set))) ==> (((v_D0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> (((v_A0 : ('a set)) DIFF (v_B0 : ('a set))) SUBSET ((v_C0 : ('a set)) DIFF (v_D0 : ('a set))))))``,
   entry "set_L1722_Collect_mono" 1722 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. (((v_P0 : ('a -> bool)) b_x) ==> ((v_Q0 : ('a -> bool)) b_x))) ==> ((v_P0 : ('a -> bool)) SUBSET (v_Q0 : ('a -> bool))))``,
   entry "set_L1725_Int_Collect_mono" 1725 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> ((!b_x : 'a. ((b_x IN (v_A0 : ('a set))) ==> (((v_P0 : ('a -> bool)) b_x) ==> ((v_Q0 : ('a -> bool)) b_x)))) ==> (((v_A0 : ('a set)) INTER (v_P0 : ('a -> bool))) SUBSET ((v_B0 : ('a set)) INTER (v_Q0 : ('a -> bool))))))``,
   entry "set_L1740_vimage_eq" 1740 "by blast" benchLib.Blast false []
     ``(((v_a0 : 'a) IN (PREIMAGE (v_f0 : ('a -> 'b)) (v_B0 : ('b set)))) = (((v_f0 : ('a -> 'b)) (v_a0 : 'a)) IN (v_B0 : ('b set))))``,
   entry "set_L1743_vimage_singleton_eq" 1743 "by simp" benchLib.Simp false []
     ``(((v_a0 : 'a) IN (PREIMAGE (v_f0 : ('a -> 'b)) ((v_b0 : 'b) INSERT {}))) = (((v_f0 : ('a -> 'b)) (v_a0 : 'a)) = (v_b0 : 'b)))``,
   entry "set_L1746_vimageI" 1746 "by blast" benchLib.Blast false []
     ``((((v_f0 : ('b -> 'a)) (v_a0 : 'b)) = (v_b0 : 'a)) ==> (((v_b0 : 'a) IN (v_B0 : ('a set))) ==> ((v_a0 : 'b) IN (PREIMAGE (v_f0 : ('b -> 'a)) (v_B0 : ('a set))))))``,
   entry "set_L1752_vimageE" 1752 "by blast" benchLib.Blast false []
     ``(((v_a0 : 'a) IN (PREIMAGE (v_f0 : ('a -> 'b)) (v_B0 : ('b set)))) ==> ((!b_x : 'b. ((((v_f0 : ('a -> 'b)) (v_a0 : 'a)) = b_x) ==> ((b_x IN (v_B0 : ('b set))) ==> (v_P0 : bool)))) ==> (v_P0 : bool)))``,
   entry "set_L1758_vimage_empty" 1758 "by blast" benchLib.Blast false []
     ``((PREIMAGE (v_f0 : ('a -> 'b)) {}) = {})``,
   entry "set_L1761_vimage_Compl" 1761 "by blast" benchLib.Blast false []
     ``((PREIMAGE (v_f0 : ('a -> 'b)) (COMPL (v_A0 : ('b set)))) = (COMPL (PREIMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('b set)))))``,
   entry "set_L1764_vimage_Un" 1764 "by blast" benchLib.Blast false []
     ``((PREIMAGE (v_f0 : ('a -> 'b)) ((v_A0 : ('b set)) UNION (v_B0 : ('b set)))) = ((PREIMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('b set))) UNION (PREIMAGE (v_f0 : ('a -> 'b)) (v_B0 : ('b set)))))``,
   entry "set_L1770_vimage_Collect_eq" 1770 "by blast" benchLib.Blast false []
     ``((PREIMAGE (v_f0 : ('a -> 'b)) (v_P0 : ('b -> bool))) = (\b_y : 'a. ((v_P0 : ('b -> bool)) ((v_f0 : ('a -> 'b)) b_y))))``,
   entry "set_L1773_vimage_Collect" 1773 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. (((v_P0 : ('b -> bool)) ((v_f0 : ('a -> 'b)) b_x)) = ((v_Q0 : ('a -> bool)) b_x))) ==> ((PREIMAGE (v_f0 : ('a -> 'b)) (v_P0 : ('b -> bool))) = (v_Q0 : ('a -> bool))))``,
   entry "set_L1776_vimage_insert" 1776 "by blast" benchLib.Blast false []
     ``((PREIMAGE (v_f0 : ('a -> 'b)) ((v_a0 : 'b) INSERT (v_B0 : ('b set)))) = ((PREIMAGE (v_f0 : ('a -> 'b)) ((v_a0 : 'b) INSERT {})) UNION (PREIMAGE (v_f0 : ('a -> 'b)) (v_B0 : ('b set)))))``,
   entry "set_L1780_vimage_Diff" 1780 "by blast" benchLib.Blast false []
     ``((PREIMAGE (v_f0 : ('a -> 'b)) ((v_A0 : ('b set)) DIFF (v_B0 : ('b set)))) = ((PREIMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('b set))) DIFF (PREIMAGE (v_f0 : ('a -> 'b)) (v_B0 : ('b set)))))``,
   entry "set_L1783_vimage_UNIV" 1783 "by blast" benchLib.Blast false []
     ``((PREIMAGE (v_f0 : ('a -> 'b)) UNIV) = UNIV)``,
   entry "set_L1786_vimage_mono" 1786 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) ==> ((PREIMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('a set))) SUBSET (PREIMAGE (v_f0 : ('b -> 'a)) (v_B0 : ('a set)))))``,
   entry "set_L1790_vimage_image_eq" 1790 "by (blast intro: sym)" benchLib.Blast false []
     ``((PREIMAGE (v_f0 : ('a -> 'b)) (IMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('a set)))) = (\b_y : 'a. (?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ (((v_f0 : ('a -> 'b)) b_x) = ((v_f0 : ('a -> 'b)) b_y)))))``,
   entry "set_L1793_image_vimage_subset" 1793 "by blast" benchLib.Blast false []
     ``((IMAGE (v_f0 : ('b -> 'a)) (PREIMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('a set)))) SUBSET (v_A0 : ('a set)))``,
   entry "set_L1796_image_vimage_eq" 1796 "by blast" benchLib.Blast false []
     ``((IMAGE (v_f0 : ('b -> 'a)) (PREIMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('a set)))) = ((v_A0 : ('a set)) INTER (IMAGE (v_f0 : ('b -> 'a)) UNIV)))``,
   entry "set_L1799_image_subset_iff_subset_vimage" 1799 "by blast" benchLib.Blast false []
     ``(((IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))) SUBSET (v_B0 : ('a set))) = ((v_A0 : ('b set)) SUBSET (PREIMAGE (v_f0 : ('b -> 'a)) (v_B0 : ('a set)))))``,
   entry "set_L1802_subset_vimage_iff" 1802 "by auto" benchLib.Auto false []
     ``(((v_A0 : ('a set)) SUBSET (PREIMAGE (v_f0 : ('a -> 'b)) (v_B0 : ('b set)))) = (!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> (((v_f0 : ('a -> 'b)) b_x) IN (v_B0 : ('b set)))))``,
   entry "set_L1805_vimage_const" 1805 "by auto" benchLib.Auto false []
     ``((PREIMAGE (\b_x : 'a. (v_c0 : 'b)) (v_A0 : ('b set))) = (if ((v_c0 : 'b) IN (v_A0 : ('b set))) then UNIV else {}))``,
   entry "set_L1808_vimage_if" 1808 "by (auto simp add: vimage_def)" benchLib.Auto false []
     ``((PREIMAGE (\b_x : 'a. (if (b_x IN (v_B0 : ('a set))) then (v_c0 : 'b) else (v_d0 : 'b))) (v_A0 : ('b set))) = (if ((v_c0 : 'b) IN (v_A0 : ('b set))) then (if ((v_d0 : 'b) IN (v_A0 : ('b set))) then UNIV else (v_B0 : ('a set))) else (if ((v_d0 : 'b) IN (v_A0 : ('b set))) then (COMPL (v_B0 : ('a set))) else {})))``,
   entry "set_L1813_vimage_inter_cong" 1813 "by auto" benchLib.Auto false []
     ``((!b_w : 'a. ((b_w IN (v_S0 : ('a set))) ==> (((v_f0 : ('a -> 'b)) b_w) = ((v_g0 : ('a -> 'b)) b_w)))) ==> (((PREIMAGE (v_f0 : ('a -> 'b)) (v_y0 : ('b set))) INTER (v_S0 : ('a set))) = ((PREIMAGE (v_g0 : ('a -> 'b)) (v_y0 : ('b set))) INTER (v_S0 : ('a set)))))``,
   entry "set_L1816_vimage_ident" 1816 "by blast" benchLib.Blast false []
     ``((PREIMAGE (\b_x : 'a. b_x) (v_Y0 : ('a set))) = (v_Y0 : ('a set)))``,
   entry "set_L1825_is_singletonI" 1825 "by simp" benchLib.Simp false []
     ``(?b_singleton : 'a. ((v_x0 : 'a) INSERT {}) = {b_singleton})``,
   entry "set_L1828_is_singletonI_" 1828 "by blast" benchLib.Blast false []
     ``((~((v_A0 : ('a set)) = {})) ==> ((!b_x : 'a. (!b_y : 'a. ((b_x IN (v_A0 : ('a set))) ==> ((b_y IN (v_A0 : ('a set))) ==> (b_x = b_y))))) ==> (?b_singleton : 'a. (v_A0 : ('a set)) = {b_singleton})))``,
   entry "set_L1831_is_singletonE" 1831 "by blast" benchLib.Blast false []
     ``((?b_singleton : 'a. (v_A0 : ('a set)) = {b_singleton}) ==> ((!b_x : 'a. (((v_A0 : ('a set)) = (b_x INSERT {})) ==> (v_P0 : bool))) ==> (v_P0 : bool)))``,
   entry "set_L1834_is_singleton_iff_ex1" 1834 "by (auto simp add: is_singleton_def)" benchLib.Auto false []
     ``((?b_singleton : 'a. (v_A0 : ('a set)) = {b_singleton}) = (?!b_x : 'a. (b_x IN (v_A0 : ('a set)))))``,
   entry "set_L1844_the_elem_eq" 1844 "by (simp add: the_elem_def)" benchLib.Simp false []
     ``((CHOICE ((v_x0 : 'a) INSERT {})) = (v_x0 : 'a))``,
   entry "set_L1847_is_singleton_the_elem" 1847 "by (auto simp: is_singleton_def)" benchLib.Auto false []
     ``((?b_singleton : 'a. (v_A0 : ('a set)) = {b_singleton}) = ((v_A0 : ('a set)) = ((CHOICE (v_A0 : ('a set))) INSERT {})))``,
   entry "set_L1870_bind_bind" 1870 "by (auto simp: bind_def)" benchLib.Auto false []
     ``((\b_bind_result : 'a. ?b_bind_source : 'b. (\b_bind_result : 'b. ?b_bind_source : 'c. (v_P0 : ('c -> bool)) b_bind_source /\ ((v_Q0 : ('c -> ('b -> bool))) b_bind_source) b_bind_result) b_bind_source /\ ((v_R0 : ('b -> ('a -> bool))) b_bind_source) b_bind_result) = (\b_bind_result : 'a. ?b_bind_source : 'c. (v_P0 : ('c -> bool)) b_bind_source /\ ((\b_x : 'c. (\b_bind_result : 'a. ?b_bind_source : 'b. ((v_Q0 : ('c -> ('b -> bool))) b_x) b_bind_source /\ ((v_R0 : ('b -> ('a -> bool))) b_bind_source) b_bind_result)) b_bind_source) b_bind_result))``,
   entry "set_L1874_empty_bind" 1874 "by (simp add: bind_def)" benchLib.Simp false []
     ``((\b_bind_result : 'a. ?b_bind_source : 'b. b_bind_source IN {} /\ b_bind_result IN ((v_f0 : ('b -> ('a set))) b_bind_source)) = {})``,
   entry "set_L1877_nonempty_bind_const" 1877 "by (auto simp: bind_def)" benchLib.Auto false []
     ``((~((v_A0 : ('a set)) = {})) ==> ((\b_bind_result : 'b. ?b_bind_source : 'a. b_bind_source IN (v_A0 : ('a set)) /\ b_bind_result IN ((\b_uu_ : 'a. (v_B0 : ('b set))) b_bind_source)) = (v_B0 : ('b set))))``,
   entry "set_L1880_bind_const" 1880 "by (auto simp: bind_def)" benchLib.Auto false []
     ``((\b_bind_result : 'a. ?b_bind_source : 'b. b_bind_source IN (v_A0 : ('b set)) /\ b_bind_result IN ((\b_uu_ : 'b. (v_B0 : ('a set))) b_bind_source)) = (if ((v_A0 : ('b set)) = {}) then {} else (v_B0 : ('a set))))``,
   entry "set_L1883_bind_singleton_conv_image" 1883 "by (auto simp: bind_def)" benchLib.Auto false []
     ``((\b_bind_result : 'a. ?b_bind_source : 'b. b_bind_source IN (v_A0 : ('b set)) /\ b_bind_result IN ((\b_x : 'b. (((v_f0 : ('b -> 'a)) b_x) INSERT {})) b_bind_source)) = (IMAGE (v_f0 : ('b -> 'a)) (v_A0 : ('b set))))``,
   entry "set_L1931_pairwise_alt" 1931 "by (auto simp add: pairwise_def)" benchLib.Auto false []
     ``((!b_pair_left : 'a. b_pair_left IN (v_S0 : ('a set)) ==> !b_pair_right : 'a. b_pair_right IN (v_S0 : ('a set)) ==> b_pair_left <> b_pair_right ==> (v_R0 : ('a -> ('a -> bool))) b_pair_left b_pair_right) = (!b_x : 'a. (b_x IN (v_S0 : ('a set))) ==> (!b_y : 'a. (b_y IN ((v_S0 : ('a set)) DIFF (b_x INSERT {}))) ==> (((v_R0 : ('a -> ('a -> bool))) b_x) b_y))))``,
   entry "set_L1934_pairwise_trivial" 1934 "by (auto simp: pairwise_def)" benchLib.Auto false []
     ``(!b_pair_left : 'a. b_pair_left IN (v_I0 : ('a set)) ==> !b_pair_right : 'a. b_pair_right IN (v_I0 : ('a set)) ==> b_pair_left <> b_pair_right ==> (\b_i : 'a. (\b_j : 'a. (~(b_j = b_i)))) b_pair_left b_pair_right)``,
   entry "set_L1937_pairwiseI" 1937 "by (simp add: pairwise_def)" benchLib.Simp false []
     ``((!b_x : 'a. (!b_y : 'a. ((b_x IN (v_S0 : ('a set))) ==> ((b_y IN (v_S0 : ('a set))) ==> ((~(b_x = b_y)) ==> (((v_R0 : ('a -> ('a -> bool))) b_x) b_y)))))) ==> (!b_pair_left : 'a. b_pair_left IN (v_S0 : ('a set)) ==> !b_pair_right : 'a. b_pair_right IN (v_S0 : ('a set)) ==> b_pair_left <> b_pair_right ==> (v_R0 : ('a -> ('a -> bool))) b_pair_left b_pair_right))``,
   entry "set_L1946_pairwise_empty" 1946 "by (simp add: pairwise_def)" benchLib.Simp false [{name = "pred_set$pairwise_EMPTY", theorem = pred_setTheory.pairwise_EMPTY}]
     ``(!b_pair_left : 'a. b_pair_left IN {} ==> !b_pair_right : 'a. b_pair_right IN {} ==> b_pair_left <> b_pair_right ==> (v_P0 : ('a -> ('a -> bool))) b_pair_left b_pair_right)``,
   entry "set_L1949_pairwise_singleton" 1949 "by (simp add: pairwise_def)" benchLib.Simp false []
     ``(!b_pair_left : 'a. b_pair_left IN ((v_A0 : 'a) INSERT {}) ==> !b_pair_right : 'a. b_pair_right IN ((v_A0 : 'a) INSERT {}) ==> b_pair_left <> b_pair_right ==> (v_P0 : ('a -> ('a -> bool))) b_pair_left b_pair_right)``,
   entry "set_L1952_pairwise_insert" 1952 "by (force simp: pairwise_def)" benchLib.Force false []
     ``((!b_pair_left : 'a. b_pair_left IN ((v_x0 : 'a) INSERT (v_s0 : ('a set))) ==> !b_pair_right : 'a. b_pair_right IN ((v_x0 : 'a) INSERT (v_s0 : ('a set))) ==> b_pair_left <> b_pair_right ==> (v_r0 : ('a -> ('a -> bool))) b_pair_left b_pair_right) = ((!b_y : 'a. (((b_y IN (v_s0 : ('a set))) /\ (~(b_y = (v_x0 : 'a)))) ==> ((((v_r0 : ('a -> ('a -> bool))) (v_x0 : 'a)) b_y) /\ (((v_r0 : ('a -> ('a -> bool))) b_y) (v_x0 : 'a))))) /\ (!b_pair_left : 'a. b_pair_left IN (v_s0 : ('a set)) ==> !b_pair_right : 'a. b_pair_right IN (v_s0 : ('a set)) ==> b_pair_left <> b_pair_right ==> (v_r0 : ('a -> ('a -> bool))) b_pair_left b_pair_right)))``,
   entry "set_L1956_pairwise_subset" 1956 "by (force simp: pairwise_def)" benchLib.Force false [{name = "pred_set$pairwise_SUBSET", theorem = pred_setTheory.pairwise_SUBSET}]
     ``((!b_pair_left : 'a. b_pair_left IN (v_S0 : ('a set)) ==> !b_pair_right : 'a. b_pair_right IN (v_S0 : ('a set)) ==> b_pair_left <> b_pair_right ==> (v_P0 : ('a -> ('a -> bool))) b_pair_left b_pair_right) ==> (((v_T0 : ('a set)) SUBSET (v_S0 : ('a set))) ==> (!b_pair_left : 'a. b_pair_left IN (v_T0 : ('a set)) ==> !b_pair_right : 'a. b_pair_right IN (v_T0 : ('a set)) ==> b_pair_left <> b_pair_right ==> (v_P0 : ('a -> ('a -> bool))) b_pair_left b_pair_right)))``,
   entry "set_L1959_pairwise_mono" 1959 "by (fastforce simp: pairwise_def)" benchLib.Fastforce false []
     ``((!b_pair_left : 'a. b_pair_left IN (v_A0 : ('a set)) ==> !b_pair_right : 'a. b_pair_right IN (v_A0 : ('a set)) ==> b_pair_left <> b_pair_right ==> (v_P0 : ('a -> ('a -> bool))) b_pair_left b_pair_right) ==> ((!b_x : 'a. (!b_y : 'a. ((((v_P0 : ('a -> ('a -> bool))) b_x) b_y) ==> (((v_Q0 : ('a -> ('a -> bool))) b_x) b_y)))) ==> (((v_B0 : ('a set)) SUBSET (v_A0 : ('a set))) ==> (!b_pair_left : 'a. b_pair_left IN (v_B0 : ('a set)) ==> !b_pair_right : 'a. b_pair_right IN (v_B0 : ('a set)) ==> b_pair_left <> b_pair_right ==> (v_Q0 : ('a -> ('a -> bool))) b_pair_left b_pair_right))))``,
   entry "set_L1962_pairwise_imageI" 1962 "by (auto intro: pairwiseI)" benchLib.Auto false []
     ``((!b_x : 'a. (!b_y : 'a. ((b_x IN (v_A0 : ('a set))) ==> ((b_y IN (v_A0 : ('a set))) ==> ((~(b_x = b_y)) ==> ((~(((v_f0 : ('a -> 'b)) b_x) = ((v_f0 : ('a -> 'b)) b_y))) ==> (((v_P0 : ('b -> ('b -> bool))) ((v_f0 : ('a -> 'b)) b_x)) ((v_f0 : ('a -> 'b)) b_y)))))))) ==> (!b_pair_left : 'b. b_pair_left IN (IMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('a set))) ==> !b_pair_right : 'b. b_pair_right IN (IMAGE (v_f0 : ('a -> 'b)) (v_A0 : ('a set))) ==> b_pair_left <> b_pair_right ==> (v_P0 : ('b -> ('b -> bool))) b_pair_left b_pair_right))``,
   entry "set_L1967_pairwise_image" 1967 "by (force simp: pairwise_def)" benchLib.Force false []
     ``((!b_pair_left : 'a. b_pair_left IN (IMAGE (v_f0 : ('b -> 'a)) (v_s0 : ('b set))) ==> !b_pair_right : 'a. b_pair_right IN (IMAGE (v_f0 : ('b -> 'a)) (v_s0 : ('b set))) ==> b_pair_left <> b_pair_right ==> (v_r0 : ('a -> ('a -> bool))) b_pair_left b_pair_right) = (!b_pair_left : 'b. b_pair_left IN (v_s0 : ('b set)) ==> !b_pair_right : 'b. b_pair_right IN (v_s0 : ('b set)) ==> b_pair_left <> b_pair_right ==> (\b_x : 'b. (\b_y : 'b. ((~(((v_f0 : ('b -> 'a)) b_x) = ((v_f0 : ('b -> 'a)) b_y))) ==> (((v_r0 : ('a -> ('a -> bool))) ((v_f0 : ('b -> 'a)) b_x)) ((v_f0 : ('b -> 'a)) b_y))))) b_pair_left b_pair_right))``,
   entry "set_L1973_disjnt_self_iff_empty" 1973 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``((DISJOINT (v_S0 : ('a set)) (v_S0 : ('a set))) = ((v_S0 : ('a set)) = {}))``,
   entry "set_L1976_disjnt_commute" 1976 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``((DISJOINT (v_A0 : ('a set)) (v_B0 : ('a set))) = (DISJOINT (v_B0 : ('a set)) (v_A0 : ('a set))))``,
   entry "set_L1979_disjnt_iff" 1979 "by (force simp: disjnt_def)" benchLib.Force false []
     ``((DISJOINT (v_A0 : ('a set)) (v_B0 : ('a set))) = (!b_x : 'a. (~((b_x IN (v_A0 : ('a set))) /\ (b_x IN (v_B0 : ('a set)))))))``,
   entry "set_L1982_disjnt_sym" 1982 "by blast" benchLib.Blast false []
     ``((DISJOINT (v_A0 : ('a set)) (v_B0 : ('a set))) ==> (DISJOINT (v_B0 : ('a set)) (v_A0 : ('a set))))``,
   entry "set_L1985_disjnt_empty1" 1985 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``(DISJOINT {} (v_A0 : ('a set)))``,
   entry "set_L1985_disjnt_empty2" 1985 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``(DISJOINT (v_A0 : ('a set)) {})``,
   entry "set_L1988_disjnt_insert1" 1988 "by (simp add: disjnt_def)" benchLib.Simp false []
     ``((DISJOINT ((v_a0 : 'a) INSERT (v_X0 : ('a set))) (v_Y0 : ('a set))) = ((~((v_a0 : 'a) IN (v_Y0 : ('a set)))) /\ (DISJOINT (v_X0 : ('a set)) (v_Y0 : ('a set)))))``,
   entry "set_L1991_disjnt_insert2" 1991 "by (simp add: disjnt_def)" benchLib.Simp false []
     ``((DISJOINT (v_Y0 : ('a set)) ((v_a0 : 'a) INSERT (v_X0 : ('a set)))) = ((~((v_a0 : 'a) IN (v_Y0 : ('a set)))) /\ (DISJOINT (v_Y0 : ('a set)) (v_X0 : ('a set)))))``,
   entry "set_L1994_disjnt_subset1" 1994 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``((DISJOINT (v_X0 : ('a set)) (v_Y0 : ('a set))) ==> (((v_Z0 : ('a set)) SUBSET (v_X0 : ('a set))) ==> (DISJOINT (v_Z0 : ('a set)) (v_Y0 : ('a set)))))``,
   entry "set_L1997_disjnt_subset2" 1997 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``((DISJOINT (v_X0 : ('a set)) (v_Y0 : ('a set))) ==> (((v_Z0 : ('a set)) SUBSET (v_Y0 : ('a set))) ==> (DISJOINT (v_X0 : ('a set)) (v_Z0 : ('a set)))))``,
   entry "set_L2000_disjnt_Un1" 2000 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``((DISJOINT ((v_A0 : ('a set)) UNION (v_B0 : ('a set))) (v_C0 : ('a set))) = ((DISJOINT (v_A0 : ('a set)) (v_C0 : ('a set))) /\ (DISJOINT (v_B0 : ('a set)) (v_C0 : ('a set)))))``,
   entry "set_L2003_disjnt_Un2" 2003 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``((DISJOINT (v_C0 : ('a set)) ((v_A0 : ('a set)) UNION (v_B0 : ('a set)))) = ((DISJOINT (v_C0 : ('a set)) (v_A0 : ('a set))) /\ (DISJOINT (v_C0 : ('a set)) (v_B0 : ('a set)))))``,
   entry "set_L2006_disjnt_Diff1" 2006 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``(((v_X0 : ('a set)) SUBSET (v_V0 : ('a set))) ==> (DISJOINT ((v_X0 : ('a set)) DIFF (v_Y0 : ('a set))) ((v_U0 : ('a set)) DIFF (v_V0 : ('a set)))))``,
   entry "set_L2006_disjnt_Diff2" 2006 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``(((v_X0 : ('a set)) SUBSET (v_V0 : ('a set))) ==> (DISJOINT ((v_U0 : ('a set)) DIFF (v_V0 : ('a set))) ((v_X0 : ('a set)) DIFF (v_Y0 : ('a set)))))``,
   entry "set_L2012_pairwise_disjnt_iff" 2012 "by (auto simp: Uniq_def disjnt_iff pairwise_def)" benchLib.Auto false []
     ``((!b_pair_left : ('a set). b_pair_left IN (v___A_0 : (('a set) set)) ==> !b_pair_right : ('a set). b_pair_right IN (v___A_0 : (('a set) set)) ==> b_pair_left <> b_pair_right ==> DISJOINT b_pair_left b_pair_right) = (!b_x : 'a. (!b_unique_left : ('a set). !b_unique_right : ('a set). ((\b_X : ('a set). ((b_X IN (v___A_0 : (('a set) set))) /\ (b_x IN b_X))) b_unique_left /\ (\b_X : ('a set). ((b_X IN (v___A_0 : (('a set) set))) /\ (b_x IN b_X))) b_unique_right) ==> b_unique_left = b_unique_right)))``,
   entry "set_L2015_disjnt_insert" 2015 "by (simp add: disjnt_def)" benchLib.Simp false []
     ``((~((v_x0 : 'a) IN (v_N0 : ('a set)))) ==> ((DISJOINT (v_M0 : ('a set)) (v_N0 : ('a set))) ==> (DISJOINT ((v_x0 : 'a) INSERT (v_M0 : ('a set))) (v_N0 : ('a set)))))``,
   entry "set_L2019_Int_emptyI" 2019 "by blast" benchLib.Blast false []
     ``((!b_x : 'a. ((b_x IN (v_A0 : ('a set))) ==> ((b_x IN (v_B0 : ('a set))) ==> F))) ==> (((v_A0 : ('a set)) INTER (v_B0 : ('a set))) = {}))``
  ]

end
