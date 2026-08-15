structure benchListRelations =
struct

open HolKernel

fun named name theorem : benchLib.named_thm =
  {name = name, theorem = theorem}

fun entry id line method recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = recipe, excl = [], provenance =
     {file = "src/HOL/List.thy", line = line, commit = "f7e02b7e"},
   representative = false}

val goals =
  [entry "list_L7054_set_trans_list_step_subset_trancl" 7054
     "unfolding trans_list_step_def by auto"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named
              "parityTranslation$source_trans_list_step_subset_tc"
              parityTranslationTheory.source_trans_list_step_subset_tc)]))
     ``!pairs.
         LIST_TO_SET
           (parityTranslation$source_trans_list_step pairs) SUBSET
         set_relation$transitive_closure (LIST_TO_SET pairs)``,
   entry "list_L7954_listrel_iff_nth" 7954
     "by (auto simp add: all_set_conv_all_nth listrel_iff_zip)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "list$LIST_REL_EL_EQN"
              listTheory.LIST_REL_EL_EQN)]))
     ``!relation xs ys.
         (LIST_REL relation xs ys <=>
          LENGTH xs = LENGTH ys /\
          !index.
            index < LENGTH xs ==>
            relation (EL index xs) (EL index ys))``,
   entry "list_L7978_listrel_sym" 7978
     "by (simp add: listrel_iff_nth sym_def)"
     (benchLib.Then
       (benchLib.Invoke
         (benchLib.Simp,
          [benchLib.DefinitionAdd
             (named "relation$symmetric_def"
                relationTheory.symmetric_def),
           benchLib.RewriteAdd
             (named "list$LIST_REL_EL_EQN"
                listTheory.LIST_REL_EL_EQN),
           benchLib.RewriteAdd
             (named "bool$EQ_SYM_EQ" boolTheory.EQ_SYM_EQ)]),
        benchLib.Invoke (benchLib.Auto, [])))
     ``!relation.
         relation$symmetric relation ==>
         relation$symmetric (LIST_REL relation)``,
   entry "list_L7995_equiv_listrel" 7995
     "by (simp add: equiv_def listrel_subset listrel_refl_on listrel_sym listrel_trans)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_equiv_LIST_REL"
              parityTranslationTheory.source_equiv_LIST_REL)]))
     ``!domain relation.
         parityTranslation$source_equiv domain relation ==>
         parityTranslation$source_equiv
           (parityTranslation$source_lists domain)
           (LIST_REL relation)``,
   entry "list_L7998_listrel_rtrancl_refl" 7998
     "using listrel_refl_on[of UNIV, OF refl_rtrancl] by auto"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "list$LIST_REL_EL_EQN"
              listTheory.LIST_REL_EL_EQN),
         benchLib.RewriteAdd
           (named "relation$RTC_REFL" relationTheory.RTC_REFL)]))
     ``!relation xs. LIST_REL (relation$RTC relation) xs xs``,
   entry "list_L8006_listrel_Nil" 8006
     "by (blast intro: listrel.intros)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_rel_image_def"
              parityTranslationTheory.source_rel_image_def),
         benchLib.DefinitionAdd
           (named "pred_set$EXTENSION" pred_setTheory.EXTENSION),
         benchLib.RewriteAdd
           (named "list$LIST_REL_NIL" listTheory.LIST_REL_NIL)]))
     ``!relation.
         parityTranslation$source_rel_image
           (LIST_REL relation) {[]} = {[]}``,
   entry "list_L8009_listrel_Cons" 8009
     "by (auto simp add: set_Cons_def intro: listrel.intros)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_rel_image_def"
              parityTranslationTheory.source_rel_image_def),
         benchLib.DefinitionAdd
           (named "parityTranslation$source_set_Cons_def"
              parityTranslationTheory.source_set_Cons_def),
         benchLib.DefinitionAdd
           (named "pred_set$EXTENSION" pred_setTheory.EXTENSION),
         benchLib.RewriteAdd
           (named "list$LIST_REL_CONS1"
              listTheory.LIST_REL_CONS1)]))
     ``!relation value xs.
         parityTranslation$source_rel_image
           (LIST_REL relation) {value::xs} =
         parityTranslation$source_set_Cons
           (parityTranslation$source_rel_image relation {value})
           (parityTranslation$source_rel_image
              (LIST_REL relation) {xs})``,
   entry "list_L8044_listrel1_subset_listrel" 8044
     "by (auto elim!: listrel1E simp add: listrel_iff_zip)"
     (benchLib.Invoke
       (benchLib.Blast,
        [benchLib.FactAdd
           (named "parityTranslation$source_listrel1_subset_LIST_REL"
              parityTranslationTheory.source_listrel1_subset_LIST_REL)]))
     ``!left_relation right_relation.
         (!left right.
            left_relation left right ==>
            right_relation left right) ==>
         relation$reflexive right_relation ==>
         !xs ys.
           parityTranslation$source_listrel1
             left_relation xs ys ==>
           LIST_REL right_relation xs ys``,
   entry "list_L8247_anon_L8247" 8247
     "by (auto simp: fun_eq_iff list_all_iff)"
     (benchLib.Invoke
       (benchLib.Auto,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_superset_def"
              parityTranslationTheory.source_superset_def),
         benchLib.DefinitionAdd
           (named "parityTranslation$source_list_all_def"
              parityTranslationTheory.source_list_all_def),
         benchLib.DefinitionAdd
           (named "bool$FUN_EQ_THM" boolTheory.FUN_EQ_THM),
         benchLib.DefinitionAdd
           (named "pred_set$SUBSET_DEF" pred_setTheory.SUBSET_DEF),
         benchLib.RewriteAdd
           (named "pred_set$IN_APP" pred_setTheory.IN_APP),
         benchLib.RewriteAdd
           (named "list$EVERY_MEM" listTheory.EVERY_MEM)]))
     ``!xs.
         parityTranslation$source_superset xs =
         (\ys.
            parityTranslation$source_list_all
              (\value. MEM value xs) ys)``,
   entry "list_L8259_anon_L8259" 8259
     "by (simp add: listrel1p_def)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_listrel1p_def"
              parityTranslationTheory.source_listrel1p_def)]))
     ``!relation xs ys.
         (parityTranslation$source_listrel1p relation xs ys <=>
          parityTranslation$source_listrel1 relation xs ys)``,
   entry "list_L8273_anon_L8273" 8273
     "by (simp add: lexordp_def)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.DefinitionAdd
           (named "parityTranslation$source_lexordp_code_def"
              parityTranslationTheory.source_lexordp_code_def)]))
     ``!relation xs ys.
         (parityTranslation$source_lexordp_code relation xs ys <=>
          parityTranslation$source_lexord relation xs ys)``,
   entry "list_L8709_wf_set" 8709
     "by (simp add: wf_iff_acyclic_if_finite)"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_wf_list_set"
              parityTranslationTheory.source_wf_list_set)]))
     ``!pairs.
         relation$WF
           (set_relation$reln_to_rel (LIST_TO_SET pairs)) <=>
         set_relation$acyclic (LIST_TO_SET pairs)``,
   entry "list_L8999_set_Cons_transfer" 8999
     "unfolding rel_fun_def rel_set_def set_Cons_def by fastforce"
     (benchLib.Invoke
       (benchLib.Simp,
        [benchLib.RewriteAdd
           (named "parityTranslation$source_set_Cons_transfer"
              parityTranslationTheory.source_set_Cons_transfer)]))
     ``!relation.
         (list$SET_REL relation ===>
          list$SET_REL (LIST_REL relation) ===>
          list$SET_REL (LIST_REL relation))
           parityTranslation$source_set_Cons
           parityTranslation$source_set_Cons``]

val shortfalls : benchLib.shortfall list = []

end
