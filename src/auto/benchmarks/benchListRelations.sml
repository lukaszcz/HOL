structure benchListRelations =
struct

open HolKernel

fun entry id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/List.thy", line = line, commit = "f7e02b7e"},
   representative = false}

(* The [code_unfold] lemmas at List.thy:8259 and 8273 are not here.
   Each states that a set-encoded relation and its predicate encoding
   agree -- [(xs, ys) : lexord r <-> lexordp (%x y. (x, y) : r) xs ys]
   -- and HOL4 has only the predicate encoding, so nothing of the
   source result survives the translation.  They are recorded as
   translation gaps in [benchLibraryShortfalls.translation]. *)
val goals =
  [entry "list_L7054_set_trans_list_step_subset_trancl" 7054
     "unfolding trans_list_step_def by auto"
     ``!pairs.
         LIST_TO_SET
           (parityTranslation$source_trans_list_step pairs) SUBSET
         set_relation$transitive_closure (LIST_TO_SET pairs)``,
   entry "list_L7954_listrel_iff_nth" 7954
     "by (auto simp add: all_set_conv_all_nth listrel_iff_zip)"
     ``!relation xs ys.
         (LIST_REL relation xs ys <=>
          LENGTH xs = LENGTH ys /\
          !index.
            index < LENGTH xs ==>
            relation (EL index xs) (EL index ys))``,
   entry "list_L7978_listrel_sym" 7978
     "by (simp add: listrel_iff_nth sym_def)"
     ``!relation.
         relation$symmetric relation ==>
         relation$symmetric (LIST_REL relation)``,
   entry "list_L7995_equiv_listrel" 7995
     "by (simp add: equiv_def listrel_subset listrel_refl_on listrel_sym listrel_trans)"
     ``!domain relation.
         parityTranslation$source_equiv domain relation ==>
         parityTranslation$source_equiv
           (parityTranslation$source_lists domain)
           (LIST_REL relation)``,
   entry "list_L7998_listrel_rtrancl_refl" 7998
     "using listrel_refl_on[of UNIV, OF refl_rtrancl] by auto"
     ``!relation xs. LIST_REL (relation$RTC relation) xs xs``,
   entry "list_L8006_listrel_Nil" 8006
     "by (blast intro: listrel.intros)"
     ``!relation.
         parityTranslation$source_rel_image
           (LIST_REL relation) {[]} = {[]}``,
   entry "list_L8009_listrel_Cons" 8009
     "by (auto simp add: set_Cons_def intro: listrel.intros)"
     ``!relation value xs.
         parityTranslation$source_rel_image
           (LIST_REL relation) {value::xs} =
         parityTranslation$source_set_Cons
           (parityTranslation$source_rel_image relation {value})
           (parityTranslation$source_rel_image
              (LIST_REL relation) {xs})``,
   entry "list_L8044_listrel1_subset_listrel" 8044
     "by (auto elim!: listrel1E simp add: listrel_iff_zip)"
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
     ``!xs.
         parityTranslation$source_superset xs =
         (\ys.
            parityTranslation$source_list_all
              (\value. MEM value xs) ys)``,
   entry "list_L8709_wf_set" 8709
     "by (simp add: wf_iff_acyclic_if_finite)"
     ``!pairs.
         relation$WF
           (set_relation$reln_to_rel (LIST_TO_SET pairs)) <=>
         set_relation$acyclic (LIST_TO_SET pairs)``,
   entry "list_L8999_set_Cons_transfer" 8999
     "unfolding rel_fun_def rel_set_def set_Cons_def by fastforce"
     ``!relation.
         (list$SET_REL relation ===>
          list$SET_REL (LIST_REL relation) ===>
          list$SET_REL (LIST_REL relation))
           parityTranslation$source_set_Cons
           parityTranslation$source_set_Cons``]

val shortfalls : benchLib.shortfall list = []

end
