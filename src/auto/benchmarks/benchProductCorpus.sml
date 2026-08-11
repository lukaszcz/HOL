structure benchProductCorpus =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun entry id line method mapped representative excl goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method, mapped = mapped,
   excl = List.filter (fn {theorem, ...} =>
     benchLib.theorem_is_goal goal theorem) excl, provenance =
     {file = "src/HOL/Product_Type.thy", line = line, commit = commit},
   representative = representative}

val goals =
  [
   entry "product_type_L107_unit_all_eq1" 107 "by simp" benchLib.Simp false []
     ``((!b_x : unit. ((v_P0 : (unit -> bool)) b_x)) = ((v_P0 : (unit -> bool)) ()))``,
   entry "product_type_L122_UNIV_unit" 122 "by auto" benchLib.Auto false []
     ``(UNIV = (() INSERT {}))``,
   entry "product_type_L419_Pair_inject" 419 "by simp" benchLib.Simp false []
     ``((((v_a0 : 'a),(v_b0 : 'b)) = ((v_a_0 : 'a),(v_b_0 : 'b))) ==> ((((v_a0 : 'a) = (v_a_0 : 'a)) ==> (((v_b0 : 'b) = (v_b_0 : 'b)) ==> (v_R0 : bool))) ==> (v_R0 : bool)))``,
   entry "product_type_L425_fst_eqD" 425 "by simp" benchLib.Simp false []
     ``(((FST ((v_x0 : 'a),(v_y0 : 'b))) = (v_a0 : 'a)) ==> ((v_x0 : 'a) = (v_a0 : 'a)))``,
   entry "product_type_L428_snd_eqD" 428 "by simp" benchLib.Simp false []
     ``(((SND ((v_x0 : 'b),(v_y0 : 'a))) = (v_a0 : 'a)) ==> ((v_y0 : 'a) = (v_a0 : 'a)))``,
   entry "product_type_L431_case_prod_unfold" 431 "by (simp add: fun_eq_iff split: prod.split)" benchLib.Simp false []
     ``(UNCURRY = (\b_c : ('a -> ('b -> 'c)). (\b_p : ('a # 'b). ((b_c (FST b_p)) (SND b_p)))))``,
   entry "product_type_L442_prod_eqI" 442 "by (simp add: prod_eq_iff)" benchLib.Simp false []
     ``(((FST (v_p0 : ('a # 'b))) = (FST (v_q0 : ('a # 'b)))) ==> (((SND (v_p0 : ('a # 'b))) = (SND (v_q0 : ('a # 'b)))) ==> ((v_p0 : ('a # 'b)) = (v_q0 : ('a # 'b)))))``,
   entry "product_type_L451_case_prod_Pair" 451 "by (simp add: fun_eq_iff split: prod.split)" benchLib.Simp false []
     ``((UNCURRY (\b_pair_left : 'a. \b_pair_right : 'b. (b_pair_left,b_pair_right))) = I)``,
   entry "product_type_L454_case_prod_eta" 454 "by (simp add: fun_eq_iff split: prod.split)" benchLib.Simp false []
     ``((UNCURRY (\b_x : 'a. (\b_y : 'b. ((v_f0 : (('a # 'b) -> 'c)) (b_x,b_y))))) = (v_f0 : (('a # 'b) -> 'c)))``,
   entry "product_type_L466_The_case_prod" 466 "by (simp add: case_prod_unfold)" benchLib.Simp false []
     ``((CHOICE (UNCURRY (v_P0 : ('a -> ('b -> bool))))) = (CHOICE (\b_xy : ('a # 'b). (((v_P0 : ('a -> ('b -> bool))) (FST b_xy)) (SND b_xy)))))``,
   entry "product_type_L469_cond_case_prod_eta" 469 "by (simp add: case_prod_eta)" benchLib.Simp false []
     ``((!b_x : 'a. (!b_y : 'b. ((((v_f0 : ('a -> ('b -> 'c))) b_x) b_y) = ((v_g0 : (('a # 'b) -> 'c)) (b_x,b_y))))) ==> ((UNCURRY (\b_x : 'a. (\b_y : 'b. (((v_f0 : ('a -> ('b -> 'c))) b_x) b_y)))) = (v_g0 : (('a # 'b) -> 'c))))``,
   entry "product_type_L527_split_paired_The" 527 "by (simp add: case_prod_eta)" benchLib.Simp false []
     ``((CHOICE (\b_x : ('a # 'b). ((v_P0 : (('a # 'b) -> bool)) b_x))) = (CHOICE (UNCURRY (\b_a : 'a. (\b_b : 'b. ((v_P0 : (('a # 'b) -> bool)) (b_a,b_b)))))))``,
   entry "product_type_L587_case_prod_beta_" 587 "by (auto simp: fun_eq_iff)" benchLib.Auto false []
     ``((UNCURRY (\b_x : 'a. (\b_y : 'b. (((v_f0 : ('a -> ('b -> 'c))) b_x) b_y)))) = (\b_x : ('a # 'b). (((v_f0 : ('a -> ('b -> 'c))) (FST b_x)) (SND b_x))))``,
   entry "product_type_L596_case_prodI2" 596 "by (simp add: split_tupled_all)" benchLib.Simp true []
     ``((!b_a : 'a. (!b_b : 'b. (((v_p0 : ('a # 'b)) = (b_a,b_b)) ==> (((v_c0 : ('a -> ('b -> bool))) b_a) b_b)))) ==> ((UNCURRY (\b_a : 'a. (\b_b : 'b. (((v_c0 : ('a -> ('b -> bool))) b_a) b_b)))) (v_p0 : ('a # 'b))))``,
   entry "product_type_L600_case_prodI2_" 600 "by (simp add: split_tupled_all)" benchLib.Simp false []
     ``((!b_a : 'a. (!b_b : 'b. (((b_a,b_b) = (v_p0 : ('a # 'b))) ==> ((((v_c0 : ('a -> ('b -> ('c -> bool)))) b_a) b_b) (v_x0 : 'c))))) ==> (((UNCURRY (\b_a : 'a. (\b_b : 'b. (((v_c0 : ('a -> ('b -> ('c -> bool)))) b_a) b_b)))) (v_p0 : ('a # 'b))) (v_x0 : 'c)))``,
   entry "product_type_L622_case_prodD_" 622 "by simp" benchLib.Simp false []
     ``((((UNCURRY (\b_c : 'a. (\b_d : 'b. (((v_R0 : ('a -> ('b -> ('c -> bool)))) b_c) b_d)))) ((v_a0 : 'a),(v_b0 : 'b))) (v_c0 : 'c)) ==> ((((v_R0 : ('a -> ('b -> ('c -> bool)))) (v_a0 : 'a)) (v_b0 : 'b)) (v_c0 : 'c)))``,
   entry "product_type_L625_mem_case_prodI" 625 "by simp" benchLib.Simp false []
     ``(((v_z0 : 'a) IN (((v_c0 : ('b -> ('c -> ('a set)))) (v_a0 : 'b)) (v_b0 : 'c))) ==> ((v_z0 : 'a) IN ((UNCURRY (\b_d : 'b. (\b_e : 'c. (((v_c0 : ('b -> ('c -> ('a set)))) b_d) b_e)))) ((v_a0 : 'b),(v_b0 : 'c)))))``,
   entry "product_type_L685_Collect_const_case_prod" 685 "by auto" benchLib.Auto false []
     ``((UNCURRY (\b_a : 'a. (\b_b : 'b. (v_P0 : bool)))) = (if (v_P0 : bool) then UNIV else {}))``,
   entry "product_type_L688_The_split_eq" 688 "by blast" benchLib.Blast false []
     ``((CHOICE (UNCURRY (\b_x_ : 'a. (\b_y_ : 'b. (((v_x0 : 'a) = b_x_) /\ ((v_y0 : 'b) = b_y_)))))) = ((v_x0 : 'a),(v_y0 : 'b)))``,
   entry "product_type_L785_curry_conv" 785 "by (simp add: curry_def)" benchLib.Simp false []
     ``((((CURRY (v_f0 : (('b # 'c) -> 'a))) (v_a0 : 'b)) (v_b0 : 'c)) = ((v_f0 : (('b # 'c) -> 'a)) ((v_a0 : 'b),(v_b0 : 'c))))``,
   entry "product_type_L788_curryI" 788 "by (simp add: curry_def)" benchLib.Simp false []
     ``(((v_f0 : (('a # 'b) -> bool)) ((v_a0 : 'a),(v_b0 : 'b))) ==> (((CURRY (v_f0 : (('a # 'b) -> bool))) (v_a0 : 'a)) (v_b0 : 'b)))``,
   entry "product_type_L791_curryD" 791 "by (simp add: curry_def)" benchLib.Simp false []
     ``((((CURRY (v_f0 : (('a # 'b) -> bool))) (v_a0 : 'a)) (v_b0 : 'b)) ==> ((v_f0 : (('a # 'b) -> bool)) ((v_a0 : 'a),(v_b0 : 'b))))``,
   entry "product_type_L794_curryE" 794 "by (simp add: curry_def)" benchLib.Simp false []
     ``((((CURRY (v_f0 : (('a # 'b) -> bool))) (v_a0 : 'a)) (v_b0 : 'b)) ==> ((((v_f0 : (('a # 'b) -> bool)) ((v_a0 : 'a),(v_b0 : 'b))) ==> (v_Q0 : bool)) ==> (v_Q0 : bool)))``,
   entry "product_type_L797_curry_case_prod" 797 "by (simp add: curry_def case_prod_unfold)" benchLib.Simp false []
     ``((CURRY (UNCURRY (v_f0 : ('a -> ('b -> 'c))))) = (v_f0 : ('a -> ('b -> 'c))))``,
   entry "product_type_L800_case_prod_curry" 800 "by (simp add: curry_def case_prod_unfold)" benchLib.Simp false []
     ``((UNCURRY (CURRY (v_f0 : (('a # 'b) -> 'c)))) = (v_f0 : (('a # 'b) -> 'c)))``,
   entry "product_type_L803_curry_K" 803 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``((CURRY (\b_x : ('a # 'b). (v_c0 : 'c))) = (\b_x : 'a. (\b_y : 'b. (v_c0 : 'c))))``,
   entry "product_type_L823_scomp_unfold" 823 "by (simp add: fun_eq_iff scomp_def case_prod_unfold)" benchLib.Simp false []
     ``((\b_scomp_source : ('a -> ('b # 'c)). \b_scomp_combine : ('b -> ('c -> 'd)). \b_scomp_input : 'a. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) = (\b_f : ('a -> ('b # 'c)). (\b_g : ('b -> ('c -> 'd)). (\b_x : 'a. ((b_g (FST (b_f b_x))) (SND (b_f b_x)))))))``,
   entry "product_type_L826_scomp_apply" 826 "by (simp add: scomp_unfold case_prod_unfold)" benchLib.Simp false []
     ``(((((\b_scomp_source : ('b -> ('c # 'd)). \b_scomp_combine : ('c -> ('d -> 'a)). \b_scomp_input : 'b. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) (v_f0 : ('b -> ('c # 'd)))) (v_g0 : ('c -> ('d -> 'a)))) (v_x0 : 'b)) = ((UNCURRY (v_g0 : ('c -> ('d -> 'a)))) ((v_f0 : ('b -> ('c # 'd))) (v_x0 : 'b))))``,
   entry "product_type_L829_Pair_scomp" 829 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``((((\b_scomp_source : ('a -> ('c # 'a)). \b_scomp_combine : ('c -> ('a -> 'b)). \b_scomp_input : 'a. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) ((\b_pair_left : 'c. \b_pair_right : 'a. (b_pair_left,b_pair_right)) (v_x0 : 'c))) (v_f0 : ('c -> ('a -> 'b)))) = ((v_f0 : ('c -> ('a -> 'b))) (v_x0 : 'c)))``,
   entry "product_type_L832_scomp_Pair" 832 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``((((\b_scomp_source : ('a -> ('b # 'c)). \b_scomp_combine : ('b -> ('c -> ('b # 'c))). \b_scomp_input : 'a. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) (v_x0 : ('a -> ('b # 'c)))) (\b_pair_left : 'b. \b_pair_right : 'c. (b_pair_left,b_pair_right))) = (v_x0 : ('a -> ('b # 'c))))``,
   entry "product_type_L835_scomp_scomp" 835 "by (simp add: fun_eq_iff scomp_unfold)" benchLib.Simp false []
     ``((((\b_scomp_source : ('a -> ('c # 'd)). \b_scomp_combine : ('c -> ('d -> 'b)). \b_scomp_input : 'a. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) (((\b_scomp_source : ('a -> ('e # 'f)). \b_scomp_combine : ('e -> ('f -> ('c # 'd))). \b_scomp_input : 'a. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) (v_f0 : ('a -> ('e # 'f)))) (v_g0 : ('e -> ('f -> ('c # 'd)))))) (v_h0 : ('c -> ('d -> 'b)))) = (((\b_scomp_source : ('a -> ('e # 'f)). \b_scomp_combine : ('e -> ('f -> 'b)). \b_scomp_input : 'a. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) (v_f0 : ('a -> ('e # 'f)))) (\b_x : 'e. (((\b_scomp_source : ('f -> ('c # 'd)). \b_scomp_combine : ('c -> ('d -> 'b)). \b_scomp_input : 'f. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) ((v_g0 : ('e -> ('f -> ('c # 'd)))) b_x)) (v_h0 : ('c -> ('d -> 'b)))))))``,
   entry "product_type_L838_scomp_fcomp" 838 "by (simp add: fun_eq_iff scomp_unfold fcomp_def)" benchLib.Simp false []
     ``((((\b_fcomp_first : ('a -> 'c). \b_fcomp_second : ('c -> 'b). \b_fcomp_input : 'a. b_fcomp_second (b_fcomp_first b_fcomp_input)) (((\b_scomp_source : ('a -> ('d # 'e)). \b_scomp_combine : ('d -> ('e -> 'c)). \b_scomp_input : 'a. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) (v_f0 : ('a -> ('d # 'e)))) (v_g0 : ('d -> ('e -> 'c))))) (v_h0 : ('c -> 'b))) = (((\b_scomp_source : ('a -> ('d # 'e)). \b_scomp_combine : ('d -> ('e -> 'b)). \b_scomp_input : 'a. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) (v_f0 : ('a -> ('d # 'e)))) (\b_x : 'd. (((\b_fcomp_first : ('e -> 'c). \b_fcomp_second : ('c -> 'b). \b_fcomp_input : 'e. b_fcomp_second (b_fcomp_first b_fcomp_input)) ((v_g0 : ('d -> ('e -> 'c))) b_x)) (v_h0 : ('c -> 'b))))))``,
   entry "product_type_L841_fcomp_scomp" 841 "by (simp add: fun_eq_iff scomp_unfold)" benchLib.Simp false []
     ``((((\b_scomp_source : ('a -> ('c # 'd)). \b_scomp_combine : ('c -> ('d -> 'b)). \b_scomp_input : 'a. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) (((\b_fcomp_first : ('a -> 'e). \b_fcomp_second : ('e -> ('c # 'd)). \b_fcomp_input : 'a. b_fcomp_second (b_fcomp_first b_fcomp_input)) (v_f0 : ('a -> 'e))) (v_g0 : ('e -> ('c # 'd))))) (v_h0 : ('c -> ('d -> 'b)))) = (((\b_fcomp_first : ('a -> 'e). \b_fcomp_second : ('e -> 'b). \b_fcomp_input : 'a. b_fcomp_second (b_fcomp_first b_fcomp_input)) (v_f0 : ('a -> 'e))) (((\b_scomp_source : ('e -> ('c # 'd)). \b_scomp_combine : ('c -> ('d -> 'b)). \b_scomp_input : 'e. b_scomp_combine (FST (b_scomp_source b_scomp_input)) (SND (b_scomp_source b_scomp_input))) (v_g0 : ('e -> ('c # 'd)))) (v_h0 : ('c -> ('d -> 'b))))))``,
   entry "product_type_L856_map_prod_simp" 856 "by (simp add: map_prod_def)" benchLib.Simp false []
     ``(((((\b_map_left : ('c -> 'a). \b_map_right : ('d -> 'b). \b_map_pair : ('c # 'd). (b_map_left (FST b_map_pair),b_map_right (SND b_map_pair))) (v_f0 : ('c -> 'a))) (v_g0 : ('d -> 'b))) ((v_a0 : 'c),(v_b0 : 'd))) = (((v_f0 : ('c -> 'a)) (v_a0 : 'c)),((v_g0 : ('d -> 'b)) (v_b0 : 'd))))``,
   entry "product_type_L900_apfst_conv" 900 "by (simp add: apfst_def)" benchLib.Simp false []
     ``((((\b_apfst_func : ('c -> 'a). \b_apfst_pair : ('c # 'b). (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) (v_f0 : ('c -> 'a))) ((v_x0 : 'c),(v_y0 : 'b))) = (((v_f0 : ('c -> 'a)) (v_x0 : 'c)),(v_y0 : 'b)))``,
   entry "product_type_L903_apsnd_conv" 903 "by (simp add: apsnd_def)" benchLib.Simp false []
     ``((((\b_apsnd_func : ('c -> 'b). \b_apsnd_pair : ('a # 'c). (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) (v_f0 : ('c -> 'b))) ((v_x0 : 'a),(v_y0 : 'c))) = ((v_x0 : 'a),((v_f0 : ('c -> 'b)) (v_y0 : 'c))))``,
   entry "product_type_L909_fst_comp_apfst" 909 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``(((combin$o FST) ((\b_apfst_func : ('a -> 'c). \b_apfst_pair : ('a # 'b). (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) (v_f0 : ('a -> 'c)))) = ((combin$o (v_f0 : ('a -> 'c))) FST))``,
   entry "product_type_L915_fst_comp_apsnd" 915 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``(((combin$o FST) ((\b_apsnd_func : ('b -> 'c). \b_apsnd_pair : ('a # 'b). (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) (v_f0 : ('b -> 'c)))) = FST)``,
   entry "product_type_L921_snd_comp_apfst" 921 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``(((combin$o SND) ((\b_apfst_func : ('a -> 'c). \b_apfst_pair : ('a # 'b). (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) (v_f0 : ('a -> 'c)))) = SND)``,
   entry "product_type_L927_snd_comp_apsnd" 927 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``(((combin$o SND) ((\b_apsnd_func : ('b -> 'c). \b_apsnd_pair : ('a # 'b). (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) (v_f0 : ('b -> 'c)))) = ((combin$o (v_f0 : ('b -> 'c))) SND))``,
   entry "product_type_L942_apfst_id" 942 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``(((\b_apfst_func : ('a -> 'a). \b_apfst_pair : ('a # 'b). (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) I) = I)``,
   entry "product_type_L945_apsnd_id" 945 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``(((\b_apsnd_func : ('b -> 'b). \b_apsnd_pair : ('a # 'b). (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) I) = I)``,
   entry "product_type_L954_apsnd_apfst_commute" 954 "by simp" benchLib.Simp false []
     ``((((\b_apsnd_func : ('c -> 'b). \b_apsnd_pair : ('a # 'c). (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) (v_f0 : ('c -> 'b))) (((\b_apfst_func : ('d -> 'a). \b_apfst_pair : ('d # 'c). (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) (v_g0 : ('d -> 'a))) (v_p0 : ('d # 'c)))) = (((\b_apfst_func : ('d -> 'a). \b_apfst_pair : ('d # 'b). (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) (v_g0 : ('d -> 'a))) (((\b_apsnd_func : ('c -> 'b). \b_apsnd_pair : ('d # 'c). (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) (v_f0 : ('c -> 'b))) (v_p0 : ('d # 'c)))))``,
   entry "product_type_L967_swap_simp" 967 "by (simp add: prod.swap_def)" benchLib.Simp false []
     ``(((\b_swap_pair : ('b # 'a). (SND b_swap_pair,FST b_swap_pair)) ((v_x0 : 'b),(v_y0 : 'a))) = ((v_y0 : 'a),(v_x0 : 'b)))``,
   entry "product_type_L973_swap_comp_swap" 973 "by (simp add: fun_eq_iff)" benchLib.Simp false []
     ``(((combin$o (\b_swap_pair : ('b # 'a). (SND b_swap_pair,FST b_swap_pair))) (\b_swap_pair : ('a # 'b). (SND b_swap_pair,FST b_swap_pair))) = I)``,
   entry "product_type_L976_pair_in_swap_image" 976 "by (auto intro!: image_eqI)" benchLib.Auto false []
     ``((((v_y0 : 'a),(v_x0 : 'b)) IN (IMAGE (\b_swap_pair : ('b # 'a). (SND b_swap_pair,FST b_swap_pair)) (v_A0 : (('b # 'a) set)))) = (((v_x0 : 'b),(v_y0 : 'a)) IN (v_A0 : (('b # 'a) set))))``,
   entry "product_type_L988_bij_swap" 988 "by (simp add: bij_def)" benchLib.Simp false [{name = "pred_set$BIJ_SWAP", theorem = pred_setTheory.BIJ_SWAP}]
     ``(((BIJ (\b_swap_pair : ('a # 'b). (SND b_swap_pair,FST b_swap_pair))) UNIV) UNIV)``,
   entry "product_type_L1000_split_pairs" 1000 "by auto" benchLib.Auto false []
     ``((((v_A0 : 'a),(v_B0 : 'b)) = (v_X0 : ('a # 'b))) = (((FST (v_X0 : ('a # 'b))) = (v_A0 : 'a)) /\ ((SND (v_X0 : ('a # 'b))) = (v_B0 : 'b))))``,
   entry "product_type_L1000_split_pairs2" 1000 "by auto" benchLib.Auto false []
     ``(((v_X0 : ('a # 'b)) = ((v_A0 : 'a),(v_B0 : 'b))) = (((FST (v_X0 : ('a # 'b))) = (v_A0 : 'a)) /\ ((SND (v_X0 : ('a # 'b))) = (v_B0 : 'b))))``,
   entry "product_type_L1028_SigmaI" 1028 "by blast" benchLib.Blast false []
     ``(((v_a0 : 'a) IN (v_A0 : ('a set))) ==> (((v_b0 : 'b) IN ((v_B0 : ('a -> ('b set))) (v_a0 : 'a))) ==> (((v_a0 : 'a),(v_b0 : 'b)) IN (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair))))))``,
   entry "product_type_L1031_SigmaE" 1031 "by blast" benchLib.Blast false []
     ``(((v_c0 : ('a # 'b)) IN (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))) ==> ((!b_x : 'a. (!b_y : 'b. ((b_x IN (v_A0 : ('a set))) ==> ((b_y IN ((v_B0 : ('a -> ('b set))) b_x)) ==> (((v_c0 : ('a # 'b)) = (b_x,b_y)) ==> (v_P0 : bool)))))) ==> (v_P0 : bool)))``,
   entry "product_type_L1040_SigmaD1" 1040 "by blast" benchLib.Blast false []
     ``((((v_a0 : 'a),(v_b0 : 'b)) IN (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))) ==> ((v_a0 : 'a) IN (v_A0 : ('a set))))``,
   entry "product_type_L1043_SigmaD2" 1043 "by blast" benchLib.Blast false []
     ``((((v_a0 : 'a),(v_b0 : 'b)) IN (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))) ==> ((v_b0 : 'b) IN ((v_B0 : ('a -> ('b set))) (v_a0 : 'a))))``,
   entry "product_type_L1046_SigmaE2" 1046 "by blast" benchLib.Blast false []
     ``((((v_a0 : 'a),(v_b0 : 'b)) IN (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))) ==> ((((v_a0 : 'a) IN (v_A0 : ('a set))) ==> (((v_b0 : 'b) IN ((v_B0 : ('a -> ('b set))) (v_a0 : 'a))) ==> (v_P0 : bool))) ==> (v_P0 : bool)))``,
   entry "product_type_L1049_Sigma_cong" 1049 "by auto" benchLib.Auto false [{name = "pred_set$SIGMA_CONG", theorem = pred_setTheory.SIGMA_CONG}]
     ``(((v_A0 : ('a set)) = (v_B0 : ('a set))) ==> ((!b_x : 'a. ((b_x IN (v_B0 : ('a set))) ==> (((v_C0 : ('a -> ('b set))) b_x) = ((v_D0 : ('a -> ('b set))) b_x)))) ==> ((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_x : 'a. ((v_C0 : ('a -> ('b set))) b_x)) (FST b_sigma_pair))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_B0 : ('a set)) /\ SND b_sigma_pair IN ((\b_x : 'a. ((v_D0 : ('a -> ('b set))) b_x)) (FST b_sigma_pair))))))``,
   entry "product_type_L1052_Sigma_mono" 1052 "by blast" benchLib.Blast false []
     ``(((v_A0 : ('a set)) SUBSET (v_C0 : ('a set))) ==> ((!b_x : 'a. ((b_x IN (v_A0 : ('a set))) ==> (((v_B0 : ('a -> ('b set))) b_x) SUBSET ((v_D0 : ('a -> ('b set))) b_x)))) ==> ((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair))) SUBSET (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_C0 : ('a set)) /\ SND b_sigma_pair IN ((v_D0 : ('a -> ('b set))) (FST b_sigma_pair))))))``,
   entry "product_type_L1055_Sigma_empty1" 1055 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN {} /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair))) = {})``,
   entry "product_type_L1058_Sigma_empty2" 1058 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. {}) (FST b_sigma_pair))) = {})``,
   entry "product_type_L1064_UNIV_Times_UNIV" 1064 "by auto" benchLib.Auto false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN UNIV /\ SND b_sigma_pair IN ((\b_uu_ : 'a. UNIV) (FST b_sigma_pair))) = UNIV)``,
   entry "product_type_L1067_Compl_Times_UNIV1" 1067 "by auto" benchLib.Auto false []
     ``((COMPL (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN UNIV /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_A0 : ('b set))) (FST b_sigma_pair)))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN UNIV /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (COMPL (v_A0 : ('b set)))) (FST b_sigma_pair))))``,
   entry "product_type_L1070_Compl_Times_UNIV2" 1070 "by auto" benchLib.Auto false []
     ``((COMPL (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. UNIV) (FST b_sigma_pair)))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (COMPL (v_A0 : ('a set))) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. UNIV) (FST b_sigma_pair))))``,
   entry "product_type_L1073_mem_Sigma_iff" 1073 "by blast" benchLib.Blast false []
     ``((((v_a0 : 'a),(v_b0 : 'b)) IN (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))) = (((v_a0 : 'a) IN (v_A0 : ('a set))) /\ ((v_b0 : 'b) IN ((v_B0 : ('a -> ('b set))) (v_a0 : 'a)))))``,
   entry "product_type_L1079_Sigma_empty_iff" 1079 "by auto" benchLib.Auto false []
     ``(((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((\b_i : 'a. ((v_X0 : ('a -> ('b set))) b_i)) (FST b_sigma_pair))) = {}) = (!b_i : 'a. (b_i IN (v_I0 : ('a set))) ==> (((v_X0 : ('a -> ('b set))) b_i) = {})))``,
   entry "product_type_L1082_Times_subset_cancel2" 1082 "by blast" benchLib.Blast false []
     ``(((v_x0 : 'a) IN (v_C0 : ('a set))) ==> (((\b_sigma_pair : ('b # 'a). FST b_sigma_pair IN (v_A0 : ('b set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'b. (v_C0 : ('a set))) (FST b_sigma_pair))) SUBSET (\b_sigma_pair : ('b # 'a). FST b_sigma_pair IN (v_B0 : ('b set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'b. (v_C0 : ('a set))) (FST b_sigma_pair)))) = ((v_A0 : ('b set)) SUBSET (v_B0 : ('b set)))))``,
   entry "product_type_L1085_Times_eq_cancel2" 1085 "by (blast elim: equalityE)" benchLib.Blast false []
     ``(((v_x0 : 'a) IN (v_C0 : ('a set))) ==> (((\b_sigma_pair : ('b # 'a). FST b_sigma_pair IN (v_A0 : ('b set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'b. (v_C0 : ('a set))) (FST b_sigma_pair))) = (\b_sigma_pair : ('b # 'a). FST b_sigma_pair IN (v_B0 : ('b set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'b. (v_C0 : ('a set))) (FST b_sigma_pair)))) = ((v_A0 : ('b set)) = (v_B0 : ('b set)))))``,
   entry "product_type_L1088_Collect_case_prod_Sigma" 1088 "by blast" benchLib.Blast false []
     ``((UNCURRY (\b_x : 'a. (\b_y : 'b. (((v_P0 : ('a -> bool)) b_x) /\ (((v_Q0 : ('a -> ('b -> bool))) b_x) b_y))))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_P0 : ('a -> bool)) /\ SND b_sigma_pair IN ((\b_x : 'a. ((v_Q0 : ('a -> ('b -> bool))) b_x)) (FST b_sigma_pair))))``,
   entry "product_type_L1094_Collect_case_prodD" 1094 "by auto" benchLib.Auto false []
     ``(((v_x0 : ('a # 'b)) IN (UNCURRY (v_A0 : ('a -> ('b -> bool))))) ==> (((v_A0 : ('a -> ('b -> bool))) (FST (v_x0 : ('a # 'b)))) (SND (v_x0 : ('a # 'b)))))``,
   entry "product_type_L1097_Collect_case_prod_mono" 1097 "by auto (auto elim!: le_funE)" benchLib.Auto false []
     ``((!b_order0 : 'a. (((v_A0 : ('a -> ('b -> bool))) b_order0) SUBSET ((v_B0 : ('a -> ('b -> bool))) b_order0))) ==> ((UNCURRY (v_A0 : ('a -> ('b -> bool)))) SUBSET (UNCURRY (v_B0 : ('a -> ('b -> bool))))))``,
   entry "product_type_L1100_Collect_split_mono_strong" 1100 "by fastforce" benchLib.Fastforce false []
     ``(((v_X0 : ('a set)) = (IMAGE FST (v_A0 : (('a # 'b) set)))) ==> (((v_Y0 : ('b set)) = (IMAGE SND (v_A0 : (('a # 'b) set)))) ==> ((!b_a : 'a. (b_a IN (v_X0 : ('a set))) ==> (!b_b : 'b. (b_b IN (v_Y0 : ('b set))) ==> ((((v_P0 : ('a -> ('b -> bool))) b_a) b_b) ==> (((v_Q0 : ('a -> ('b -> bool))) b_a) b_b)))) ==> (((v_A0 : (('a # 'b) set)) SUBSET (UNCURRY (v_P0 : ('a -> ('b -> bool))))) ==> ((v_A0 : (('a # 'b) set)) SUBSET (UNCURRY (v_Q0 : ('a -> ('b -> bool)))))))))``,
   entry "product_type_L1109_split_paired_Ball_Sigma" 1109 "by blast" benchLib.Blast false []
     ``((!b_z : ('a # 'b). (b_z IN (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))) ==> ((v_P0 : (('a # 'b) -> bool)) b_z)) = (!b_x : 'a. (b_x IN (v_A0 : ('a set))) ==> (!b_y : 'b. (b_y IN ((v_B0 : ('a -> ('b set))) b_x)) ==> ((v_P0 : (('a # 'b) -> bool)) (b_x,b_y)))))``,
   entry "product_type_L1112_split_paired_Bex_Sigma" 1112 "by blast" benchLib.Blast false []
     ``((?b_z : ('a # 'b). (b_z IN (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))) /\ ((v_P0 : (('a # 'b) -> bool)) b_z)) = (?b_x : 'a. (b_x IN (v_A0 : ('a set))) /\ (?b_y : 'b. (b_y IN ((v_B0 : ('a -> ('b set))) b_x)) /\ ((v_P0 : (('a # 'b) -> bool)) (b_x,b_y)))))``,
   entry "product_type_L1115_Sigma_Un_distrib1" 1115 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN ((v_I0 : ('a set)) UNION (v_J0 : ('a set))) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair))) = ((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair))) UNION (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_J0 : ('a set)) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair)))))``,
   entry "product_type_L1118_Sigma_Un_distrib2" 1118 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((\b_i : 'a. (((v_A0 : ('a -> ('b set))) b_i) UNION ((v_B0 : ('a -> ('b set))) b_i))) (FST b_sigma_pair))) = ((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((v_A0 : ('a -> ('b set))) (FST b_sigma_pair))) UNION (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))))``,
   entry "product_type_L1121_Sigma_Int_distrib1" 1121 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN ((v_I0 : ('a set)) INTER (v_J0 : ('a set))) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair))) = ((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair))) INTER (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_J0 : ('a set)) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair)))))``,
   entry "product_type_L1124_Sigma_Int_distrib2" 1124 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((\b_i : 'a. (((v_A0 : ('a -> ('b set))) b_i) INTER ((v_B0 : ('a -> ('b set))) b_i))) (FST b_sigma_pair))) = ((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((v_A0 : ('a -> ('b set))) (FST b_sigma_pair))) INTER (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))))``,
   entry "product_type_L1127_Sigma_Diff_distrib1" 1127 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN ((v_I0 : ('a set)) DIFF (v_J0 : ('a set))) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair))) = ((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair))) DIFF (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_J0 : ('a set)) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair)))))``,
   entry "product_type_L1130_Sigma_Diff_distrib2" 1130 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((\b_i : 'a. (((v_A0 : ('a -> ('b set))) b_i) DIFF ((v_B0 : ('a -> ('b set))) b_i))) (FST b_sigma_pair))) = ((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((v_A0 : ('a -> ('b set))) (FST b_sigma_pair))) DIFF (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_I0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))))``,
   entry "product_type_L1133_Sigma_Union" 1133 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (BIGUNION (v_X0 : (('a set) set))) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair))) = (BIGUNION (IMAGE (\b_A : ('a set). (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN b_A /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))) (v_X0 : (('a set) set)))))``,
   entry "product_type_L1136_Pair_vimage_Sigma" 1136 "by auto" benchLib.Auto false []
     ``((PREIMAGE ((\b_pair_left : 'b. \b_pair_right : 'a. (b_pair_left,b_pair_right)) (v_x0 : 'b)) (\b_sigma_pair : ('b # 'a). FST b_sigma_pair IN (v_A0 : ('b set)) /\ SND b_sigma_pair IN ((v_f0 : ('b -> ('a set))) (FST b_sigma_pair)))) = (if ((v_x0 : 'b) IN (v_A0 : ('b set))) then ((v_f0 : ('b -> ('a set))) (v_x0 : 'b)) else {}))``,
   entry "product_type_L1153_Times_empty" 1153 "by auto" benchLib.Auto false []
     ``(((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair))) = {}) = (((v_A0 : ('a set)) = {}) \/ ((v_B0 : ('b set)) = {})))``,
   entry "product_type_L1156_times_subset_iff" 1156 "by blast" benchLib.Blast false []
     ``(((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_C0 : ('b set))) (FST b_sigma_pair))) SUBSET (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_B0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_D0 : ('b set))) (FST b_sigma_pair)))) = (((v_A0 : ('a set)) = {}) \/ (((v_C0 : ('b set)) = {}) \/ (((v_A0 : ('a set)) SUBSET (v_B0 : ('a set))) /\ ((v_C0 : ('b set)) SUBSET (v_D0 : ('b set)))))))``,
   entry "product_type_L1159_times_eq_iff" 1159 "by auto" benchLib.Auto false []
     ``(((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_C0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_D0 : ('b set))) (FST b_sigma_pair)))) = ((((v_A0 : ('a set)) = (v_C0 : ('a set))) /\ ((v_B0 : ('b set)) = (v_D0 : ('b set)))) \/ ((((v_A0 : ('a set)) = {}) \/ ((v_B0 : ('b set)) = {})) /\ (((v_C0 : ('a set)) = {}) \/ ((v_D0 : ('b set)) = {})))))``,
   entry "product_type_L1162_fst_image_times" 1162 "by force" benchLib.Force false []
     ``((IMAGE FST (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair)))) = (if ((v_B0 : ('b set)) = {}) then {} else (v_A0 : ('a set))))``,
   entry "product_type_L1165_snd_image_times" 1165 "by force" benchLib.Force false []
     ``((IMAGE SND (\b_sigma_pair : ('b # 'a). FST b_sigma_pair IN (v_A0 : ('b set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'b. (v_B0 : ('a set))) (FST b_sigma_pair)))) = (if ((v_A0 : ('b set)) = {}) then {} else (v_B0 : ('a set))))``,
   entry "product_type_L1168_fst_image_Sigma" 1168 "by force" benchLib.Force false []
     ``((IMAGE FST (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_B0 : ('a -> ('b set))) (FST b_sigma_pair)))) = (\b_x : 'a. ((b_x IN (v_A0 : ('a set))) /\ (~(((v_B0 : ('a -> ('b set))) b_x) = {})))))``,
   entry "product_type_L1171_snd_image_Sigma" 1171 "by force" benchLib.Force false []
     ``((IMAGE SND (\b_sigma_pair : ('b # 'a). FST b_sigma_pair IN (v_A0 : ('b set)) /\ SND b_sigma_pair IN ((v_B0 : ('b -> ('a set))) (FST b_sigma_pair)))) = (BIGUNION (IMAGE (\b_x : 'b. ((v_B0 : ('b -> ('a set))) b_x)) (v_A0 : ('b set)))))``,
   entry "product_type_L1174_vimage_fst" 1174 "by auto" benchLib.Auto false []
     ``((PREIMAGE FST (v_A0 : ('a set))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. UNIV) (FST b_sigma_pair))))``,
   entry "product_type_L1177_vimage_snd" 1177 "by auto" benchLib.Auto false []
     ``((PREIMAGE SND (v_A0 : ('b set))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN UNIV /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_A0 : ('b set))) (FST b_sigma_pair))))``,
   entry "product_type_L1180_insert_Times_insert" 1180 "by blast" benchLib.Blast false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN ((v_a0 : 'a) INSERT (v_A0 : ('a set))) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. ((v_b0 : 'b) INSERT (v_B0 : ('b set)))) (FST b_sigma_pair))) = (((v_a0 : 'a),(v_b0 : 'b)) INSERT ((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. ((v_b0 : 'b) INSERT (v_B0 : ('b set)))) (FST b_sigma_pair))) UNION (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN ((v_a0 : 'a) INSERT {}) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair))))))``,
   entry "product_type_L1184_sing_Times_sing" 1184 "by simp" benchLib.Simp false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN ((v_x0 : 'a) INSERT {}) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. ((v_y0 : 'b) INSERT {})) (FST b_sigma_pair))) = (((v_x0 : 'a),(v_y0 : 'b)) INSERT {}))``,
   entry "product_type_L1193_Times_Int_Times" 1193 "by auto" benchLib.Auto false []
     ``(((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair))) INTER (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_C0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_D0 : ('b set))) (FST b_sigma_pair)))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN ((v_A0 : ('a set)) INTER (v_C0 : ('a set))) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. ((v_B0 : ('b set)) INTER (v_D0 : ('b set)))) (FST b_sigma_pair))))``,
   entry "product_type_L1196_image_paired_Times" 1196 "by auto" benchLib.Auto false []
     ``((IMAGE (UNCURRY (\b_x : 'c. (\b_y : 'd. (((v_f0 : ('c -> 'a)) b_x),((v_g0 : ('d -> 'b)) b_y))))) (\b_sigma_pair : ('c # 'd). FST b_sigma_pair IN (v_A0 : ('c set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'c. (v_B0 : ('d set))) (FST b_sigma_pair)))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (IMAGE (v_f0 : ('c -> 'a)) (v_A0 : ('c set))) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (IMAGE (v_g0 : ('d -> 'b)) (v_B0 : ('d set)))) (FST b_sigma_pair))))``,
   entry "product_type_L1200_Times_insert_right" 1200 "by auto" benchLib.Auto false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. ((v_y0 : 'b) INSERT (v_B0 : ('b set)))) (FST b_sigma_pair))) = ((IMAGE (\b_x : 'a. (b_x,(v_y0 : 'b))) (v_A0 : ('a set))) UNION (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair)))))``,
   entry "product_type_L1203_Times_insert_left" 1203 "by auto" benchLib.Auto false []
     ``((\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN ((v_x0 : 'a) INSERT (v_A0 : ('a set))) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair))) = ((IMAGE (\b_y : 'b. ((v_x0 : 'a),b_y)) (v_B0 : ('b set))) UNION (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair)))))``,
   entry "product_type_L1206_product_swap" 1206 "by (auto simp add: set_eq_iff)" benchLib.Auto false []
     ``((IMAGE (\b_swap_pair : ('b # 'a). (SND b_swap_pair,FST b_swap_pair)) (\b_sigma_pair : ('b # 'a). FST b_sigma_pair IN (v_A0 : ('b set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'b. (v_B0 : ('a set))) (FST b_sigma_pair)))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_B0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_A0 : ('b set))) (FST b_sigma_pair))))``,
   entry "product_type_L1209_swap_product" 1209 "by (auto simp add: set_eq_iff)" benchLib.Auto false []
     ``((IMAGE (UNCURRY (\b_i : 'b. (\b_j : 'a. (b_j,b_i)))) (\b_sigma_pair : ('b # 'a). FST b_sigma_pair IN (v_A0 : ('b set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'b. (v_B0 : ('a set))) (FST b_sigma_pair)))) = (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_B0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_A0 : ('b set))) (FST b_sigma_pair))))``,
   entry "product_type_L1220_subset_fst_snd" 1220 "by force" benchLib.Force false []
     ``((v_A0 : (('a # 'b) set)) SUBSET (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (IMAGE FST (v_A0 : (('a # 'b) set))) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (IMAGE SND (v_A0 : (('a # 'b) set)))) (FST b_sigma_pair))))``,
   entry "product_type_L1223_inj_on_apfst" 1223 "by (auto simp add: inj_on_def)" benchLib.Auto false []
     ``((((\b_inj_func : (('a # 'b) -> ('c # 'b)). \b_inj_set : (('a # 'b) set). INJ b_inj_func b_inj_set UNIV) ((\b_apfst_func : ('a -> 'c). \b_apfst_pair : ('a # 'b). (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) (v_f0 : ('a -> 'c)))) (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. UNIV) (FST b_sigma_pair)))) = (((\b_inj_func : ('a -> 'c). \b_inj_set : ('a set). INJ b_inj_func b_inj_set UNIV) (v_f0 : ('a -> 'c))) (v_A0 : ('a set))))``,
   entry "product_type_L1226_inj_apfst" 1226 "by simp" benchLib.Simp false []
     ``((((\b_inj_func : (('a # 'b) -> ('c # 'b)). \b_inj_set : (('a # 'b) set). INJ b_inj_func b_inj_set UNIV) ((\b_apfst_func : ('a -> 'c). \b_apfst_pair : ('a # 'b). (b_apfst_func (FST b_apfst_pair),SND b_apfst_pair)) (v_f0 : ('a -> 'c)))) UNIV) = (((\b_inj_func : ('a -> 'c). \b_inj_set : ('a set). INJ b_inj_func b_inj_set UNIV) (v_f0 : ('a -> 'c))) UNIV))``,
   entry "product_type_L1229_inj_on_apsnd" 1229 "by (auto simp add: inj_on_def)" benchLib.Auto false []
     ``((((\b_inj_func : (('a # 'b) -> ('a # 'c)). \b_inj_set : (('a # 'b) set). INJ b_inj_func b_inj_set UNIV) ((\b_apsnd_func : ('b -> 'c). \b_apsnd_pair : ('a # 'b). (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) (v_f0 : ('b -> 'c)))) (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN UNIV /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_A0 : ('b set))) (FST b_sigma_pair)))) = (((\b_inj_func : ('b -> 'c). \b_inj_set : ('b set). INJ b_inj_func b_inj_set UNIV) (v_f0 : ('b -> 'c))) (v_A0 : ('b set))))``,
   entry "product_type_L1232_inj_apsnd" 1232 "by simp" benchLib.Simp false []
     ``((((\b_inj_func : (('a # 'b) -> ('a # 'c)). \b_inj_set : (('a # 'b) set). INJ b_inj_func b_inj_set UNIV) ((\b_apsnd_func : ('b -> 'c). \b_apsnd_pair : ('a # 'b). (FST b_apsnd_pair,b_apsnd_func (SND b_apsnd_pair))) (v_f0 : ('b -> 'c)))) UNIV) = (((\b_inj_func : ('b -> 'c). \b_inj_set : ('b set). INJ b_inj_func b_inj_set UNIV) (v_f0 : ('b -> 'c))) UNIV))``,
   entry "product_type_L1241_member_product" 1241 "by (simp add: product_def)" benchLib.Simp false []
     ``(((v_x0 : ('a # 'b)) IN (((\b_product_left : ('a set). \b_product_right : ('b set). \b_product_pair : ('a # 'b). FST b_product_pair IN b_product_left /\ SND b_product_pair IN b_product_right) (v_A0 : ('a set))) (v_B0 : ('b set)))) = ((v_x0 : ('a # 'b)) IN (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair)))))``,
   entry "product_type_L1329_bij_betw_map_prod" 1329 "by auto" benchLib.Auto false []
     ``((((BIJ (v_f0 : ('a -> 'b))) (v_A0 : ('a set))) (v_C0 : ('b set))) ==> ((((BIJ (v_g0 : ('c -> 'd))) (v_B0 : ('c set))) (v_D0 : ('d set))) ==> (((BIJ (((\b_map_left : ('a -> 'b). \b_map_right : ('c -> 'd). \b_map_pair : ('a # 'c). (b_map_left (FST b_map_pair),b_map_right (SND b_map_pair))) (v_f0 : ('a -> 'b))) (v_g0 : ('c -> 'd)))) (\b_sigma_pair : ('a # 'c). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('c set))) (FST b_sigma_pair)))) (\b_sigma_pair : ('b # 'd). FST b_sigma_pair IN (v_C0 : ('b set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'b. (v_D0 : ('d set))) (FST b_sigma_pair))))))``,
   entry "product_type_L1364_disjnt_Times1_iff" 1364 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``((DISJOINT (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_C0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_A0 : ('b set))) (FST b_sigma_pair))) (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_C0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_B0 : ('b set))) (FST b_sigma_pair)))) = (((v_C0 : ('a set)) = {}) \/ (DISJOINT (v_A0 : ('b set)) (v_B0 : ('b set)))))``,
   entry "product_type_L1367_disjnt_Times2_iff" 1367 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``((DISJOINT (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_C0 : ('b set))) (FST b_sigma_pair))) (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_B0 : ('a set)) /\ SND b_sigma_pair IN ((\b_uu_ : 'a. (v_C0 : ('b set))) (FST b_sigma_pair)))) = (((v_C0 : ('b set)) = {}) \/ (DISJOINT (v_A0 : ('a set)) (v_B0 : ('a set)))))``,
   entry "product_type_L1370_disjnt_Sigma_iff" 1370 "by (auto simp: disjnt_def)" benchLib.Auto false []
     ``((DISJOINT (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_A0 : ('a set)) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair))) (\b_sigma_pair : ('a # 'b). FST b_sigma_pair IN (v_B0 : ('a set)) /\ SND b_sigma_pair IN ((v_C0 : ('a -> ('b set))) (FST b_sigma_pair)))) = ((!b_i : 'a. (b_i IN ((v_A0 : ('a set)) INTER (v_B0 : ('a set)))) ==> (((v_C0 : ('a -> ('b set))) b_i) = {})) \/ (DISJOINT (v_A0 : ('a set)) (v_B0 : ('a set)))))``
  ]

end
