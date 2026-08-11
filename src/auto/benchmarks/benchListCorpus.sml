structure benchListCorpus =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun entry id line method mapped representative excl goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method, mapped = mapped,
   excl = List.filter (fn {theorem, ...} =>
     benchLib.theorem_is_goal goal theorem) excl, provenance =
     {file = "src/HOL/List.thy", line = line, commit = commit},
   representative = representative}

val goals =
  [
   entry "list_L849_inj_split_Cons" 849 "by (auto intro!: inj_onI)" benchLib.Auto false []
     ``(((\b_inj_func : ((('a list) # 'a) -> ('a list)). \b_inj_set : ((('a list) # 'a) set). INJ b_inj_func b_inj_set UNIV) (UNCURRY (\b_xs : ('a list). (\b_n : 'a. ((CONS b_n) b_xs))))) (v_X0 : ((('a list) # 'a) set)))``,
   entry "list_L852_inj_on_Cons1" 852 "by(simp add: inj_on_def)" benchLib.Simp false []
     ``(((\b_inj_func : (('a list) -> ('a list)). \b_inj_set : (('a list) set). INJ b_inj_func b_inj_set UNIV) (CONS (v_x0 : 'a))) (v_A0 : (('a list) set)))``,
   entry "list_L880_length_pos_if_in_set" 880 "by auto" benchLib.Auto false []
     ``(((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> (0 < (LENGTH (v_xs0 : ('a list)))))``,
   entry "list_L981_same_append_eq" 981 "by simp" benchLib.Simp false []
     ``((((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list))) = ((APPEND (v_xs0 : ('a list))) (v_zs0 : ('a list)))) = ((v_ys0 : ('a list)) = (v_zs0 : ('a list))))``,
   entry "list_L984_append1_eq_conv" 984 "by simp" benchLib.Simp false []
     ``((((APPEND (v_xs0 : ('a list))) ((CONS (v_x0 : 'a)) [])) = ((APPEND (v_ys0 : ('a list))) ((CONS (v_y0 : 'a)) []))) = (((v_xs0 : ('a list)) = (v_ys0 : ('a list))) /\ ((v_x0 : 'a) = (v_y0 : 'a))))``,
   entry "list_L987_append_same_eq" 987 "by simp" benchLib.Simp false []
     ``((((APPEND (v_ys0 : ('a list))) (v_xs0 : ('a list))) = ((APPEND (v_zs0 : ('a list))) (v_xs0 : ('a list)))) = ((v_ys0 : ('a list)) = (v_zs0 : ('a list))))``,
   entry "list_L990_append_self_conv2" 990 "by auto" benchLib.Auto false []
     ``((((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list))) = (v_ys0 : ('a list))) = ((v_xs0 : ('a list)) = []))``,
   entry "list_L1001_hd_append2" 1001 "by (simp add: hd_append split: list.split)" benchLib.Simp false []
     ``((~((v_xs0 : ('a list)) = [])) ==> ((HD ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = (HD (v_xs0 : ('a list)))))``,
   entry "list_L1004_tl_append" 1004 "by (simp split: list.split)" benchLib.Simp false []
     ``((TL ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = ((((\b_list_nil : ('a list). \b_list_cons : ('a -> (('a list) -> ('a list))). \b_list_value : ('a list). list_CASE b_list_value b_list_nil b_list_cons) (TL (v_ys0 : ('a list)))) (\b_z : 'a. (\b_zs : ('a list). ((APPEND b_zs) (v_ys0 : ('a list)))))) (v_xs0 : ('a list))))``,
   entry "list_L1007_tl_append2" 1007 "by (simp add: tl_append split: list.split)" benchLib.Simp false []
     ``((~((v_xs0 : ('a list)) = [])) ==> ((TL ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = ((APPEND (TL (v_xs0 : ('a list)))) (v_ys0 : ('a list)))))``,
   entry "list_L1010_tl_append_if" 1010 "by (simp)" benchLib.Simp false []
     ``((TL ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = (if ((v_xs0 : ('a list)) = []) then (TL (v_ys0 : ('a list))) else ((APPEND (TL (v_xs0 : ('a list)))) (v_ys0 : ('a list)))))``,
   entry "list_L1030_eq_Nil_appendI" 1030 "by simp" benchLib.Simp false []
     ``(((v_xs0 : ('a list)) = (v_ys0 : ('a list))) ==> ((v_xs0 : ('a list)) = ((APPEND []) (v_ys0 : ('a list)))))``,
   entry "list_L1033_Cons_eq_appendI" 1033 "by auto" benchLib.Auto false []
     ``((((CONS (v_x0 : 'a)) (v_xs10 : ('a list))) = (v_ys0 : ('a list))) ==> (((v_xs0 : ('a list)) = ((APPEND (v_xs10 : ('a list))) (v_zs0 : ('a list)))) ==> (((CONS (v_x0 : 'a)) (v_xs0 : ('a list))) = ((APPEND (v_ys0 : ('a list))) (v_zs0 : ('a list))))))``,
   entry "list_L1036_append_eq_appendI" 1036 "by auto" benchLib.Auto false []
     ``((((APPEND (v_xs0 : ('a list))) (v_xs10 : ('a list))) = (v_zs0 : ('a list))) ==> (((v_ys0 : ('a list)) = ((APPEND (v_xs10 : ('a list))) (v_us0 : ('a list)))) ==> (((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list))) = ((APPEND (v_zs0 : ('a list))) (v_us0 : ('a list))))))``,
   entry "list_L1119_map_cong" 1119 "by simp" benchLib.Simp false [{name = "list$MAP_CONG", theorem = listTheory.MAP_CONG}]
     ``(((v_xs0 : ('a list)) = (v_ys0 : ('a list))) ==> ((!b_x : 'a. ((b_x IN (LIST_TO_SET (v_ys0 : ('a list)))) ==> (((v_f0 : ('a -> 'b)) b_x) = ((v_g0 : ('a -> 'b)) b_x)))) ==> (((MAP (v_f0 : ('a -> 'b))) (v_xs0 : ('a list))) = ((MAP (v_g0 : ('a -> 'b))) (v_ys0 : ('a list))))))``,
   entry "list_L1193_inj_on_map_eq_map" 1193 "by(blast dest:map_inj_on)" benchLib.Blast false []
     ``((((\b_inj_func : ('a -> 'b). \b_inj_set : ('a set). INJ b_inj_func b_inj_set UNIV) (v_f0 : ('a -> 'b))) ((LIST_TO_SET (v_xs0 : ('a list))) UNION (LIST_TO_SET (v_ys0 : ('a list))))) ==> ((((MAP (v_f0 : ('a -> 'b))) (v_xs0 : ('a list))) = ((MAP (v_f0 : ('a -> 'b))) (v_ys0 : ('a list)))) = ((v_xs0 : ('a list)) = (v_ys0 : ('a list)))))``,
   entry "list_L1201_inj_map_eq_map" 1201 "by(blast dest:map_injective)" benchLib.Blast false []
     ``((((\b_inj_func : ('a -> 'b). \b_inj_set : ('a set). INJ b_inj_func b_inj_set UNIV) (v_f0 : ('a -> 'b))) UNIV) ==> ((((MAP (v_f0 : ('a -> 'b))) (v_xs0 : ('a list))) = ((MAP (v_f0 : ('a -> 'b))) (v_ys0 : ('a list)))) = ((v_xs0 : ('a list)) = (v_ys0 : ('a list)))))``,
   entry "list_L1210_inj_map" 1210 "by (blast dest: inj_mapD intro: inj_mapI)" benchLib.Blast false []
     ``((((\b_inj_func : (('a list) -> ('b list)). \b_inj_set : (('a list) set). INJ b_inj_func b_inj_set UNIV) (MAP (v_f0 : ('a -> 'b)))) UNIV) = (((\b_inj_func : ('a -> 'b). \b_inj_set : ('a set). INJ b_inj_func b_inj_set UNIV) (v_f0 : ('a -> 'b))) UNIV))``,
   entry "list_L1213_inj_on_mapI" 1213 "by (blast intro:inj_onI dest:inj_onD map_inj_on)" benchLib.Blast false []
     ``((((\b_inj_func : ('a -> 'b). \b_inj_set : ('a set). INJ b_inj_func b_inj_set UNIV) (v_f0 : ('a -> 'b))) (BIGUNION (IMAGE LIST_TO_SET (v_A0 : (('a list) set))))) ==> (((\b_inj_func : (('a list) -> ('b list)). \b_inj_set : (('a list) set). INJ b_inj_func b_inj_set UNIV) (MAP (v_f0 : ('a -> 'b)))) (v_A0 : (('a list) set))))``,
   entry "list_L1255_rev_involution" 1255 "by auto" benchLib.Auto false []
     ``(((combin$o REVERSE) REVERSE) = I)``,
   entry "list_L1258_rev_swap" 1258 "by auto" benchLib.Auto false []
     ``(((REVERSE (v_xs0 : ('a list))) = (v_ys0 : ('a list))) = ((v_xs0 : ('a list)) = (REVERSE (v_ys0 : ('a list)))))``,
   entry "list_L1287_rev_eq_Cons_iff" 1287 "by (simp add: rev_swap)" benchLib.Simp false []
     ``(((REVERSE (v_xs0 : ('a list))) = ((CONS (v_y0 : 'a)) (v_ys0 : ('a list)))) = ((v_xs0 : ('a list)) = ((APPEND (REVERSE (v_ys0 : ('a list)))) ((CONS (v_y0 : 'a)) []))))``,
   entry "list_L1292_inj_on_rev" 1292 "by(simp add:inj_on_def)" benchLib.Simp false []
     ``(((\b_inj_func : (('a list) -> ('a list)). \b_inj_set : (('a list) set). INJ b_inj_func b_inj_set UNIV) REVERSE) (v_A0 : (('a list) set)))``,
   entry "list_L1356_set_subset_Cons" 1356 "by auto" benchLib.Auto false []
     ``((LIST_TO_SET (v_xs0 : ('a list))) SUBSET (LIST_TO_SET ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))))``,
   entry "list_L1359_set_ConsD" 1359 "by auto" benchLib.Auto false []
     ``(((v_y0 : 'a) IN (LIST_TO_SET ((CONS (v_x0 : 'a)) (v_xs0 : ('a list))))) ==> (((v_y0 : 'a) = (v_x0 : 'a)) \/ ((v_y0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list))))))``,
   entry "list_L1367_append_eq_append_conv_if_disj" 1367 "by (auto simp: all_conj_distrib disjoint_iff append_eq_append_conv2)" benchLib.Auto false []
     ``(((((LIST_TO_SET (v_xs0 : ('a list))) UNION (LIST_TO_SET (v_xs_0 : ('a list)))) INTER ((LIST_TO_SET (v_ys0 : ('a list))) UNION (LIST_TO_SET (v_ys_0 : ('a list))))) = {}) ==> ((((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list))) = ((APPEND (v_xs_0 : ('a list))) (v_ys_0 : ('a list)))) = (((v_xs0 : ('a list)) = (v_xs_0 : ('a list))) /\ ((v_ys0 : ('a list)) = (v_ys_0 : ('a list))))))``,
   entry "list_L1384_atMost_upto" 1384 "by auto" benchLib.Auto false []
     ``(((\b_at_most : num. \b_at_most_item : num. b_at_most_item <= b_at_most) (v_n0 : num)) = (LIST_TO_SET (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) 0) (SUC (v_n0 : num)))))``,
   entry "list_L1388_atLeast_upt" 1388 "by auto" benchLib.Auto false []
     ``(((\b_less_than : num. \b_less_item : num. b_less_item < b_less_than) (v_n0 : num)) = (LIST_TO_SET (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) 0) (v_n0 : num))))``,
   entry "list_L1392_greaterThanLessThan_upt" 1392 "by auto" benchLib.Auto false []
     ``((((\b_open_left : num. \b_open_right : num. \b_open_item : num. b_open_left < b_open_item /\ b_open_item < b_open_right) (v_n0 : num)) (v_m0 : num)) = (LIST_TO_SET (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (SUC (v_n0 : num))) (v_m0 : num))))``,
   entry "list_L1396_atLeastLessThan_upt" 1396 "by auto" benchLib.Auto false []
     ``((((\b_interval_left : num. \b_interval_right : num. \b_interval_item : num. b_interval_left <= b_interval_item /\ b_interval_item < b_interval_right) (v_i0 : num)) (v_j0 : num)) = (LIST_TO_SET (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (v_i0 : num)) (v_j0 : num))))``,
   entry "list_L1400_greaterThanAtMost_upt" 1400 "by auto" benchLib.Auto false []
     ``((((\b_interval_left : num. \b_interval_right : num. \b_interval_item : num. b_interval_left < b_interval_item /\ b_interval_item <= b_interval_right) (v_n0 : num)) (v_m0 : num)) = (LIST_TO_SET (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (SUC (v_n0 : num))) (SUC (v_m0 : num)))))``,
   entry "list_L1404_atLeastAtMost_upt" 1404 "by auto" benchLib.Auto false []
     ``((((\b_closed_left : num. \b_closed_right : num. \b_closed_item : num. b_closed_left <= b_closed_item /\ b_closed_item <= b_closed_right) (v_n0 : num)) (v_m0 : num)) = (LIST_TO_SET (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (v_n0 : num)) (SUC (v_m0 : num)))))``,
   entry "list_L1415_in_set_conv_decomp" 1415 "by (auto elim: split_list)" benchLib.Auto false []
     ``(((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) = (?b_ys : ('a list). (?b_zs : ('a list). ((v_xs0 : ('a list)) = ((APPEND b_ys) ((CONS (v_x0 : 'a)) b_zs))))))``,
   entry "list_L1431_in_set_conv_decomp_first" 1431 "by (auto dest!: split_list_first)" benchLib.Auto false []
     ``(((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) = (?b_ys : ('a list). (?b_zs : ('a list). (((v_xs0 : ('a list)) = ((APPEND b_ys) ((CONS (v_x0 : 'a)) b_zs))) /\ (~((v_x0 : 'a) IN (LIST_TO_SET b_ys)))))))``,
   entry "list_L1448_in_set_conv_decomp_last" 1448 "by (auto dest!: split_list_last)" benchLib.Auto false []
     ``(((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) = (?b_ys : ('a list). (?b_zs : ('a list). (((v_xs0 : ('a list)) = ((APPEND b_ys) ((CONS (v_x0 : 'a)) b_zs))) /\ (~((v_x0 : 'a) IN (LIST_TO_SET b_zs)))))))``,
   entry "list_L1460_split_list_propE" 1460 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) /\ ((v_P0 : ('a -> bool)) b_x)) ==> ((!b_ys : ('a list). (!b_x : 'a. (!b_zs : ('a list). (((v_xs0 : ('a list)) = ((APPEND b_ys) ((CONS b_x) b_zs))) ==> (((v_P0 : ('a -> bool)) b_x) ==> (v_thesis0 : bool)))))) ==> (v_thesis0 : bool)))``,
   entry "list_L1484_split_list_first_propE" 1484 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) /\ ((v_P0 : ('a -> bool)) b_x)) ==> ((!b_ys : ('a list). (!b_x : 'a. (!b_zs : ('a list). (((v_xs0 : ('a list)) = ((APPEND b_ys) ((CONS b_x) b_zs))) ==> (((v_P0 : ('a -> bool)) b_x) ==> ((!b_y : 'a. (b_y IN (LIST_TO_SET b_ys)) ==> (~((v_P0 : ('a -> bool)) b_y))) ==> (v_thesis0 : bool))))))) ==> (v_thesis0 : bool)))``,
   entry "list_L1511_split_list_last_propE" 1511 "by blast" benchLib.Blast false []
     ``((?b_x : 'a. (b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) /\ ((v_P0 : ('a -> bool)) b_x)) ==> ((!b_ys : ('a list). (!b_x : 'a. (!b_zs : ('a list). (((v_xs0 : ('a list)) = ((APPEND b_ys) ((CONS b_x) b_zs))) ==> (((v_P0 : ('a -> bool)) b_x) ==> ((!b_z : 'a. (b_z IN (LIST_TO_SET b_zs)) ==> (~((v_P0 : ('a -> bool)) b_z))) ==> (v_thesis0 : bool))))))) ==> (v_thesis0 : bool)))``,
   entry "list_L1532_append_Cons_eq_iff" 1532 "by(auto simp: append_eq_Cons_conv Cons_eq_append_conv append_eq_append_conv2)" benchLib.Auto false []
     ``((~((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list))))) ==> ((~((v_x0 : 'a) IN (LIST_TO_SET (v_ys0 : ('a list))))) ==> ((((APPEND (v_xs0 : ('a list))) ((CONS (v_x0 : 'a)) (v_ys0 : ('a list)))) = ((APPEND (v_xs_0 : ('a list))) ((CONS (v_x0 : 'a)) (v_ys_0 : ('a list))))) = (((v_xs0 : ('a list)) = (v_xs_0 : ('a list))) /\ ((v_ys0 : ('a list)) = (v_ys_0 : ('a list)))))))``,
   entry "list_L1569_concat_injective" 1569 "by (simp add: concat_eq_concat_iff)" benchLib.Simp false []
     ``(((FLAT (v_xs0 : (('a list) list))) = (FLAT (v_ys0 : (('a list) list)))) ==> (((LENGTH (v_xs0 : (('a list) list))) = (LENGTH (v_ys0 : (('a list) list)))) ==> ((!b_set : (('a list) # ('a list)). (b_set IN (LIST_TO_SET (ZIP ((v_xs0 : (('a list) list)),(v_ys0 : (('a list) list)))))) ==> ((UNCURRY (\b_x : ('a list). (\b_y : ('a list). ((LENGTH b_x) = (LENGTH b_y))))) b_set)) ==> ((v_xs0 : (('a list) list)) = (v_ys0 : (('a list) list))))))``,
   entry "list_L1590_concat_eq_append_conv" 1590 "by(auto dest: concat_eq_appendD)" benchLib.Auto false []
     ``(((FLAT (v_xss0 : (('a list) list))) = ((APPEND (v_ys0 : ('a list))) (v_zs0 : ('a list)))) = (if ((v_xss0 : (('a list) list)) = []) then (((v_ys0 : ('a list)) = []) /\ ((v_zs0 : ('a list)) = [])) else (?b_xss1 : (('a list) list). (?b_xs : ('a list). (?b_xs_ : ('a list). (?b_xss2 : (('a list) list). (((v_xss0 : (('a list) list)) = ((APPEND b_xss1) ((CONS ((APPEND b_xs) b_xs_)) b_xss2))) /\ (((v_ys0 : ('a list)) = ((APPEND (FLAT b_xss1)) b_xs)) /\ ((v_zs0 : ('a list)) = ((APPEND b_xs_) (FLAT b_xss2)))))))))))``,
   entry "list_L1706_length_filter_map" 1706 "by (simp add:filter_map)" benchLib.Simp false []
     ``((LENGTH ((FILTER (v_P0 : ('a -> bool))) ((MAP (v_f0 : ('b -> 'a))) (v_xs0 : ('b list))))) = (LENGTH ((FILTER ((combin$o (v_P0 : ('a -> bool))) (v_f0 : ('b -> 'a)))) (v_xs0 : ('b list)))))``,
   entry "list_L1710_filter_is_subset" 1710 "by auto" benchLib.Auto false []
     ``((LIST_TO_SET ((FILTER (v_P0 : ('a -> bool))) (v_xs0 : ('a list)))) SUBSET (LIST_TO_SET (v_xs0 : ('a list))))``,
   entry "list_L1789_filter_eq_Cons_iff" 1789 "by(auto dest:filter_eq_ConsD)" benchLib.Auto false []
     ``((((FILTER (v_P0 : ('a -> bool))) (v_ys0 : ('a list))) = ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) = (?b_us : ('a list). (?b_vs : ('a list). (((v_ys0 : ('a list)) = ((APPEND b_us) ((CONS (v_x0 : 'a)) b_vs))) /\ ((!b_u : 'a. (b_u IN (LIST_TO_SET b_us)) ==> (~((v_P0 : ('a -> bool)) b_u))) /\ (((v_P0 : ('a -> bool)) (v_x0 : 'a)) /\ ((v_xs0 : ('a list)) = ((FILTER (v_P0 : ('a -> bool))) b_vs))))))))``,
   entry "list_L1838_partition_filter_conv" 1838 "by simp" benchLib.Simp false []
     ``((((\b_partition_predicate : ('a -> bool). \b_partition_list : ('a list). (FILTER b_partition_predicate b_partition_list,FILTER (\b_partition_item. ~b_partition_predicate b_partition_item) b_partition_list)) (v_f0 : ('a -> bool))) (v_xs0 : ('a list))) = (((FILTER (v_f0 : ('a -> bool))) (v_xs0 : ('a list))),((FILTER ((combin$o (\b_not : bool. ~b_not)) (v_f0 : ('a -> bool)))) (v_xs0 : ('a list)))))``,
   entry "list_L1848_nth_Cons_0" 1848 "by auto" benchLib.Auto false []
     ``((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) 0) = (v_x0 : 'a))``,
   entry "list_L1851_nth_Cons_Suc" 1851 "by auto" benchLib.Auto false []
     ``((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) (SUC (v_n0 : num))) = (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_n0 : num)))``,
   entry "list_L1856_nth_Cons_pos" 1856 "by(auto simp: Nat.gr0_conv_Suc)" benchLib.Auto false []
     ``((0 < (v_n0 : num)) ==> ((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) (v_n0 : num)) = (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) ((v_n0 : num) - 1))))``,
   entry "list_L1867_nth_append_left" 1867 "by (auto simp: nth_append)" benchLib.Auto false []
     ``(((v_i0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> ((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) (v_i0 : num)) = (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_i0 : num))))``,
   entry "list_L1870_nth_append_right" 1870 "by (auto simp: nth_append)" benchLib.Auto false []
     ``(((LENGTH (v_xs0 : ('a list))) <= (v_i0 : num)) ==> ((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) (v_i0 : num)) = (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_ys0 : ('a list))) ((v_i0 : num) - (LENGTH (v_xs0 : ('a list)))))))``,
   entry "list_L1903_map_equality_iff" 1903 "by (fastforce simp: list_eq_iff_nth_eq)" benchLib.Fastforce false []
     ``((((MAP (v_f0 : ('b -> 'a))) (v_xs0 : ('b list))) = ((MAP (v_g0 : ('c -> 'a))) (v_ys0 : ('c list)))) = (((LENGTH (v_xs0 : ('b list))) = (LENGTH (v_ys0 : ('c list)))) /\ (!b_i : num. ((b_i < (LENGTH (v_ys0 : ('c list)))) ==> (((v_f0 : ('b -> 'a)) (((\b_nth_list : ('b list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('b list))) b_i)) = ((v_g0 : ('c -> 'a)) (((\b_nth_list : ('c list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_ys0 : ('c list))) b_i)))))))``,
   entry "list_L1921_in_set_conv_nth" 1921 "by(auto simp:set_conv_nth)" benchLib.Auto false []
     ``(((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) = (?b_i : num. ((b_i < (LENGTH (v_xs0 : ('a list)))) /\ ((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) b_i) = (v_x0 : 'a)))))``,
   entry "list_L1953_list_ball_nth" 1953 "by (auto simp add: set_conv_nth)" benchLib.Auto false []
     ``(((v_n0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> ((!b_x : 'a. (b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) b_x)) ==> ((v_P0 : ('a -> bool)) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_n0 : num)))))``,
   entry "list_L1956_nth_mem" 1956 "by (auto simp add: set_conv_nth)" benchLib.Auto false []
     ``(((v_n0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> ((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_n0 : num)) IN (LIST_TO_SET (v_xs0 : ('a list)))))``,
   entry "list_L1959_all_nth_imp_all_set" 1959 "by (auto simp add: set_conv_nth)" benchLib.Auto false []
     ``((!b_i : num. ((b_i < (LENGTH (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) b_i)))) ==> (((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) (v_x0 : 'a))))``,
   entry "list_L1963_all_set_conv_all_nth" 1963 "by (auto simp add: set_conv_nth)" benchLib.Auto false []
     ``((!b_x : 'a. (b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) b_x)) = (!b_i : num. ((b_i < (LENGTH (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) b_i)))))``,
   entry "list_L2015_nth_list_update_eq" 2015 "by (simp add: nth_list_update)" benchLib.Simp false []
     ``(((v_i0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> ((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) ((((\b_update_list : ('a list). \b_update_index : num. \b_update_item : 'a. LUPDATE b_update_item b_update_index b_update_list) (v_xs0 : ('a list))) (v_i0 : num)) (v_x0 : 'a))) (v_i0 : num)) = (v_x0 : 'a)))``,
   entry "list_L2065_set_update_subsetI" 2065 "by (blast dest!: set_update_subset_insert [THEN subsetD])" benchLib.Blast false []
     ``(((LIST_TO_SET (v_xs0 : ('a list))) SUBSET (v_A0 : ('a set))) ==> (((v_x0 : 'a) IN (v_A0 : ('a set))) ==> ((LIST_TO_SET ((((\b_update_list : ('a list). \b_update_index : num. \b_update_item : 'a. LUPDATE b_update_item b_update_index b_update_list) (v_xs0 : ('a list))) (v_i0 : num)) (v_x0 : 'a))) SUBSET (v_A0 : ('a set)))))``,
   entry "list_L2088_hd_Nil_eq_last" 2088 "by simp" benchLib.Simp false []
     ``((HD []) = (LAST []))``,
   entry "list_L2097_last_ConsL" 2097 "by simp" benchLib.Simp false []
     ``(((v_xs0 : ('a list)) = []) ==> ((LAST ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) = (v_x0 : 'a)))``,
   entry "list_L2100_last_ConsR" 2100 "by simp" benchLib.Simp false []
     ``((~((v_xs0 : ('a list)) = [])) ==> ((LAST ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) = (LAST (v_xs0 : ('a list)))))``,
   entry "list_L2106_last_appendL" 2106 "by(simp add:last_append)" benchLib.Simp false []
     ``(((v_ys0 : ('a list)) = []) ==> ((LAST ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = (LAST (v_xs0 : ('a list)))))``,
   entry "list_L2109_last_appendR" 2109 "by(simp add:last_append)" benchLib.Simp false []
     ``((~((v_ys0 : ('a list)) = [])) ==> ((LAST ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = (LAST (v_ys0 : ('a list)))))``,
   entry "list_L2141_in_set_butlast_appendI" 2141 "by (auto dest: in_set_butlastD simp add: butlast_append)" benchLib.Auto false []
     ``((((v_x0 : 'a) IN (LIST_TO_SET (FRONT (v_xs0 : ('a list))))) \/ ((v_x0 : 'a) IN (LIST_TO_SET (FRONT (v_ys0 : ('a list)))))) ==> ((v_x0 : 'a) IN (LIST_TO_SET (FRONT ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))))))``,
   entry "list_L2163_last_list_update" 2163 "by (auto simp: last_conv_nth)" benchLib.Auto false []
     ``((~((v_xs0 : ('a list)) = [])) ==> ((LAST ((((\b_update_list : ('a list). \b_update_index : num. \b_update_item : 'a. LUPDATE b_update_item b_update_index b_update_list) (v_xs0 : ('a list))) (v_k0 : num)) (v_x0 : 'a))) = (if ((v_k0 : num) = ((LENGTH (v_xs0 : ('a list))) - 1)) then (v_x0 : 'a) else (LAST (v_xs0 : ('a list))))))``,
   entry "list_L2178_snoc_eq_iff_butlast" 2178 "by fastforce" benchLib.Fastforce false []
     ``((((APPEND (v_xs0 : ('a list))) ((CONS (v_x0 : 'a)) [])) = (v_ys0 : ('a list))) = ((~((v_ys0 : ('a list)) = [])) /\ (((FRONT (v_ys0 : ('a list))) = (v_xs0 : ('a list))) /\ ((LAST (v_ys0 : ('a list))) = (v_x0 : 'a)))))``,
   entry "list_L2206_take_Suc_Cons" 2206 "by simp" benchLib.Simp false []
     ``(((TAKE (SUC (v_n0 : num))) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) = ((CONS (v_x0 : 'a)) ((TAKE (v_n0 : num)) (v_xs0 : ('a list)))))``,
   entry "list_L2209_drop_Suc_Cons" 2209 "by simp" benchLib.Simp false []
     ``(((DROP (SUC (v_n0 : num))) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) = ((DROP (v_n0 : num)) (v_xs0 : ('a list))))``,
   entry "list_L2214_take_Suc" 2214 "by(clarsimp simp add:neq_Nil_conv)" benchLib.Clarsimp false [{name = "rich_list$TAKE_SUC", theorem = rich_listTheory.TAKE_SUC}]
     ``((~((v_xs0 : ('a list)) = [])) ==> (((TAKE (SUC (v_n0 : num))) (v_xs0 : ('a list))) = ((CONS (HD (v_xs0 : ('a list)))) ((TAKE (v_n0 : num)) (TL (v_xs0 : ('a list)))))))``,
   entry "list_L2396_butlast_take" 2396 "by (simp add: butlast_conv_take)" benchLib.Simp false []
     ``(((v_n0 : num) <= (LENGTH (v_xs0 : ('a list)))) ==> ((FRONT ((TAKE (v_n0 : num)) (v_xs0 : ('a list)))) = ((TAKE ((v_n0 : num) - 1)) (v_xs0 : ('a list)))))``,
   entry "list_L2400_butlast_drop" 2400 "by (simp add: butlast_conv_take drop_take ac_simps)" benchLib.Simp false []
     ``((FRONT ((DROP (v_n0 : num)) (v_xs0 : ('a list)))) = ((DROP (v_n0 : num)) (FRONT (v_xs0 : ('a list)))))``,
   entry "list_L2403_take_butlast" 2403 "by (simp add: butlast_conv_take)" benchLib.Simp false []
     ``(((v_n0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> (((TAKE (v_n0 : num)) (FRONT (v_xs0 : ('a list)))) = ((TAKE (v_n0 : num)) (v_xs0 : ('a list)))))``,
   entry "list_L2406_drop_butlast" 2406 "by (simp add: butlast_conv_take drop_take ac_simps)" benchLib.Simp false []
     ``(((DROP (v_n0 : num)) (FRONT (v_xs0 : ('a list)))) = (FRONT ((DROP (v_n0 : num)) (v_xs0 : ('a list)))))``,
   entry "list_L2412_hd_drop_conv_nth" 2412 "by(simp add: hd_conv_nth)" benchLib.Simp false []
     ``(((v_n0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> ((HD ((DROP (v_n0 : num)) (v_xs0 : ('a list)))) = (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_n0 : num))))``,
   entry "list_L2480_take_update_cancel" 2480 "by(simp add: list_eq_iff_nth_eq)" benchLib.Simp false []
     ``(((v_n0 : num) <= (v_m0 : num)) ==> (((TAKE (v_n0 : num)) ((((\b_update_list : ('a list). \b_update_index : num. \b_update_item : 'a. LUPDATE b_update_item b_update_index b_update_list) (v_xs0 : ('a list))) (v_m0 : num)) (v_y0 : 'a))) = ((TAKE (v_n0 : num)) (v_xs0 : ('a list)))))``,
   entry "list_L2483_drop_update_cancel" 2483 "by(simp add: list_eq_iff_nth_eq)" benchLib.Simp false []
     ``(((v_n0 : num) < (v_m0 : num)) ==> (((DROP (v_m0 : num)) ((((\b_update_list : ('a list). \b_update_index : num. \b_update_item : 'a. LUPDATE b_update_item b_update_index b_update_list) (v_xs0 : ('a list))) (v_n0 : num)) (v_x0 : 'a))) = ((DROP (v_m0 : num)) (v_xs0 : ('a list)))))``,
   entry "list_L2545_takeWhile_append" 2545 "by auto" benchLib.Auto false []
     ``(((takeWhile (v_P0 : ('a -> bool))) ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = (if (!b_x : 'a. (b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) b_x)) then ((APPEND (v_xs0 : ('a list))) ((takeWhile (v_P0 : ('a -> bool))) (v_ys0 : ('a list)))) else ((takeWhile (v_P0 : ('a -> bool))) (v_xs0 : ('a list)))))``,
   entry "list_L2576_dropWhile_id" 2576 "by fastforce" benchLib.Fastforce false [{name = "list$dropWhile_id", theorem = listTheory.dropWhile_id}]
     ``((!b_x : 'a. ((b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> (~((v_P0 : ('a -> bool)) b_x)))) ==> (((dropWhile (v_P0 : ('a -> bool))) (v_xs0 : ('a list))) = (v_xs0 : ('a list))))``,
   entry "list_L2585_dropWhile_append" 2585 "by auto" benchLib.Auto false []
     ``(((dropWhile (v_P0 : ('a -> bool))) ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = (if (!b_x : 'a. (b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) b_x)) then ((dropWhile (v_P0 : ('a -> bool))) (v_ys0 : ('a list))) else ((APPEND ((dropWhile (v_P0 : ('a -> bool))) (v_xs0 : ('a list)))) (v_ys0 : ('a list)))))``,
   entry "list_L2589_dropWhile_last" 2589 "by (auto simp add: dropWhile_append3 in_set_conv_decomp)" benchLib.Auto false []
     ``(((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> ((~((v_P0 : ('a -> bool)) (v_x0 : 'a))) ==> ((LAST ((dropWhile (v_P0 : ('a -> bool))) (v_xs0 : ('a list)))) = (LAST (v_xs0 : ('a list))))))``,
   entry "list_L2740_zip_Cons_Cons" 2740 "by simp" benchLib.Simp false []
     ``((ZIP (((CONS (v_x0 : 'a)) (v_xs0 : ('a list))),((CONS (v_y0 : 'b)) (v_ys0 : ('b list))))) = ((CONS ((v_x0 : 'a),(v_y0 : 'b))) (ZIP ((v_xs0 : ('a list)),(v_ys0 : ('b list))))))``,
   entry "list_L2751_zip_Cons1" 2751 "by(auto split:list.split)" benchLib.Auto false []
     ``((ZIP (((CONS (v_x0 : 'a)) (v_xs0 : ('a list))),(v_ys0 : ('b list)))) = ((((\b_list_nil : (('a # 'b) list). \b_list_cons : ('b -> (('b list) -> (('a # 'b) list))). \b_list_value : ('b list). list_CASE b_list_value b_list_nil b_list_cons) []) (\b_y : 'b. (\b_ys : ('b list). ((CONS ((v_x0 : 'a),b_y)) (ZIP ((v_xs0 : ('a list)),b_ys)))))) (v_ys0 : ('b list))))``,
   entry "list_L2786_zip_append" 2786 "by (simp add: zip_append1)" benchLib.Simp false [{name = "rich_list$ZIP_APPEND", theorem = rich_listTheory.ZIP_APPEND}]
     ``(((LENGTH (v_xs0 : ('a list))) = (LENGTH (v_us0 : ('b list)))) ==> ((ZIP (((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list))),((APPEND (v_us0 : ('b list))) (v_vs0 : ('b list))))) = ((APPEND (ZIP ((v_xs0 : ('a list)),(v_us0 : ('b list))))) (ZIP ((v_ys0 : ('a list)),(v_vs0 : ('b list)))))))``,
   entry "list_L2806_zip_map1" 2806 "by simp" benchLib.Simp false []
     ``((ZIP (((MAP (v_f0 : ('c -> 'a))) (v_xs0 : ('c list))),(v_ys0 : ('b list)))) = ((MAP (UNCURRY (\b_x : 'c. (\b_y : 'b. (((v_f0 : ('c -> 'a)) b_x),b_y))))) (ZIP ((v_xs0 : ('c list)),(v_ys0 : ('b list))))))``,
   entry "list_L2810_zip_map2" 2810 "by simp" benchLib.Simp false []
     ``((ZIP ((v_xs0 : ('a list)),((MAP (v_f0 : ('c -> 'b))) (v_ys0 : ('c list))))) = ((MAP (UNCURRY (\b_x : 'a. (\b_y : 'c. (b_x,((v_f0 : ('c -> 'b)) b_y)))))) (ZIP ((v_xs0 : ('a list)),(v_ys0 : ('c list))))))``,
   entry "list_L2814_map_zip_map" 2814 "by (auto simp: zip_map1)" benchLib.Auto false []
     ``(((MAP (v_f0 : (('b # 'c) -> 'a))) (ZIP (((MAP (v_g0 : ('d -> 'b))) (v_xs0 : ('d list))),(v_ys0 : ('c list))))) = ((MAP (UNCURRY (\b_x : 'd. (\b_y : 'c. ((v_f0 : (('b # 'c) -> 'a)) (((v_g0 : ('d -> 'b)) b_x),b_y)))))) (ZIP ((v_xs0 : ('d list)),(v_ys0 : ('c list))))))``,
   entry "list_L2818_map_zip_map2" 2818 "by (auto simp: zip_map2)" benchLib.Auto false []
     ``(((MAP (v_f0 : (('b # 'c) -> 'a))) (ZIP ((v_xs0 : ('b list)),((MAP (v_g0 : ('d -> 'c))) (v_ys0 : ('d list)))))) = ((MAP (UNCURRY (\b_x : 'b. (\b_y : 'd. ((v_f0 : (('b # 'c) -> 'a)) (b_x,((v_g0 : ('d -> 'c)) b_y))))))) (ZIP ((v_xs0 : ('b list)),(v_ys0 : ('d list))))))``,
   entry "list_L2834_set_zip" 2834 "by(simp add: set_conv_nth cong: rev_conj_cong)" benchLib.Simp false []
     ``((LIST_TO_SET (ZIP ((v_xs0 : ('a list)),(v_ys0 : ('b list))))) = (\b_uu_ : ('a # 'b). (?b_i : num. ((b_uu_ = ((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) b_i),(((\b_nth_list : ('b list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_ys0 : ('b list))) b_i))) /\ (b_i < ((MIN (LENGTH (v_xs0 : ('a list)))) (LENGTH (v_ys0 : ('b list)))))))))``,
   entry "list_L2841_zip_update" 2841 "by (simp add: update_zip)" benchLib.Simp false []
     ``((ZIP (((((\b_update_list : ('a list). \b_update_index : num. \b_update_item : 'a. LUPDATE b_update_item b_update_index b_update_list) (v_xs0 : ('a list))) (v_i0 : num)) (v_x0 : 'a)),((((\b_update_list : ('b list). \b_update_index : num. \b_update_item : 'b. LUPDATE b_update_item b_update_index b_update_list) (v_ys0 : ('b list))) (v_i0 : num)) (v_y0 : 'b)))) = ((((\b_update_list : (('a # 'b) list). \b_update_index : num. \b_update_item : ('a # 'b). LUPDATE b_update_item b_update_index b_update_list) (ZIP ((v_xs0 : ('a list)),(v_ys0 : ('b list))))) (v_i0 : num)) ((v_x0 : 'a),(v_y0 : 'b))))``,
   entry "list_L2897_in_set_zipE" 2897 "by(blast dest: set_zip_leftD set_zip_rightD)" benchLib.Blast false []
     ``((((v_x0 : 'a),(v_y0 : 'b)) IN (LIST_TO_SET (ZIP ((v_xs0 : ('a list)),(v_ys0 : ('b list)))))) ==> ((((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> (((v_y0 : 'b) IN (LIST_TO_SET (v_ys0 : ('b list)))) ==> (v_R0 : bool))) ==> (v_R0 : bool)))``,
   entry "list_L2904_zip_eq_conv" 2904 "by (auto simp add: zip_map_fst_snd)" benchLib.Auto false []
     ``(((LENGTH (v_xs0 : ('a list))) = (LENGTH (v_ys0 : ('b list)))) ==> (((ZIP ((v_xs0 : ('a list)),(v_ys0 : ('b list)))) = (v_zs0 : (('a # 'b) list))) = ((((MAP FST) (v_zs0 : (('a # 'b) list))) = (v_xs0 : ('a list))) /\ (((MAP SND) (v_zs0 : (('a # 'b) list))) = (v_ys0 : ('b list))))))``,
   entry "list_L3010_list_all2_lengthD" 3010 "by (simp add: list_all2_iff)" benchLib.Simp false []
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_xs0 : ('a list))) (v_ys0 : ('b list))) ==> ((LENGTH (v_xs0 : ('a list))) = (LENGTH (v_ys0 : ('b list)))))``,
   entry "list_L3014_list_all2_Nil" 3014 "by (simp add: list_all2_iff)" benchLib.Simp true [{name = "listAutoSeed$LIST_REL_NIL_LEFT_AUTO", theorem = listAutoSeedTheory.LIST_REL_NIL_LEFT_AUTO}, {name = "list$LIST_REL_NIL", theorem = CONJUNCT1 listTheory.LIST_REL_NIL}]
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) []) (v_ys0 : ('b list))) = ((v_ys0 : ('b list)) = []))``,
   entry "list_L3017_list_all2_Nil2" 3017 "by (simp add: list_all2_iff)" benchLib.Simp false []
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_xs0 : ('a list))) []) = ((v_xs0 : ('a list)) = []))``,
   entry "list_L3020_list_all2_Cons" 3020 "by (auto simp add: list_all2_iff)" benchLib.Auto false []
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) ((CONS (v_y0 : 'b)) (v_ys0 : ('b list)))) = ((((v_P0 : ('a -> ('b -> bool))) (v_x0 : 'a)) (v_y0 : 'b)) /\ (((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_xs0 : ('a list))) (v_ys0 : ('b list)))))``,
   entry "list_L3042_list_all2_rev" 3042 "by (simp add: list_all2_iff zip_rev cong: conj_cong)" benchLib.Simp false []
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (REVERSE (v_xs0 : ('a list)))) (REVERSE (v_ys0 : ('b list)))) = (((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_xs0 : ('a list))) (v_ys0 : ('b list))))``,
   entry "list_L3089_list_all2_appendI" 3089 "by (simp add: list_all2_append list_all2_lengthD)" benchLib.Simp false []
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_a0 : ('a list))) (v_b0 : ('b list))) ==> ((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_c0 : ('a list))) (v_d0 : ('b list))) ==> (((LIST_REL (v_P0 : ('a -> ('b -> bool)))) ((APPEND (v_a0 : ('a list))) (v_c0 : ('a list)))) ((APPEND (v_b0 : ('b list))) (v_d0 : ('b list))))))``,
   entry "list_L3093_list_all2_conv_all_nth" 3093 "by (force simp add: list_all2_iff set_zip)" benchLib.Force false []
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_xs0 : ('a list))) (v_ys0 : ('b list))) = (((LENGTH (v_xs0 : ('a list))) = (LENGTH (v_ys0 : ('b list)))) /\ (!b_i : num. ((b_i < (LENGTH (v_xs0 : ('a list)))) ==> (((v_P0 : ('a -> ('b -> bool))) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) b_i)) (((\b_nth_list : ('b list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_ys0 : ('b list))) b_i))))))``,
   entry "list_L3112_list_all2_all_nthI" 3112 "by (simp add: list_all2_conv_all_nth)" benchLib.Simp false []
     ``(((LENGTH (v_a0 : ('a list))) = (LENGTH (v_b0 : ('b list)))) ==> ((!b_n : num. ((b_n < (LENGTH (v_a0 : ('a list)))) ==> (((v_P0 : ('a -> ('b -> bool))) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_a0 : ('a list))) b_n)) (((\b_nth_list : ('b list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_b0 : ('b list))) b_n)))) ==> (((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_a0 : ('a list))) (v_b0 : ('b list)))))``,
   entry "list_L3116_list_all2I" 3116 "by (simp add: list_all2_iff)" benchLib.Simp false []
     ``((!b_x : ('a # 'b). (b_x IN (LIST_TO_SET (ZIP ((v_a0 : ('a list)),(v_b0 : ('b list)))))) ==> ((UNCURRY (v_P0 : ('a -> ('b -> bool)))) b_x)) ==> (((LENGTH (v_a0 : ('a list))) = (LENGTH (v_b0 : ('b list)))) ==> (((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_a0 : ('a list))) (v_b0 : ('b list)))))``,
   entry "list_L3120_list_all2_nthD" 3120 "by (simp add: list_all2_conv_all_nth)" benchLib.Simp false []
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_xs0 : ('a list))) (v_ys0 : ('b list))) ==> (((v_p0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> (((v_P0 : ('a -> ('b -> bool))) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_p0 : num))) (((\b_nth_list : ('b list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_ys0 : ('b list))) (v_p0 : num)))))``,
   entry "list_L3128_list_all2_map1" 3128 "by (simp add: list_all2_conv_all_nth)" benchLib.Simp false []
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) ((MAP (v_f0 : ('c -> 'a))) (v_as0 : ('c list)))) (v_bs0 : ('b list))) = (((LIST_REL (\b_x : 'c. (\b_y : 'b. (((v_P0 : ('a -> ('b -> bool))) ((v_f0 : ('c -> 'a)) b_x)) b_y)))) (v_as0 : ('c list))) (v_bs0 : ('b list))))``,
   entry "list_L3132_list_all2_map2" 3132 "by (auto simp add: list_all2_conv_all_nth)" benchLib.Auto false []
     ``((((LIST_REL (v_P0 : ('a -> ('b -> bool)))) (v_as0 : ('a list))) ((MAP (v_f0 : ('c -> 'b))) (v_bs0 : ('c list)))) = (((LIST_REL (\b_x : 'a. (\b_y : 'c. (((v_P0 : ('a -> ('b -> bool))) b_x) ((v_f0 : ('c -> 'b)) b_y))))) (v_as0 : ('a list))) (v_bs0 : ('c list))))``,
   entry "list_L3136_list_all2_refl" 3136 "by (simp add: list_all2_conv_all_nth)" benchLib.Simp false []
     ``((!b_x : 'a. (((v_P0 : ('a -> ('a -> bool))) b_x) b_x)) ==> (((LIST_REL (v_P0 : ('a -> ('a -> bool)))) (v_xs0 : ('a list))) (v_xs0 : ('a list))))``,
   entry "list_L3168_list_eq_iff_zip_eq" 3168 "by(auto simp add: set_zip list_all2_eq list_all2_conv_all_nth cong: conj_cong)" benchLib.Auto false []
     ``(((v_xs0 : ('a list)) = (v_ys0 : ('a list))) = (((LENGTH (v_xs0 : ('a list))) = (LENGTH (v_ys0 : ('a list)))) /\ (!b_set : ('a # 'a). (b_set IN (LIST_TO_SET (ZIP ((v_xs0 : ('a list)),(v_ys0 : ('a list)))))) ==> ((UNCURRY (\b_x : 'a. (\b_y : 'a. (b_x = b_y)))) b_set))))``,
   entry "list_L3172_list_all2_same" 3172 "by(auto simp add: list_all2_conv_all_nth set_conv_nth)" benchLib.Auto false []
     ``((((LIST_REL (v_P0 : ('a -> ('a -> bool)))) (v_xs0 : ('a list))) (v_xs0 : ('a list))) = (!b_x : 'a. (b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> (((v_P0 : ('a -> ('a -> bool))) b_x) b_x)))``,
   entry "list_L3286_rev_conv_fold" 3286 "by (simp add: fold_Cons_rev)" benchLib.Simp false []
     ``((REVERSE (v_xs0 : ('a list))) = ((((\b_fold_function : ('a -> (('a list) -> ('a list))). \b_fold_list : ('a list). \b_fold_initial : ('a list). FOLDR b_fold_function b_fold_initial b_fold_list) CONS) (v_xs0 : ('a list))) []))``,
   entry "list_L3320_union_coset_filter" 3320 "by auto" benchLib.Auto false []
     ``((((\b_coset_list : ('a list). COMPL (LIST_TO_SET b_coset_list) : 'a set) (v_xs0 : ('a list))) UNION (v_A0 : ('a set))) = ((\b_coset_list : ('a list). COMPL (LIST_TO_SET b_coset_list) : 'a set) ((FILTER (\b_x : 'a. (~(b_x IN (v_A0 : ('a set)))))) (v_xs0 : ('a list)))))``,
   entry "list_L3332_minus_coset_filter" 3332 "by auto" benchLib.Auto false []
     ``(((v_A0 : ('a set)) DIFF ((\b_coset_list : ('a list). COMPL (LIST_TO_SET b_coset_list) : 'a set) (v_xs0 : ('a list)))) = (LIST_TO_SET ((FILTER (\b_x : 'a. (b_x IN (v_A0 : ('a set))))) (v_xs0 : ('a list)))))``,
   entry "list_L3336_inter_set_filter" 3336 "by auto" benchLib.Auto false []
     ``(((v_A0 : ('a set)) INTER (LIST_TO_SET (v_xs0 : ('a list)))) = (LIST_TO_SET ((FILTER (\b_x : 'a. (b_x IN (v_A0 : ('a set))))) (v_xs0 : ('a list)))))``,
   entry "list_L3340_inter_coset_fold" 3340 "by (simp add: Diff_eq [symmetric] minus_set_fold)" benchLib.Simp false []
     ``(((v_A0 : ('a set)) INTER ((\b_coset_list : ('a list). COMPL (LIST_TO_SET b_coset_list) : 'a set) (v_xs0 : ('a list)))) = ((((\b_fold_function : ('a -> (('a set) -> ('a set))). \b_fold_list : ('a list). \b_fold_initial : ('a set). FOLDR b_fold_function b_fold_initial b_fold_list) (\b_remove_item : 'a. \b_remove_set : ('a set). b_remove_set DELETE b_remove_item)) (v_xs0 : ('a list))) (v_A0 : ('a set))))``,
   entry "list_L3400_foldr_conv_foldl" 3400 "by (simp add: foldr_conv_fold foldl_conv_fold)" benchLib.Simp false []
     ``(((((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (v_f0 : ('b -> ('a -> 'a)))) (v_xs0 : ('b list))) (v_a0 : 'a)) = (((FOLDL (\b_x : 'a. (\b_y : 'b. (((v_f0 : ('b -> ('a -> 'a))) b_y) b_x)))) (v_a0 : 'a)) (REVERSE (v_xs0 : ('b list)))))``,
   entry "list_L3404_foldl_conv_foldr" 3404 "by (simp add: foldr_conv_fold foldl_conv_fold)" benchLib.Simp false []
     ``((((FOLDL (v_f0 : ('a -> ('b -> 'a)))) (v_a0 : 'a)) (v_xs0 : ('b list))) = ((((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (\b_x : 'b. (\b_y : 'a. (((v_f0 : ('a -> ('b -> 'a))) b_y) b_x)))) (REVERSE (v_xs0 : ('b list)))) (v_a0 : 'a)))``,
   entry "list_L3413_foldr_cong" 3413 "by (auto simp add: foldr_conv_fold intro!: fold_cong)" benchLib.Auto false [{name = "list$FOLDR_CONG", theorem = listTheory.FOLDR_CONG}]
     ``(((v_a0 : 'a) = (v_b0 : 'a)) ==> (((v_l0 : ('b list)) = (v_k0 : ('b list))) ==> ((!b_a : 'a. (!b_x : 'b. ((b_x IN (LIST_TO_SET (v_l0 : ('b list)))) ==> ((((v_f0 : ('b -> ('a -> 'a))) b_x) b_a) = (((v_g0 : ('b -> ('a -> 'a))) b_x) b_a))))) ==> (((((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (v_f0 : ('b -> ('a -> 'a)))) (v_l0 : ('b list))) (v_a0 : 'a)) = ((((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (v_g0 : ('b -> ('a -> 'a)))) (v_k0 : ('b list))) (v_b0 : 'a))))))``,
   entry "list_L3417_foldl_cong" 3417 "by (auto simp add: foldl_conv_fold intro!: fold_cong)" benchLib.Auto false [{name = "list$FOLDL_CONG", theorem = listTheory.FOLDL_CONG}]
     ``(((v_a0 : 'a) = (v_b0 : 'a)) ==> (((v_l0 : ('b list)) = (v_k0 : ('b list))) ==> ((!b_a : 'a. (!b_x : 'b. ((b_x IN (LIST_TO_SET (v_l0 : ('b list)))) ==> ((((v_f0 : ('a -> ('b -> 'a))) b_a) b_x) = (((v_g0 : ('a -> ('b -> 'a))) b_a) b_x))))) ==> ((((FOLDL (v_f0 : ('a -> ('b -> 'a)))) (v_a0 : 'a)) (v_l0 : ('b list))) = (((FOLDL (v_g0 : ('a -> ('b -> 'a)))) (v_b0 : 'a)) (v_k0 : ('b list)))))))``,
   entry "list_L3421_foldr_append" 3421 "by (simp add: foldr_conv_fold)" benchLib.Simp false [{name = "rich_list$FOLDR_APPEND", theorem = rich_listTheory.FOLDR_APPEND}]
     ``(((((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (v_f0 : ('b -> ('a -> 'a)))) ((APPEND (v_xs0 : ('b list))) (v_ys0 : ('b list)))) (v_a0 : 'a)) = ((((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (v_f0 : ('b -> ('a -> 'a)))) (v_xs0 : ('b list))) ((((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (v_f0 : ('b -> ('a -> 'a)))) (v_ys0 : ('b list))) (v_a0 : 'a))))``,
   entry "list_L3424_foldl_append" 3424 "by (simp add: foldl_conv_fold)" benchLib.Simp false [{name = "rich_list$FOLDL_APPEND", theorem = rich_listTheory.FOLDL_APPEND}]
     ``((((FOLDL (v_f0 : ('a -> ('b -> 'a)))) (v_a0 : 'a)) ((APPEND (v_xs0 : ('b list))) (v_ys0 : ('b list)))) = (((FOLDL (v_f0 : ('a -> ('b -> 'a)))) (((FOLDL (v_f0 : ('a -> ('b -> 'a)))) (v_a0 : 'a)) (v_xs0 : ('b list)))) (v_ys0 : ('b list))))``,
   entry "list_L3427_foldr_map" 3427 "by (simp add: foldr_conv_fold fold_map rev_map)" benchLib.Simp false [{name = "rich_list$FOLDR_MAP", theorem = rich_listTheory.FOLDR_MAP}]
     ``(((((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (v_g0 : ('b -> ('a -> 'a)))) ((MAP (v_f0 : ('c -> 'b))) (v_xs0 : ('c list)))) (v_a0 : 'a)) = ((((\b_fold_function : ('c -> ('a -> 'a)). \b_fold_list : ('c list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) ((combin$o (v_g0 : ('b -> ('a -> 'a)))) (v_f0 : ('c -> 'b)))) (v_xs0 : ('c list))) (v_a0 : 'a)))``,
   entry "list_L3430_foldr_filter" 3430 "by (simp add: foldr_conv_fold rev_filter fold_filter)" benchLib.Simp false [{name = "rich_list$FOLDR_FILTER", theorem = rich_listTheory.FOLDR_FILTER}]
     ``((((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (v_f0 : ('b -> ('a -> 'a)))) ((FILTER (v_P0 : ('b -> bool))) (v_xs0 : ('b list)))) = (((\b_fold_function : ('b -> ('a -> 'a)). \b_fold_list : ('b list). \b_fold_initial : 'a. FOLDR b_fold_function b_fold_initial b_fold_list) (\b_x : 'b. (if ((v_P0 : ('b -> bool)) b_x) then ((v_f0 : ('b -> ('a -> 'a))) b_x) else I))) (v_xs0 : ('b list))))``,
   entry "list_L3434_foldl_map" 3434 "by (simp add: foldl_conv_fold fold_map comp_def)" benchLib.Simp false [{name = "rich_list$FOLDL_MAP", theorem = rich_listTheory.FOLDL_MAP}]
     ``((((FOLDL (v_g0 : ('a -> ('b -> 'a)))) (v_a0 : 'a)) ((MAP (v_f0 : ('c -> 'b))) (v_xs0 : ('c list)))) = (((FOLDL (\b_a : 'a. (\b_x : 'c. (((v_g0 : ('a -> ('b -> 'a))) b_a) ((v_f0 : ('c -> 'b)) b_x))))) (v_a0 : 'a)) (v_xs0 : ('c list))))``,
   entry "list_L3438_concat_conv_foldr" 3438 "by (simp add: fold_append_concat_rev foldr_conv_fold)" benchLib.Simp false []
     ``((FLAT (v_xss0 : (('a list) list))) = ((((\b_fold_function : (('a list) -> (('a list) -> ('a list))). \b_fold_list : (('a list) list). \b_fold_initial : ('a list). FOLDR b_fold_function b_fold_initial b_fold_list) APPEND) (v_xss0 : (('a list) list))) []))``,
   entry "list_L3481_upt_Suc_append" 3481 "by simp" benchLib.Simp false []
     ``(((v_i0 : num) <= (v_j0 : num)) ==> ((((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (v_i0 : num)) (SUC (v_j0 : num))) = ((APPEND (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (v_i0 : num)) (v_j0 : num))) ((CONS (v_j0 : num)) []))))``,
   entry "list_L3485_upt_conv_Cons" 3485 "by (simp add: upt_rec)" benchLib.Simp false []
     ``(((v_i0 : num) < (v_j0 : num)) ==> ((((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (v_i0 : num)) (v_j0 : num)) = ((CONS (v_i0 : num)) (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (SUC (v_i0 : num))) (v_j0 : num)))))``,
   entry "list_L3506_hd_upt" 3506 "by(simp add:upt_conv_Cons)" benchLib.Simp false []
     ``(((v_i0 : num) < (v_j0 : num)) ==> ((HD (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (v_i0 : num)) (v_j0 : num))) = (v_i0 : num)))``,
   entry "list_L3509_tl_upt" 3509 "by (simp add: upt_rec)" benchLib.Simp false []
     ``((TL (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (v_m0 : num)) (v_n0 : num))) = (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (SUC (v_m0 : num))) (v_n0 : num)))``,
   entry "list_L3569_list_all2_antisym" 3569 "by (simp add: list_all2_conv_all_nth nth_equalityI)" benchLib.Simp false []
     ``((!b_x : 'a. (!b_y : 'a. ((((v_P0 : ('a -> ('a -> bool))) b_x) b_y) ==> ((((v_Q0 : ('a -> ('a -> bool))) b_y) b_x) ==> (b_x = b_y))))) ==> ((((LIST_REL (v_P0 : ('a -> ('a -> bool)))) (v_xs0 : ('a list))) (v_ys0 : ('a list))) ==> ((((LIST_REL (v_Q0 : ('a -> ('a -> bool)))) (v_ys0 : ('a list))) (v_xs0 : ('a list))) ==> ((v_xs0 : ('a list)) = (v_ys0 : ('a list))))))``,
   entry "list_L3908_nth_eq_iff_index_eq" 3908 "by(auto simp: distinct_conv_nth)" benchLib.Auto false []
     ``((ALL_DISTINCT (v_xs0 : ('a list))) ==> (((v_i0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> (((v_j0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> (((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_i0 : num)) = (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_j0 : num))) = ((v_i0 : num) = (v_j0 : num))))))``,
   entry "list_L3912_distinct_Ex1" 3912 "by (auto simp: in_set_conv_nth nth_eq_iff_index_eq)" benchLib.Auto false []
     ``((ALL_DISTINCT (v_xs0 : ('a list))) ==> (((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> (?!b_i : num. ((b_i < (LENGTH (v_xs0 : ('a list)))) /\ ((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) b_i) = (v_x0 : 'a))))))``,
   entry "list_L3919_bij_betw_nth" 3919 "by (auto intro!: inj_on_nth simp: set_conv_nth)" benchLib.Auto false []
     ``((ALL_DISTINCT (v_xs0 : ('a list))) ==> (((v_A0 : (num set)) = ((\b_less_than : num. \b_less_item : num. b_less_item < b_less_than) (LENGTH (v_xs0 : ('a list))))) ==> (((v_B0 : ('a set)) = (LIST_TO_SET (v_xs0 : ('a list)))) ==> (((BIJ ((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list)))) (v_A0 : (num set))) (v_B0 : ('a set))))))``,
   entry "list_L3925_set_update_distinct" 3925 "by(auto simp: set_eq_iff in_set_conv_nth nth_list_update nth_eq_iff_index_eq)" benchLib.Auto false []
     ``((ALL_DISTINCT (v_xs0 : ('a list))) ==> (((v_n0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> ((LIST_TO_SET ((((\b_update_list : ('a list). \b_update_index : num. \b_update_item : 'a. LUPDATE b_update_item b_update_index b_update_list) (v_xs0 : ('a list))) (v_n0 : num)) (v_x0 : 'a))) = ((v_x0 : 'a) INSERT ((LIST_TO_SET (v_xs0 : ('a list))) DIFF ((((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_n0 : num)) INSERT {}))))))``,
   entry "list_L4011_length_remdups_concat" 4011 "by (simp add: distinct_card [symmetric])" benchLib.Simp false []
     ``((LENGTH (nub (FLAT (v_xss0 : (('a list) list))))) = (CARD (BIGUNION (IMAGE (\b_xs : ('a list). (LIST_TO_SET b_xs)) (LIST_TO_SET (v_xss0 : (('a list) list)))))))``,
   entry "list_L4065_set_take_disj_set_drop_if_distinct" 4065 "by (auto simp: in_set_conv_nth distinct_conv_nth)" benchLib.Auto false []
     ``((ALL_DISTINCT (v_vs0 : ('a list))) ==> (((v_i0 : num) <= (v_j0 : num)) ==> (((LIST_TO_SET ((TAKE (v_i0 : num)) (v_vs0 : ('a list)))) INTER (LIST_TO_SET ((DROP (v_j0 : num)) (v_vs0 : ('a list))))) = {})))``,
   entry "list_L4071_distinct_singleton" 4071 "by simp" benchLib.Simp false []
     ``(ALL_DISTINCT ((CONS (v_x0 : 'a)) []))``,
   entry "list_L4073_distinct_length_2_or_more" 4073 "by force" benchLib.Force false []
     ``((ALL_DISTINCT ((CONS (v_a0 : 'a)) ((CONS (v_b0 : 'a)) (v_xs0 : ('a list))))) = ((~((v_a0 : 'a) = (v_b0 : 'a))) /\ ((ALL_DISTINCT ((CONS (v_a0 : 'a)) (v_xs0 : ('a list)))) /\ (ALL_DISTINCT ((CONS (v_b0 : 'a)) (v_xs0 : ('a list)))))))``,
   entry "list_L4464_in_set_insert" 4464 "by (simp add: List.insert_def)" benchLib.Simp false []
     ``(((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> ((if (v_x0 : 'a) IN LIST_TO_SET (v_xs0 : ('a list)) then (v_xs0 : ('a list)) else CONS (v_x0 : 'a) (v_xs0 : ('a list))) = (v_xs0 : ('a list))))``,
   entry "list_L4468_not_in_set_insert" 4468 "by (simp add: List.insert_def)" benchLib.Simp false []
     ``((~((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list))))) ==> ((if (v_x0 : 'a) IN LIST_TO_SET (v_xs0 : ('a list)) then (v_xs0 : ('a list)) else CONS (v_x0 : 'a) (v_xs0 : ('a list))) = ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))))``,
   entry "list_L4472_insert_Nil" 4472 "by simp" benchLib.Simp false []
     ``((if (v_x0 : 'a) IN LIST_TO_SET [] then [] else CONS (v_x0 : 'a) []) = ((CONS (v_x0 : 'a)) []))``,
   entry "list_L4475_set_insert" 4475 "by (auto simp add: List.insert_def)" benchLib.Auto false []
     ``((LIST_TO_SET (if (v_x0 : 'a) IN LIST_TO_SET (v_xs0 : ('a list)) then (v_xs0 : ('a list)) else CONS (v_x0 : 'a) (v_xs0 : ('a list)))) = ((v_x0 : 'a) INSERT (LIST_TO_SET (v_xs0 : ('a list)))))``,
   entry "list_L4478_distinct_insert" 4478 "by (simp add: List.insert_def)" benchLib.Simp false []
     ``((ALL_DISTINCT (if (v_x0 : 'a) IN LIST_TO_SET (v_xs0 : ('a list)) then (v_xs0 : ('a list)) else CONS (v_x0 : 'a) (v_xs0 : ('a list)))) = (ALL_DISTINCT (v_xs0 : ('a list))))``,
   entry "list_L4481_insert_remdups" 4481 "by (simp add: List.insert_def)" benchLib.Simp false []
     ``((if (v_x0 : 'a) IN LIST_TO_SET (nub (v_xs0 : ('a list))) then (nub (v_xs0 : ('a list))) else CONS (v_x0 : 'a) (nub (v_xs0 : ('a list)))) = (nub (if (v_x0 : 'a) IN LIST_TO_SET (v_xs0 : ('a list)) then (v_xs0 : ('a list)) else CONS (v_x0 : 'a) (v_xs0 : ('a list)))))``,
   entry "list_L4553_count_notin" 4553 "by(simp add: count_list_0_iff)" benchLib.Simp false []
     ``((~((v_x0 : 'a) IN (LIST_TO_SET (v_xs0 : ('a list))))) ==> ((((\b_count_list : ('a list). \b_count_item : 'a. LIST_ELEM_COUNT b_count_item b_count_list) (v_xs0 : ('a list))) (v_x0 : 'a)) = 0))``,
   entry "list_L4854_minus_list_set_Nil2" 4854 "by(simp add: minus_list_set_def)" benchLib.Simp false []
     ``((((\b_minus_left : ('a list). \b_minus_right : ('a list). FILTER (\b_minus_item : 'a. ~(b_minus_item IN LIST_TO_SET b_minus_right)) b_minus_left) (v_xs0 : ('a list))) []) = (v_xs0 : ('a list)))``,
   entry "list_L4867_minus_list_set_Nil1" 4867 "by (simp add: minus_list_set_eq_filter)" benchLib.Simp false []
     ``((((\b_minus_left : ('a list). \b_minus_right : ('a list). FILTER (\b_minus_item : 'a. ~(b_minus_item IN LIST_TO_SET b_minus_right)) b_minus_left) []) (v_xs0 : ('a list))) = [])``,
   entry "list_L4870_minus_list_set_Cons1" 4870 "by(simp add:minus_list_set_eq_filter)" benchLib.Simp false []
     ``((((\b_minus_left : ('a list). \b_minus_right : ('a list). FILTER (\b_minus_item : 'a. ~(b_minus_item IN LIST_TO_SET b_minus_right)) b_minus_left) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) (v_ys0 : ('a list))) = (if ((v_x0 : 'a) IN (LIST_TO_SET (v_ys0 : ('a list)))) then (((\b_minus_left : ('a list). \b_minus_right : ('a list). FILTER (\b_minus_item : 'a. ~(b_minus_item IN LIST_TO_SET b_minus_right)) b_minus_left) (v_xs0 : ('a list))) (v_ys0 : ('a list))) else ((CONS (v_x0 : 'a)) (((\b_minus_left : ('a list). \b_minus_right : ('a list). FILTER (\b_minus_item : 'a. ~(b_minus_item IN LIST_TO_SET b_minus_right)) b_minus_left) (v_xs0 : ('a list))) (v_ys0 : ('a list))))))``,
   entry "list_L4878_length_minus_list_set" 4878 "by (simp add: minus_list_set_eq_filter)" benchLib.Simp false []
     ``((LENGTH (((\b_minus_left : ('a list). \b_minus_right : ('a list). FILTER (\b_minus_item : 'a. ~(b_minus_item IN LIST_TO_SET b_minus_right)) b_minus_left) (v_xs0 : ('a list))) (v_ys0 : ('a list)))) <= (LENGTH (v_xs0 : ('a list))))``,
   entry "list_L4881_distinct_minus_list_set" 4881 "by (simp add: minus_list_set_eq_filter)" benchLib.Simp false []
     ``((ALL_DISTINCT (v_xs0 : ('a list))) ==> (ALL_DISTINCT (((\b_minus_left : ('a list). \b_minus_right : ('a list). FILTER (\b_minus_item : 'a. ~(b_minus_item IN LIST_TO_SET b_minus_right)) b_minus_left) (v_xs0 : ('a list))) (v_ys0 : ('a list)))))``,
   entry "list_L4890_set_inter_list_set" 4890 "by(auto simp add: inter_list_set_def)" benchLib.Auto false []
     ``((LIST_TO_SET (((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = ((LIST_TO_SET (v_xs0 : ('a list))) INTER (LIST_TO_SET (v_ys0 : ('a list)))))``,
   entry "list_L4893_inter_list_set_Nil" 4893 "by (simp add: inter_list_set_def)" benchLib.Simp false []
     ``((((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) []) (v_xs0 : ('a list))) = [])``,
   entry "list_L4896_inter_list_set_Cons" 4896 "by(simp add:inter_list_set_def)" benchLib.Simp false []
     ``((((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) (v_ys0 : ('a list))) = (if ((v_x0 : 'a) IN (LIST_TO_SET (v_ys0 : ('a list)))) then ((CONS (v_x0 : 'a)) (((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) (v_xs0 : ('a list))) (v_ys0 : ('a list)))) else (((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) (v_xs0 : ('a list))) (v_ys0 : ('a list)))))``,
   entry "list_L4900_inter_list_set_Nil2" 4900 "by(simp add: inter_list_set_def)" benchLib.Simp false []
     ``((((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) (v_xs0 : ('a list))) []) = [])``,
   entry "list_L4903_distinct_inter_list_set" 4903 "by (simp add: inter_list_set_def)" benchLib.Simp false []
     ``((ALL_DISTINCT (v_xs0 : ('a list))) ==> (ALL_DISTINCT (((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) (v_xs0 : ('a list))) (v_ys0 : ('a list)))))``,
   entry "list_L4906_inter_list_set_append" 4906 "by (simp add: inter_list_set_def)" benchLib.Simp false []
     ``((((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) (v_zs0 : ('a list))) = ((APPEND (((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) (v_xs0 : ('a list))) (v_zs0 : ('a list)))) (((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) (v_ys0 : ('a list))) (v_zs0 : ('a list)))))``,
   entry "list_L4910_length_inter_list_set" 4910 "by (simp add: inter_list_set_def)" benchLib.Simp false []
     ``((LENGTH (((\b_inter_left : ('a list). \b_inter_right : ('a list). FILTER (\b_inter_item : 'a. b_inter_item IN LIST_TO_SET b_inter_right) b_inter_left) (v_xs0 : ('a list))) (v_ys0 : ('a list)))) <= (LENGTH (v_xs0 : ('a list))))``,
   entry "list_L4998_set_replicate_conv_if" 4998 "by auto" benchLib.Auto false []
     ``((LIST_TO_SET ((REPLICATE (v_n0 : num)) (v_x0 : 'a))) = (if ((v_n0 : num) = 0) then {} else ((v_x0 : 'a) INSERT {})))``,
   entry "list_L5001_in_set_replicate" 5001 "by (simp add: set_replicate_conv_if)" benchLib.Simp false []
     ``(((v_x0 : 'a) IN (LIST_TO_SET ((REPLICATE (v_n0 : num)) (v_y0 : 'a)))) = (((v_x0 : 'a) = (v_y0 : 'a)) /\ (~((v_n0 : num) = 0))))``,
   entry "list_L5008_Ball_set_replicate" 5008 "by(simp add: set_replicate_conv_if)" benchLib.Simp false []
     ``((!b_x : 'a. (b_x IN (LIST_TO_SET ((REPLICATE (v_n0 : num)) (v_a0 : 'a)))) ==> ((v_P0 : ('a -> bool)) b_x)) = (((v_P0 : ('a -> bool)) (v_a0 : 'a)) \/ ((v_n0 : num) = 0)))``,
   entry "list_L5012_Bex_set_replicate" 5012 "by(simp add: set_replicate_conv_if)" benchLib.Simp false []
     ``((?b_x : 'a. (b_x IN (LIST_TO_SET ((REPLICATE (v_n0 : num)) (v_a0 : 'a)))) /\ ((v_P0 : ('a -> bool)) b_x)) = (((v_P0 : ('a -> bool)) (v_a0 : 'a)) /\ (~((v_n0 : num) = 0))))``,
   entry "list_L5044_takeWhile_replicate" 5044 "by fastforce" benchLib.Fastforce false []
     ``(((takeWhile (v_P0 : ('a -> bool))) ((REPLICATE (v_n0 : num)) (v_x0 : 'a))) = (if ((v_P0 : ('a -> bool)) (v_x0 : 'a)) then ((REPLICATE (v_n0 : num)) (v_x0 : 'a)) else []))``,
   entry "list_L5048_dropWhile_replicate" 5048 "by fastforce" benchLib.Fastforce false []
     ``(((dropWhile (v_P0 : ('a -> bool))) ((REPLICATE (v_n0 : num)) (v_x0 : 'a))) = (if ((v_P0 : ('a -> bool)) (v_x0 : 'a)) then [] else ((REPLICATE (v_n0 : num)) (v_x0 : 'a))))``,
   entry "list_L5788_lists_length_Suc_eq" 5788 "by (auto simp: length_Suc_conv)" benchLib.Auto false []
     ``((\b_xs : ('a list). (((LIST_TO_SET b_xs) SUBSET (v_A0 : ('a set))) /\ ((LENGTH b_xs) = (SUC (v_n0 : num))))) = (IMAGE (UNCURRY (\b_xs : ('a list). (\b_n : 'a. ((CONS b_n) b_xs)))) (\b_sigma_pair : (('a list) # 'a). FST b_sigma_pair IN (\b_xs : ('a list). (((LIST_TO_SET b_xs) SUBSET (v_A0 : ('a set))) /\ ((LENGTH b_xs) = (v_n0 : num)))) /\ SND b_sigma_pair IN ((\b_uu_ : ('a list). (v_A0 : ('a set))) (FST b_sigma_pair)))))``,
   entry "list_L5911_sorted_wrt1" 5911 "by(simp)" benchLib.Simp false []
     ``(((SORTED (v_P0 : ('a -> ('a -> bool)))) ((CONS (v_x0 : 'a)) [])) = T)``,
   entry "list_L5946_sorted_wrt_dropWhile" 5946 "by (auto dest: sorted_wrt_drop simp: dropWhile_eq_drop)" benchLib.Auto false []
     ``(((SORTED (v_R0 : ('a -> ('a -> bool)))) (v_xs0 : ('a list))) ==> ((SORTED (v_R0 : ('a -> ('a -> bool)))) ((dropWhile (v_P0 : ('a -> bool))) (v_xs0 : ('a list)))))``,
   entry "list_L5964_sorted_wrt01" 5964 "by(auto simp: le_Suc_eq length_Suc_conv)" benchLib.Auto false []
     ``(((LENGTH (v_xs0 : ('a list))) <= 1) ==> ((SORTED (v_P0 : ('a -> ('a -> bool)))) (v_xs0 : ('a list))))``,
   entry "list_L5971_sorted_wrt_nth_less" 5971 "by(auto simp: sorted_wrt_iff_nth_less)" benchLib.Auto false []
     ``(((SORTED (v_P0 : ('a -> ('a -> bool)))) (v_xs0 : ('a list))) ==> (((v_i0 : num) < (v_j0 : num)) ==> (((v_j0 : num) < (LENGTH (v_xs0 : ('a list)))) ==> (((v_P0 : ('a -> ('a -> bool))) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_i0 : num))) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) (v_j0 : num))))))``,
   entry "list_L6208_sorted_upt" 6208 "by(simp add: sorted_wrt_mono_rel[OF _ sorted_wrt_upt])" benchLib.Simp false []
     ``((SORTED (\b_order_left : num. \b_order_right : num. b_order_left <= b_order_right)) (((\b_upt_start : num. \b_upt_end : num. GENLIST (\b_upt_offset. b_upt_start + b_upt_offset) (b_upt_end - b_upt_start)) (v_m0 : num)) (v_n0 : num)))``,
   entry "list_L6948_Cons_in_lists_iff" 6948 "by auto" benchLib.Auto false []
     ``((((CONS (v_x0 : 'a)) (v_xs0 : ('a list))) IN ((\b_lists_set : ('a set). \b_lists_list : ('a list). LIST_TO_SET b_lists_list SUBSET b_lists_set) (v_A0 : ('a set)))) = (((v_x0 : 'a) IN (v_A0 : ('a set))) /\ ((v_xs0 : ('a list)) IN ((\b_lists_set : ('a set). \b_lists_list : ('a list). LIST_TO_SET b_lists_list SUBSET b_lists_set) (v_A0 : ('a set))))))``,
   entry "list_L6975_lists_eq_set" 6975 "by auto" benchLib.Auto false []
     ``(((\b_lists_set : ('a set). \b_lists_list : ('a list). LIST_TO_SET b_lists_list SUBSET b_lists_set) (v_A0 : ('a set))) = (\b_xs : ('a list). ((LIST_TO_SET b_xs) SUBSET (v_A0 : ('a set)))))``,
   entry "list_L6978_lists_empty" 6978 "by auto" benchLib.Auto false []
     ``(((\b_lists_set : ('a set). \b_lists_list : ('a list). LIST_TO_SET b_lists_list SUBSET b_lists_set) {}) = ([] INSERT {}))``,
   entry "list_L6981_lists_UNIV" 6981 "by auto" benchLib.Auto false []
     ``(((\b_lists_set : ('a set). \b_lists_list : ('a list). LIST_TO_SET b_lists_list SUBSET b_lists_set) UNIV) = UNIV)``,
   entry "list_L7035_set_Cons_sing_Nil" 7035 "by (auto simp add: set_Cons_def)" benchLib.Auto false []
     ``((((\b_cons_heads : ('a set). \b_cons_tails : (('a list) set). \b_cons_list : ('a list). ?b_cons_head : 'a. ?b_cons_tail : ('a list). b_cons_head IN b_cons_heads /\ b_cons_tail IN b_cons_tails /\ b_cons_list = CONS b_cons_head b_cons_tail) (v_A0 : ('a set))) ([] INSERT {})) = (IMAGE (\b_x : 'a. ((CONS b_x) [])) (v_A0 : ('a set))))``,
   entry "list_L8167_list_all_iff" 8167 "by (simp add: list.pred_set)" benchLib.Simp false []
     ``(((EVERY (v_P0 : ('a -> bool))) (v_xs0 : ('a list))) = (!b_set : 'a. (b_set IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) b_set)))``,
   entry "list_L8183_list_all_Nil_iff" 8183 "by (simp add: list_all_iff)" benchLib.Simp false []
     ``(((EVERY (v_P0 : ('a -> bool))) []) = T)``,
   entry "list_L8187_list_all_Cons_iff" 8187 "by (simp add: list_all_iff)" benchLib.Simp false []
     ``(((EVERY (v_P0 : ('a -> bool))) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) = (((v_P0 : ('a -> bool)) (v_x0 : 'a)) /\ ((EVERY (v_P0 : ('a -> bool))) (v_xs0 : ('a list)))))``,
   entry "list_L8191_list_ex_Nil_iff" 8191 "by (simp add: list_ex_iff)" benchLib.Simp false []
     ``(((EXISTS (v_P0 : ('a -> bool))) []) = F)``,
   entry "list_L8195_list_ex_Cons_iff" 8195 "by (simp add: list_ex_iff)" benchLib.Simp false []
     ``(((EXISTS (v_P0 : ('a -> bool))) ((CONS (v_x0 : 'a)) (v_xs0 : ('a list)))) = (((v_P0 : ('a -> bool)) (v_x0 : 'a)) \/ ((EXISTS (v_P0 : ('a -> bool))) (v_xs0 : ('a list)))))``,
   entry "list_L8207_list_all_append" 8207 "by (auto simp add: list_all_iff)" benchLib.Auto false []
     ``(((EVERY (v_P0 : ('a -> bool))) ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = (((EVERY (v_P0 : ('a -> bool))) (v_xs0 : ('a list))) /\ ((EVERY (v_P0 : ('a -> bool))) (v_ys0 : ('a list)))))``,
   entry "list_L8211_list_ex_append" 8211 "by (auto simp add: list_ex_iff)" benchLib.Auto false []
     ``(((EXISTS (v_P0 : ('a -> bool))) ((APPEND (v_xs0 : ('a list))) (v_ys0 : ('a list)))) = (((EXISTS (v_P0 : ('a -> bool))) (v_xs0 : ('a list))) \/ ((EXISTS (v_P0 : ('a -> bool))) (v_ys0 : ('a list)))))``,
   entry "list_L8215_list_all_rev" 8215 "by (simp add: list_all_iff)" benchLib.Simp false []
     ``(((EVERY (v_P0 : ('a -> bool))) (REVERSE (v_xs0 : ('a list)))) = ((EVERY (v_P0 : ('a -> bool))) (v_xs0 : ('a list))))``,
   entry "list_L8219_list_ex_rev" 8219 "by (simp add: list_ex_iff)" benchLib.Simp false []
     ``(((EXISTS (v_P0 : ('a -> bool))) (REVERSE (v_xs0 : ('a list)))) = ((EXISTS (v_P0 : ('a -> bool))) (v_xs0 : ('a list))))``,
   entry "list_L8223_list_all_length" 8223 "by (auto simp add: list_all_iff set_conv_nth)" benchLib.Auto false []
     ``(((EVERY (v_P0 : ('a -> bool))) (v_xs0 : ('a list))) = (!b_n : num. ((b_n < (LENGTH (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) b_n)))))``,
   entry "list_L8227_list_ex_length" 8227 "by (auto simp add: list_ex_iff set_conv_nth)" benchLib.Auto false []
     ``(((EXISTS (v_P0 : ('a -> bool))) (v_xs0 : ('a list))) = (?b_n : num. ((b_n < (LENGTH (v_xs0 : ('a list)))) /\ ((v_P0 : ('a -> bool)) (((\b_nth_list : ('a list). \b_nth_index : num. EL b_nth_index b_nth_list) (v_xs0 : ('a list))) b_n)))))``,
   entry "list_L8236_list_ex_cong" 8236 "by (simp add: list_ex_iff)" benchLib.Simp false []
     ``(((v_xs0 : ('a list)) = (v_ys0 : ('a list))) ==> ((!b_x : 'a. ((b_x IN (LIST_TO_SET (v_ys0 : ('a list)))) ==> (((v_f0 : ('a -> bool)) b_x) = ((v_g0 : ('a -> bool)) b_x)))) ==> (((EXISTS (v_f0 : ('a -> bool))) (v_xs0 : ('a list))) = ((EXISTS (v_g0 : ('a -> bool))) (v_ys0 : ('a list))))))``,
   entry "list_L8607_empty_set" 8607 "by simp" benchLib.Simp false []
     ``({} = (LIST_TO_SET []))``,
   entry "list_L8611_UNIV_coset" 8611 "by simp" benchLib.Simp false []
     ``(UNIV = ((\b_coset_list : ('a list). COMPL (LIST_TO_SET b_coset_list) : 'a set) []))``,
   entry "list_L8615_compl_set" 8615 "by simp" benchLib.Simp false []
     ``((COMPL (LIST_TO_SET (v_xs0 : ('a list)))) = ((\b_coset_list : ('a list). COMPL (LIST_TO_SET b_coset_list) : 'a set) (v_xs0 : ('a list))))``,
   entry "list_L8619_compl_coset" 8619 "by simp" benchLib.Simp false []
     ``((COMPL ((\b_coset_list : ('a list). COMPL (LIST_TO_SET b_coset_list) : 'a set) (v_xs0 : ('a list)))) = (LIST_TO_SET (v_xs0 : ('a list))))``,
   entry "list_L8638_filter_set" 8638 "by simp" benchLib.Simp false []
     ``((((\b_filter_predicate : ('a -> bool). \b_filter_set : ('a set). \b_filter_item : 'a. b_filter_item IN b_filter_set /\ b_filter_predicate b_filter_item) (v_P0 : ('a -> bool))) (LIST_TO_SET (v_xs0 : ('a list)))) = (LIST_TO_SET ((FILTER (v_P0 : ('a -> bool))) (v_xs0 : ('a list)))))``,
   entry "list_L8642_image_set" 8642 "by simp" benchLib.Simp false []
     ``((IMAGE (v_f0 : ('b -> 'a)) (LIST_TO_SET (v_xs0 : ('b list)))) = (LIST_TO_SET ((MAP (v_f0 : ('b -> 'a))) (v_xs0 : ('b list)))))``,
   entry "list_L8646_subset_code_1" 8646 "by auto" benchLib.Auto false []
     ``(((LIST_TO_SET (v_xs0 : ('a list))) SUBSET (v_B0 : ('a set))) = (!b_x : 'a. (b_x IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> (b_x IN (v_B0 : ('a set)))))``,
   entry "list_L8646_subset_code_2" 8646 "by auto" benchLib.Auto false []
     ``(((v_A0 : ('b set)) SUBSET ((\b_coset_list : ('b list). COMPL (LIST_TO_SET b_coset_list) : 'b set) (v_ys0 : ('b list)))) = (!b_y : 'b. (b_y IN (LIST_TO_SET (v_ys0 : ('b list)))) ==> (~(b_y IN (v_A0 : ('b set))))))``,
   entry "list_L8646_subset_code_3" 8646 "by auto" benchLib.Auto false []
     ``((((\b_coset_list : ('c list). COMPL (LIST_TO_SET b_coset_list) : 'c set) []) SUBSET (LIST_TO_SET [])) = F)``,
   entry "list_L8652_Ball_set" 8652 "by (simp add: list_all_iff)" benchLib.Simp false []
     ``((!b_set : 'a. (b_set IN (LIST_TO_SET (v_xs0 : ('a list)))) ==> ((v_P0 : ('a -> bool)) b_set)) = ((EVERY (v_P0 : ('a -> bool))) (v_xs0 : ('a list))))``,
   entry "list_L8656_Bex_set" 8656 "by (simp add: list_ex_iff)" benchLib.Simp false []
     ``((?b_set : 'a. (b_set IN (LIST_TO_SET (v_xs0 : ('a list)))) /\ ((v_P0 : ('a -> bool)) b_set)) = ((EXISTS (v_P0 : ('a -> bool))) (v_xs0 : ('a list))))``,
   entry "list_L8660_card_set" 8660 "by (simp add: length_remdups_card_conv)" benchLib.Simp false []
     ``((CARD (LIST_TO_SET (v_xs0 : ('a list)))) = (LENGTH (nub (v_xs0 : ('a list)))))``,
   entry "list_L8664_the_elem_set" 8664 "by simp" benchLib.Simp false []
     ``((CHOICE (LIST_TO_SET ((CONS (v_x0 : 'a)) []))) = (v_x0 : 'a))``,
   entry "list_L8687_product_code" 8687 "by (auto simp add: Product_Type.product_def)" benchLib.Auto false []
     ``((((\b_product_left : ('a set). \b_product_right : ('b set). \b_product_pair : ('a # 'b). FST b_product_pair IN b_product_left /\ SND b_product_pair IN b_product_right) (LIST_TO_SET (v_xs0 : ('a list)))) (LIST_TO_SET (v_ys0 : ('b list)))) = (LIST_TO_SET (FLAT ((MAP (\b_x : 'a. ((MAP (\b_y : 'b. (b_x,b_y))) (v_ys0 : ('b list))))) (v_xs0 : ('a list))))))``,
   entry "list_L8705_set_relcomp" 8705 "by simp (auto simp add: Bex_def image_def)" benchLib.Simp false []
     ``((((\b_relcomp_left : (('a # 'c) set). \b_relcomp_right : (('c # 'b) set). \b_relcomp_pair : ('a # 'b). ?b_relcomp_middle : 'c. (FST b_relcomp_pair,b_relcomp_middle) IN b_relcomp_left /\ (b_relcomp_middle,SND b_relcomp_pair) IN b_relcomp_right) (LIST_TO_SET (v_xys0 : (('a # 'c) list)))) (LIST_TO_SET (v_yzs0 : (('c # 'b) list)))) = (LIST_TO_SET (FLAT ((MAP (\b_xy : ('a # 'c). (FLAT ((MAP (\b_yz : ('c # 'b). (if ((SND b_xy) = (FST b_yz)) then ((CONS ((FST b_xy),(SND b_yz))) []) else []))) (v_yzs0 : (('c # 'b) list)))))) (v_xys0 : (('a # 'c) list))))))``,
   entry "list_L9013_list_all_transfer" 9013 "by blast" benchLib.Blast false []
     ``(((((\b_rel_left : (('a -> bool) -> (('b -> bool) -> bool)). \b_rel_right : ((('a list) -> bool) -> ((('b list) -> bool) -> bool)). \b_rel_left_function : (('a -> bool) -> (('a list) -> bool)). \b_rel_right_function : (('b -> bool) -> (('b list) -> bool)). !b_rel_x : ('a -> bool). !b_rel_y : ('b -> bool). b_rel_left b_rel_x b_rel_y ==> b_rel_right (b_rel_left_function b_rel_x) (b_rel_right_function b_rel_y)) (((\b_rel_left : ('a -> ('b -> bool)). \b_rel_right : (bool -> (bool -> bool)). \b_rel_left_function : ('a -> bool). \b_rel_right_function : ('b -> bool). !b_rel_x : 'a. !b_rel_y : 'b. b_rel_left b_rel_x b_rel_y ==> b_rel_right (b_rel_left_function b_rel_x) (b_rel_right_function b_rel_y)) (v_A0 : ('a -> ('b -> bool)))) (\b_equal_left : bool. \b_equal_right : bool. b_equal_left = b_equal_right))) (((\b_rel_left : (('a list) -> (('b list) -> bool)). \b_rel_right : (bool -> (bool -> bool)). \b_rel_left_function : (('a list) -> bool). \b_rel_right_function : (('b list) -> bool). !b_rel_x : ('a list). !b_rel_y : ('b list). b_rel_left b_rel_x b_rel_y ==> b_rel_right (b_rel_left_function b_rel_x) (b_rel_right_function b_rel_y)) (LIST_REL (v_A0 : ('a -> ('b -> bool))))) (\b_equal_left : bool. \b_equal_right : bool. b_equal_left = b_equal_right))) EVERY) EVERY)``
  ]

end
