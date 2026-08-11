structure benchSetShortfalls =
struct

(* Exact negative results from the mapped-tactic gate.  Entries marked as
   timeouts were separately rerun at the production 30-second budget. *)
val entries : benchLib.shortfall list =
  [
   {id =
      "set_theory_L36",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_theory_L40",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_theory_L44",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_theory_L48",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_theory_L79",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_theory_L164",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_theory_L168",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_theory_L172",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_theory_L180",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_theory_L184",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_theory_L199",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L108_Collect_eqI",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L421_ball_triv",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L425_bex_triv",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L429_bex_triv_one_point1",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L432_bex_triv_one_point2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L435_bex_one_point1",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L438_bex_one_point2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L466_bex_cong",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L572_empty_subsetI",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L579_equals0D",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L651_Pow_not_empty",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L675_Compl_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L687_Int_def",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L690_Int_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L714_Un_def",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L717_Un_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L733_insert_def",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L758_set_diff_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L796_insert_ident",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L842_singleton_insert_inj_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L851_subset_singleton_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L857_singleton_conv",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L860_singleton_conv2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L869_doubleton_eq_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L872_Un_singleton_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L875_singleton_Un_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L910_image_subsetI",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L915_image_subset_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L928_subset_image_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L931_image_ident",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L958_image_Collect",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L982_Setcompr_eq_image",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L985_setcompr_eq_image",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L988_ball_imageD",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1013_range_eqI",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1016_rangeI",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1031_range_constant",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1034_range_eq_singletonD",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1088_psubsetE",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1091_psubset_insert_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1113_psubset_imp_ex_mem",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1122_image_Pow_mono",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1125_image_Pow_surj",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1172_Diff_subset_conv",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1192_Collect_empty_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1195_empty_Collect_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1198_Collect_neg_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1201_Collect_disj_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1204_Collect_imp_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1207_Collect_conj_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1210_Collect_conj_eq2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1213_Collect_mono_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1245_insert_Collect",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1251_insert_disjoint_1",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1251_insert_disjoint_2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1294_disjoint_eq_subset_Compl",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1297_disjoint_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1300_disjoint_iff_not_equal",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1321_Int_Collect",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1366_Un_insert_right",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1393_Un_Int_crazy",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1448_subset_Compl_self_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1451_Un_Int_assoc_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1499_Diff_triv",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1540_Diff_partition",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1543_double_diff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1546_Un_Diff_cancel",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1555_Diff_Int",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1558_Diff_Diff_Int",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1561_Un_Diff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1587_all_bool_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1593_ex_bool_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1604_Pow_singleton_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1610_Pow_Compl",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1628_Int_Diff_Un",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1637_subset_iff_psubset_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1640_all_not_in_conv",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1643_ex_in_conv",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1646_ball_simps_8",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1659_bex_simps_6",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1722_Collect_mono",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1725_Int_Collect_mono",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1758_vimage_empty",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1764_vimage_Un",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1770_vimage_Collect_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1773_vimage_Collect",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1790_vimage_image_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1793_image_vimage_subset",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1796_image_vimage_eq",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1799_image_subset_iff_subset_vimage",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1870_bind_bind",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1874_empty_bind",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1967_pairwise_image",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1976_disjnt_commute",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1979_disjnt_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1982_disjnt_sym",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1988_disjnt_insert1",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1991_disjnt_insert2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1994_disjnt_subset1",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1997_disjnt_subset2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L2003_disjnt_Un2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L2006_disjnt_Diff1",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L2006_disjnt_Diff2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L2012_pairwise_disjnt_iff",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L563_empty_def",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L595_UNIV_def",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L627_empty_not_UNIV",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L968_image_cong",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1256_disjoint_insert_1",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1256_disjoint_insert_2",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"},
   {id =
      "set_L1505_Diff_empty",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic terminated without a proof on the exact " ^
           "translated Isabelle goal"},
   {id =
      "set_L1607_Pow_insert",
    cause = benchLib.EngineLimitation,
    date = "2026-08-11",
    note = "mapped tactic exceeded the 30-second family budget on " ^
           "the exact translated Isabelle goal"}
  ]

end
