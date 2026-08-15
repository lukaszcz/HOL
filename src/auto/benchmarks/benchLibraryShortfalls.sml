structure benchLibraryShortfalls =
struct

val translation : benchLib.shortfall list =
  []

val execution : benchLib.shortfall list =
  map
    (fn id =>
      {id = id, cause = benchLib.EngineLimitation,
       date = "2026-08-15",
       note = "assigned tactic does not close without a direct analogue"})
    ["list_L5241_rotate_conv_mod",
     "list_L5409_nths_drop",
     "list_L6101_sorted_remove1",
     "list_L6104_sorted_butlast",
     "list_L6138_map_sorted_distinct_set_unique",
     "list_L6146_sorted_dropWhile",
     "list_L6211_sorted_upto",
     "list_L6292_sorted_insort",
     "list_L6298_sorted_sort",
     "list_L6312_sorted_sort_id",
     "list_L6315_sort_replicate",
     "list_L6384_sorted_insort_insert_key",
     "list_L6389_sorted_insort_insert",
     "list_L6433_sorted_indexed_from",
     "list_L6444_stable_sort_key_sort_key",
     "list_L6453_sorted_transpose",
     "list_L6487_nth_nth_transpose_sorted",
     "list_L6690_distinct_if_distinct_map",
     "list_L6761_anon_L6761",
     "list_L6770_sorted_key_list_of_set_unique",
     "list_L6835_sorted_list_of_set_lessThan_Suc",
     "list_L6839_sorted_list_of_set_atMost_Suc",
     "list_L6847_sorted_list_of_set_nonempty",
     "list_L6873_nth_sorted_list_of_set_greaterThanAtMost",
     "list_L3349_anon_L3349",
     "list_L3381_anon_L3381",
     "list_L3385_anon_L3385",
     "list_L5527_Nil_in_shufflesI",
     "list_L5470_subset_subseqs",
     "list_L5441_distinct_set_subseqs",
     "list_L6972_mono_lists",
     "list_L8673_these_set_code",
     "list_L8701_trancl_set_ntrancl",
     "list_L7922_wf_listrel1_iff",
     "list_L7771_wf_measures",
     "list_L7247_lex_conv",
     "list_L7256_lenlex_conv",
     "list_L7387_lexord_same_pref_if_irrefl",
     "list_L7508_lexord_trans",
     "list_L7537_lexord_irrefl",
     "list_L7570_asym_lenlex",
     "list_L7716_lexordp_conv_lexord",
     "list_L7752_lexordp_eq_conv_lexord",
     "list_L7054_set_trans_list_step_subset_trancl",
     "list_L7954_listrel_iff_nth",
     "list_L7995_equiv_listrel",
     "list_L8259_anon_L8259",
     "list_L8273_anon_L8273",
     "list_L8709_wf_set",
     "list_L8999_set_Cons_transfer"]

end
