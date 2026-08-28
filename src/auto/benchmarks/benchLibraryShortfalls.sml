structure benchLibraryShortfalls =
struct

(* Records for the list, map, option, string and product-type goals
   that the assigned tactic did not close in the 2026-08-25
   measurement.  The classification names the root cause and the note
   says what stands in the way.  A goal listed in [over_budget] was
   cut off by the budget rather than reporting no proof, so its
   classification is the family it belongs to rather than an observed
   residual. *)

(* Isabelle's [code_unfold] lemmas at List.thy:8259 and 8273 state that
   a set-encoded relation and its predicate encoding agree:
   [(xs, ys) : lexord r <-> lexordp (%x y. (x, y) : r) xs ys], and the
   same for [listrel1].  HOL4 encodes a relation one way only, so both
   sides of each translate to the same term and the source result has
   no HOL4 statement.  They carry no goal, and the corpus accounts for
   them here instead. *)
fun encoding_gap id line : benchLib.shortfall =
  {id = id, cause = benchLib.TranslationGap, date = "2026-08-25",
   note =
     "predicate and set encodings: the source result at List.thy:" ^
     Int.toString line ^ " relates Isabelle's set encoding of a " ^
     "relation to its predicate encoding, a distinction HOL4 does " ^
     "not make, so the translated statement is not the source result"}

val translation : benchLib.shortfall list =
  [encoding_gap "list_L8259_anon_L8259" 8259,
   encoding_gap "list_L8273_anon_L8273" 8273]

val over_budget =
  ["list_L1460_split_list_propE", "list_L1484_split_list_first_propE",
   "list_L1511_split_list_last_propE", "list_L1789_filter_eq_Cons_iff",
   "list_L1903_map_equality_iff", "list_L1921_in_set_conv_nth",
   "list_L2412_hd_drop_conv_nth", "list_L2576_dropWhile_id",
   "list_L3400_foldr_conv_foldl", "list_L3404_foldl_conv_foldr",
   "list_L3417_foldl_cong", "list_L3424_foldl_append",
   "list_L3434_foldl_map", "list_L3485_upt_conv_Cons",
   "list_L3506_hd_upt", "list_L3509_tl_upt", "list_L3635_upto_empty",
   "list_L3638_upto_single", "list_L3641_upto_Nil",
   "list_L3646_upto_rec1",
   "list_L4065_set_take_disj_set_drop_if_distinct",
   "list_L4406_distinct_adj_Cons_Cons", "list_L4628_extract_None_iff",
   "list_L4632_extract_SomeE", "list_L4645_extract_Cons_code",
   "list_L5044_takeWhile_replicate", "list_L5048_dropWhile_replicate",
   "list_L5325_bij_rotate1", "list_L5388_notin_set_nthsI",
   "list_L7998_listrel_rtrancl_refl",
   "list_L6138_map_sorted_distinct_set_unique",
   "list_L6669_sorted_key_list_of_set_eq_Nil_iff",
   "list_L6847_sorted_list_of_set_nonempty", "list_L8705_set_relcomp",
   "map_L723_ran_map_upd", "map_L730_ran_map_upd_Some",
   "map_L899_map_add_subsumed1", "product_type_L1031_SigmaE",
   "product_type_L1109_split_paired_Ball_Sigma",
   "product_type_L1133_Sigma_Union",
   "product_type_L1364_disjnt_Times1_iff",
   "product_type_L1367_disjnt_Times2_iff",
   "product_type_L1370_disjnt_Sigma_iff", "string_L34_of_char_Char",
   "string_L357_integer_of_char_code"]

fun record note id : benchLib.shortfall =
  {id = id, cause = benchLib.EngineLimitation, date = "2026-08-25",
   note =
     if List.exists (fn other => other = id) over_budget then
       note ^ " (the search did not return within the budget rather " ^
       "than reporting no proof)"
     else
       note}

fun classified classification note ids =
  map (record (classification ^ ": " ^ note)) ids

val conditional_list_rewrites =
  classified "conditional list rewrites"
    ("the residual is a conditional equation about TL, LAST, "
     ^ "FRONT, NULL, nub or dropWhile that the simpset does not "
     ^ "carry")
    ["list_L1010_tl_append_if", "list_L2100_last_ConsR",
     "list_L2141_in_set_butlast_appendI", "list_L2589_dropWhile_last",
     "list_L4481_insert_remdups", "list_L4642_extract_Nil_code",
     "list_L8603_is_empty_set"]

val congruence_rules =
  classified "congruence rules"
    ("the goal is a congruence rule for a list combinator and "
     ^ "the simpset carries no corresponding congruence")
    ["list_L1119_map_cong", "list_L3417_foldl_cong",
     "list_L8236_list_ex_cong"]

val interval_membership =
  classified "interval membership"
    ("membership in a GENLIST is not reduced to an arithmetic "
     ^ "bound")
    ["list_L1384_atMost_upto", "list_L1388_atLeast_upt",
     "list_L1392_greaterThanLessThan_upt",
     "list_L1396_atLeastLessThan_upt",
     "list_L1400_greaterThanAtMost_upt",
     "list_L1404_atLeastAtMost_upt", "list_L3566_map_nth_upt0",
     "list_L5140_map_fst_indexed_from",
     "list_L5144_map_snd_indexed_from",
     "list_L5163_nth_indexed_from_eq",
     "list_L5176_distinct_indexed_from",
     "list_L5180_indexed_from_append_eq",
     "list_L6433_sorted_indexed_from", "list_L6453_sorted_transpose"]

val emptiness_from_disjoint_membership =
  classified "emptiness from disjoint membership"
    ("the residual is [x = []] under hypotheses saying no element "
     ^ "of x occurs in either of two other lists; concluding it "
     ^ "needs induction on x, which the search does not perform")
    ["list_L1367_append_eq_append_conv_if_disj"]

val list_decomposition_witnesses =
  classified "list decomposition witnesses"
    ("the residual needs an existential witness splitting a list "
     ^ "at a member")
    ["list_L1415_in_set_conv_decomp",
     "list_L1590_concat_eq_append_conv", "list_L7823_append_listrel1I",
     "list_L8673_these_set_code"]

val instantiated_fact_citation =
  classified "instantiated fact citation"
    ("the source method instantiates its cited facts with [OF "
     ^ "...], [of ...] or [where ...]; the recipe compiler "
     ^ "represents a citation but not its instantiation")
    ["list_L1460_split_list_propE",
     "list_L1484_split_list_first_propE",
     "list_L1511_split_list_last_propE", "list_L2576_dropWhile_id",
     "list_L2806_zip_map1", "list_L2810_zip_map2",
     "list_L5301_nth_rotate1", "list_L6101_sorted_remove1",
     "list_L6202_sorted_same", "list_L6208_sorted_upt",
     "list_L6211_sorted_upto", "list_L6292_sorted_insort",
     "list_L6298_sorted_sort", "list_L6389_sorted_insort_insert"]

val zip_against_map =
  classified "zip against map"
    ("ZIP against MAP is not normalised")
    ["list_L1569_concat_injective", "list_L2751_zip_Cons1",
     "list_L2904_zip_eq_conv"]

val over_budget_with_no_residual =
  classified "over budget with no residual"
    ("the assigned tactic did not return within the budget")
    ["list_L1789_filter_eq_Cons_iff", "list_L1903_map_equality_iff",
     "list_L1921_in_set_conv_nth", "list_L2412_hd_drop_conv_nth",
     "list_L7998_listrel_rtrancl_refl", "map_L899_map_add_subsumed1",
     "list_L3400_foldr_conv_foldl", "list_L3404_foldl_conv_foldr",
     "list_L3424_foldl_append", "list_L3434_foldl_map",
     "list_L3485_upt_conv_Cons", "list_L3506_hd_upt",
     "list_L3509_tl_upt", "list_L3635_upto_empty",
     "list_L3638_upto_single", "list_L3641_upto_Nil",
     "list_L3646_upto_rec1",
     "list_L4065_set_take_disj_set_drop_if_distinct",
     "list_L4406_distinct_adj_Cons_Cons",
     "list_L4628_extract_None_iff", "list_L4632_extract_SomeE",
     "list_L4645_extract_Cons_code", "list_L5044_takeWhile_replicate",
     "list_L5048_dropWhile_replicate", "list_L5325_bij_rotate1",
     "list_L5388_notin_set_nthsI",
     "list_L6138_map_sorted_distinct_set_unique",
     "list_L6669_sorted_key_list_of_set_eq_Nil_iff",
     "list_L6847_sorted_list_of_set_nonempty",
     "list_L8705_set_relcomp", "map_L723_ran_map_upd",
     "map_L730_ran_map_upd_Some",
     "product_type_L1100_Collect_split_mono_strong",
     "product_type_L1133_Sigma_Union",
     "product_type_L1364_disjnt_Times1_iff",
     "product_type_L1367_disjnt_Times2_iff",
     "product_type_L1370_disjnt_Sigma_iff", "string_L34_of_char_Char",
     "string_L357_integer_of_char_code"]

val filter_normalisation =
  classified "filter normalisation"
    ("FILTER against a composed or negated predicate is not "
     ^ "normalised")
    ["list_L1838_partition_filter_conv",
     "list_L4762_length_removeAll_less",
     "list_L4906_inter_list_set_append"]

val indexing_through_list_constructors =
  classified "indexing through list constructors"
    ("the goal characterises a list operation by index, and the "
     ^ "residual is either an EL application whose list is built by "
     ^ "::, MAP, ZIP, LUPDATE, TAKE or DROP -- which the simpset does "
     ^ "not push EL through, so the two index forms never meet -- or "
     ^ "the index characterisation itself, which neither "
     ^ "simplification nor search reduces")
    ["list_L1856_nth_Cons_pos", "list_L2163_last_list_update",
     "list_L2480_take_update_cancel", "list_L2483_drop_update_cancel",
     "list_L2834_set_zip", "list_L3128_list_all2_map1",
     "list_L3132_list_all2_map2", "list_L3168_list_eq_iff_zip_eq",
     "list_L3919_bij_betw_nth", "list_L3925_set_update_distinct",
     "list_L6487_nth_nth_transpose_sorted",
     "list_L6873_nth_sorted_list_of_set_greaterThanAtMost",
     "list_L7954_listrel_iff_nth", "list_L7978_listrel_sym"]

val simplification_and_search_reports_no_proof =
  classified "simplification and search reports no proof"
    ("the clasimp method terminates and reports no proof")
    ["list_L2178_snoc_eq_iff_butlast", "list_L2814_map_zip_map",
     "list_L2818_map_zip_map2", "list_L4637_extract_Some_iff",
     "list_L4707_foldr_fold_remove1",
     "list_L4781_foldr_fold_removeAll", "list_L5409_nths_drop",
     "list_L6839_sorted_list_of_set_atMost_Suc", "list_L7247_lex_conv",
     "list_L7321_lex_append_rightI",
     "list_L8044_listrel1_subset_listrel",
     "list_L8999_set_Cons_transfer", "map_L519_map_upds_twist",
     "map_L565_dom_eq_empty_conv", "map_L810_graph_map_add",
     "product_type_L1097_Collect_case_prod_mono",
     "string_L178_card_UNIV_char"]

val take_and_drop_arithmetic =
  classified "take and drop arithmetic"
    ("the residual is a TAKE or DROP identity whose side "
     ^ "condition is arithmetic the simpset does not discharge")
    ["list_L2396_butlast_take", "list_L2400_butlast_drop",
     "list_L2403_take_butlast", "list_L2406_drop_butlast"]

val list_relation_lifting =
  classified "list relation lifting"
    ("LIST_REL and LLEX carry no claset rules and SHORTLEX carries "
     ^ "only its two length rules, so the goal is never decomposed")
    ["list_L3089_list_all2_appendI",
     "list_L7995_equiv_listrel", "list_L7256_lenlex_conv",
     "list_L7401_lexord_append_leftD", "list_L7508_lexord_trans",
     "list_L7570_asym_lenlex", "list_L7922_wf_listrel1_iff",
     "list_L9009_null_transfer"]

val fold_direction =
  classified "fold direction"
    ("the translation renders foldr as FOLDL over REVERSE and "
     ^ "nothing relates the two")
    ["list_L3340_inter_coset_fold", "list_L3381_anon_L3381",
     "list_L3385_anon_L3385", "list_L3413_foldr_cong",
     "list_L3421_foldr_append", "list_L3427_foldr_map",
     "list_L3430_foldr_filter"]

val finite_cardinality =
  classified "finite cardinality"
    ("the residual is a CARD identity over a finite set built "
     ^ "from a list")
    ["list_L4011_length_remdups_concat",
     "list_L6770_sorted_key_list_of_set_unique"]

val propositional_rearrangement =
  classified "propositional rearrangement"
    ("the residual is a propositional rearrangement the "
     ^ "simplifier does not orient; Isabelle's simplifier orders "
     ^ "such equations by its term order")
    ["list_L5001_in_set_replicate", "list_L5008_Ball_set_replicate",
     "list_L5012_Bex_set_replicate", "option_L111_map_option_eq_Some"]

val sorted_against_sorted_wrt =
  classified "SORTED against sorted_wrt"
    ("Isabelle's sorted is sorted_wrt (<=) by definition; HOL4's "
     ^ "SORTED is the adjacent-pairs predicate and the bridge "
     ^ "needs transitivity, a step the source method never names")
    ["list_L412_sorted_simps_2", "list_L415_strict_sorted_simps_2",
     "list_L5946_sorted_wrt_dropWhile", "list_L5964_sorted_wrt01",
     "list_L6034_sorted_append", "list_L6038_sorted_map",
     "list_L6042_sorted01", "list_L6049_sorted_iff_nth_mono_less",
     "list_L6053_sorted_iff_nth_mono", "list_L6057_sorted_nth_mono",
     "list_L6061_sorted_iff_nth_Suc", "list_L6104_sorted_butlast",
     "list_L6146_sorted_dropWhile",
     "list_L6384_sorted_insort_insert_key", "list_L6761_anon_L6761"]

val characterisation_is_the_goal =
  classified "characterisation is the goal"
    ("the HOL4 theorem that is this goal -- the one the Isabelle "
     ^ "method cites, or one the simpset carries, or one a seed file "
     ^ "declares -- is excluded by A1, up to the orientation of an "
     ^ "equation or an equivalence or the unfolding of a constant the "
     ^ "translation introduces, and the assigned tactic has no second "
     ^ "route")
    ["list_L6444_stable_sort_key_sort_key", "list_L7318_lenlex_length",
     "list_L8167_list_all_iff",
     "list_L8642_image_set", "list_L8660_card_set",
     "list_L8683_can_select_set_list_ex1",
     "option_L361_equal_None_code_unfold_1", "string_L728_anon_L728"]

val predicate_and_set_representation =
  classified "predicate and set representation"
    ("the translation writes a set as a lambda and membership as "
     ^ "application; the assigned tactic does not identify (\x. F) "
     ^ "with EMPTY, (\x. t x) with t, or x IN P with P x")
    ["list_L8638_filter_set", "map_L346_map_add_empty",
     "map_L578_dom_empty", "map_L786_graph_empty",
     "option_L288_these_empty",
     "product_type_L1094_Collect_case_prodD",
     "product_type_L1184_sing_Times_sing",
     "product_type_L469_cond_case_prod_eta",
     "product_type_L600_case_prodI2_", "product_type_L785_curry_conv",
     "product_type_L797_curry_case_prod",
     "product_type_L800_case_prod_curry"]

val pair_membership_after_flattening =
  classified "pair membership after flattening"
    ("membership of a pair in a flattened list of maps is not "
     ^ "reduced")
    ["list_L7054_set_trans_list_step_subset_trancl",
     "list_L8687_product_code", "list_L8691_Id_on_set"]

val blast_search_reports_no_proof =
  classified "blast search reports no proof"
    ("the tableau search exhausts its depths without a "
     ^ "reconstructible proof")
    ["list_L4319_successively_nth", "list_L4326_distinct_adj_nth",
     "list_L4450_distinct_adj_map_iff", "list_L7771_wf_measures",
     "list_L7861_listrel1_converse", "list_L8006_listrel_Nil",
     "list_L9013_list_all_transfer", "map_L789_in_graphI",
     "map_L792_in_graphD", "map_L828_finite_graph_map_of",
     "option_L59_split_option_ex"]

val integer_interval =
  classified "integer interval"
    ("source_upto is unfolded but its recursion is not")
    ["list_L3683_upto_split2", "list_L3687_upto_split3",
     "list_L3695_upto_aux_rec"]

val rotation_by_iteration =
  classified "rotation by iteration"
    ("rotate_def unfolds to FUNPOW and nothing reduces the "
     ^ "iteration")
    ["list_L5191_rotate0", "list_L5194_rotate_Suc",
     "list_L5197_rotate_add", "list_L5207_rotate1_rotate_swap",
     "list_L5241_rotate_conv_mod", "list_L5244_rotate_id",
     "list_L5259_rotate_map"]

val index_selection =
  classified "index selection"
    ("nths_def unfolds and the comprehension over indices it "
     ^ "exposes is not reduced")
    ["list_L5334_nths_empty", "list_L5344_length_nths",
     "list_L5385_set_nths_subset", "list_L5391_in_set_nthsD"]

val decision_procedure_scope =
  classified "decision procedure scope"
    ("the goal is outside what the HOL4 counterpart of the cited "
     ^ "decision procedure decides")
    ["list_L6315_sort_replicate",
     "list_L6835_sorted_list_of_set_lessThan_Suc"]

val definitional_unfolding_stops_short =
  classified "definitional unfolding stops short"
    ("the cited definition unfolds one constant and nothing "
     ^ "reduces what it exposes")
    ["list_L5441_distinct_set_subseqs", "list_L5470_subset_subseqs",
     "list_L5527_Nil_in_shufflesI",
     "list_L6367_insort_insert_insort_key", "list_L8247_anon_L8247",
     "list_L8543_map_filter_map_filter",
     "list_L8701_trancl_set_ntrancl"]

val injectivity_and_surjectivity =
  classified "injectivity and surjectivity"
    ("the residual is an INJ, SURJ or BIJ claim the assigned "
     ^ "tactic does not decompose")
    ["list_L6690_distinct_if_distinct_map",
     "product_type_L1329_bij_betw_map_prod",
     "product_type_L988_bij_swap"]

val finite_map_update =
  classified "finite map update"
    ("map_upds_def unfolds to an ALOOKUP over a reversed zip and "
     ^ "nothing reduces it")
    ["map_L372_map_add_upds", "map_L467_map_upds_Nil1",
     "map_L470_map_upds_Nil2", "map_L473_map_upds_Cons",
     "map_L776_ran_map_of_zip"]

val option_relations =
  classified "option relations"
    ("OPTREL and the option-set constructions carry no claset "
     ^ "rules")
    ["option_L317_these_empty_eq", "option_L320_these_not_empty_eq",
     "option_L337_option_bind_transfer",
     "option_L361_equal_None_code_unfold_2"]

val character_arithmetic =
  classified "character arithmetic"
    ("the residual is modular arithmetic on character codes; "
     ^ "HOL4's char is a numeral typedef and the source proof "
     ^ "reasons about bits")
    ["string_L344_char_of_integer_code",
     "string_L60_char_of_take_bit_eq",
     "string_L68_char_of_comp_of_char"]

val sigma_and_times_rule_forms =
  classified "Sigma and Times rule forms"
    ("Isabelle states these about the constant Sigma, whose claset "
     ^ "carries SigmaI, SigmaE and mem_Sigma_iff; the translation "
     ^ "inlines the definition, so the goal reaching HOL4 is about "
     ^ "FST and SND of an explicit pair, and a claset rule is about "
     ^ "a formula rather than a projection")
    ["product_type_L1028_SigmaI", "product_type_L1031_SigmaE",
     "product_type_L1040_SigmaD1", "product_type_L1043_SigmaD2",
     "product_type_L1046_SigmaE2",
     "product_type_L1073_mem_Sigma_iff",
     "product_type_L1082_Times_subset_cancel2",
     "product_type_L1085_Times_eq_cancel2",
     "product_type_L1088_Collect_case_prod_Sigma",
     "product_type_L1109_split_paired_Ball_Sigma",
     "product_type_L1112_split_paired_Bex_Sigma",
     "product_type_L688_The_split_eq"]

val execution : benchLib.shortfall list =
  conditional_list_rewrites @
  congruence_rules @
  interval_membership @
  emptiness_from_disjoint_membership @
  list_decomposition_witnesses @
  instantiated_fact_citation @
  zip_against_map @
  over_budget_with_no_residual @
  filter_normalisation @
  indexing_through_list_constructors @
  simplification_and_search_reports_no_proof @
  take_and_drop_arithmetic @
  list_relation_lifting @
  fold_direction @
  finite_cardinality @
  propositional_rearrangement @
  sorted_against_sorted_wrt @
  characterisation_is_the_goal @
  predicate_and_set_representation @
  pair_membership_after_flattening @
  blast_search_reports_no_proof @
  integer_interval @
  rotation_by_iteration @
  index_selection @
  decision_procedure_scope @
  definitional_unfolding_stops_short @
  injectivity_and_surjectivity @
  finite_map_update @
  option_relations @
  character_arithmetic @
  sigma_and_times_rule_forms

end
