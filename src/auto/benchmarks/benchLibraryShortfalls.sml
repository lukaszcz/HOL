structure benchLibraryShortfalls =
struct

(* Records for the list, map, option, string and product-type goals
   that the assigned tactic did not close in the 2026-08-28
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
  {id = id, cause = benchLib.TranslationGap, date = "2026-08-28",
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
   "list_L1921_in_set_conv_nth",
   "list_L4065_set_take_disj_set_drop_if_distinct",
   "list_L4406_distinct_adj_Cons_Cons",
   "list_L4632_extract_SomeE",
   "list_L5325_bij_rotate1", "list_L7998_listrel_rtrancl_refl",
   "list_L6138_map_sorted_distinct_set_unique",
   "list_L6669_sorted_key_list_of_set_eq_Nil_iff",
   "list_L6847_sorted_list_of_set_nonempty",
   "list_L7861_listrel1_converse",
   "list_L8044_listrel1_subset_listrel", "list_L8705_set_relcomp",
   "list_L9013_list_all_transfer",
   "map_L723_ran_map_upd", "map_L730_ran_map_upd_Some",
   "map_L899_map_add_subsumed1", "product_type_L1031_SigmaE",
   "product_type_L1109_split_paired_Ball_Sigma",
   "product_type_L1133_Sigma_Union",
   "string_L34_of_char_Char",
   "string_L357_integer_of_char_code"]

fun record note id : benchLib.shortfall =
  {id = id, cause = benchLib.EngineLimitation, date = "2026-08-28",
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
     "list_L4481_insert_remdups", "list_L8603_is_empty_set"]

val congruence_rules =
  classified "congruence rules"
    ("the goal is a congruence rule for a list combinator and "
     ^ "the simpset carries no corresponding congruence")
    ["list_L1119_map_cong", "list_L8236_list_ex_cong"]

val prefix_from_its_indices =
  classified "prefix from its indices"
    ("the residual is [GENLIST (\\index. EL index xs) count = TAKE "
     ^ "count xs]; rebuilding a prefix out of the indices it is "
     ^ "read at is not a rewrite either simpset carries")
    ["list_L3566_map_nth_upt0"]

val distinctness_through_a_zip =
  classified "distinctness through a zip"
    ("the residual is ALL_DISTINCT of a ZIP whose first column is "
     ^ "an interval; distinctness of the pairs does not reduce to "
     ^ "distinctness of that column by rewriting")
    ["list_L5176_distinct_indexed_from"]

val zip_over_an_append =
  classified "zip over an append"
    ("the residual needs the interval of length [LENGTH xs + LENGTH "
     ^ "ys] split into the two intervals the two ZIPs consume, a "
     ^ "rewrite whose direction depends on the lengths")
    ["list_L5180_indexed_from_append_eq"]

val transpose_column_lengths =
  classified "transpose column lengths"
    ("the residual is that the column lengths of a transpose "
     ^ "decrease; it holds because the number of rows reaching an "
     ^ "index falls as the index grows, which is an induction "
     ^ "rather than a rewrite")
    ["list_L6453_sorted_transpose"]

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
    ["list_L7823_append_listrel1I", "list_L8673_these_set_code"]

(* Re-measured at ten times the budget: all three still return nothing.
   The citation they were filed under is not what stands in the way --
   [OF assms] discharges a premise from the goal's own assumption and
   each resolves.  What is left is the search. *)
val search_returns_nothing_at_ten_times_the_budget =
  classified "search returns nothing at ten times the budget"
    ("the cited facts resolve and are supplied, and the assigned "
     ^ "search returns neither a proof nor a residual in 300 "
     ^ "seconds")
    ["list_L1460_split_list_propE",
     "list_L1484_split_list_first_propE",
     "list_L1511_split_list_last_propE"]

(* Diagnosed: a fact reaches a goal as an inserted premise, and a
   premise's type variables are fixed -- only its term variables can be
   specialised.  So an instantiated citation applies exactly when its
   type variables already coincide with the goal's, which they do when
   the instantiating term is matched against the theorem as written and
   need not when it is not.  [zip_map_map] uses the identity's own type
   variable for an unrelated component, so its instance comes out
   narrower than the citation warrants; renaming the term's type
   variables apart makes the instance correct and then unusable, and
   was measured at four goals lost and none gained.  The fix is to
   instantiate a supplied fact's types against the goal where facts are
   supplied, not in the name table. *)
val instantiated_fact_not_applied =
  classified "instantiated fact not applied"
    ("the instantiated citation reaches the goal as a premise, whose "
     ^ "type variables are fixed; the instance is narrower than the "
     ^ "citation because the identity shares a type variable with an "
     ^ "unrelated component of the cited theorem")
    ["list_L2806_zip_map1", "list_L2810_zip_map2"]

val zip_against_map =
  classified "zip against map"
    ("ZIP against MAP is not normalised")
    ["list_L1569_concat_injective", "list_L2751_zip_Cons1"]

val over_budget_with_no_residual =
  classified "over budget with no residual"
    ("the assigned tactic did not return within the budget")
    ["list_L1789_filter_eq_Cons_iff", "list_L1921_in_set_conv_nth",
     "list_L7998_listrel_rtrancl_refl", "map_L899_map_add_subsumed1",
     "list_L4065_set_take_disj_set_drop_if_distinct",
     "list_L4406_distinct_adj_Cons_Cons",
     "list_L4632_extract_SomeE", "list_L5325_bij_rotate1",
     "list_L6138_map_sorted_distinct_set_unique",
     "list_L6669_sorted_key_list_of_set_eq_Nil_iff",
     "list_L6847_sorted_list_of_set_nonempty",
     "list_L8705_set_relcomp", "map_L723_ran_map_upd",
     "map_L730_ran_map_upd_Some",
     "product_type_L1133_Sigma_Union", "string_L34_of_char_Char",
     "string_L357_integer_of_char_code"]

val arithmetic_residual_after_unfolding =
  classified "arithmetic residual after unfolding"
    ("the interval equation unfolds now that the conditional "
     ^ "congruence is the weak one, and what is left is a linear "
     ^ "arithmetic fact about num -- [~(m < n) ==> ~(SUC m < n)] and "
     ^ "[!i j. j < i ==> ~(i <= j)].  The assigned simp method carries "
     ^ "linarith as a side-condition solver, which discharges the "
     ^ "conditions of conditional rewrites and not the goal it is left "
     ^ "with")
    ["list_L3509_tl_upt", "list_L3646_upto_rec1"]

(* Isabelle beta-normalises the instance of a rewrite's right-hand side,
   so the shape below cannot arise there whatever its congruences do. *)
val beta_redex_in_a_branch =
  classified "beta redex in a branch"
    ("unfolding the definition leaves [(\\k. if k IN D then "
     ^ "(\\x. NONE) k else NONE) = (\\x. NONE)], whose then-branch "
     ^ "holds an uncontracted redex.  The weak conditional congruence "
     ^ "does not enter a branch, so the redex stays, and COND_ID never "
     ^ "meets the [if c then NONE else NONE] it would close.  HOL4 "
     ^ "contracts a redex where its traversal reaches one; recovering "
     ^ "this would mean beta-normalising rewrite instantiation, which "
     ^ "is the simplifier's own business rather than this layer's")
    ["map_L420_restrict_map_empty"]

val filter_normalisation =
  classified "filter normalisation"
    ("FILTER against a composed or negated predicate is not "
     ^ "normalised")
    ["list_L1838_partition_filter_conv",
     "list_L4762_length_removeAll_less",
     "list_L4906_inter_list_set_append"]

val indexing_through_list_constructors =
  classified "indexing through list constructors"
    ("the goal characterises a list operation by index.  The "
     ^ "simpset pushes EL through MAP, ZIP, LUPDATE, TAKE and DROP, "
     ^ "so what is left is a constructor it does not push EL "
     ^ "through -- :: against an index written [n - 1] or [PRE n] -- "
     ^ "a side condition on one of those rules that the goal does "
     ^ "not supply, or the index characterisation itself, which "
     ^ "neither simplification nor search reduces")
    ["list_L1856_nth_Cons_pos", "list_L2163_last_list_update",
     "list_L2480_take_update_cancel", "list_L2483_drop_update_cancel",
     "list_L2834_set_zip", "list_L3168_list_eq_iff_zip_eq",
     "list_L3919_bij_betw_nth",
     "list_L6487_nth_nth_transpose_sorted",
     "list_L6873_nth_sorted_list_of_set_greaterThanAtMost",
     "list_L7978_listrel_sym"]

val simplification_and_search_reports_no_proof =
  classified "simplification and search reports no proof"
    ("the clasimp method terminates and reports no proof")
    ["list_L2178_snoc_eq_iff_butlast", "list_L2814_map_zip_map",
     "list_L2818_map_zip_map2",
     "list_L4707_foldr_fold_remove1",
     "list_L4781_foldr_fold_removeAll", "list_L5409_nths_drop",
     "list_L7247_lex_conv",
     "list_L7321_lex_append_rightI",
     "list_L8044_listrel1_subset_listrel",
     "list_L8999_set_Cons_transfer", "map_L519_map_upds_twist",
     "string_L178_card_UNIV_char"]

val take_and_drop_arithmetic =
  classified "take and drop arithmetic"
    ("the residual is a TAKE or DROP identity whose side "
     ^ "condition is arithmetic the simpset does not discharge")
    ["list_L2396_butlast_take", "list_L2400_butlast_drop",
     "list_L2403_take_butlast", "list_L2406_drop_butlast"]

val list_relation_lifting =
  classified "list relation lifting"
    ("the declared rules take a LIST_REL apart at a nil, a cons or a "
     ^ "REVERSE, and trade a SHORTLEX for a length comparison; these "
     ^ "goals are about the relation as a whole -- an append, a "
     ^ "transitivity chain, asymmetry, well-foundedness, an "
     ^ "equivalence, or NULL carried across -- and need an induction "
     ^ "over the list rather than a rule application")
    ["list_L3089_list_all2_appendI",
     "list_L7995_equiv_listrel", "list_L7256_lenlex_conv",
     "list_L7401_lexord_append_leftD", "list_L7508_lexord_trans",
     "list_L7570_asym_lenlex", "list_L7922_wf_listrel1_iff",
     "list_L9009_null_transfer"]

(* The earlier reading -- that the translation renders foldr as FOLDL
   over REVERSE -- was wrong: [source_foldr] is FOLDR.  The FOLDL over
   a REVERSE arrives from the cited [foldr_conv_fold], which is what
   Isabelle's own proofs rewrite with. *)
val fold_direction =
  classified "fold direction"
    ("the cited foldr_conv_fold rewrites the goal into a FOLDL over "
     ^ "a REVERSE, which is where Isabelle's proof continues into its "
     ^ "fold lemmas; the HOL4 fold law that would close each residual "
     ^ "is either declared to no simpset or, for the append law, the "
     ^ "goal itself, which rule A1 withholds")
    ["list_L3421_foldr_append", "list_L3427_foldr_map",
     "list_L3430_foldr_filter"]

val fold_against_a_set_aggregate =
  classified "fold against a set aggregate"
    ("the goal relates a set-valued aggregate to a fold over any list "
     ^ "with that set, and the residual still carries the aggregate: "
     ^ "nothing turns the hypothesis about every list into the "
     ^ "instance the goal needs")
    ["list_L3340_inter_coset_fold", "list_L3381_anon_L3381",
     "list_L3385_anon_L3385"]

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

(* [source_sorted] is now [source_sorted_wrt], and the ambient bridge
   has crossed: every residual below is stated on HOL4's own adjacent
   SORTED, with nothing of the all-pairs reading left in it.  So the
   class is no longer about the two readings at all -- it is what the
   engine cannot do with SORTED once it has it. *)
val sortedness_beyond_the_bridge =
  classified "sortedness beyond the bridge"
    ("the residual is stated on HOL4's adjacent SORTED, so the "
     ^ "ambient bridge has crossed; what is left is a fact about "
     ^ "SORTED itself -- an order step between two of its members, "
     ^ "or its closure under a list operation, which needs an "
     ^ "induction the search does not perform")
    ["list_L415_strict_sorted_simps_2",
     "list_L6053_sorted_iff_nth_mono", "list_L6104_sorted_butlast",
     "list_L6384_sorted_insort_insert_key", "list_L6761_anon_L6761"]

val numeral_against_Suc =
  classified "numeral against Suc"
    ("the residual has the same successor in both spellings -- "
     ^ "[1 + index] on one side and [SUC index] on the other -- and "
     ^ "neither is HOL4's normal form for the other, so the cited "
     ^ "fact stands in the assumptions stating the goal it was cited "
     ^ "for")
    ["list_L5301_nth_rotate1"]

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
     ^ "application; the assigned tactic does not identify (\x. t x) "
     ^ "with t, or x IN P with P x")
    ["list_L8638_filter_set",
     "product_type_L1184_sing_Times_sing",
     "product_type_L469_cond_case_prod_eta",
     "product_type_L600_case_prodI2_", "product_type_L785_curry_conv",
     "product_type_L797_curry_case_prod"]

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
    ["list_L7771_wf_measures",
     "list_L7861_listrel1_converse", "list_L8006_listrel_Nil",
     "list_L9013_list_all_transfer",
     "map_L828_finite_graph_map_of",
     "option_L59_split_option_ex"]

val integer_interval_emptiness =
  classified "integer interval emptiness"
    ("the residual is [j < i ==> source_upto i j = []], which the "
     ^ "source method does not name and no simpset carries")
    ["list_L3695_upto_aux_rec"]

val rotation_by_iteration =
  classified "rotation by iteration"
    ("rotate_def unfolds to FUNPOW and nothing reduces the "
     ^ "iteration")
    ["list_L5191_rotate0", "list_L5194_rotate_Suc",
     "list_L5197_rotate_add", "list_L5207_rotate1_rotate_swap"]

val decision_procedure_scope =
  classified "decision procedure scope"
    ("the goal is outside what the HOL4 counterpart of the cited "
     ^ "decision procedure decides: the cited facts are supplied and "
     ^ "the procedure rejects what is left of the goal")
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
     "map_L470_map_upds_Nil2", "map_L473_map_upds_Cons"]

val option_relations =
  classified "option relations"
    ("OPTREL and the option-set constructions carry no claset "
     ^ "rules")
    ["option_L317_these_empty_eq", "option_L320_these_not_empty_eq",
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
    ("the translation inlines Sigma, so the goal reaching HOL4 is "
     ^ "about FST and SND of an explicit pair; the engines reduce a "
     ^ "projection applied to a pair, and these two are what is left "
     ^ "-- the search reports no proof rather than running out of "
     ^ "budget")
    ["product_type_L1088_Collect_case_prod_Sigma",
     "product_type_L688_The_split_eq"]

(* Four of what used to be one class are budget, not shape: each
   returns nothing within the budget rather than reporting no proof,
   so what stands in the way is not established.  Two of them --
   split_paired_Ball_Sigma and its Bex twin -- relate a quantifier over
   a pair to quantifiers over its components, which Isabelle decides
   with split_paired_All. *)
val sigma_over_budget =
  classified "Sigma over budget"
    ("the goal is about a quantifier or a subset over an inlined "
     ^ "Sigma and the search does not return within the budget")
    ["product_type_L1031_SigmaE",
     "product_type_L1082_Times_subset_cancel2",
     "product_type_L1109_split_paired_Ball_Sigma",
     "product_type_L1112_split_paired_Bex_Sigma"]

(* Eight goals the corrected circularity guard newly withholds a rule
   from, all in the [characterisation is the goal] class above and
   dated to the measurement that found them.  Seven are one conjunct of
   a conjunctive rule -- [listTheory.EL], [ZIP], [LIST_REL_NIL],
   [EVERY_DEF], [EXISTS_DEF] and the translation's own
   [source_measures_def], which the cited method unfolds -- and the
   simpset splits each into a rewrite that is the goal.  The eighth is
   [listTheory.SHORTLEX_NIL2], which is the goal once the translation
   of [lenlex] is unfolded; the guard used to compare a rule's
   conclusion against the goal with the goal's quantifier prefix still
   on, so neither reading matched. *)
val a_reading_of_the_characterisation_is_the_goal =
  map
    (fn id =>
      {id = id, cause = benchLib.EngineLimitation, date = "2026-09-03",
       note =
         "a reading of the characterisation is the goal: the HOL4 " ^
         "rule that reaches this goal states it as one conjunct of a " ^
         "conjunction, or states it with its quantifiers in another " ^
         "order, and A1 withholds it under either reading; the " ^
         "assigned tactic has no second route"} : benchLib.shortfall)
    ["list_L1851_nth_Cons_Suc", "list_L2740_zip_Cons_Cons",
     "list_L3014_list_all2_Nil", "list_L3017_list_all2_Nil2",
     "list_L7300_Nil_lenlex_iff2", "list_L7775_in_measures_2",
     "list_L8187_list_all_Cons_iff", "list_L8195_list_ex_Cons_iff"]

val execution : benchLib.shortfall list =
  conditional_list_rewrites @
  congruence_rules @
  prefix_from_its_indices @
  distinctness_through_a_zip @
  zip_over_an_append @
  transpose_column_lengths @
  emptiness_from_disjoint_membership @
  list_decomposition_witnesses @
  search_returns_nothing_at_ten_times_the_budget @
  instantiated_fact_not_applied @
  zip_against_map @
  over_budget_with_no_residual @
  arithmetic_residual_after_unfolding @
  beta_redex_in_a_branch @
  filter_normalisation @
  indexing_through_list_constructors @
  simplification_and_search_reports_no_proof @
  take_and_drop_arithmetic @
  list_relation_lifting @
  fold_direction @
  fold_against_a_set_aggregate @
  finite_cardinality @
  propositional_rearrangement @
  sortedness_beyond_the_bridge @
  numeral_against_Suc @
  characterisation_is_the_goal @
  predicate_and_set_representation @
  pair_membership_after_flattening @
  blast_search_reports_no_proof @
  integer_interval_emptiness @
  rotation_by_iteration @
  decision_procedure_scope @
  definitional_unfolding_stops_short @
  injectivity_and_surjectivity @
  finite_map_update @
  option_relations @
  character_arithmetic @
  sigma_and_times_rule_forms @
  sigma_over_budget @
  a_reading_of_the_characterisation_is_the_goal

end
