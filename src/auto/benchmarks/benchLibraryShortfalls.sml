structure benchLibraryShortfalls =
struct

(* Records for the list, map, option, string and product-type goals
   that the assigned tactic did not close in the 2026-08-28
   measurement.  The classification names the root cause and the note
   says what stands in the way.  A goal listed in [over_budget] was
   cut off by the budget rather than reporting no proof, so its
   classification is the family it belongs to rather than an observed
   residual.  That list is measured, not inherited: the engine work
   since has brought ten of its goals back inside the budget, and each
   now carries the class its residual says it belongs to (re-measured
   2026-09-07). *)

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
   "list_L1511_split_list_last_propE",
   "list_L5325_bij_rotate1",
   "list_L6138_map_sorted_distinct_set_unique",
   "list_L8044_listrel1_subset_listrel",
   "list_L9013_list_all_transfer",
   "map_L723_ran_map_upd", "map_L730_ran_map_upd_Some"]

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
    ("the residual is a conditional equation about TL, LAST or nub "
     ^ "that the simpset does not carry")
    ["list_L1010_tl_append_if", "list_L2100_last_ConsR",
     "list_L4481_insert_remdups"]

val congruence_rules =
  classified "congruence rules"
    ("the goal is a congruence rule for a list combinator and "
     ^ "the simpset carries no corresponding congruence")
    ["list_L8236_list_ex_cong"]

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
    ["list_L5325_bij_rotate1",
     "list_L6138_map_sorted_distinct_set_unique",
     "list_L8044_listrel1_subset_listrel",
     "list_L9013_list_all_transfer",
     "map_L723_ran_map_upd", "map_L730_ran_map_upd_Some"]

(* src/HOL/List.thy:6669,6847 @ f7e02b7e.  The residual is stated on
   the translated [sorted_key_list_of_set], which is a sort of the set's
   elements in an arbitrary listing.  The source's facts about it are
   the locale lemmas of the fold that builds it -- its head is the
   least element, and it is empty exactly when the set is -- and HOL4
   has no constant of its own to state them on, so a sort at a set
   known only to be finite reduces nowhere. *)
val sorted_list_of_a_set =
  classified "sorted list of a set"
    ("the residual is a sort over a set's elements, which the source "
     ^ "reads through the locale lemmas of the fold that builds it "
     ^ "and HOL4 states on no constant of its own")
    ["list_L6669_sorted_key_list_of_set_eq_Nil_iff",
     "list_L6847_sorted_list_of_set_nonempty"]

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

val filter_normalisation =
  classified "filter normalisation"
    ("FILTER against a composed or negated predicate is not "
     ^ "normalised")
    ["list_L1838_partition_filter_conv",
     "list_L4762_length_removeAll_less"]

val indexing_through_list_constructors =
  classified "indexing through list constructors"
    ("the goal characterises a list operation by index.  The "
     ^ "simpset pushes EL through MAP, ZIP, LUPDATE, TAKE, DROP and "
     ^ "a cons, so what is left is a side condition on one of those "
     ^ "rules that the goal does not supply, or the index "
     ^ "characterisation itself, which neither simplification nor "
     ^ "search reduces")
    ["list_L2480_take_update_cancel", "list_L2483_drop_update_cancel",
     "list_L3168_list_eq_iff_zip_eq",
     "list_L3919_bij_betw_nth",
     "list_L6487_nth_nth_transpose_sorted",
     "list_L6873_nth_sorted_list_of_set_greaterThanAtMost"]

val simplification_and_search_reports_no_proof =
  classified "simplification and search reports no proof"
    ("the clasimp method terminates and reports no proof")
    ["list_L2178_snoc_eq_iff_butlast",
     "list_L7998_listrel_rtrancl_refl",
     "list_L5409_nths_drop",
     "list_L7247_lex_conv",
     "list_L7321_lex_append_rightI",
     "list_L8999_set_Cons_transfer", "map_L519_map_upds_twist",
     "string_L178_card_UNIV_char"]

val list_relation_lifting =
  classified "list relation lifting"
    ("the declared rules take a LIST_REL apart at a nil, a cons or a "
     ^ "REVERSE, and trade a SHORTLEX for a length comparison; these "
     ^ "goals are about the relation as a whole -- an append, a "
     ^ "transitivity chain, asymmetry, well-foundedness or an "
     ^ "equivalence -- and need an induction over the list rather "
     ^ "than a rule application")
    ["list_L3089_list_all2_appendI",
     "list_L7995_equiv_listrel", "list_L7256_lenlex_conv",
     "list_L7401_lexord_append_leftD", "list_L7508_lexord_trans",
     "list_L7570_asym_lenlex", "list_L7922_wf_listrel1_iff"]

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
    ["list_L3381_anon_L3381", "list_L3385_anon_L3385"]

val finite_cardinality =
  classified "finite cardinality"
    ("the residual is a CARD identity over a finite set built "
     ^ "from a list")
    ["list_L4011_length_remdups_concat",
     "list_L6770_sorted_key_list_of_set_unique"]

(* Three of what used to be one class were permutations of a single
   statement and now close.  What is left is not propositional: the
   residual is [0 < n ==> P a <=> P a \/ n = 0], and the two sides
   agree only once [n = 0] is read as the complement of [0 < n].  The
   note this class carried -- that Isabelle's simplifier orders such
   equations by its term order -- was false: [conj_ac], [disj_ac] and
   [eq_ac] are all stated in HOL.thy and none is declared [simp]. *)
val arithmetic_complement_in_a_disjunct =
  classified "arithmetic complement in a disjunct"
    ("the residual is an equivalence whose two sides agree only "
     ^ "once a disjunct is read as the complement of a bound, "
     ^ "which is arithmetic and not a propositional rearrangement")
    ["list_L5008_Ball_set_replicate"]

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
     ^ "declares -- is withheld as the goal's own statement, by A1 or "
     ^ "by the recipe's self-citation filter, up to the orientation "
     ^ "of an equation or an equivalence or the unfolding of a "
     ^ "constant the translation introduces, and the assigned tactic "
     ^ "has no second route")
    ["list_L1856_nth_Cons_pos", "list_L1921_in_set_conv_nth",
     "list_L6444_stable_sort_key_sort_key", "list_L7318_lenlex_length",
     "product_type_L785_curry_conv",
     "list_L8167_list_all_iff",
     "list_L8642_image_set", "list_L8660_card_set",
     "list_L8683_can_select_set_list_ex1",
     "option_L361_equal_None_code_unfold_1", "string_L728_anon_L728"]

val membership_through_a_guarded_flatten =
  classified "membership through a guarded flatten"
    ("the membership is in a flatten over a map whose body maps each "
     ^ "element to a singleton or to nothing according to a test, so "
     ^ "the pair has to be placed in the branch the test selects and, "
     ^ "in the other direction, read back out of it; the search "
     ^ "reports no proof well inside its budget")
    ["list_L8705_set_relcomp"]

val transitive_closure_from_a_step_list =
  classified "transitive closure from a step list"
    ("the flattened list of steps is taken apart, and what is left is "
     ^ "a pair drawn from a map over a filter together with the two "
     ^ "steps of the transitive closure it has to be built into; the "
     ^ "source method names neither the closure's introduction rules "
     ^ "nor an induction")
    ["list_L7054_set_trans_list_step_subset_trancl"]

val blast_search_reports_no_proof =
  classified "blast search reports no proof"
    ("the tableau search exhausts its depths without a "
     ^ "reconstructible proof")
    ["list_L7771_wf_measures",
     "list_L7861_listrel1_converse",
     "map_L828_finite_graph_map_of",
     "option_L59_split_option_ex"]

val integer_interval_emptiness =
  classified "integer interval emptiness"
    ("the residual is [j < i ==> source_upto i j = []], which the "
     ^ "source method does not name and no simpset carries")
    ["list_L3695_upto_aux_rec"]

val rotation_by_iteration =
  classified "rotation by iteration"
    ("the iteration unfolds and the residual is a FUNPOW law HOL4 "
     ^ "does not have where the source does: the successor clause, "
     ^ "which the source declares to its simpset and HOL4 to none, "
     ^ "and the swap, which HOL4 states only as the commuting law "
     ^ "between two iterations and never as the single step the goal "
     ^ "carries")
    ["list_L5194_rotate_Suc", "list_L5207_rotate1_rotate_swap"]

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
    ["map_L467_map_upds_Nil1",
     "map_L470_map_upds_Nil2", "map_L473_map_upds_Cons"]

(* src/HOL/Map.thy:363 @ f7e02b7e.  Isabelle closes this one from its
   simpset, by [map_add_find_right], and that declaration's translated
   statement is this goal once [map_le] is unfolded -- two source facts
   onto one HOL4 theorem.  The measurement withholds a rule that states
   the goal it is offered on, so the goal runs without the fact the
   source proof read. *)
val the_ambient_rule_is_the_goal =
  classified "the ambient rule is the goal"
    ("Isabelle reads this from its simpset as map_add_find_right, "
     ^ "whose translated statement is the goal, so the measurement "
     ^ "withholds it here")
    ["map_L887_map_le_map_add"]

(* src/HOL/Map.thy:810 @ f7e02b7e.  [map_add_comm] reaches the goal as a
   rewrite now.  It goes in as a fact, so it stands as a universal
   assumption with a domain-disjointness condition, and the simplifier
   the search runs before each unsafe step instantiates it at the redex
   that condition pins and commutes there.  That step is the one the
   source proof needs: the membership branch it serves -- a value held
   by one map read out of the sum -- closes outright once the commuted
   sum is in reach of the ambient [map_add_find_right].  What is left is
   the set equality the goal is stated as, on which the recipe still
   runs out a budget ten times the measurement's. *)
val map_sum_commuted_under_a_fact =
  classified "map sum commuted under a fact"
    ("the commuting fact now reaches its redex and the membership "
     ^ "branch it serves closes, and the set equality around it still "
     ^ "runs out a budget ten times the measurement's")
    ["map_L810_graph_map_add"]

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
     "string_L60_char_of_take_bit_eq"]

val sigma_and_times_rule_forms =
  classified "Sigma and Times rule forms"
    ("the goal equates a set written as a paired abstraction with one "
     ^ "written another way -- a Sigma on one side, a choice over the "
     ^ "abstraction on the other -- and nothing relates the two "
     ^ "spellings")
    ["product_type_L1088_Collect_case_prod_Sigma",
     "product_type_L688_The_split_eq"]

(* Seven goals the corrected circularity guard newly withholds a rule
   from, all in the [characterisation is the goal] class above and
   dated to the measurement that found them.  Six are one conjunct of a
   conjunctive rule -- [listTheory.ZIP], [LIST_REL_NIL], [EVERY_DEF],
   [EXISTS_DEF] and the translation's own [source_measures_def], which
   the cited method unfolds -- and the simpset splits each into a
   rewrite that is the goal.  The seventh is
   [listTheory.SHORTLEX_NIL2], which is the goal once the translation
   of [lenlex] is unfolded; the guard used to compare a rule's
   conclusion against the goal with the goal's quantifier prefix still
   on, so neither reading matched.

   The eighth was [list_L1851_nth_Cons_Suc], whose withheld rule is one
   conjunct of [listTheory.EL].  A withheld rule leaves the goal to the
   rest of the layer rather than closing the class, and the seeded cons
   rule is a second route to it: EL_CONS reaches a cons at an index
   known only to be non-zero, which the successor in the goal is. *)
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
    ["list_L2740_zip_Cons_Cons",
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
  sorted_list_of_a_set @
  arithmetic_residual_after_unfolding @
  filter_normalisation @
  indexing_through_list_constructors @
  simplification_and_search_reports_no_proof @
  list_relation_lifting @
  fold_direction @
  fold_against_a_set_aggregate @
  finite_cardinality @
  arithmetic_complement_in_a_disjunct @
  sortedness_beyond_the_bridge @
  numeral_against_Suc @
  characterisation_is_the_goal @
  membership_through_a_guarded_flatten @
  transitive_closure_from_a_step_list @
  blast_search_reports_no_proof @
  integer_interval_emptiness @
  rotation_by_iteration @
  decision_procedure_scope @
  definitional_unfolding_stops_short @
  injectivity_and_surjectivity @
  finite_map_update @
  the_ambient_rule_is_the_goal @
  map_sum_commuted_under_a_fact @
  option_relations @
  character_arithmetic @
  sigma_and_times_rule_forms @
  a_reading_of_the_characterisation_is_the_goal

end
