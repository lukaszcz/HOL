structure benchMapCorpus =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun named name theorem = {name = name, theorem = theorem}

val ran_update_bridge =
  parityTranslationTheory.source_ran_update_injective_pointwise_iff

fun contains_constant constant goal =
  can (find_term (same_const constant)) goal

fun method_args method goal =
  [benchLib.RewriteAdd
     (named "pred_set$SPECIFICATION" pred_setTheory.SPECIFICATION),
   benchLib.DefinitionAdd
     (named "pred_set$EXTENSION" pred_setTheory.EXTENSION),
   benchLib.DefinitionAdd
     (named "pred_set$SUBSET_DEF" pred_setTheory.SUBSET_DEF),
   benchLib.RewriteAdd
     (named "bool$FUN_EQ_THM" boolTheory.FUN_EQ_THM),
   benchLib.RewriteAdd
     (named "parityTranslation$source_range_update_none"
        parityTranslationTheory.source_range_update_none)] @
  (if String.isSubstring "map_upds_def" method orelse
      String.isSubstring "option.splits" method orelse
      String.isSubstring "option.split" method orelse
      (String.isSubstring "dom_def" method andalso
       contains_constant ``option$option_CASE`` goal) then []
   else
     [benchLib.RewriteAdd
        (named "option$option_case_eq" optionTheory.option_case_eq)]) @
  (if String.isSubstring "option.splits" method orelse
      String.isSubstring "option.split" method then
     [benchLib.SplitAdd
        (named "parityTranslation$source_option_split"
           parityTranslationTheory.source_option_split)]
   else
     []) @
  (if String.isSubstring "dom_def" method andalso
      contains_constant ``option$option_CASE`` goal then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_option_overlay_not_none"
           parityTranslationTheory.source_option_overlay_not_none)]
   else if contains_constant ``option$option_CASE`` goal andalso
      not (String.isSubstring "option.splits" method orelse
           String.isSubstring "option.split" method) then
     [benchLib.SplitAdd
        (named "parityTranslation$source_option_split"
           parityTranslationTheory.source_option_split),
      benchLib.RewriteAdd
        (named "parityTranslation$source_option_overlay_not_none"
           parityTranslationTheory.source_option_overlay_not_none)]
   else
     []) @
  (if String.isSubstring "inj_on_def" method orelse
      String.isSubstring "inj_onD" method then
     [benchLib.DefinitionAdd
        (named "pred_set$INJ_DEF" pred_setTheory.INJ_DEF)] @
     (if String.isSubstring "inj_onD" method then
        [benchLib.DestAdd
           (benchLib.SafeRule,
            named "parityTranslation$source_inj_onD"
              parityTranslationTheory.source_inj_onD)]
      else
        [])
   else
     []) @
  (if String.isSubstring "domI" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_domI"
           parityTranslationTheory.source_domI)]
   else
     []) @
  (if String.isSubstring "simp del: map_of_eq_Some_iff" method then
     [benchLib.RewriteDelete
        "finite_mapAutoSeed.ALOOKUP_EQ_SOME_DISTINCT_AUTO",
      benchLib.RewriteAdd
        (named "finite_mapAutoSeed$ALOOKUP_MEM_DISTINCT_AUTO"
           finite_mapAutoSeedTheory.ALOOKUP_MEM_DISTINCT_AUTO),
      benchLib.RewriteAdd
        (named "bool$EQ_SYM_EQ" boolTheory.EQ_SYM_EQ)]
   else
     []) @
  (if String.isSubstring "ran_distinct" method then
     [benchLib.RewriteAdd
        (named "finite_mapAutoSeed$ALOOKUP_EQ_SOME_DISTINCT_AUTO"
           finite_mapAutoSeedTheory.ALOOKUP_EQ_SOME_DISTINCT_AUTO),
      benchLib.RewriteAdd
        (named "list$MAP_ZIP" listTheory.MAP_ZIP),
      benchLib.FactAdd
        (named "finite_mapAutoSeed$MEM_SND_ZIP_AUTO"
           finite_mapAutoSeedTheory.MEM_SND_ZIP_AUTO),
      benchLib.RewriteAdd
        (named "bool$EQ_SYM_EQ" boolTheory.EQ_SYM_EQ)]
   else
     []) @
  (if String.isSubstring "map_upd_upds_conv_if" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_map_upd_upds_conv_if"
           parityTranslationTheory.source_map_upd_upds_conv_if),
      benchLib.DestAdd
        (benchLib.SafeRule,
         named "parityTranslation$source_alookup_reverse_zip_none_full"
           parityTranslationTheory.source_alookup_reverse_zip_none_full),
      benchLib.RewriteAdd
        (named "parityTranslation$source_option_update_twist"
           parityTranslationTheory.source_option_update_twist)]
   else
     []) @
  (if String.isSubstring "map_upds_def" method then
     [benchLib.DefinitionAdd
        (named "list$ZIP_def" listTheory.ZIP_def),
      benchLib.DefinitionAdd
        (named "list$REVERSE_DEF" listTheory.REVERSE_DEF),
      benchLib.DefinitionAdd
        (named "parityTranslation$source_alookup_def"
           parityTranslationTheory.source_alookup_def),
      benchLib.RewriteAdd
        (named "parityTranslation$source_alookup_append"
           parityTranslationTheory.source_alookup_append),
      benchLib.RewriteAdd
        (named "parityTranslation$source_option_overlay_assoc"
           parityTranslationTheory.source_option_overlay_assoc),
      benchLib.RewriteAdd
        (named "parityTranslation$source_map_upds_cons_pointwise"
           parityTranslationTheory.source_map_upds_cons_pointwise)]
   else
     []) @
  (if String.isSubstring "map_add_le_mapI" method andalso
      String.isSubstring "map_le_antisym" method then
     [benchLib.RewriteAdd
        (named "parityTranslation$source_map_add_subsumed_step"
           parityTranslationTheory.source_map_add_subsumed_step)]
   else
     []) @
  (if contains_constant ``alist$ALOOKUP`` goal then
     [benchLib.IntroAdd
        (benchLib.SafeRule,
         named "parityTranslation$source_finite_graph_alookup"
           parityTranslationTheory.source_finite_graph_alookup)]
   else
     []) @
  (if contains_constant ``parityTranslation$source_alookup`` goal then
     [benchLib.RewriteAdd
        (named "bool$EQ_SYM_EQ" boolTheory.EQ_SYM_EQ),
      benchLib.DestAdd
        (benchLib.SafeRule,
        (named "parityTranslation$source_alookup_some_mem"
           parityTranslationTheory.source_alookup_some_mem)),
      benchLib.DestAdd
        (benchLib.SafeRule,
        (named "parityTranslation$source_mem_alookup_some"
           parityTranslationTheory.source_mem_alookup_some)),
      benchLib.DestAdd
        (benchLib.SafeRule,
        (named "parityTranslation$source_distinct_keys_unique"
           parityTranslationTheory.source_distinct_keys_unique))]
   else
     [])

fun entry id line method mapped representative excl goal : benchLib.corpus_goal =
  let
    val arguments = method_args method goal
    val recipe =
      if method =
           "by (fastforce simp add: map_upd_upds_conv_if)" then
        benchLib.Invoke
          (benchLib.Simp,
           [benchLib.RewriteAdd
              (named
                 "parityTranslation$source_map_upd_upds_twist_full_iff"
                 parityTranslationTheory.source_map_upd_upds_twist_full_iff)])
      else if method =
           "by(force simp add: ran_def domI inj_onD)" then
        benchLib.AllGoals
          (benchLib.Invoke (benchLib.Simp, arguments),
           benchLib.Invoke
             (benchLib.Simp,
              [benchLib.RewriteAdd
                 (named
                    "parityTranslation$source_ran_update_injective_pointwise_iff"
                    ran_update_bridge)]))
      else if method =
           "by (fastforce simp add: map_le_def dom_def)" then
        benchLib.Invoke (benchLib.Auto, arguments)
      else if method = "by (fastforce simp add: map_le_def)" orelse
         method = "by (fastforce simp: map_le_def)" orelse
         method =
           "by (fastforce simp: map_le_def map_add_def dom_def)" then
        benchLib.AllGoals
          (benchLib.Invoke (benchLib.Simp, arguments),
           benchLib.Invoke (benchLib.Fastforce, arguments))
      else
        benchLib.Invoke (mapped, arguments)
  in
    {id = id, goal = goal, source_method = method, recipe = recipe,
     excl = List.filter (fn {theorem, ...} =>
       benchLib.theorem_is_goal goal theorem) excl, provenance =
       {file = "src/HOL/Map.thy", line = line, commit = commit},
     representative = representative}
  end

val goals =
  [
   entry "map_L151_map_upd_Some_unfold" 151 "by auto" benchLib.Auto false []
     ``(((((((\b_update_func : ('b -> ('a option)). \b_update_key : 'b. \b_update_value : ('a option). \b_update_query : 'b. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('b -> ('a option)))) (v_a0 : 'b)) (SOME (v_b0 : 'a))) (v_x0 : 'b)) = (SOME (v_y0 : 'a))) = ((((v_x0 : 'b) = (v_a0 : 'b)) /\ ((v_b0 : 'a) = (v_y0 : 'a))) \/ ((~((v_x0 : 'b) = (v_a0 : 'b))) /\ (((v_m0 : ('b -> ('a option))) (v_x0 : 'b)) = (SOME (v_y0 : 'a))))))``,
   entry "map_L155_image_map_upd" 155 "by auto" benchLib.Auto false []
     ``((~((v_x0 : 'a) IN (v_A0 : ('a set)))) ==> ((IMAGE ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('a -> ('b option)))) (v_x0 : 'a)) (SOME (v_y0 : 'b))) (v_A0 : ('a set))) = (IMAGE (v_m0 : ('a -> ('b option))) (v_A0 : ('a set)))))``,
   entry "map_L193_Some_eq_map_of_iff" 193
     "by (auto simp del: map_of_eq_Some_iff simp: map_of_eq_Some_iff [symmetric])"
     benchLib.Auto false []
     ``((ALL_DISTINCT ((MAP FST) (v_xys0 : (('a # 'b) list)))) ==> (((SOME (v_y0 : 'b)) = ((alist$ALOOKUP (v_xys0 : (('a # 'b) list))) (v_x0 : 'a))) = (((v_x0 : 'a),(v_y0 : 'b)) IN (LIST_TO_SET (v_xys0 : (('a # 'b) list))))))``,
   entry "map_L197_map_of_is_SomeI" 197
     "by simp" benchLib.Simp false []
     ``((ALL_DISTINCT ((MAP FST) (v_xys0 : (('a # 'b) list)))) ==> ((((v_x0 : 'a),(v_y0 : 'b)) IN (LIST_TO_SET (v_xys0 : (('a # 'b) list)))) ==> (((alist$ALOOKUP (v_xys0 : (('a # 'b) list))) (v_x0 : 'a)) = (SOME (v_y0 : 'b)))))``,
   entry "map_L304_dom_map_option" 304 "by (simp add: dom_def)" benchLib.Simp false []
     ``(((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (\b_k : 'a. ((OPTION_MAP ((v_f0 : ('a -> ('c -> 'b))) b_k)) ((v_m0 : ('a -> ('c option))) b_k)))) = ((\b_dom_func : ('a -> ('c option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m0 : ('a -> ('c option)))))``,
   entry "map_L308_dom_map_option_comp" 308 "by (simp add: comp_def)" benchLib.Simp false []
     ``(((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) ((combin$o (OPTION_MAP (v_g0 : ('c -> 'b)))) (v_m0 : ('a -> ('c option))))) = ((\b_dom_func : ('a -> ('c option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m0 : ('a -> ('c option)))))``,
   entry "map_L325_map_comp_empty_1" 325 "by (auto simp: map_comp_def split: option.splits)" benchLib.Auto false []
     ``((((\b_comp_left : ('c -> ('b option)). \b_comp_right : ('a -> ('c option)). \b_comp_key : 'a. OPTION_BIND (b_comp_right b_comp_key) b_comp_left) (v_m0 : ('c -> ('b option)))) (\b_x : 'a. NONE)) = (\b_x : 'a. NONE))``,
   entry "map_L325_map_comp_empty_2" 325 "by (auto simp: map_comp_def split: option.splits)" benchLib.Auto false []
     ``((((\b_comp_left : ('b -> ('d option)). \b_comp_right : ('c -> ('b option)). \b_comp_key : 'c. OPTION_BIND (b_comp_right b_comp_key) b_comp_left) (\b_x : 'b. NONE)) (v_m0 : ('c -> ('b option)))) = (\b_x : 'c. NONE))``,
   entry "map_L330_map_comp_simps_1" 330 "by (auto simp: map_comp_def)" benchLib.Auto false []
     ``((((v_m20 : ('b -> ('a option))) (v_k0 : 'b)) = NONE) ==> (((((\b_comp_left : ('a -> ('c option)). \b_comp_right : ('b -> ('a option)). \b_comp_key : 'b. OPTION_BIND (b_comp_right b_comp_key) b_comp_left) (v_m10 : ('a -> ('c option)))) (v_m20 : ('b -> ('a option)))) (v_k0 : 'b)) = NONE))``,
   entry "map_L330_map_comp_simps_2" 330 "by (auto simp: map_comp_def)" benchLib.Auto false []
     ``((((v_m20 : ('b -> ('a option))) (v_k0 : 'b)) = (SOME (v_k_0 : 'a))) ==> (((((\b_comp_left : ('a -> ('c option)). \b_comp_right : ('b -> ('a option)). \b_comp_key : 'b. OPTION_BIND (b_comp_right b_comp_key) b_comp_left) (v_m10 : ('a -> ('c option)))) (v_m20 : ('b -> ('a option)))) (v_k0 : 'b)) = ((v_m10 : ('a -> ('c option))) (v_k_0 : 'a))))``,
   entry "map_L335_map_comp_Some_iff" 335 "by (auto simp: map_comp_def split: option.splits)" benchLib.Auto false []
     ``((((((\b_comp_left : ('b -> ('a option)). \b_comp_right : ('c -> ('b option)). \b_comp_key : 'c. OPTION_BIND (b_comp_right b_comp_key) b_comp_left) (v_m10 : ('b -> ('a option)))) (v_m20 : ('c -> ('b option)))) (v_k0 : 'c)) = (SOME (v_v0 : 'a))) = (?b_k_ : 'b. ((((v_m20 : ('c -> ('b option))) (v_k0 : 'c)) = (SOME b_k_)) /\ (((v_m10 : ('b -> ('a option))) b_k_) = (SOME (v_v0 : 'a))))))``,
   entry "map_L339_map_comp_None_iff" 339 "by (auto simp: map_comp_def split: option.splits)" benchLib.Auto false []
     ``((((((\b_comp_left : ('b -> ('a option)). \b_comp_right : ('c -> ('b option)). \b_comp_key : 'c. OPTION_BIND (b_comp_right b_comp_key) b_comp_left) (v_m10 : ('b -> ('a option)))) (v_m20 : ('c -> ('b option)))) (v_k0 : 'c)) = NONE) = ((((v_m20 : ('c -> ('b option))) (v_k0 : 'c)) = NONE) \/ (?b_k_ : 'b. ((((v_m20 : ('c -> ('b option))) (v_k0 : 'c)) = (SOME b_k_)) /\ (((v_m10 : ('b -> ('a option))) b_k_) = NONE)))))``,
   entry "map_L346_map_add_empty" 346 "by(simp add: map_add_def)" benchLib.Simp false []
     ``((((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_m0 : ('a -> ('b option)))) (\b_x : 'a. NONE)) = (v_m0 : ('a -> ('b option))))``,
   entry "map_L355_map_add_Some_iff" 355 "by (simp add: map_add_def split: option.split)" benchLib.Simp false []
     ``((((((\b_add_left : ('b -> ('a option)). \b_add_right : ('b -> ('a option)). \b_add_key : 'b. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_m0 : ('b -> ('a option)))) (v_n0 : ('b -> ('a option)))) (v_k0 : 'b)) = (SOME (v_x0 : 'a))) = ((((v_n0 : ('b -> ('a option))) (v_k0 : 'b)) = (SOME (v_x0 : 'a))) \/ ((((v_n0 : ('b -> ('a option))) (v_k0 : 'b)) = NONE) /\ (((v_m0 : ('b -> ('a option))) (v_k0 : 'b)) = (SOME (v_x0 : 'a))))))``,
   entry "map_L366_map_add_None" 366 "by (simp add: map_add_def split: option.split)" benchLib.Simp true []
     ``((((((\b_add_left : ('b -> ('a option)). \b_add_right : ('b -> ('a option)). \b_add_key : 'b. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_m0 : ('b -> ('a option)))) (v_n0 : ('b -> ('a option)))) (v_k0 : 'b)) = NONE) = ((((v_n0 : ('b -> ('a option))) (v_k0 : 'b)) = NONE) /\ (((v_m0 : ('b -> ('a option))) (v_k0 : 'b)) = NONE)))``,
   entry "map_L372_map_add_upds" 372 "by (simp add: map_upds_def)" benchLib.Simp false []
     ``((((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_m10 : ('a -> ('b option)))) ((((\b_upds_func : ('a -> ('b option)). \b_upds_keys : ('a list). \b_upds_values : ('b list). \b_upds_key : 'a. option_CASE (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key) (b_upds_func b_upds_key) SOME) (v_m20 : ('a -> ('b option)))) (v_xs0 : ('a list))) (v_ys0 : ('b list)))) = ((((\b_upds_func : ('a -> ('b option)). \b_upds_keys : ('a list). \b_upds_values : ('b list). \b_upds_key : 'a. option_CASE (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key) (b_upds_func b_upds_key) SOME) (((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_m10 : ('a -> ('b option)))) (v_m20 : ('a -> ('b option))))) (v_xs0 : ('a list))) (v_ys0 : ('b list))))``,
   entry "map_L394_inj_on_map_add_dom" 394 "by (fastforce simp: map_add_def dom_def inj_on_def split: option.splits)" benchLib.Fastforce false []
     ``((((\b_inj_func : ('a -> ('b option)). \b_inj_set : ('a set). INJ b_inj_func b_inj_set UNIV) (((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_m0 : ('a -> ('b option)))) (v_m_0 : ('a -> ('b option))))) ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m_0 : ('a -> ('b option))))) = (((\b_inj_func : ('a -> ('b option)). \b_inj_set : ('a set). INJ b_inj_func b_inj_set UNIV) (v_m_0 : ('a -> ('b option)))) ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m_0 : ('a -> ('b option))))))``,
   entry "map_L414_restrict_map_to_empty" 414 "by (simp add: restrict_map_def)" benchLib.Simp false []
     ``((((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) {}) = (\b_x : 'a. NONE))``,
   entry "map_L417_restrict_map_insert" 417 "by (auto simp: restrict_map_def)" benchLib.Auto false []
     ``((((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_f0 : ('a -> ('b option)))) ((v_a0 : 'a) INSERT (v_A0 : ('a set)))) = ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_f0 : ('a -> ('b option)))) (v_A0 : ('a set)))) (v_a0 : 'a)) ((v_f0 : ('a -> ('b option))) (v_a0 : 'a))))``,
   entry "map_L420_restrict_map_empty" 420 "by (simp add: restrict_map_def)" benchLib.Simp false []
     ``((((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (\b_x : 'a. NONE)) (v_D0 : ('a set))) = (\b_x : 'a. NONE))``,
   entry "map_L423_restrict_in" 423 "by (simp add: restrict_map_def)" benchLib.Simp false []
     ``(((v_x0 : 'a) IN (v_A0 : ('a set))) ==> (((((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) (v_A0 : ('a set))) (v_x0 : 'a)) = ((v_m0 : ('a -> ('b option))) (v_x0 : 'a))))``,
   entry "map_L426_restrict_out" 426 "by (simp add: restrict_map_def)" benchLib.Simp false []
     ``((~((v_x0 : 'a) IN (v_A0 : ('a set)))) ==> (((((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) (v_A0 : ('a set))) (v_x0 : 'a)) = NONE))``,
   entry "map_L429_ran_restrictD" 429 "by (auto simp: restrict_map_def ran_def split: if_split_asm)" benchLib.Auto false []
     ``(((v_y0 : 'a) IN ((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) (((\b_restrict_func : ('b -> ('a option)). \b_restrict_set : ('b set). \b_restrict_key : 'b. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('b -> ('a option)))) (v_A0 : ('b set))))) ==> (?b_x : 'b. (b_x IN (v_A0 : ('b set))) /\ (((v_m0 : ('b -> ('a option))) b_x) = (SOME (v_y0 : 'a)))))``,
   entry "map_L432_dom_restrict" 432 "by (auto simp: restrict_map_def dom_def split: if_split_asm)" benchLib.Auto false []
     ``(((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) (v_A0 : ('a set)))) = (((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m0 : ('a -> ('b option)))) INTER (v_A0 : ('a set))))``,
   entry "map_L441_restrict_fun_upd" 441 "by (simp add: restrict_map_def fun_eq_iff)" benchLib.Simp false []
     ``((((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('a -> ('b option)))) (v_x0 : 'a)) (v_y0 : ('b option)))) (v_D0 : ('a set))) = (if ((v_x0 : 'a) IN (v_D0 : ('a set))) then ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) ((v_D0 : ('a set)) DIFF ((v_x0 : 'a) INSERT {})))) (v_x0 : 'a)) (v_y0 : ('b option))) else (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) (v_D0 : ('a set)))))``,
   entry "map_L445_fun_upd_None_restrict" 445 "by (simp add: restrict_map_def fun_eq_iff)" benchLib.Simp false []
     ``(((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) (v_D0 : ('a set)))) (v_x0 : 'a)) NONE) = (if ((v_x0 : 'a) IN (v_D0 : ('a set))) then (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) ((v_D0 : ('a set)) DIFF ((v_x0 : 'a) INSERT {}))) else (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) (v_D0 : ('a set)))))``,
   entry "map_L449_fun_upd_restrict" 449 "by (simp add: restrict_map_def fun_eq_iff)" benchLib.Simp false []
     ``(((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) (v_D0 : ('a set)))) (v_x0 : 'a)) (v_y0 : ('b option))) = ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) ((v_D0 : ('a set)) DIFF ((v_x0 : 'a) INSERT {})))) (v_x0 : 'a)) (v_y0 : ('b option))))``,
   entry "map_L460_restrict_complement_singleton_eq" 460 "by auto" benchLib.Auto false []
     ``((((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_f0 : ('a -> ('b option)))) (COMPL ((v_x0 : 'a) INSERT {}))) = ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_f0 : ('a -> ('b option)))) (v_x0 : 'a)) NONE))``,
   entry "map_L467_map_upds_Nil1" 467 "by (simp add: map_upds_def)" benchLib.Simp false []
     ``(((((\b_upds_func : ('a -> ('b option)). \b_upds_keys : ('a list). \b_upds_values : ('b list). \b_upds_key : 'a. option_CASE (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key) (b_upds_func b_upds_key) SOME) (v_m0 : ('a -> ('b option)))) []) (v_bs0 : ('b list))) = (v_m0 : ('a -> ('b option))))``,
   entry "map_L470_map_upds_Nil2" 470 "by (simp add:map_upds_def)" benchLib.Simp false []
     ``(((((\b_upds_func : ('a -> ('b option)). \b_upds_keys : ('a list). \b_upds_values : ('b list). \b_upds_key : 'a. option_CASE (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key) (b_upds_func b_upds_key) SOME) (v_m0 : ('a -> ('b option)))) (v_as0 : ('a list))) []) = (v_m0 : ('a -> ('b option))))``,
   entry "map_L473_map_upds_Cons" 473 "by (simp add:map_upds_def)" benchLib.Simp false []
     ``(((((\b_upds_func : ('a -> ('b option)). \b_upds_keys : ('a list). \b_upds_values : ('b list). \b_upds_key : 'a. option_CASE (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key) (b_upds_func b_upds_key) SOME) (v_m0 : ('a -> ('b option)))) ((CONS (v_a0 : 'a)) (v_as0 : ('a list)))) ((CONS (v_b0 : 'b)) (v_bs0 : ('b list)))) = ((((\b_upds_func : ('a -> ('b option)). \b_upds_keys : ('a list). \b_upds_values : ('b list). \b_upds_key : 'a. option_CASE (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key) (b_upds_func b_upds_key) SOME) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('a -> ('b option)))) (v_a0 : 'a)) (SOME (v_b0 : 'b)))) (v_as0 : ('a list))) (v_bs0 : ('b list))))``,
   entry "map_L519_map_upds_twist" 519 "by (fastforce simp add: map_upd_upds_conv_if)" benchLib.Fastforce false []
     ``((~((v_a0 : 'a) IN (LIST_TO_SET (v_as0 : ('a list))))) ==> (((((\b_upds_func : ('a -> ('b option)). \b_upds_keys : ('a list). \b_upds_values : ('b list). \b_upds_key : 'a. option_CASE (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key) (b_upds_func b_upds_key) SOME) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('a -> ('b option)))) (v_a0 : 'a)) (SOME (v_b0 : 'b)))) (v_as0 : ('a list))) (v_bs0 : ('b list))) = ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) ((((\b_upds_func : ('a -> ('b option)). \b_upds_keys : ('a list). \b_upds_values : ('b list). \b_upds_key : 'a. option_CASE (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key) (b_upds_func b_upds_key) SOME) (v_m0 : ('a -> ('b option)))) (v_as0 : ('a list))) (v_bs0 : ('b list)))) (v_a0 : 'a)) (SOME (v_b0 : 'b)))))``,
   entry "map_L565_dom_eq_empty_conv" 565 "by (auto simp: dom_def)" benchLib.Auto false []
     ``((((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_f0 : ('a -> ('b option)))) = {}) = ((v_f0 : ('a -> ('b option))) = (\b_x : 'a. NONE)))``,
   entry "map_L568_domI" 568 "by (simp add: dom_def)" benchLib.Simp false []
     ``((((v_m0 : ('b -> ('a option))) (v_a0 : 'b)) = (SOME (v_b0 : 'a))) ==> ((v_a0 : 'b) IN ((\b_dom_func : ('b -> ('a option)). \b_dom_key : 'b. b_dom_func b_dom_key <> NONE) (v_m0 : ('b -> ('a option))))))``,
   entry "map_L575_domIff" 575 "by (simp add: dom_def)" benchLib.Simp false []
     ``(((v_a0 : 'a) IN ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m0 : ('a -> ('b option))))) = (~(((v_m0 : ('a -> ('b option))) (v_a0 : 'a)) = NONE)))``,
   entry "map_L578_dom_empty" 578 "by (simp add: dom_def)" benchLib.Simp false []
     ``(((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (\b_x : 'a. NONE)) = {})``,
   entry "map_L581_dom_fun_upd" 581 "by (auto simp: dom_def)" benchLib.Auto false []
     ``(((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_f0 : ('a -> ('b option)))) (v_x0 : 'a)) (v_y0 : ('b option)))) = (if ((v_y0 : ('b option)) = NONE) then (((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_f0 : ('a -> ('b option)))) DIFF ((v_x0 : 'a) INSERT {})) else ((v_x0 : 'a) INSERT ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_f0 : ('a -> ('b option)))))))``,
   entry "map_L588_dom_if" 588 "by (auto split: if_splits)" benchLib.Auto false []
     ``(((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (\b_x : 'a. (if ((v_P0 : ('a -> bool)) b_x) then ((v_f0 : ('a -> ('b option))) b_x) else ((v_g0 : ('a -> ('b option))) b_x)))) = ((((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_f0 : ('a -> ('b option)))) INTER (\b_x : 'a. ((v_P0 : ('a -> bool)) b_x))) UNION (((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_g0 : ('a -> ('b option)))) INTER (\b_x : 'a. (~((v_P0 : ('a -> bool)) b_x))))))``,
   entry "map_L611_dom_map_add" 611 "by (auto simp: dom_def)" benchLib.Auto false []
     ``(((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_m0 : ('a -> ('b option)))) (v_n0 : ('a -> ('b option))))) = (((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_n0 : ('a -> ('b option)))) UNION ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m0 : ('a -> ('b option))))))``,
   entry "map_L614_dom_override_on" 614 "by (auto simp: dom_def override_on_def)" benchLib.Auto false []
     ``(((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) ((((\b_override_left : ('a -> ('b option)). \b_override_right : ('a -> ('b option)). \b_override_set : ('a set). \b_override_key : 'a. if b_override_key IN b_override_set then b_override_right b_override_key else b_override_left b_override_key) (v_f0 : ('a -> ('b option)))) (v_g0 : ('a -> ('b option)))) (v_A0 : ('a set)))) = ((((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_f0 : ('a -> ('b option)))) DIFF (\b_a : 'a. (b_a IN ((v_A0 : ('a set)) DIFF ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_g0 : ('a -> ('b option)))))))) UNION (\b_a : 'a. (b_a IN ((v_A0 : ('a set)) INTER ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_g0 : ('a -> ('b option)))))))))``,
   entry "map_L622_map_add_dom_app_simps_1" 622 "by (auto simp add: map_add_def split: option.split_asm)" benchLib.Auto false []
     ``(((v_m0 : 'a) IN ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_l20 : ('a -> ('b option))))) ==> (((((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_l10 : ('a -> ('b option)))) (v_l20 : ('a -> ('b option)))) (v_m0 : 'a)) = ((v_l20 : ('a -> ('b option))) (v_m0 : 'a))))``,
   entry "map_L622_map_add_dom_app_simps_2" 622 "by (auto simp add: map_add_def split: option.split_asm)" benchLib.Auto false []
     ``((~((v_m0 : 'a) IN ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_l10 : ('a -> ('b option)))))) ==> (((((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_l10 : ('a -> ('b option)))) (v_l20 : ('a -> ('b option)))) (v_m0 : 'a)) = ((v_l20 : ('a -> ('b option))) (v_m0 : 'a))))``,
   entry "map_L622_map_add_dom_app_simps_3" 622 "by (auto simp add: map_add_def split: option.split_asm)" benchLib.Auto false []
     ``((~((v_m0 : 'a) IN ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_l20 : ('a -> ('b option)))))) ==> (((((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_l10 : ('a -> ('b option)))) (v_l20 : ('a -> ('b option)))) (v_m0 : 'a)) = ((v_l10 : ('a -> ('b option))) (v_m0 : 'a))))``,
   entry "map_L628_dom_const" 628 "by auto" benchLib.Auto false []
     ``(((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (\b_x : 'a. (SOME ((v_f0 : ('a -> 'b)) b_x)))) = UNIV)``,
   entry "map_L638_dom_minus" 638 "by simp" benchLib.Simp false []
     ``((((v_f0 : ('b -> ('a option))) (v_x0 : 'b)) = NONE) ==> ((((\b_dom_func : ('b -> ('a option)). \b_dom_key : 'b. b_dom_func b_dom_key <> NONE) (v_f0 : ('b -> ('a option)))) DIFF ((v_x0 : 'b) INSERT (v_A0 : ('b set)))) = (((\b_dom_func : ('b -> ('a option)). \b_dom_key : 'b. b_dom_func b_dom_key <> NONE) (v_f0 : ('b -> ('a option)))) DIFF (v_A0 : ('b set)))))``,
   entry "map_L642_insert_dom" 642 "by auto" benchLib.Auto false []
     ``((((v_f0 : ('b -> ('a option))) (v_x0 : 'b)) = (SOME (v_y0 : 'a))) ==> (((v_x0 : 'b) INSERT ((\b_dom_func : ('b -> ('a option)). \b_dom_key : 'b. b_dom_func b_dom_key <> NONE) (v_f0 : ('b -> ('a option))))) = ((\b_dom_func : ('b -> ('a option)). \b_dom_key : 'b. b_dom_func b_dom_key <> NONE) (v_f0 : ('b -> ('a option))))))``,
   entry "map_L699_ranI" 699 "by (auto simp: ran_def)" benchLib.Auto false []
     ``((((v_m0 : ('b -> ('a option))) (v_a0 : 'b)) = (SOME (v_b0 : 'a))) ==> ((v_b0 : 'a) IN ((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) (v_m0 : ('b -> ('a option))))))``,
   entry "map_L703_ran_empty" 703 "by (auto simp: ran_def)" benchLib.Auto false []
     ``(((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) (\b_x : 'b. NONE)) = {})``,
   entry "map_L723_ran_map_upd" 723 "by force" benchLib.Force false []
     ``((((v_m0 : ('b -> ('a option))) (v_a0 : 'b)) = NONE) ==> (((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) ((((\b_update_func : ('b -> ('a option)). \b_update_key : 'b. \b_update_value : ('a option). \b_update_query : 'b. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('b -> ('a option)))) (v_a0 : 'b)) (SOME (v_b0 : 'a)))) = ((v_b0 : 'a) INSERT ((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) (v_m0 : ('b -> ('a option)))))))``,
   entry "map_L727_fun_upd_None_if_notin_dom" 727 "by auto" benchLib.Auto false []
     ``((~((v_k0 : 'a) IN ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m0 : ('a -> ('b option)))))) ==> (((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('a -> ('b option)))) (v_k0 : 'a)) NONE) = (v_m0 : ('a -> ('b option)))))``,
   entry "map_L730_ran_map_upd_Some" 730 "by(force simp add: ran_def domI inj_onD)" benchLib.Force false []
     ``((((v_m0 : ('b -> ('a option))) (v_x0 : 'b)) = (SOME (v_y0 : 'a))) ==> ((((\b_inj_func : ('b -> ('a option)). \b_inj_set : ('b set). INJ b_inj_func b_inj_set UNIV) (v_m0 : ('b -> ('a option)))) ((\b_dom_func : ('b -> ('a option)). \b_dom_key : 'b. b_dom_func b_dom_key <> NONE) (v_m0 : ('b -> ('a option))))) ==> ((~((v_z0 : 'a) IN ((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) (v_m0 : ('b -> ('a option)))))) ==> (((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) ((((\b_update_func : ('b -> ('a option)). \b_update_key : 'b. \b_update_value : ('a option). \b_update_query : 'b. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('b -> ('a option)))) (v_x0 : 'b)) (SOME (v_z0 : 'a)))) = ((((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) (v_m0 : ('b -> ('a option)))) DIFF ((v_y0 : 'a) INSERT {})) UNION ((v_z0 : 'a) INSERT {}))))))``,
   entry "map_L776_ran_map_of_zip" 776 "by (simp add: ran_distinct set_map[symmetric])" benchLib.Simp false []
     ``(((LENGTH (v_xs0 : ('a list))) = (LENGTH (v_ys0 : ('b list)))) ==> ((ALL_DISTINCT (v_xs0 : ('a list))) ==> (((\b_ran_func : ('a -> ('b option)). \b_ran_value : 'b. ?b_ran_key : 'a. b_ran_func b_ran_key = SOME b_ran_value) (alist$ALOOKUP (ZIP ((v_xs0 : ('a list)),(v_ys0 : ('b list)))))) = (LIST_TO_SET (v_ys0 : ('b list))))))``,
   entry "map_L781_ran_map_option" 781 "by (auto simp add: ran_def)" benchLib.Auto false []
     ``(((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) (\b_x : 'b. ((OPTION_MAP (v_f0 : ('c -> 'a))) ((v_m0 : ('b -> ('c option))) b_x)))) = (IMAGE (v_f0 : ('c -> 'a)) ((\b_ran_func : ('b -> ('c option)). \b_ran_value : 'c. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) (v_m0 : ('b -> ('c option))))))``,
   entry "map_L786_graph_empty" 786 "by simp" benchLib.Simp false []
     ``(((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (\b_x : 'a. NONE)) = {})``,
   entry "map_L789_in_graphI" 789 "by blast" benchLib.Blast false []
     ``((((v_m0 : ('b -> ('a option))) (v_k0 : 'b)) = (SOME (v_v0 : 'a))) ==> (((v_k0 : 'b),(v_v0 : 'a)) IN ((\b_graph_func : ('b -> ('a option)). \b_graph_pair : ('b # 'a). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m0 : ('b -> ('a option))))))``,
   entry "map_L792_in_graphD" 792 "by blast" benchLib.Blast false []
     ``((((v_k0 : 'a),(v_v0 : 'b)) IN ((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m0 : ('a -> ('b option))))) ==> (((v_m0 : ('a -> ('b option))) (v_k0 : 'a)) = (SOME (v_v0 : 'b))))``,
   entry "map_L795_graph_map_upd" 795 "by (auto split: if_splits)" benchLib.Auto false []
     ``(((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('a -> ('b option)))) (v_k0 : 'a)) (SOME (v_v0 : 'b)))) = (((v_k0 : 'a),(v_v0 : 'b)) INSERT ((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('a -> ('b option)))) (v_k0 : 'a)) NONE))))``,
   entry "map_L798_graph_fun_upd_None" 798 "by (auto split: if_splits)" benchLib.Auto false []
     ``(((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m0 : ('a -> ('b option)))) (v_k0 : 'a)) NONE)) = (\b_e : ('a # 'b). ((b_e IN ((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m0 : ('a -> ('b option))))) /\ (~((FST b_e) = (v_k0 : 'a))))))``,
   entry "map_L801_graph_restrictD_1" 801 "by (auto simp: restrict_map_def split: if_splits)" benchLib.Auto false []
     ``((((v_k0 : 'a),(v_v0 : 'b)) IN ((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) (v_A0 : ('a set))))) ==> ((v_k0 : 'a) IN (v_A0 : ('a set))))``,
   entry "map_L801_graph_restrictD_2" 801 "by (auto simp: restrict_map_def split: if_splits)" benchLib.Auto false []
     ``((((v_k0 : 'a),(v_v0 : 'b)) IN ((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (((\b_restrict_func : ('a -> ('b option)). \b_restrict_set : ('a set). \b_restrict_key : 'a. if b_restrict_key IN b_restrict_set then b_restrict_func b_restrict_key else NONE) (v_m0 : ('a -> ('b option)))) (v_A0 : ('a set))))) ==> (((v_m0 : ('a -> ('b option))) (v_k0 : 'a)) = (SOME (v_v0 : 'b))))``,
   entry "map_L807_graph_map_comp" 807 "by (auto simp: map_comp_Some_iff relcomp_unfold)" benchLib.Auto false []
     ``(((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (((\b_comp_left : ('c -> ('b option)). \b_comp_right : ('a -> ('c option)). \b_comp_key : 'a. OPTION_BIND (b_comp_right b_comp_key) b_comp_left) (v_m10 : ('c -> ('b option)))) (v_m20 : ('a -> ('c option))))) = (((\b_relcomp_left : (('a # 'c) set). \b_relcomp_right : (('c # 'b) set). \b_relcomp_pair : ('a # 'b). ?b_relcomp_middle : 'c. (FST b_relcomp_pair,b_relcomp_middle) IN b_relcomp_left /\ (b_relcomp_middle,SND b_relcomp_pair) IN b_relcomp_right) ((\b_graph_func : ('a -> ('c option)). \b_graph_pair : ('a # 'c). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m20 : ('a -> ('c option))))) ((\b_graph_func : ('c -> ('b option)). \b_graph_pair : ('c # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m10 : ('c -> ('b option))))))``,
   entry "map_L810_graph_map_add" 810 "by force" benchLib.Force false []
     ``(((((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m10 : ('a -> ('b option)))) INTER ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m20 : ('a -> ('b option))))) = {}) ==> (((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_m10 : ('a -> ('b option)))) (v_m20 : ('a -> ('b option))))) = (((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m10 : ('a -> ('b option)))) UNION ((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m20 : ('a -> ('b option)))))))``,
   entry "map_L813_graph_eq_to_snd_dom" 813 "by force" benchLib.Force false []
     ``(((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m0 : ('a -> ('b option)))) = (IMAGE (\b_x : 'a. (b_x,(THE ((v_m0 : ('a -> ('b option))) b_x)))) ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m0 : ('a -> ('b option))))))``,
   entry "map_L816_fst_graph_eq_dom" 816 "by force" benchLib.Force false []
     ``((IMAGE FST ((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m0 : ('a -> ('b option))))) = ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_m0 : ('a -> ('b option)))))``,
   entry "map_L822_snd_graph_ran" 822 "by force" benchLib.Force false []
     ``((IMAGE SND ((\b_graph_func : ('b -> ('a option)). \b_graph_pair : ('b # 'a). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m0 : ('b -> ('a option))))) = ((\b_ran_func : ('b -> ('a option)). \b_ran_value : 'a. ?b_ran_key : 'b. b_ran_func b_ran_key = SOME b_ran_value) (v_m0 : ('b -> ('a option)))))``,
   entry "map_L828_finite_graph_map_of" 828 "by blast" benchLib.Blast false []
     ``(FINITE ((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (alist$ALOOKUP (v_al0 : (('a # 'b) list)))))``,
   entry "map_L832_graph_map_of_if_distinct_dom" 832 "by auto" benchLib.Auto false []
     ``((ALL_DISTINCT ((MAP FST) (v_al0 : (('a # 'b) list)))) ==> (((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (alist$ALOOKUP (v_al0 : (('a # 'b) list)))) = (LIST_TO_SET (v_al0 : (('a # 'b) list)))))``,
   entry "map_L849_inj_on_fst_graph" 849 "by force" benchLib.Force false []
     ``(((\b_inj_func : (('a # 'b) -> 'a). \b_inj_set : (('a # 'b) set). INJ b_inj_func b_inj_set UNIV) FST) ((\b_graph_func : ('a -> ('b option)). \b_graph_pair : ('a # 'b). b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (v_m0 : ('a -> ('b option)))))``,
   entry "map_L854_map_le_empty" 854 "by (simp add: map_le_def)" benchLib.Simp false []
     ``(((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (\b_x : 'a. NONE)) (v_g0 : ('a -> ('b option))))``,
   entry "map_L857_upd_None_map_le" 857 "by (force simp add: map_le_def)" benchLib.Force false []
     ``(((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_f0 : ('a -> ('b option)))) (v_x0 : 'a)) NONE)) (v_f0 : ('a -> ('b option))))``,
   entry "map_L860_map_le_upd" 860 "by (fastforce simp add: map_le_def)" benchLib.Fastforce false []
     ``((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_f0 : ('a -> ('b option)))) (v_g0 : ('a -> ('b option)))) ==> (((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_f0 : ('a -> ('b option)))) (v_a0 : 'a)) (v_b0 : ('b option)))) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_g0 : ('a -> ('b option)))) (v_a0 : 'a)) (v_b0 : ('b option)))))``,
   entry "map_L863_map_le_imp_upd_le" 863 "by (force simp add: map_le_def)" benchLib.Force false []
     ``((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_m10 : ('a -> ('b option)))) (v_m20 : ('a -> ('b option)))) ==> (((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m10 : ('a -> ('b option)))) (v_x0 : 'a)) NONE)) ((((\b_update_func : ('a -> ('b option)). \b_update_key : 'a. \b_update_value : ('b option). \b_update_query : 'a. if b_update_query = b_update_key then b_update_value else b_update_func b_update_query) (v_m20 : ('a -> ('b option)))) (v_x0 : 'a)) (SOME (v_y0 : 'b)))))``,
   entry "map_L874_map_le_implies_dom_le" 874 "by (fastforce simp add: map_le_def dom_def)" benchLib.Fastforce false []
     ``((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_f0 : ('a -> ('b option)))) (v_g0 : ('a -> ('b option)))) ==> (((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_f0 : ('a -> ('b option)))) SUBSET ((\b_dom_func : ('a -> ('b option)). \b_dom_key : 'a. b_dom_func b_dom_key <> NONE) (v_g0 : ('a -> ('b option))))))``,
   entry "map_L877_map_le_refl" 877 "by (simp add: map_le_def)" benchLib.Simp false []
     ``(((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_f0 : ('a -> ('b option)))) (v_f0 : ('a -> ('b option))))``,
   entry "map_L880_map_le_trans" 880 "by (auto simp add: map_le_def dom_def)" benchLib.Auto false []
     ``((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_m10 : ('a -> ('b option)))) (v_m20 : ('a -> ('b option)))) ==> ((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_m20 : ('a -> ('b option)))) (v_m30 : ('a -> ('b option)))) ==> (((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_m10 : ('a -> ('b option)))) (v_m30 : ('a -> ('b option))))))``,
   entry "map_L887_map_le_map_add" 887 "by (fastforce simp: map_le_def)" benchLib.Fastforce false []
     ``(((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_f0 : ('a -> ('b option)))) (((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_g0 : ('a -> ('b option)))) (v_f0 : ('a -> ('b option)))))``,
   entry "map_L890_map_le_iff_map_add_commute" 890 "by (fastforce simp: map_add_def map_le_def fun_eq_iff split: option.splits)" benchLib.Fastforce false []
     ``((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_f0 : ('a -> ('b option)))) (((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_f0 : ('a -> ('b option)))) (v_g0 : ('a -> ('b option))))) = ((((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_f0 : ('a -> ('b option)))) (v_g0 : ('a -> ('b option)))) = (((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_g0 : ('a -> ('b option)))) (v_f0 : ('a -> ('b option))))))``,
   entry "map_L893_map_add_le_mapE" 893 "by (fastforce simp: map_le_def map_add_def dom_def)" benchLib.Fastforce false []
     ``((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_f0 : ('a -> ('b option)))) (v_g0 : ('a -> ('b option))))) (v_h0 : ('a -> ('b option)))) ==> (((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_g0 : ('a -> ('b option)))) (v_h0 : ('a -> ('b option)))))``,
   entry "map_L896_map_add_le_mapI" 896 "by (auto simp: map_le_def map_add_def dom_def split: option.splits)" benchLib.Auto false []
     ``((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_f0 : ('a -> ('b option)))) (v_h0 : ('a -> ('b option)))) ==> ((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_g0 : ('a -> ('b option)))) (v_h0 : ('a -> ('b option)))) ==> (((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_f0 : ('a -> ('b option)))) (v_g0 : ('a -> ('b option))))) (v_h0 : ('a -> ('b option))))))``,
   entry "map_L899_map_add_subsumed1" 899
     "by (simp add: map_add_le_mapI map_le_antisym)" benchLib.Simp false []
     ``((((\b_le_left : ('a -> ('b option)). \b_le_right : ('a -> ('b option)). !b_le_key : 'a. !b_le_value : 'b. b_le_left b_le_key = SOME b_le_value ==> b_le_right b_le_key = SOME b_le_value) (v_f0 : ('a -> ('b option)))) (v_g0 : ('a -> ('b option)))) ==> ((((\b_add_left : ('a -> ('b option)). \b_add_right : ('a -> ('b option)). \b_add_key : 'a. option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) (v_f0 : ('a -> ('b option)))) (v_g0 : ('a -> ('b option)))) = (v_g0 : ('a -> ('b option)))))``
  ]

end
