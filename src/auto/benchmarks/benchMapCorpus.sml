structure benchMapCorpus =
struct

open HolKernel autoSeedTheory

val goals : benchLib.corpus_goal list =
[{id = "map_L151_map_upd_Some_unfold",
 goal = ``(λb_update_func b_update_key b_update_value b_update_query.
     if b_update_query = b_update_key then b_update_value
     else b_update_func b_update_query) v_m0 v_a0 (SOME v_b0) v_x0 =
SOME v_y0 ⇔ v_x0 = v_a0 ∧ v_b0 = v_y0 ∨ v_x0 ≠ v_a0 ∧ v_m0 v_x0 = SOME v_y0``,
 source_method = "by auto",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 151, commit = "f7e02b7e"},
 representative = false},
{id = "map_L155_image_map_upd",
 goal = ``v_x0 ∉ v_A0 ⇒
IMAGE
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m0 v_x0 (SOME v_y0)) v_A0 =
IMAGE v_m0 v_A0``,
 source_method = "by auto",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 155, commit = "f7e02b7e"},
 representative = false},
{id = "map_L193_Some_eq_map_of_iff",
 goal =
   ``(ALL_DISTINCT (MAP FST (v_xys0 : ('a # 'b) list)) ==>
      ((SOME (v_y0 : 'b) =
        alist$ALOOKUP (v_xys0 : ('a # 'b) list) (v_x0 : 'a)) =
       (((v_x0 : 'a), (v_y0 : 'b)) IN
        LIST_TO_SET (v_xys0 : ('a # 'b) list))))``,
 source_method = "by (auto simp del: map_of_eq_Some_iff simp: map_of_eq_Some_iff [symmetric])",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq"),
benchLib.RewriteDelete "finite_mapAutoSeed.ALOOKUP_EQ_SOME_DISTINCT_AUTO",
benchLib.RewriteAdd (benchExplicit.named_at "finite_mapAutoSeed$ALOOKUP_MEM_DISTINCT_AUTO" "finite_mapAutoSeed" "ALOOKUP_MEM_DISTINCT_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$EQ_SYM_EQ" "bool" "EQ_SYM_EQ")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 193, commit = "f7e02b7e"},
 representative = false},
{id = "map_L197_map_of_is_SomeI",
 goal =
   ``(ALL_DISTINCT (MAP FST (v_xys0 : ('a # 'b) list)) ==>
      ((((v_x0 : 'a), (v_y0 : 'b)) IN
        LIST_TO_SET (v_xys0 : ('a # 'b) list)) ==>
       alist$ALOOKUP (v_xys0 : ('a # 'b) list) (v_x0 : 'a) =
       SOME (v_y0 : 'b)))``,
 source_method = "by simp",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 197, commit = "f7e02b7e"},
 representative = false},
{id = "map_L304_dom_map_option",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE)
  (λb_k. OPTION_MAP (v_f0 b_k) (v_m0 b_k)) =
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0``,
 source_method = "by (simp add: dom_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 304, commit = "f7e02b7e"},
 representative = false},
{id = "map_L308_dom_map_option_comp",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) (OPTION_MAP v_g0 ∘ v_m0) =
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0``,
 source_method = "by (simp add: comp_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 308, commit = "f7e02b7e"},
 representative = false},
{id = "map_L325_map_comp_empty_1",
 goal = ``(λb_comp_left b_comp_right b_comp_key.
     OPTION_BIND (b_comp_right b_comp_key) b_comp_left) v_m0 (λb_x. NONE) =
(λb_x. NONE)``,
 source_method = "by (auto simp: map_comp_def split: option.splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 325, commit = "f7e02b7e"},
 representative = false},
{id = "map_L325_map_comp_empty_2",
 goal = ``(λb_comp_left b_comp_right b_comp_key.
     OPTION_BIND (b_comp_right b_comp_key) b_comp_left) (λb_x. NONE) v_m0 =
(λb_x. NONE)``,
 source_method = "by (auto simp: map_comp_def split: option.splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 325, commit = "f7e02b7e"},
 representative = false},
{id = "map_L330_map_comp_simps_1",
 goal = ``v_m20 v_k0 = NONE ⇒
(λb_comp_left b_comp_right b_comp_key.
     OPTION_BIND (b_comp_right b_comp_key) b_comp_left) v_m10 v_m20 v_k0 =
NONE``,
 source_method = "by (auto simp: map_comp_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 330, commit = "f7e02b7e"},
 representative = false},
{id = "map_L330_map_comp_simps_2",
 goal = ``v_m20 v_k0 = SOME v_k_0 ⇒
(λb_comp_left b_comp_right b_comp_key.
     OPTION_BIND (b_comp_right b_comp_key) b_comp_left) v_m10 v_m20 v_k0 =
v_m10 v_k_0``,
 source_method = "by (auto simp: map_comp_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 330, commit = "f7e02b7e"},
 representative = false},
{id = "map_L335_map_comp_Some_iff",
 goal = ``(λb_comp_left b_comp_right b_comp_key.
     OPTION_BIND (b_comp_right b_comp_key) b_comp_left) v_m10 v_m20 v_k0 =
SOME v_v0 ⇔ ∃b_k_. v_m20 v_k0 = SOME b_k_ ∧ v_m10 b_k_ = SOME v_v0``,
 source_method = "by (auto simp: map_comp_def split: option.splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 335, commit = "f7e02b7e"},
 representative = false},
{id = "map_L339_map_comp_None_iff",
 goal = ``(λb_comp_left b_comp_right b_comp_key.
     OPTION_BIND (b_comp_right b_comp_key) b_comp_left) v_m10 v_m20 v_k0 =
NONE ⇔ v_m20 v_k0 = NONE ∨ ∃b_k_. v_m20 v_k0 = SOME b_k_ ∧ v_m10 b_k_ = NONE``,
 source_method = "by (auto simp: map_comp_def split: option.splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 339, commit = "f7e02b7e"},
 representative = false},
{id = "map_L346_map_add_empty",
 goal = ``(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_m0
  (λb_x. NONE) = v_m0``,
 source_method = "by(simp add: map_add_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 346, commit = "f7e02b7e"},
 representative = false},
{id = "map_L355_map_add_Some_iff",
 goal = ``(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_m0
  v_n0 v_k0 = SOME v_x0 ⇔
v_n0 v_k0 = SOME v_x0 ∨ v_n0 v_k0 = NONE ∧ v_m0 v_k0 = SOME v_x0``,
 source_method = "by (simp add: map_add_def split: option.split)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 355, commit = "f7e02b7e"},
 representative = false},
{id = "map_L366_map_add_None",
 goal = ``(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_m0
  v_n0 v_k0 = NONE ⇔ v_n0 v_k0 = NONE ∧ v_m0 v_k0 = NONE``,
 source_method = "by (simp add: map_add_def split: option.split)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 366, commit = "f7e02b7e"},
 representative = true},
{id = "map_L372_map_add_upds",
 goal = ``(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_m10
  ((λb_upds_func b_upds_keys b_upds_values b_upds_key.
        option_CASE
          (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key)
          (b_upds_func b_upds_key) SOME) v_m20 v_xs0 v_ys0) =
(λb_upds_func b_upds_keys b_upds_values b_upds_key.
     option_CASE
       (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key)
       (b_upds_func b_upds_key) SOME)
  ((λb_add_left b_add_right b_add_key.
        option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME)
     v_m10 v_m20) v_xs0 v_ys0``,
 source_method = "by (simp add: map_upds_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none"),
benchLib.DefinitionAdd (benchExplicit.named_at "list$ZIP_def" "list" "ZIP_def"),
benchLib.DefinitionAdd (benchExplicit.named_at "list$REVERSE_DEF" "list" "REVERSE_DEF"),
benchLib.DefinitionAdd (benchExplicit.named_at "parityTranslation$source_alookup_def" "parityTranslation" "source_alookup_def"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_alookup_append" "parityTranslation" "source_alookup_append"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_assoc" "parityTranslation" "source_option_overlay_assoc"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_map_upds_cons_pointwise" "parityTranslation" "source_map_upds_cons_pointwise"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$EQ_SYM_EQ" "bool" "EQ_SYM_EQ"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_alookup_some_mem" "parityTranslation" "source_alookup_some_mem"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_mem_alookup_some" "parityTranslation" "source_mem_alookup_some"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_distinct_keys_unique" "parityTranslation" "source_distinct_keys_unique")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 372, commit = "f7e02b7e"},
 representative = false},
{id = "map_L394_inj_on_map_add_dom",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:β option))
  ((λb_add_left b_add_right b_add_key.
        option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_m0
     v_m_0) ((λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m_0) ⇔
(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:β option)) v_m_0
  ((λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m_0)``,
 source_method = "by (fastforce simp: map_add_def dom_def inj_on_def split: option.splits)",
 recipe = benchLib.Invoke (benchLib.Fastforce,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$INJ_DEF" "pred_setAutoSeed" "INJ_DEF_AUTO")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 394, commit = "f7e02b7e"},
 representative = false},
{id = "map_L414_restrict_map_to_empty",
 goal = ``(λb_restrict_func b_restrict_set b_restrict_key.
     if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
     else NONE) v_m0 ∅ = (λb_x. NONE)``,
 source_method = "by (simp add: restrict_map_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 414, commit = "f7e02b7e"},
 representative = false},
{id = "map_L417_restrict_map_insert",
 goal = ``(λb_restrict_func b_restrict_set b_restrict_key.
     if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
     else NONE) v_f0 (v_a0 INSERT v_A0) =
(λb_update_func b_update_key b_update_value b_update_query.
     if b_update_query = b_update_key then b_update_value
     else b_update_func b_update_query)
  ((λb_restrict_func b_restrict_set b_restrict_key.
        if b_restrict_key ∈ b_restrict_set then
          b_restrict_func b_restrict_key
        else NONE) v_f0 v_A0) v_a0 (v_f0 v_a0)``,
 source_method = "by (auto simp: restrict_map_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 417, commit = "f7e02b7e"},
 representative = false},
{id = "map_L420_restrict_map_empty",
 goal = ``(λb_restrict_func b_restrict_set b_restrict_key.
     if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
     else NONE) (λb_x. NONE) v_D0 = (λb_x. NONE)``,
 source_method = "by (simp add: restrict_map_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 420, commit = "f7e02b7e"},
 representative = false},
{id = "map_L423_restrict_in",
 goal = ``v_x0 ∈ v_A0 ⇒
(λb_restrict_func b_restrict_set b_restrict_key.
     if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
     else NONE) v_m0 v_A0 v_x0 = v_m0 v_x0``,
 source_method = "by (simp add: restrict_map_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 423, commit = "f7e02b7e"},
 representative = false},
{id = "map_L426_restrict_out",
 goal = ``v_x0 ∉ v_A0 ⇒
(λb_restrict_func b_restrict_set b_restrict_key.
     if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
     else NONE) v_m0 v_A0 v_x0 = NONE``,
 source_method = "by (simp add: restrict_map_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 426, commit = "f7e02b7e"},
 representative = false},
{id = "map_L429_ran_restrictD",
 goal = ``v_y0 ∈
(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  ((λb_restrict_func b_restrict_set b_restrict_key.
        if b_restrict_key ∈ b_restrict_set then
          b_restrict_func b_restrict_key
        else NONE) v_m0 v_A0) ⇒
∃b_x. b_x ∈ v_A0 ∧ v_m0 b_x = SOME v_y0``,
 source_method = "by (auto simp: restrict_map_def ran_def split: if_split_asm)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 429, commit = "f7e02b7e"},
 representative = false},
{id = "map_L432_dom_restrict",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE)
  ((λb_restrict_func b_restrict_set b_restrict_key.
        if b_restrict_key ∈ b_restrict_set then
          b_restrict_func b_restrict_key
        else NONE) v_m0 v_A0) =
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0 ∩ v_A0``,
 source_method = "by (auto simp: restrict_map_def dom_def split: if_split_asm)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 432, commit = "f7e02b7e"},
 representative = false},
{id = "map_L441_restrict_fun_upd",
 goal = ``(λb_restrict_func b_restrict_set b_restrict_key.
     if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
     else NONE)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m0 v_x0 v_y0) v_D0 =
if v_x0 ∈ v_D0 then
  (λb_update_func b_update_key b_update_value b_update_query.
       if b_update_query = b_update_key then b_update_value
       else b_update_func b_update_query)
    ((λb_restrict_func b_restrict_set b_restrict_key.
          if b_restrict_key ∈ b_restrict_set then
            b_restrict_func b_restrict_key
          else NONE) v_m0 (v_D0 DIFF {v_x0})) v_x0 v_y0
else
  (λb_restrict_func b_restrict_set b_restrict_key.
       if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
       else NONE) v_m0 v_D0``,
 source_method = "by (simp add: restrict_map_def fun_eq_iff)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 441, commit = "f7e02b7e"},
 representative = false},
{id = "map_L445_fun_upd_None_restrict",
 goal = ``(λb_update_func b_update_key b_update_value b_update_query.
     if b_update_query = b_update_key then b_update_value
     else b_update_func b_update_query)
  ((λb_restrict_func b_restrict_set b_restrict_key.
        if b_restrict_key ∈ b_restrict_set then
          b_restrict_func b_restrict_key
        else NONE) v_m0 v_D0) v_x0 NONE =
if v_x0 ∈ v_D0 then
  (λb_restrict_func b_restrict_set b_restrict_key.
       if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
       else NONE) v_m0 (v_D0 DIFF {v_x0})
else
  (λb_restrict_func b_restrict_set b_restrict_key.
       if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
       else NONE) v_m0 v_D0``,
 source_method = "by (simp add: restrict_map_def fun_eq_iff)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 445, commit = "f7e02b7e"},
 representative = false},
{id = "map_L449_fun_upd_restrict",
 goal = ``(λb_update_func b_update_key b_update_value b_update_query.
     if b_update_query = b_update_key then b_update_value
     else b_update_func b_update_query)
  ((λb_restrict_func b_restrict_set b_restrict_key.
        if b_restrict_key ∈ b_restrict_set then
          b_restrict_func b_restrict_key
        else NONE) v_m0 v_D0) v_x0 v_y0 =
(λb_update_func b_update_key b_update_value b_update_query.
     if b_update_query = b_update_key then b_update_value
     else b_update_func b_update_query)
  ((λb_restrict_func b_restrict_set b_restrict_key.
        if b_restrict_key ∈ b_restrict_set then
          b_restrict_func b_restrict_key
        else NONE) v_m0 (v_D0 DIFF {v_x0})) v_x0 v_y0``,
 source_method = "by (simp add: restrict_map_def fun_eq_iff)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 449, commit = "f7e02b7e"},
 representative = false},
{id = "map_L460_restrict_complement_singleton_eq",
 goal = ``(λb_restrict_func b_restrict_set b_restrict_key.
     if b_restrict_key ∈ b_restrict_set then b_restrict_func b_restrict_key
     else NONE) v_f0 (COMPL {v_x0}) =
(λb_update_func b_update_key b_update_value b_update_query.
     if b_update_query = b_update_key then b_update_value
     else b_update_func b_update_query) v_f0 v_x0 NONE``,
 source_method = "by auto",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 460, commit = "f7e02b7e"},
 representative = false},
{id = "map_L467_map_upds_Nil1",
 goal = ``(λb_upds_func b_upds_keys b_upds_values b_upds_key.
     option_CASE
       (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key)
       (b_upds_func b_upds_key) SOME) v_m0 [] v_bs0 = v_m0``,
 source_method = "by (simp add: map_upds_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none"),
benchLib.DefinitionAdd (benchExplicit.named_at "list$ZIP_def" "list" "ZIP_def"),
benchLib.DefinitionAdd (benchExplicit.named_at "list$REVERSE_DEF" "list" "REVERSE_DEF"),
benchLib.DefinitionAdd (benchExplicit.named_at "parityTranslation$source_alookup_def" "parityTranslation" "source_alookup_def"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_alookup_append" "parityTranslation" "source_alookup_append"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_assoc" "parityTranslation" "source_option_overlay_assoc"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_map_upds_cons_pointwise" "parityTranslation" "source_map_upds_cons_pointwise"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$EQ_SYM_EQ" "bool" "EQ_SYM_EQ"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_alookup_some_mem" "parityTranslation" "source_alookup_some_mem"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_mem_alookup_some" "parityTranslation" "source_mem_alookup_some"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_distinct_keys_unique" "parityTranslation" "source_distinct_keys_unique")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 467, commit = "f7e02b7e"},
 representative = false},
{id = "map_L470_map_upds_Nil2",
 goal = ``(λb_upds_func b_upds_keys b_upds_values b_upds_key.
     option_CASE
       (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key)
       (b_upds_func b_upds_key) SOME) v_m0 v_as0 [] = v_m0``,
 source_method = "by (simp add:map_upds_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none"),
benchLib.DefinitionAdd (benchExplicit.named_at "list$ZIP_def" "list" "ZIP_def"),
benchLib.DefinitionAdd (benchExplicit.named_at "list$REVERSE_DEF" "list" "REVERSE_DEF"),
benchLib.DefinitionAdd (benchExplicit.named_at "parityTranslation$source_alookup_def" "parityTranslation" "source_alookup_def"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_alookup_append" "parityTranslation" "source_alookup_append"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_assoc" "parityTranslation" "source_option_overlay_assoc"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_map_upds_cons_pointwise" "parityTranslation" "source_map_upds_cons_pointwise"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$EQ_SYM_EQ" "bool" "EQ_SYM_EQ"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_alookup_some_mem" "parityTranslation" "source_alookup_some_mem"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_mem_alookup_some" "parityTranslation" "source_mem_alookup_some"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_distinct_keys_unique" "parityTranslation" "source_distinct_keys_unique")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 470, commit = "f7e02b7e"},
 representative = false},
{id = "map_L473_map_upds_Cons",
 goal = ``(λb_upds_func b_upds_keys b_upds_values b_upds_key.
     option_CASE
       (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key)
       (b_upds_func b_upds_key) SOME) v_m0 (v_a0::v_as0) (v_b0::v_bs0) =
(λb_upds_func b_upds_keys b_upds_values b_upds_key.
     option_CASE
       (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key)
       (b_upds_func b_upds_key) SOME)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m0 v_a0 (SOME v_b0)) v_as0 v_bs0``,
 source_method = "by (simp add:map_upds_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none"),
benchLib.DefinitionAdd (benchExplicit.named_at "list$ZIP_def" "list" "ZIP_def"),
benchLib.DefinitionAdd (benchExplicit.named_at "list$REVERSE_DEF" "list" "REVERSE_DEF"),
benchLib.DefinitionAdd (benchExplicit.named_at "parityTranslation$source_alookup_def" "parityTranslation" "source_alookup_def"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_alookup_append" "parityTranslation" "source_alookup_append"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_assoc" "parityTranslation" "source_option_overlay_assoc"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_map_upds_cons_pointwise" "parityTranslation" "source_map_upds_cons_pointwise"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$EQ_SYM_EQ" "bool" "EQ_SYM_EQ"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_alookup_some_mem" "parityTranslation" "source_alookup_some_mem"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_mem_alookup_some" "parityTranslation" "source_mem_alookup_some"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_distinct_keys_unique" "parityTranslation" "source_distinct_keys_unique")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 473, commit = "f7e02b7e"},
 representative = false},
{id = "map_L519_map_upds_twist",
 goal = ``¬MEM v_a0 v_as0 ⇒
(λb_upds_func b_upds_keys b_upds_values b_upds_key.
     option_CASE
       (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key)
       (b_upds_func b_upds_key) SOME)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m0 v_a0 (SOME v_b0)) v_as0 v_bs0 =
(λb_update_func b_update_key b_update_value b_update_query.
     if b_update_query = b_update_key then b_update_value
     else b_update_func b_update_query)
  ((λb_upds_func b_upds_keys b_upds_values b_upds_key.
        option_CASE
          (ALOOKUP (REVERSE (ZIP (b_upds_keys,b_upds_values))) b_upds_key)
          (b_upds_func b_upds_key) SOME) v_m0 v_as0 v_bs0) v_a0 (SOME v_b0)``,
 source_method = "by (fastforce simp add: map_upd_upds_conv_if)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_alookup_reverse_zip_none_full" "parityTranslation" "source_alookup_reverse_zip_none_full"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_update_twist" "parityTranslation" "source_option_update_twist")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 519, commit = "f7e02b7e"},
 representative = false},
{id = "map_L565_dom_eq_empty_conv",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0 = ∅ ⇔
v_f0 = (λb_x. NONE)``,
 source_method = "by (auto simp: dom_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 565, commit = "f7e02b7e"},
 representative = false},
{id = "map_L568_domI",
 goal = ``v_m0 v_a0 = SOME v_b0 ⇒
v_a0 ∈ (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0``,
 source_method = "by (simp add: dom_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 568, commit = "f7e02b7e"},
 representative = false},
{id = "map_L575_domIff",
 goal = ``v_a0 ∈ (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0 ⇔
v_m0 v_a0 ≠ NONE``,
 source_method = "by (simp add: dom_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 575, commit = "f7e02b7e"},
 representative = false},
{id = "map_L578_dom_empty",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) (λb_x. NONE) = ∅``,
 source_method = "by (simp add: dom_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 578, commit = "f7e02b7e"},
 representative = false},
{id = "map_L581_dom_fun_upd",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_f0 v_x0 v_y0) =
if v_y0 = NONE then
  (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0 DIFF {v_x0}
else v_x0 INSERT (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0``,
 source_method = "by (auto simp: dom_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 581, commit = "f7e02b7e"},
 representative = false},
{id = "map_L588_dom_if",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE)
  (λb_x. if v_P0 b_x then v_f0 b_x else v_g0 b_x) =
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0 ∩ (λb_x. v_P0 b_x) ∪
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_g0 ∩ (λb_x. ¬v_P0 b_x)``,
 source_method = "by (auto split: if_splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 588, commit = "f7e02b7e"},
 representative = false},
{id = "map_L611_dom_map_add",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE)
  ((λb_add_left b_add_right b_add_key.
        option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_m0
     v_n0) =
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_n0 ∪
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0``,
 source_method = "by (auto simp: dom_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 611, commit = "f7e02b7e"},
 representative = false},
{id = "map_L614_dom_override_on",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE)
  ((λb_override_left b_override_right b_override_set b_override_key.
        if b_override_key ∈ b_override_set then
          b_override_right b_override_key
        else b_override_left b_override_key) v_f0 v_g0 v_A0) =
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0 DIFF
(λb_a.
     b_a ∈
     v_A0 DIFF (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_g0) ∪
(λb_a. b_a ∈ v_A0 ∩ (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_g0)``,
 source_method = "by (auto simp: dom_def override_on_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 614, commit = "f7e02b7e"},
 representative = false},
{id = "map_L622_map_add_dom_app_simps_1",
 goal = ``v_m0 ∈ (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_l20 ⇒
(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_l10
  v_l20 v_m0 = v_l20 v_m0``,
 source_method = "by (auto simp add: map_add_def split: option.split_asm)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 622, commit = "f7e02b7e"},
 representative = false},
{id = "map_L622_map_add_dom_app_simps_2",
 goal = ``v_m0 ∉ (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_l10 ⇒
(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_l10
  v_l20 v_m0 = v_l20 v_m0``,
 source_method = "by (auto simp add: map_add_def split: option.split_asm)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 622, commit = "f7e02b7e"},
 representative = false},
{id = "map_L622_map_add_dom_app_simps_3",
 goal = ``v_m0 ∉ (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_l20 ⇒
(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_l10
  v_l20 v_m0 = v_l10 v_m0``,
 source_method = "by (auto simp add: map_add_def split: option.split_asm)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 622, commit = "f7e02b7e"},
 representative = false},
{id = "map_L628_dom_const",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) (λb_x. SOME (v_f0 b_x)) =
𝕌(:α)``,
 source_method = "by auto",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 628, commit = "f7e02b7e"},
 representative = false},
{id = "map_L638_dom_minus",
 goal = ``v_f0 v_x0 = NONE ⇒
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0 DIFF
(v_x0 INSERT v_A0) =
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0 DIFF v_A0``,
 source_method = "by simp",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 638, commit = "f7e02b7e"},
 representative = false},
{id = "map_L642_insert_dom",
 goal = ``v_f0 v_x0 = SOME v_y0 ⇒
v_x0 INSERT (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0 =
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0``,
 source_method = "by auto",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 642, commit = "f7e02b7e"},
 representative = false},
{id = "map_L699_ranI",
 goal = ``v_m0 v_a0 = SOME v_b0 ⇒
v_b0 ∈
(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  v_m0``,
 source_method = "by (auto simp: ran_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 699, commit = "f7e02b7e"},
 representative = false},
{id = "map_L703_ran_empty",
 goal = ``(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  (λb_x. NONE) = ∅``,
 source_method = "by (auto simp: ran_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 703, commit = "f7e02b7e"},
 representative = false},
{id = "map_L723_ran_map_upd",
 goal = ``v_m0 v_a0 = NONE ⇒
(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m0 v_a0 (SOME v_b0)) =
v_b0 INSERT
(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  v_m0``,
 source_method = "by force",
 recipe = benchLib.Invoke (benchLib.Force,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 723, commit = "f7e02b7e"},
 representative = false},
{id = "map_L727_fun_upd_None_if_notin_dom",
 goal = ``v_k0 ∉ (λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0 ⇒
(λb_update_func b_update_key b_update_value b_update_query.
     if b_update_query = b_update_key then b_update_value
     else b_update_func b_update_query) v_m0 v_k0 NONE = v_m0``,
 source_method = "by auto",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 727, commit = "f7e02b7e"},
 representative = false},
{id = "map_L730_ran_map_upd_Some",
 goal = ``v_m0 v_x0 = SOME v_y0 ⇒
(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:α option)) v_m0
  ((λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0) ⇒
v_z0 ∉
(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  v_m0 ⇒
(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m0 v_x0 (SOME v_z0)) =
(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  v_m0 DIFF {v_y0} ∪ {v_z0}``,
 source_method = "by(force simp add: ran_def domI inj_onD)",
 recipe = benchLib.AllGoals (
benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$INJ_DEF" "pred_setAutoSeed" "INJ_DEF_AUTO"),
benchLib.DestAdd (benchLib.SafeRule, benchExplicit.named_at "parityTranslation$source_inj_onD" "parityTranslation" "source_inj_onD"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_domI" "parityTranslation" "source_domI")]),
benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_ran_update_injective_pointwise_iff" "parityTranslation" "source_ran_update_injective_pointwise_iff")])),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 730, commit = "f7e02b7e"},
 representative = false},
{id = "map_L776_ran_map_of_zip",
 goal =
   ``((LENGTH (v_xs0 : 'a list) = LENGTH (v_ys0 : 'b list)) ==>
      (ALL_DISTINCT (v_xs0 : 'a list) ==>
       ((\b_ran_func : 'a -> 'b option.
           \b_ran_value : 'b.
             ?b_ran_key : 'a.
               b_ran_func b_ran_key = SOME b_ran_value)
          (alist$ALOOKUP
             (ZIP ((v_xs0 : 'a list), (v_ys0 : 'b list)))) =
        LIST_TO_SET (v_ys0 : 'b list))))``,
 source_method = "by (simp add: ran_distinct set_map[symmetric])",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd
   {name = "pred_set$SPECIFICATION",
    theorem = pred_setTheory.SPECIFICATION},
 benchLib.DefinitionAdd
   {name = "pred_set$EXTENSION", theorem = pred_setTheory.EXTENSION},
 benchLib.DefinitionAdd
   {name = "pred_set$SUBSET_DEF", theorem = pred_setTheory.SUBSET_DEF},
 benchLib.RewriteAdd
   {name = "bool$FUN_EQ_THM", theorem = boolTheory.FUN_EQ_THM},
 benchLib.RewriteAdd
   {name = "parityTranslation$source_range_update_none",
    theorem = parityTranslationTheory.source_range_update_none},
 benchLib.RewriteAdd
   {name = "option$option_case_eq", theorem = optionTheory.option_case_eq},
 benchLib.RewriteAdd
   {name = "finite_mapAutoSeed$ALOOKUP_EQ_SOME_DISTINCT_AUTO",
    theorem = finite_mapAutoSeedTheory.ALOOKUP_EQ_SOME_DISTINCT_AUTO},
 benchLib.RewriteAdd
   {name = "list$MAP_ZIP", theorem = listTheory.MAP_ZIP},
 benchLib.FactAdd
   {name = "finite_mapAutoSeed$MEM_SND_ZIP_AUTO",
    theorem = finite_mapAutoSeedTheory.MEM_SND_ZIP_AUTO},
 benchLib.RewriteAdd
   {name = "bool$EQ_SYM_EQ", theorem = boolTheory.EQ_SYM_EQ}]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 776, commit = "f7e02b7e"},
 representative = false},
{id = "map_L781_ran_map_option",
 goal = ``(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  (λb_x. OPTION_MAP v_f0 (v_m0 b_x)) =
IMAGE v_f0
  ((λb_ran_func b_ran_value.
        ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value) v_m0)``,
 source_method = "by (auto simp add: ran_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 781, commit = "f7e02b7e"},
 representative = false},
{id = "map_L786_graph_empty",
 goal = ``(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) (λb_x. NONE) =
∅``,
 source_method = "by simp",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 786, commit = "f7e02b7e"},
 representative = false},
{id = "map_L789_in_graphI",
 goal = ``v_m0 v_k0 = SOME v_v0 ⇒
(v_k0,v_v0) ∈
(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m0``,
 source_method = "by blast",
 recipe = benchLib.Invoke (benchLib.Blast,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 789, commit = "f7e02b7e"},
 representative = false},
{id = "map_L792_in_graphD",
 goal = ``(v_k0,v_v0) ∈
(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m0 ⇒
v_m0 v_k0 = SOME v_v0``,
 source_method = "by blast",
 recipe = benchLib.Invoke (benchLib.Blast,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 792, commit = "f7e02b7e"},
 representative = false},
{id = "map_L795_graph_map_upd",
 goal = ``(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair))
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m0 v_k0 (SOME v_v0)) =
(v_k0,v_v0) INSERT
(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair))
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m0 v_k0 NONE)``,
 source_method = "by (auto split: if_splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 795, commit = "f7e02b7e"},
 representative = false},
{id = "map_L798_graph_fun_upd_None",
 goal = ``(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair))
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m0 v_k0 NONE) =
(λb_e.
     b_e ∈
     (λb_graph_func b_graph_pair.
          b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m0 ∧
     FST b_e ≠ v_k0)``,
 source_method = "by (auto split: if_splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 798, commit = "f7e02b7e"},
 representative = false},
{id = "map_L801_graph_restrictD_1",
 goal = ``(v_k0,v_v0) ∈
(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair))
  ((λb_restrict_func b_restrict_set b_restrict_key.
        if b_restrict_key ∈ b_restrict_set then
          b_restrict_func b_restrict_key
        else NONE) v_m0 v_A0) ⇒
v_k0 ∈ v_A0``,
 source_method = "by (auto simp: restrict_map_def split: if_splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 801, commit = "f7e02b7e"},
 representative = false},
{id = "map_L801_graph_restrictD_2",
 goal = ``(v_k0,v_v0) ∈
(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair))
  ((λb_restrict_func b_restrict_set b_restrict_key.
        if b_restrict_key ∈ b_restrict_set then
          b_restrict_func b_restrict_key
        else NONE) v_m0 v_A0) ⇒
v_m0 v_k0 = SOME v_v0``,
 source_method = "by (auto simp: restrict_map_def split: if_splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 801, commit = "f7e02b7e"},
 representative = false},
{id = "map_L807_graph_map_comp",
 goal = ``(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair))
  ((λb_comp_left b_comp_right b_comp_key.
        OPTION_BIND (b_comp_right b_comp_key) b_comp_left) v_m10 v_m20) =
(λb_relcomp_left b_relcomp_right b_relcomp_pair.
     ∃b_relcomp_middle.
       (FST b_relcomp_pair,b_relcomp_middle) ∈ b_relcomp_left ∧
       (b_relcomp_middle,SND b_relcomp_pair) ∈ b_relcomp_right)
  ((λb_graph_func b_graph_pair.
        b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m20)
  ((λb_graph_func b_graph_pair.
        b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m10)``,
 source_method = "by (auto simp: map_comp_Some_iff relcomp_unfold)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 807, commit = "f7e02b7e"},
 representative = false},
{id = "map_L810_graph_map_add",
 goal = ``(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m10 ∩
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m20 = ∅ ⇒
(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair))
  ((λb_add_left b_add_right b_add_key.
        option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME)
     v_m10 v_m20) =
(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m10 ∪
(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m20``,
 source_method = "by force",
 recipe = benchLib.Invoke (benchLib.Force,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 810, commit = "f7e02b7e"},
 representative = false},
{id = "map_L813_graph_eq_to_snd_dom",
 goal = ``(λb_graph_func b_graph_pair.
     b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m0 =
IMAGE (λb_x. (b_x,THE (v_m0 b_x)))
  ((λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0)``,
 source_method = "by force",
 recipe = benchLib.Invoke (benchLib.Force,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 813, commit = "f7e02b7e"},
 representative = false},
{id = "map_L816_fst_graph_eq_dom",
 goal = ``IMAGE FST
  ((λb_graph_func b_graph_pair.
        b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m0) =
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_m0``,
 source_method = "by force",
 recipe = benchLib.Invoke (benchLib.Force,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 816, commit = "f7e02b7e"},
 representative = false},
{id = "map_L822_snd_graph_ran",
 goal = ``IMAGE SND
  ((λb_graph_func b_graph_pair.
        b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m0) =
(λb_ran_func b_ran_value. ∃b_ran_key. b_ran_func b_ran_key = SOME b_ran_value)
  v_m0``,
 source_method = "by force",
 recipe = benchLib.Invoke (benchLib.Force,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 822, commit = "f7e02b7e"},
 representative = false},
{id = "map_L828_finite_graph_map_of",
 goal =
   ``FINITE
       ((\b_graph_func : 'a -> 'b option.
           \b_graph_pair : 'a # 'b.
             b_graph_func (FST b_graph_pair) =
             SOME (SND b_graph_pair))
          (alist$ALOOKUP (v_al0 : ('a # 'b) list)))``,
 source_method = "by blast",
 recipe = benchLib.Invoke (benchLib.Blast,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_finite_bounded_lookup_graph" "parityTranslation" "source_finite_bounded_lookup_graph"),
benchLib.RewriteAdd (benchExplicit.named_at "alist$ALOOKUP_MEM" "alist" "ALOOKUP_MEM")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 828, commit = "f7e02b7e"},
 representative = false},
{id = "map_L832_graph_map_of_if_distinct_dom",
 goal =
   ``(ALL_DISTINCT (MAP FST (v_al0 : ('a # 'b) list)) ==>
      ((\b_graph_func : 'a -> 'b option.
          \b_graph_pair : 'a # 'b.
            b_graph_func (FST b_graph_pair) =
            SOME (SND b_graph_pair))
         (alist$ALOOKUP (v_al0 : ('a # 'b) list)) =
       LIST_TO_SET (v_al0 : ('a # 'b) list)))``,
 source_method = "by auto",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 832, commit = "f7e02b7e"},
 representative = false},
{id = "map_L849_inj_on_fst_graph",
 goal = ``(λb_inj_func b_inj_set. INJ b_inj_func b_inj_set 𝕌(:α)) FST
  ((λb_graph_func b_graph_pair.
        b_graph_func (FST b_graph_pair) = SOME (SND b_graph_pair)) v_m0)``,
 source_method = "by force",
 recipe = benchLib.Invoke (benchLib.Force,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 849, commit = "f7e02b7e"},
 representative = false},
{id = "map_L854_map_le_empty",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) (λb_x. NONE) v_g0``,
 source_method = "by (simp add: map_le_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 854, commit = "f7e02b7e"},
 representative = false},
{id = "map_L857_upd_None_map_le",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_f0 v_x0 NONE) v_f0``,
 source_method = "by (force simp add: map_le_def)",
 recipe = benchLib.Invoke (benchLib.Force,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 857, commit = "f7e02b7e"},
 representative = false},
{id = "map_L860_map_le_upd",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_f0 v_g0 ⇒
(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_f0 v_a0 v_b0)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_g0 v_a0 v_b0)``,
 source_method = "by (fastforce simp add: map_le_def)",
 recipe = benchLib.AllGoals (
benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
benchLib.Invoke (benchLib.Fastforce,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")])),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 860, commit = "f7e02b7e"},
 representative = false},
{id = "map_L863_map_le_imp_upd_le",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_m10 v_m20 ⇒
(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m10 v_x0 NONE)
  ((λb_update_func b_update_key b_update_value b_update_query.
        if b_update_query = b_update_key then b_update_value
        else b_update_func b_update_query) v_m20 v_x0 (SOME v_y0))``,
 source_method = "by (force simp add: map_le_def)",
 recipe = benchLib.Invoke (benchLib.Force,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 863, commit = "f7e02b7e"},
 representative = false},
{id = "map_L874_map_le_implies_dom_le",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_f0 v_g0 ⇒
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_f0 ⊆
(λb_dom_func b_dom_key. b_dom_func b_dom_key ≠ NONE) v_g0``,
 source_method = "by (fastforce simp add: map_le_def dom_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 874, commit = "f7e02b7e"},
 representative = false},
{id = "map_L877_map_le_refl",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_f0 v_f0``,
 source_method = "by (simp add: map_le_def)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 877, commit = "f7e02b7e"},
 representative = false},
{id = "map_L880_map_le_trans",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_m10 v_m20 ⇒
(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_m20 v_m30 ⇒
(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_m10 v_m30``,
 source_method = "by (auto simp add: map_le_def dom_def)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 880, commit = "f7e02b7e"},
 representative = false},
{id = "map_L887_map_le_map_add",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_f0
  ((λb_add_left b_add_right b_add_key.
        option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_g0
     v_f0)``,
 source_method = "by (fastforce simp: map_le_def)",
 recipe = benchLib.AllGoals (
benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none")]),
benchLib.Invoke (benchLib.Fastforce,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none")])),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 887, commit = "f7e02b7e"},
 representative = false},
{id = "map_L890_map_le_iff_map_add_commute",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_f0
  ((λb_add_left b_add_right b_add_key.
        option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_f0
     v_g0) ⇔
(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_f0
  v_g0 =
(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_g0
  v_f0``,
 source_method = "by (fastforce simp: map_add_def map_le_def fun_eq_iff split: option.splits)",
 recipe = benchLib.Invoke (benchLib.Fastforce,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 890, commit = "f7e02b7e"},
 representative = false},
{id = "map_L893_map_add_le_mapE",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value)
  ((λb_add_left b_add_right b_add_key.
        option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_f0
     v_g0) v_h0 ⇒
(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_g0 v_h0``,
 source_method = "by (fastforce simp: map_le_def map_add_def dom_def)",
 recipe = benchLib.AllGoals (
benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none")]),
benchLib.Invoke (benchLib.Fastforce,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none")])),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 893, commit = "f7e02b7e"},
 representative = false},
{id = "map_L896_map_add_le_mapI",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_f0 v_h0 ⇒
(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_g0 v_h0 ⇒
(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value)
  ((λb_add_left b_add_right b_add_key.
        option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_f0
     v_g0) v_h0``,
 source_method = "by (auto simp: map_le_def map_add_def dom_def split: option.splits)",
 recipe = benchLib.Invoke (benchLib.Auto,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 896, commit = "f7e02b7e"},
 representative = false},
{id = "map_L899_map_add_subsumed1",
 goal = ``(λb_le_left b_le_right.
     ∀b_le_key b_le_value.
       b_le_left b_le_key = SOME b_le_value ⇒
       b_le_right b_le_key = SOME b_le_value) v_f0 v_g0 ⇒
(λb_add_left b_add_right b_add_key.
     option_CASE (b_add_right b_add_key) (b_add_left b_add_key) SOME) v_f0
  v_g0 = v_g0``,
 source_method = "by (simp add: map_add_le_mapI map_le_antisym)",
 recipe = benchLib.Invoke (benchLib.Simp,
[benchLib.RewriteAdd (benchExplicit.named_at "pred_set$SPECIFICATION" "pred_set" "SPECIFICATION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$EXTENSION" "pred_set" "EXTENSION"),
benchLib.DefinitionAdd (benchExplicit.named_at "pred_set$SUBSET_DEF" "pred_setAutoSeed" "SUBSET_DEF_AUTO"),
benchLib.RewriteAdd (benchExplicit.named_at "bool$FUN_EQ_THM" "bool" "FUN_EQ_THM"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_range_update_none" "parityTranslation" "source_range_update_none"),
benchLib.RewriteAdd (benchExplicit.named_at "option$option_case_eq" "option" "option_case_eq"),
benchLib.SplitAdd (benchExplicit.named_at "parityTranslation$source_option_split" "parityTranslation" "source_option_split"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_option_overlay_not_none" "parityTranslation" "source_option_overlay_not_none"),
benchLib.RewriteAdd (benchExplicit.named_at "parityTranslation$source_map_add_subsumed_step" "parityTranslation" "source_map_add_subsumed_step")]),
 excl = [],
 provenance = {file = "src/HOL/Map.thy", line = 899, commit = "f7e02b7e"},
 representative = false}]

end
