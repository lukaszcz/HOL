structure benchSetShortfalls =
struct

(* Every record here is an executable Set.thy or Set_Theory.thy goal
   that the assigned tactic did not close in the 2026-08-20
   measurement.  The classification names the root cause and the note
   says what stands in the way.  A goal listed in [over_budget] was
   still searching when the budget expired, so its classification is
   the family it belongs to rather than an observed residual. *)

val over_budget =
  ["set_L1088_psubsetE", "set_L1091_psubset_insert_iff",
   "set_L1113_psubset_imp_ex_mem", "set_L1122_image_Pow_mono",
   "set_L1172_Diff_subset_conv", "set_L1540_Diff_partition",
   "set_L1604_Pow_singleton_iff", "set_L1607_Pow_insert",
   "set_L1610_Pow_Compl", "set_L1637_subset_iff_psubset_eq",
   "set_L1725_Int_Collect_mono", "set_L1790_vimage_image_eq",
   "set_L1799_image_subset_iff_subset_vimage",
   "set_L1847_is_singleton_the_elem", "set_L1976_disjnt_commute",
   "set_L1979_disjnt_iff", "set_L1994_disjnt_subset1",
   "set_L1997_disjnt_subset2", "set_L2003_disjnt_Un2",
   "set_L910_image_subsetI", "set_L915_image_subset_iff",
   "set_L928_subset_image_iff", "set_L994_image_add_0",
   "set_theory_L164", "set_theory_L168", "set_theory_L184",
   "set_theory_L36", "set_theory_L44", "set_theory_L48"]

fun record note id : benchLib.shortfall =
  {id = id, cause = benchLib.EngineLimitation, date = "2026-08-20",
   note =
     if List.exists (fn other => other = id) over_budget then
       note ^ " (the search exceeded the budget rather than " ^
       "reporting no proof)"
     else
       note}

fun classified classification note ids =
  map (record (classification ^ ": " ^ note)) ids

val blast_set_rule_forms =
  classified "blast set rule forms"
    ("BLAST_TAC has no Isabelle-style set introduction and "
     ^ "elimination rules, so excluding the characterisation that "
     ^ "is the goal leaves it no second route")
    ["set_L1088_psubsetE", "set_L1091_psubset_insert_iff",
     "set_L1113_psubset_imp_ex_mem", "set_L1122_image_Pow_mono",
     "set_L1125_image_Pow_surj", "set_L1172_Diff_subset_conv",
     "set_L1192_Collect_empty_eq", "set_L1195_empty_Collect_eq",
     "set_L1213_Collect_mono_iff", "set_L1321_Int_Collect",
     "set_L1366_Un_insert_right", "set_L1393_Un_Int_crazy",
     "set_L1499_Diff_triv", "set_L1540_Diff_partition",
     "set_L1546_Un_Diff_cancel", "set_L1555_Diff_Int",
     "set_L1561_Un_Diff", "set_L1604_Pow_singleton_iff",
     "set_L1607_Pow_insert", "set_L1610_Pow_Compl",
     "set_L1628_Int_Diff_Un", "set_L1637_subset_iff_psubset_eq",
     "set_L1722_Collect_mono", "set_L1725_Int_Collect_mono",
     "set_L1982_disjnt_sym", "set_L572_empty_subsetI",
     "set_L690_Int_iff", "set_L717_Un_iff", "set_L769_insert_iff",
     "set_L796_insert_ident", "set_L869_doubleton_eq_iff",
     "set_L872_Un_singleton_iff", "set_L875_singleton_Un_iff",
     "set_L910_image_subsetI", "set_L915_image_subset_iff",
     "set_L928_subset_image_iff", "set_L994_image_add_0",
     "set_theory_L36", "set_theory_L44", "set_theory_L48",
     "set_theory_L164", "set_theory_L168", "set_theory_L184"]

val membership_against_predicate_application =
  classified "membership against predicate application"
    ("neither the claset nor BLAST_TAC's preprocessing crosses "
     ^ "SPECIFICATION, which separates x IN P from P x")
    ["set_L108_Collect_eqI", "set_L1245_insert_Collect",
     "set_L1646_ball_simps_8", "set_L1659_bex_simps_6"]

val isabelle_lattice_instance =
  classified "Isabelle lattice instance"
    ("the source proof unfolds the lattice instance for 'a set; "
     ^ "pred_set defines the operation directly and has no "
     ^ "instance to unfold")
    ["set_L563_empty_def", "set_L595_UNIV_def", "set_L687_Int_def",
     "set_L714_Un_def"]

val disjnt =
  classified "disjnt"
    ("DISJOINT_DEF reduces the goal to a set equality that then "
     ^ "meets the membership-against-application gap")
    ["set_L1976_disjnt_commute", "set_L1979_disjnt_iff",
     "set_L1988_disjnt_insert1", "set_L1991_disjnt_insert2",
     "set_L1994_disjnt_subset1", "set_L1997_disjnt_subset2",
     "set_L2003_disjnt_Un2", "set_L2012_pairwise_disjnt_iff"]

val bounded_quantifier_one_point =
  classified "bounded-quantifier one-point"
    ("the goal states bounded quantification with IN rather than "
     ^ "with RES_FORALL, so the one-point rewrite never fires")
    ["set_L421_ball_triv", "set_L425_bex_triv",
     "set_L429_bex_triv_one_point1", "set_L432_bex_triv_one_point2",
     "set_L435_bex_one_point1", "set_L438_bex_one_point2"]

val vimage =
  classified "vimage"
    ("PREIMAGE reasoning is downstream of the missing set rule "
     ^ "forms")
    ["set_L1740_vimage_eq", "set_L1770_vimage_Collect_eq",
     "set_L1773_vimage_Collect", "set_L1790_vimage_image_eq",
     "set_L1793_image_vimage_subset", "set_L1796_image_vimage_eq",
     "set_L1799_image_subset_iff_subset_vimage"]

val definite_description =
  classified "definite description"
    ("CHOICE over a singleton is not reduced by the assigned "
     ^ "tactic")
    ["set_L1844_the_elem_eq", "set_L1847_is_singleton_the_elem"]

val set_monad_bind =
  classified "set monad bind"
    ("the set-monad bind has no pred_set counterpart the "
     ^ "assigned tactic unfolds")
    ["set_L1874_empty_bind"]

val image_comprehension =
  classified "image comprehension"
    ("IMAGE is not unfolded to its comprehension by the assigned "
     ^ "tactic")
    ["set_L968_image_cong"]

val boolean_induction_rule =
  classified "boolean induction rule"
    ("the source proof cites an induction rule as an "
     ^ "introduction rule; the claset has no boolean case-split "
     ^ "rule of that shape")
    ["set_L1587_all_bool_eq"]

val instantiated_fact_citation =
  classified "instantiated fact citation"
    ("the source method instantiates its cited facts with [OF "
     ^ "...] and [of ...]; the recipe compiler represents a "
     ^ "citation but not its instantiation")
    ["set_theory_L79"]

val entries : benchLib.shortfall list =
  blast_set_rule_forms @
  membership_against_predicate_application @
  isabelle_lattice_instance @
  disjnt @
  bounded_quantifier_one_point @
  vimage @
  definite_description @
  set_monad_bind @
  image_comprehension @
  boolean_induction_rule @
  instantiated_fact_citation

end
