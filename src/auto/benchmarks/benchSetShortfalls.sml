structure benchSetShortfalls =
struct

(* Every record here is an executable Set.thy or Set_Theory.thy goal
   that the assigned tactic did not close in the 2026-08-28
   measurement.  The classification names the root cause and the note
   says what stands in the way.  A goal listed in [over_budget] was
   still searching when the budget expired, so its classification is
   the family it belongs to rather than an observed residual. *)

val over_budget =
  ["set_L1091_psubset_insert_iff", "set_L1125_image_Pow_surj",
   "set_L1604_Pow_singleton_iff", "set_L1607_Pow_insert",
   "set_L1790_vimage_image_eq",
   "set_L1847_is_singleton_the_elem", "set_L1976_disjnt_commute",
   "set_L1979_disjnt_iff", "set_L1994_disjnt_subset1",
   "set_L1997_disjnt_subset2", "set_L2003_disjnt_Un2",
   "set_L928_subset_image_iff", "set_L994_image_add_0",
   "set_theory_L168", "set_theory_L184", "set_theory_L36",
   "set_theory_L44", "set_theory_L48"]

fun record note id : benchLib.shortfall =
  {id = id, cause = benchLib.EngineLimitation, date = "2026-08-28",
   note =
     if List.exists (fn other => other = id) over_budget then
       note ^ " (the search exceeded the budget rather than " ^
       "reporting no proof)"
     else
       note}

fun classified classification note ids =
  map (record (classification ^ ": " ^ note)) ids

(* The four goals below are the only ones in this family whose
   assigned tactic is denied a fact it would otherwise have: each goal
   is itself an ambient characterisation, and rule A1 withholds it. *)
val excluded_characterisation =
  classified "excluded characterisation"
    ("the goal is the ambient characterisation itself, so the "
     ^ "measurement withholds the one fact that closes it and there "
     ^ "is no second route to search for")
    ["set_L572_empty_subsetI", "set_L690_Int_iff", "set_L717_Un_iff",
     "set_L769_insert_iff"]

val blast_set_rule_forms =
  classified "blast set rule forms"
    ("BLAST_TAC reports no proof and the obstruction is not "
     ^ "isolated: these goals withhold no ambient analogue at all, "
     ^ "so the earlier reading -- that excluding the goal's own "
     ^ "characterisation left no second route -- was wrong for them")
    ["set_L1091_psubset_insert_iff", "set_L1125_image_Pow_surj",
     "set_L1499_Diff_triv", "set_L1604_Pow_singleton_iff",
     "set_L1607_Pow_insert", "set_L1982_disjnt_sym",
     "set_L796_insert_ident", "set_L869_doubleton_eq_iff",
     "set_L872_Un_singleton_iff", "set_L875_singleton_Un_iff",
     "set_L928_subset_image_iff", "set_L994_image_add_0",
     "set_theory_L36", "set_theory_L44", "set_theory_L48",
     "set_theory_L168", "set_theory_L184"]

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
     "set_L2003_disjnt_Un2"]

val bounded_quantifier_one_point =
  classified "bounded-quantifier one-point"
    ("the goal states bounded quantification with IN rather than "
     ^ "with RES_FORALL, so the one-point rewrite never fires")
    ["set_L421_ball_triv", "set_L425_bex_triv"]

val vimage =
  classified "vimage"
    ("PREIMAGE reasoning is downstream of the missing set rule "
     ^ "forms")
    ["set_L1740_vimage_eq", "set_L1790_vimage_image_eq"]

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

val equality_between_two_abstractions =
  classified "equality between two abstractions"
    ("the goal is an equation between two functions, which the "
     ^ "simpset can only reach pointwise; the translation writes a "
     ^ "set as a lambda, so [{x | P x} = {x | Q x}] arrives as "
     ^ "[(\\x. P x) = (\\x. Q x)], the simpset's eta step contracts "
     ^ "both sides before the antecedent can rewrite under the "
     ^ "binder, and function extensionality -- which Isabelle's set "
     ^ "type supplies and the predicate encoding drops -- is not an "
     ^ "ambient rule")
    ["set_L76_Collect_cong"]

val entries : benchLib.shortfall list =
  blast_set_rule_forms @
  excluded_characterisation @
  isabelle_lattice_instance @
  disjnt @
  bounded_quantifier_one_point @
  vimage @
  definite_description @
  set_monad_bind @
  image_comprehension @
  boolean_induction_rule @
  instantiated_fact_citation @
  equality_between_two_abstractions

end
