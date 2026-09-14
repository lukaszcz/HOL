Theory pred_setAutoSeed
Ancestors
  pred_set relation
Libs
  clasetLib clasimpLib

fun export_iff (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = "iff", args = [], thm = saved}
  end

val sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}

Theorem EXISTS_SAME_IMAGE_AUTO[iff]:
  !function item. ?witness. function item = function witness
Proof
  metis_tac[]
QED

(* src/HOL/Fun.thy:140 @ f7e02b7e.  A rewrite only: Isabelle states
   inj_on as a definition and declares it to neither simpset nor
   claset, and the [iff] elimination this used to carry unfolded every
   INJ assumption before a supplied inj_onD could apply to it. *)
Theorem INJ_DEF_AUTO[simp]:
  !function source target.
    INJ function source target <=>
    (!item. item IN source ==> function item IN target) /\
    (!left right.
       left IN source /\ right IN source ==>
       function left = function right ==> left = right)
Proof
  MATCH_ACCEPT_TAC pred_setTheory.INJ_DEF
QED

(* src/HOL/Set.thy:566-1088 @ f7e02b7e *)
val _ =
  List.app export_iff
    [(* src/HOL/Set.thy:566-569 @ f7e02b7e.  This one declaration carries
        both empty_iff and emptyE: stated as a negation, the [iff]
        machinery derives the safe elimination that closes a branch on
        a membership in the empty set.  The tableau leg has no simpset,
        so without the rule it can only carry such a membership along. *)
     ("NOT_IN_EMPTY_AUTO", pred_setTheory.NOT_IN_EMPTY),
     ("EMPTY_SUBSET_AUTO", pred_setTheory.EMPTY_SUBSET),
     ("UNIV_NOT_EMPTY_AUTO", pred_setTheory.UNIV_NOT_EMPTY),
     ("IN_POW_AUTO", pred_setTheory.IN_POW),
     ("IN_COMPL_AUTO", pred_setTheory.IN_COMPL),
     ("IN_INTER_AUTO", pred_setTheory.IN_INTER),
     ("IN_UNION_AUTO", pred_setTheory.IN_UNION),
     ("IN_DIFF_AUTO", pred_setTheory.IN_DIFF),
     ("IN_INSERT_AUTO", pred_setTheory.IN_INSERT),
     ("IN_SING_AUTO", pred_setTheory.IN_SING),
     ("EQUAL_SING_AUTO", pred_setTheory.EQUAL_SING),
     ("INSERT_EQ_SING_AUTO", pred_setTheory.INSERT_EQ_SING),
     ("IN_IMAGE_AUTO", pred_setTheory.IN_IMAGE),
     ("FORALL_IN_IMAGE_AUTO", pred_setTheory.FORALL_IN_IMAGE),
     ("IMAGE_EQ_EMPTY_1_AUTO",
      GEN_ALL (CONJUNCT1 (SPEC_ALL pred_setTheory.IMAGE_EQ_EMPTY))),
     ("IMAGE_EQ_EMPTY_2_AUTO",
      GEN_ALL (CONJUNCT2 (SPEC_ALL pred_setTheory.IMAGE_EQ_EMPTY))),
     ("PSUBSET_DEF_AUTO", pred_setTheory.PSUBSET_DEF)]

(* src/HOL/Set.thy:598-601 @ f7e02b7e.  Isabelle states UNIV_I as [simp]
   and declares the classical half separately as an unsafe [intro] --
   "unsafe makes it less likely to cause problems".  Safe, it fires on
   any [item IN unknown] and settles the unknown on the universe before
   the branch's other goals are looked at; pred_set already carries
   IN_UNIV as [simp], so only the classical half is declared here. *)
Theorem IN_UNIV_AUTO[intro]:
  !item. item IN univ(:'a)
Proof
  MATCH_ACCEPT_TAC pred_setTheory.IN_UNIV
QED

(* src/HOL/Complete_Lattices.thy:950,955,1055,1060 @ f7e02b7e.  Isabelle
   keeps a union membership in the claset as rules, not as the [simp]
   equivalence [Union_iff] beside them, and declares the plain and the
   indexed union separately: HOL4 writes the indexed one as a union over
   an image, so the pair over [BIGUNION (IMAGE f sos)] is the one a goal
   stated with a set-valued function meets.  Without them a membership in
   a BIGUNION is inert in a claset search -- the tableau leg has no
   simpset, so it can only carry such a literal along. *)
Theorem BIGUNION_I_AUTO[intro]:
  !item s sos. s IN sos ==> item IN s ==> item IN BIGUNION sos
Proof
  SIMP_TAC bool_ss [pred_setTheory.IN_BIGUNION] THEN METIS_TAC []
QED

Theorem BIGUNION_E_AUTO[selim]:
  !item sos conclusion.
    item IN BIGUNION sos ==>
    (!s. item IN s ==> s IN sos ==> conclusion) ==>
    conclusion
Proof
  SIMP_TAC bool_ss [pred_setTheory.IN_BIGUNION] THEN METIS_TAC []
QED

Theorem BIGUNION_IMAGE_I_AUTO[intro]:
  !item f sos index.
    index IN sos ==> item IN f index ==> item IN BIGUNION (IMAGE f sos)
Proof
  SIMP_TAC bool_ss [pred_setTheory.IN_BIGUNION_IMAGE] THEN METIS_TAC []
QED

Theorem BIGUNION_IMAGE_E_AUTO[selim]:
  !item f sos conclusion.
    item IN BIGUNION (IMAGE f sos) ==>
    (!index. index IN sos ==> item IN f index ==> conclusion) ==>
    conclusion
Proof
  SIMP_TAC bool_ss [pred_setTheory.IN_BIGUNION_IMAGE] THEN METIS_TAC []
QED

(* src/HOL/Set.thy:1746-1752 @ f7e02b7e. *)
val _ =
  export_iff ("IN_PREIMAGE_AUTO", pred_setTheory.IN_PREIMAGE)

(* src/HOL/Set.thy:484,493,501,505 @ f7e02b7e.  Isabelle states the
   membership reading of a subset as [subset_eq] (:505) and declares it
   to neither simpset nor claset: a subset is settled classically, by
   [subsetI] [intro!] and the two unsafe eliminations [subsetD] (:493)
   and [subsetCE] (:501).  Carrying the equivalence as an [iff] instead
   put the reading in the simpset, where Isabelle keeps it out, and a
   quantified subset among the assumptions then became a conditional
   rewrite whose condition carries a variable its left-hand side does
   not: [set (TAKE i l) SUBSET set l] rewrites to [MEM x l] conditional
   on [MEM x (TAKE i l)], and since the left-hand side is a membership
   at two variables it matches every membership, while discharging the
   condition reproduces the same shape.  [map_L519] is the goal that
   found it -- its [using set_take_subset] hands the search exactly
   that assumption, and simplification did not return inside five
   minutes. *)
Theorem SUBSET_I_AUTO[sintro]:
  !left right.
    (!item. item IN left ==> item IN right) ==> left SUBSET right
Proof
  REWRITE_TAC [pred_setTheory.SUBSET_DEF]
QED

Theorem SUBSET_D_AUTO[elim]:
  !left right item.
    left SUBSET right ==> item IN left ==> item IN right
Proof
  REWRITE_TAC [pred_setTheory.SUBSET_DEF] THEN METIS_TAC []
QED

Theorem SUBSET_CE_AUTO[elim]:
  !left right item conclusion.
    left SUBSET right ==>
    (item NOTIN left ==> conclusion) ==>
    (item IN right ==> conclusion) ==>
    conclusion
Proof
  REWRITE_TAC [pred_setTheory.SUBSET_DEF] THEN METIS_TAC []
QED

val _ =
  clasetLib.export_rule sintro_spec "pred_set.SUBSET_ANTISYM"

(* src/HOL/Set.thy:551 @ f7e02b7e.  SUBSET_ANTISYM is Isabelle's
   equalityI; this is its elimination counterpart.  Without it the
   claset reaches a set equality only by proving one, so an equality
   among the hypotheses contributes nothing.  The case split is what
   makes it usable in a search: the item is left to unification, and
   both branches keep the equality's full content. *)
Theorem SET_EQUALITY_CASES_AUTO[elim]:
  !left right item conclusion.
    left = right ==>
    (item IN left ==> item IN right ==> conclusion) ==>
    (item NOTIN left ==> item NOTIN right ==> conclusion) ==>
    conclusion
Proof
  REPEAT GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN metis_tac[]
QED

(* src/HOL/Set.thy:1192-1195 @ f7e02b7e.  Collect_empty_eq and
   empty_Collect_eq.  Sets are predicates here, so every set is a set
   former and Isabelle's two rules are one schema stated on an arbitrary
   set, in both orientations.  Without it an emptiness claim reached by
   unfolding stays an equation between formers, and the search can only
   attack it by splitting the equation on an undetermined item. *)
Theorem SET_EQ_EMPTY_AUTO[iff]:
  !collection. (collection = {}) <=> !item. item NOTIN collection
Proof
  REWRITE_TAC [pred_setTheory.EXTENSION, pred_setTheory.NOT_IN_EMPTY]
QED

Theorem EMPTY_EQ_SET_AUTO[iff]:
  !collection. ({} = collection) <=> !item. item NOTIN collection
Proof
  ONCE_REWRITE_TAC [boolTheory.EQ_SYM_EQ] THEN
  REWRITE_TAC [pred_setTheory.EXTENSION, pred_setTheory.NOT_IN_EMPTY]
QED

(* src/HOL/Finite_Set.thy:158-532 @ f7e02b7e.  HOL4 COUNT k is
   Isabelle's set comprehension {n | n < k}. *)
val _ =
  List.app export_iff
    [("FINITE_COUNT_AUTO", pred_setTheory.FINITE_COUNT),
     ("FINITE_UNION_AUTO", pred_setTheory.FINITE_UNION),
     ("FINITE_POW_AUTO", pred_setTheory.FINITE_POW_EQN)]

(* src/HOL/Relation.thy:19-1426 @ f7e02b7e.  Isabelle r O s maps to
   HOL4 s O r because the two libraries print composition oppositely. *)
val _ =
  List.app export_iff
    [("EMPTY_REL_AUTO", relationTheory.EMPTY_REL_DEF),
     ("RUNIV_AUTO", relationTheory.RUNIV),
     ("RINTER_AUTO", relationTheory.RINTER),
     ("RUNION_AUTO", relationTheory.RUNION),
     ("REL_COMP_AUTO", relationTheory.O_DEF),
     ("REL_INV_AUTO", relationTheory.inv_DEF),
     ("IN_RDOM_AUTO", relationTheory.IN_RDOM),
     ("IN_RRANGE_AUTO", relationTheory.IN_RRANGE)]
