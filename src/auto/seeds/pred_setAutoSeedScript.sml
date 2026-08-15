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

Theorem INJ_DEF_AUTO[iff]:
  !function source target.
    INJ function source target <=>
    (!item. item IN source ==> function item IN target) /\
    (!left right.
       left IN source /\ right IN source ==>
       function left = function right ==> left = right)
Proof
  MATCH_ACCEPT_TAC pred_setTheory.INJ_DEF
QED

(* src/HOL/Set.thy:484-1088 @ f7e02b7e *)
val _ =
  List.app export_iff
    [("SUBSET_DEF_AUTO", pred_setTheory.SUBSET_DEF),
     ("EMPTY_SUBSET_AUTO", pred_setTheory.EMPTY_SUBSET),
     ("IN_UNIV_AUTO", pred_setTheory.IN_UNIV),
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

(* src/HOL/Set.thy:1746-1752 @ f7e02b7e. *)
val _ =
  export_iff ("IN_PREIMAGE_AUTO", pred_setTheory.IN_PREIMAGE)

val _ =
  clasetLib.export_rule sintro_spec "pred_set.SUBSET_ANTISYM"

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
