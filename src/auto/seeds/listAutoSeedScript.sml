Theory listAutoSeed
Ancestors
  list
Libs
  clasetLib clasimpLib

fun export_iff (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = "iff", args = [], thm = saved}
  end

(* src/HOL/List.thy:874-993 @ f7e02b7e *)
val _ =
  List.app export_iff
    [("LENGTH_EQ_0_AUTO", listTheory.LENGTH_EQ_0),
     ("LENGTH_NON_NIL_AUTO", listTheory.LENGTH_NON_NIL),
     ("APPEND_EQ_NIL_LEFT_AUTO", CONJUNCT1 listTheory.APPEND_eq_NIL),
     ("APPEND_EQ_NIL_RIGHT_AUTO", CONJUNCT2 listTheory.APPEND_eq_NIL),
     ("APPEND_EQ_SELF_1_AUTO", CONJUNCT1 listTheory.APPEND_EQ_SELF),
     ("APPEND_EQ_SELF_2_AUTO",
      CONJUNCT1 (CONJUNCT2 listTheory.APPEND_EQ_SELF)),
     ("APPEND_EQ_SELF_3_AUTO",
      CONJUNCT1 (CONJUNCT2 (CONJUNCT2 listTheory.APPEND_EQ_SELF))),
     ("APPEND_EQ_SELF_4_AUTO",
      CONJUNCT2 (CONJUNCT2 (CONJUNCT2 listTheory.APPEND_EQ_SELF))),
     ("APPEND_11_LEFT_AUTO", CONJUNCT1 listTheory.APPEND_11),
     ("APPEND_11_RIGHT_AUTO", CONJUNCT2 listTheory.APPEND_11),
     ("SNOC_11_AUTO", listTheory.SNOC_11)]

(* src/HOL/List.thy:1123-1292 @ f7e02b7e *)
val _ =
  List.app export_iff
    [("MAP_EQ_NIL_LEFT_AUTO",
      GEN_ALL (CONJUNCT1 (SPEC_ALL listTheory.MAP_EQ_NIL))),
     ("MAP_EQ_NIL_RIGHT_AUTO",
      GEN_ALL (CONJUNCT2 (SPEC_ALL listTheory.MAP_EQ_NIL))),
     ("MAP_EQ_CONS_AUTO", listTheory.MAP_EQ_CONS),
     ("REVERSE_EQ_NIL_AUTO", listTheory.REVERSE_EQ_NIL),
     ("REVERSE_11_AUTO", listTheory.REVERSE_11)]

(* src/HOL/List.thy:3014-3042,6917-6970 @ f7e02b7e *)
val _ =
  List.app export_iff
    [("LIST_REL_NIL_LEFT_AUTO",
      GEN_ALL (CONJUNCT1 (SPEC_ALL listTheory.LIST_REL_NIL))),
     ("LIST_REL_NIL_RIGHT_AUTO",
      GEN_ALL (CONJUNCT2 (SPEC_ALL listTheory.LIST_REL_NIL))),
     ("LIST_REL_CONS1_AUTO", listTheory.LIST_REL_CONS1),
     ("LIST_REL_CONS2_AUTO", listTheory.LIST_REL_CONS2),
     ("EVERY_APPEND_AUTO", listTheory.EVERY_APPEND),
     ("EVERY_MEM_AUTO", listTheory.EVERY_MEM)]

Theorem LIST_REL_REVERSE_AUTO[iff]:
  !R left right.
    LIST_REL R (REVERSE left) (REVERSE right) <=> LIST_REL R left right
Proof
  metis_tac [LIST_REL_REVERSE, REVERSE_REVERSE]
QED
