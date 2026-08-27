Theory listAutoSeed
Ancestors
  list
Libs
  clasetLib clasimpLib

fun export_at attr (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = attr, args = [], thm = saved}
  end

fun export_iff entry = export_at "iff" entry

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
     ("EVERY_MEM_AUTO", listTheory.EVERY_MEM),
     ("MEM_FILTER_AUTO", listTheory.MEM_FILTER)]

Theorem LIST_REL_REVERSE_AUTO[iff]:
  !R left right.
    LIST_REL R (REVERSE left) (REVERSE right) <=> LIST_REL R left right
Proof
  metis_tac [LIST_REL_REVERSE, REVERSE_REVERSE]
QED

(* src/HOL/List.thy:3475-3481 @ f7e02b7e.  The translated half-open
   interval [start..<finish] is GENLIST (\offset. start + offset)
   (finish - start). *)
Theorem GENLIST_RANGE_SUC_AUTO[simp]:
  !start finish.
    start <= finish ==>
    GENLIST (\offset. start + offset) (SUC finish - start) =
    SNOC finish (GENLIST (\offset. start + offset) (finish - start))
Proof
  rpt strip_tac
  >> `SUC finish - start = SUC (finish - start)` by decide_tac
  >> `start + (finish - start) = finish` by decide_tac
  >> simp[listTheory.GENLIST]
QED

(* src/HOL/List.thy:7279 @ f7e02b7e.  Isabelle gives lexicographic
   transitivity to the classical reasoner as [intro], where HOL4 states it
   but declares it to no claset.  The rest of the lexicographic block needs
   nothing: [simp] already covers lexord_Nil_left, lexord_Nil_right,
   lexord_cons_cons and Nil_lenlex_iff1 and iff2 through LLEX_THM,
   LLEX_NIL2, SHORTLEX_THM and SHORTLEX_NIL2, and lexord_transI carries no
   attribute, so LLEX_transitive gets none.

   wf_lenlex is [intro!] at 7253 and is deliberately not transplanted.
   HOL4 carries WF_SHORTLEX as a [simp] rule, which already closes
   WF (SHORTLEX R) from WF R, and declaring it a *safe* intro rule instead
   owes seedAudit the invertibility obligation WF (SHORTLEX R) ==> WF R.
   That obligation is true but the audit's fixed prover stack does not
   close it, and an unproven safety claim is not worth the little the
   declaration would add. *)
val _ =
  export_at "intro"
    ("SHORTLEX_TRANSITIVE_AUTO", listTheory.SHORTLEX_transitive)
