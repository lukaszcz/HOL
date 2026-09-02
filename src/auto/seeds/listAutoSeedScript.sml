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
   (finish - start), written here in the eta-contracted spelling the
   src/auto simpsets normalise to. *)
Theorem GENLIST_RANGE_SUC_AUTO[simp]:
  !start finish.
    start <= finish ==>
    GENLIST ($+ start) (SUC finish - start) =
    SNOC finish (GENLIST ($+ start) (finish - start))
Proof
  rpt strip_tac
  >> `SUC finish - start = SUC (finish - start)` by decide_tac
  >> `start + (finish - start) = finish` by decide_tac
  >> simp[listTheory.GENLIST]
QED

(* src/HOL/List.thy:1381 @ f7e02b7e.  [set_upt] rewrites the set of a
   half-open interval to the interval itself, whose membership Isabelle's
   ambient interval rules then decide; the translated interval is
   GENLIST (\offset. start + offset) (finish - start), so here the same
   consequence is one rewrite.

   The zero-start spelling below is a HOL4 normalisation artefact rather
   than a second Isabelle rule: Isabelle writes one term for every start,
   while HOL4's simplifier cancels the [0 +] and leaves an abstraction
   that no eta-instance of [$+ start] matches. *)
Theorem MEM_GENLIST_INTERVAL_AUTO[simp]:
  !start count item.
    MEM item (GENLIST ($+ start) count) <=>
    start <= item /\ item < start + count
Proof
  rpt gen_tac
  >> simp[listTheory.MEM_GENLIST]
  >> eq_tac
  >- (strip_tac >> simp[])
  >> strip_tac >> qexists_tac `item - start` >> simp[]
QED

Theorem MEM_GENLIST_FROM_ZERO_AUTO[simp]:
  !count item. MEM item (GENLIST (\offset. offset) count) <=> item < count
Proof
  rpt gen_tac >> simp[listTheory.MEM_GENLIST]
QED

(* src/HOL/List.thy:1222-1228,2826-2827 @ f7e02b7e.  [map_fst_zip],
   [map_snd_zip] and [nth_zip] are simp there and undeclared here; HOL4's
   MAP_ZIP carries the two composed forms as well, which Isabelle reaches
   by rewriting under the map. *)
val _ =
  List.app (export_at "simp")
    [("MAP_ZIP_AUTO", listTheory.MAP_ZIP),
     ("EL_ZIP_AUTO", listTheory.EL_ZIP)]

(* src/HOL/List.thy:1956 @ f7e02b7e.  [nth_mem] is simp there and
   declared to no simpset here, so a goal that indexes a list and then
   asks about membership stops at [MEM (EL index xs) xs] with the index
   bound already in hand. *)
val _ =
  export_at "simp" ("EL_MEM_AUTO", listTheory.EL_MEM)

(* src/HOL/List.thy:1830,1966-1969,2328,2337 @ f7e02b7e.  The rest of
   the indexing family, which Isabelle declares simp entire so that an
   index reaches through a list however the list was built: nth_map,
   nth_list_update_eq and _neq, nth_take, nth_drop.  HOL4 states each
   and declares none, which leaves a goal that characterises an
   operation by index with the two spellings of the index side by side
   and nothing to push the index through the constructor between them.
   EL_LUPDATE is the two Isabelle update rules in one conditional
   equation; the zip case is seeded above with map_snd_zip. *)
val _ =
  List.app (export_at "simp")
    [("EL_MAP_AUTO", listTheory.EL_MAP),
     ("EL_LUPDATE_AUTO", listTheory.EL_LUPDATE),
     ("EL_TAKE_AUTO", listTheory.EL_TAKE),
     ("EL_DROP_AUTO", listTheory.EL_DROP)]

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

(* src/HOL/List.thy:7256,7318 @ f7e02b7e.  These two carry no Isabelle
   attribute, and are declared here anyway because they compensate for a
   definitional mismatch rather than add strength Isabelle lacks.

   Isabelle *defines* lenlex as the disjunction

     length xs < length ys \/ length xs = length ys /\ (xs,ys) : lex r

   so lenlex_conv is free by unfolding and the length facts never need an
   attribute: any Isabelle method that has the definition has them.  HOL4's
   SHORTLEX_def is primitive-recursive, so the same facts are theorems that
   no claset carries, and a search that unfolds SHORTLEX gets the recursion
   rather than the length comparison.  Declaring them restores what the
   Isabelle definition supplies for free; it does not go past it.

   Both are unsafe.  Read backwards, LENGTH_LT_SHORTLEX turns a SHORTLEX
   goal into a strict length comparison and loses the equal-length
   solutions, so it must not be a safe intro rule.  SHORTLEX_LENGTH_LE
   reads a SHORTLEX hypothesis, so it is a destruction rule; [forward]
   would not serve, because a forward declaration leaves the classical
   netpairs untouched and these goals are handed auto.
   SHORTLEX_LENGTH_LE is itself a corpus goal, which A1 withholds it
   from; that is the mechanism working, not an exemption. *)
val _ =
  export_at "intro" ("LENGTH_LT_SHORTLEX_AUTO", listTheory.LENGTH_LT_SHORTLEX)

val _ =
  export_at "dest" ("SHORTLEX_LENGTH_LE_AUTO", listTheory.SHORTLEX_LENGTH_LE)
