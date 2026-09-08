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

(* src/HOL/List.thy:1106,1115 @ f7e02b7e.  [map_map] and [map_eq_conv]
   are simp there and declared to no simpset here.  Without the first a
   map of a map stays two walks down the list; without the second an
   equality between two maps over one list is left as it stands, and
   the two mapped functions are never brought together -- neither
   simplification nor search has a step that relates them.  Together
   they read such an equality as the pointwise equality of the two
   functions on the list's elements, which the seeded pair quantifier
   takes apart where the elements are pairs. *)
val _ =
  List.app (export_at "simp")
    [("MAP_MAP_o_AUTO", listTheory.MAP_MAP_o),
     ("MAP_EQ_f_AUTO", listTheory.MAP_EQ_f)]

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

(* src/HOL/List.thy:1351 @ f7e02b7e.  [set_filter] reads a membership in
   a filtered list as the membership in the list and then the predicate;
   HOL4's MEM_FILTER states the predicate first.  A goal translated from
   the source states its own comprehensions the source's way round, so
   the two readings meet as an iff between the same two conjuncts in
   opposite orders -- which neither system's simplifier closes, both
   declaring associativity of the conjunction and not commutativity.
   The seed states the source's orientation. *)
Theorem MEM_FILTER_AUTO[iff]:
  !P L x. MEM x (FILTER P L) <=> MEM x L /\ P x
Proof
  metis_tac [listTheory.MEM_FILTER]
QED

Theorem LIST_REL_REVERSE_AUTO[iff]:
  !R left right.
    LIST_REL R (REVERSE left) (REVERSE right) <=> LIST_REL R left right
Proof
  metis_tac [LIST_REL_REVERSE, REVERSE_REVERSE]
QED

(* src/HOL/List.thy:1616,1635,1638 @ f7e02b7e.  [filter_append] is simp
   there and declared to no simpset here, and with it the two rules that
   collapse a filter whose predicate the list itself settles,
   [filter_True] and [filter_False].  HOL4 states the collapses as
   equivalences between an equation and an EVERY and declares neither,
   so a goal that filters across an append keeps the append whole, and
   the half whose elements the context already decides stays a filter
   beside the list it would reduce to.  The rest of the family,
   [length_filter_le] and [distinct_filter], is seeded in
   rich_listAutoSeed.  [filter_filter] is simp there as well and is
   left undeclared: a composite filter is settled by the collapses
   below, which read the inner walk's elements through the seeded
   MEM_FILTER_AUTO, so nothing reaches the rule that writes two walks as
   one. *)
val _ =
  export_at "simp"
    ("FILTER_APPEND_DISTRIB_AUTO", listTheory.FILTER_APPEND_DISTRIB)

Theorem FILTER_NONE_AUTO[simp]:
  !P l. EVERY (\item. ~P item) l ==> FILTER P l = []
Proof
  simp[listTheory.FILTER_EQ_NIL]
QED

Theorem FILTER_ID_AUTO[simp]:
  !P l. EVERY P l ==> FILTER P l = l
Proof
  simp[listTheory.FILTER_EQ_ID]
QED

(* src/HOL/List.thy:1348,1521 @ f7e02b7e.  [set_map] and [set_concat]
   are simp there, so a membership in a mapped or a flattened list is
   read as one in the image, or the union, the list is built from.  HOL4
   states the composite readings as MEM_MAP and MEM_FLAT and declares
   neither, so a membership in [MAP f xs] or [FLAT xss] is inert and the
   element it would name is never introduced.  The other two of the
   four, [set_append] and [set_filter], need no analogue here:
   MEM_APPEND is ambient, and MEM_FILTER is seeded above.

   Both are declared in the membership reading rather than the source's
   set reading, which is the reading the goals are in: [MEM x l] is
   [x IN set l] itself, so the set form is met as a subterm and leaves
   an image or a union membership where a membership already stood.

   The union is a rewrite and the image is not, which is the split the
   source makes: [UN_iff] of src/HOL/Complete_Lattices.thy:1052 is simp,
   while an image membership is left to [image_eqI] and [imageE] of
   src/HOL/Set.thy:882,893 -- an unsafe introduction and a safe
   elimination -- and [image_iff] beside them is declared to nothing.
   The split earns its keep here: a rewrite of the image reading reaches
   an enclosing membership before the MAP beneath it, and the ambient
   projections of a zip, which are conditional on the two sides having
   equal length, then never see the MAP they reduce.

   The elimination is declared unsafe where the source declares it safe,
   which is the same deviation MEM_takeWhile_HOLDS_AUTO below records and
   is made for the same reason: what is wanted is strength, and here the
   safe reading costs more than it earns.  A safe elimination is tried at
   every node of the tableau, and its major premise is entirely schematic,
   so it meets the undetermined literals a witness-guessing branch leaves
   behind.  Declared safe, [set_L1610_Pow_Compl] of the sets corpus --
   whose source method supplies the witness this layer's recipe has to
   guess -- goes from 88 branches to 3638 and past its budget; declared
   unsafe it stays at 88, and the goals the rule exists for still close.
   The [selim] spelling costs the same, and so does declaring the
   pre-existing MEM_takeWhile_HOLDS_AUTO below safe, so what costs is the
   safety class rather than this rule or its shape. *)
val _ = export_at "simp" ("MEM_FLAT_AUTO", listTheory.MEM_FLAT)

Theorem MEM_MAP_IMAGE_AUTO[intro]:
  !f y x (xs : 'a list). y = f x /\ MEM x xs ==> MEM y (MAP f xs)
Proof
  metis_tac [listTheory.MEM_MAP]
QED

Theorem MEM_MAP_CASES_AUTO[dest]:
  !f y (xs : 'a list). MEM y (MAP f xs) ==> ?x. y = f x /\ MEM x xs
Proof
  metis_tac [listTheory.MEM_MAP]
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
   operation by index with nothing to push the index through the
   constructor it was built with.  EL_LUPDATE is the two Isabelle
   update rules in one conditional equation; the zip case is seeded
   above with map_snd_zip. *)
val _ =
  List.app (export_at "simp")
    [("EL_MAP_AUTO", listTheory.EL_MAP),
     ("EL_LUPDATE_AUTO", listTheory.EL_LUPDATE),
     ("EL_TAKE_AUTO", listTheory.EL_TAKE),
     ("EL_DROP_AUTO", listTheory.EL_DROP)]

(* src/HOL/List.thy:2247 @ f7e02b7e.  [take_take] is simp there and
   declared to no simpset here, so a take of a take stays two walks
   down the list and the length that decides it is never formed.  Its
   [drop_drop] counterpart is seeded in rich_listAutoSeed, which
   states it. *)
val _ =
  export_at "simp" ("TAKE_TAKE_MIN_AUTO", listTheory.TAKE_TAKE_MIN)

(* src/HOL/List.thy:2209 @ f7e02b7e.  [length_take] is simp there and
   is unconditional, the length being the smaller of the two.  HOL4
   declares the conditional reading, which says nothing about a take
   whose length is not already known to be within the list, and states
   the unconditional one as a conditional expression that no rule about
   MIN meets.  A bound on the length of a take is where a rule that
   reaches through the take gets its side condition. *)
Theorem LENGTH_TAKE_MIN_AUTO[simp]:
  !n (l : 'a list). LENGTH (TAKE n l) = MIN (LENGTH l) n
Proof
  rw[listTheory.LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> fs[]
QED

(* src/HOL/List.thy @ f7e02b7e, [drop_append], [take_all] and
   [drop_all], simp there and declared to no simpset here.  Isabelle
   pushes a drop through an append and then reads off each half by its
   length; HOL4 states the three and carries none, so a rewrite that
   introduces [DROP n (l1 ++ l2)] leaves it and the subtracted length
   standing.  [take_append] is rich_list$TAKE_APPEND and is seeded
   with it. *)
val _ =
  List.app (export_at "simp")
    [("DROP_APPEND_AUTO", listTheory.DROP_APPEND),
     ("TAKE_LENGTH_TOO_LONG_AUTO", listTheory.TAKE_LENGTH_TOO_LONG),
     ("DROP_LENGTH_TOO_LONG_AUTO", listTheory.DROP_LENGTH_TOO_LONG)]

(* src/HOL/List.thy @ f7e02b7e, the takeWhile and dropWhile primrecs.
   Both are primrec there, so both recursion equations are simp.  HOL4
   tags dropWhile_def and leaves takeWhile_def untagged -- it is the newer
   constant and its equations were added without changing any
   pre-existing simpset -- so the two halves of one decomposition
   reduce differently: a goal that walks a list drops its dropWhile
   away and keeps the takeWhile whole. *)
val _ =
  export_at "simp" ("takeWhile_AUTO", listTheory.takeWhile_def)

(* src/HOL/List.thy @ f7e02b7e, the results about those two that
   Isabelle declares simp: takeWhile_dropWhile_id, dropWhile_append1,
   dropWhile_append2, takeWhile_eq_all_conv and dropWhile_eq_Nil_conv.
   HOL4 states all five and declares none, so a goal that pushes a
   dropWhile through an append, or reads a takeWhile or a dropWhile off
   against the list it ran down, keeps both spellings side by side.

   dropWhile_id is simp there and is the implication from a predicate
   no element satisfies; HOL4's theorem of that name is the equivalence
   Isabelle calls dropWhile_eq_self_iff and leaves undeclared, so it is
   not seeded here. *)
val _ =
  List.app (export_at "simp")
    [("takeWhile_APPEND_dropWhile_AUTO",
      listTheory.takeWhile_APPEND_dropWhile),
     ("dropWhile_APPEND_EVERY_AUTO", listTheory.dropWhile_APPEND_EVERY),
     ("dropWhile_APPEND_EXISTS_AUTO", listTheory.dropWhile_APPEND_EXISTS)]

val _ =
  List.app export_iff
    [("takeWhile_id_AUTO", listTheory.takeWhile_id),
     ("dropWhile_eq_nil_AUTO", listTheory.dropWhile_eq_nil)]

(* src/HOL/List.thy:2559 @ f7e02b7e.  [set_takeWhileD] reads a member of
   a takeWhile as a member of the list that satisfies the predicate, and
   Isabelle declares it to no simpset and no claset.  HOL4 states its
   first half as [MEM_takeWhile_IMP] and carries the second only inside
   [EVERY_takeWhile], where nothing takes it apart: a walk stopped by
   its own predicate leaves an element of the prefix against the
   predicate it was taken by, and neither system's declared rules reach
   it.  Declared here as a dest rule, which is a declaration Isabelle
   does not make: the target is automation at least as strong as
   Isabelle's, and what is declared is a schema about the walk.  Its
   companion needs no declaration -- [MEM_takeWhile_IMP] gives
   membership in the list, which the goals reach by other routes. *)
Theorem MEM_takeWhile_HOLDS_AUTO[dest]:
  !P l x. MEM x (takeWhile P (l : 'a list)) ==> P x
Proof
  metis_tac [listTheory.EVERY_takeWhile, listTheory.EVERY_MEM]
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

(* src/HOL/List.thy:254-257 @ f7e02b7e.  [successively] is a fun there,
   so its three defining equations are simp by construction, and it is
   the third of them --

     successively P (x # y # xs) = (P x y /\ successively P (y # xs))

   -- that [auto simp: distinct_adj_def] rewrites a successively over a
   cons with.  HOL4 has no such constant, and the translation states
   successively through [adjacent].  Its declared equations
   ([adjacent_thm]) settle the empty list, the singleton, and a pair
   that is the head of the list; a pair anywhere else is [adjacent_iff],
   which HOL4 states and declares to no simpset.  So unfolding a
   successively over a cons left an [adjacent] on that cons with nothing
   to take it apart.  The rule recurses into the tail, so it terminates
   where the list does. *)
val _ =
  export_at "simp" ("adjacent_iff_AUTO", listTheory.adjacent_iff)
