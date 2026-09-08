Theory arithmeticAutoSeed
Ancestors
  arithmetic
Libs
  clasetLib clasimpLib seedCollections

fun export_at attr (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = attr, args = [], thm = saved}
  end

fun export_iff entry = export_at "iff" entry
fun export_algebra (name, theorem) =
  let
    val saved = save_thm (name, theorem)
    fun store attr =
      ThmAttribute.store_at_attribute
        {name = name, attrname = attr, args = [], thm = saved}
  in
    List.app store ["algebra_simps", "field_simps"]
  end

(* src/HOL/Nat.thy:303-769 @ f7e02b7e;
   src/HOL/Orderings.thy:208-228 @ f7e02b7e *)
val _ =
  List.app export_iff
    [("ADD_EQ_0_AUTO", arithmeticTheory.ADD_EQ_0),
     ("ZERO_LESS_EQ_AUTO", arithmeticTheory.ZERO_LESS_EQ),
     ("LESS_EQ_MONO_AUTO", arithmeticTheory.LESS_EQ_MONO),
     ("LESS_EQ_0_AUTO", arithmeticTheory.LESS_EQ_0),
     ("NOT_LESS_0_AUTO", prim_recTheory.NOT_LESS_0),
     ("LESS_MONO_EQ_AUTO", arithmeticTheory.LESS_MONO_EQ),
     ("LESS_SUC_REFL_AUTO", prim_recTheory.LESS_SUC_REFL),
     ("LESS_0_AUTO", prim_recTheory.LESS_0),
     ("NOT_ZERO_AUTO", arithmeticTheory.NOT_ZERO),
     ("NOT_LT_ZERO_EQ_ZERO_AUTO",
      arithmeticTheory.NOT_LT_ZERO_EQ_ZERO),
     ("ZERO_LESS_ADD_AUTO", arithmeticTheory.ZERO_LESS_ADD),
     ("LESS_EQ_REFL_AUTO", arithmeticTheory.LESS_EQ_REFL),
     ("LESS_REFL_AUTO", prim_recTheory.LESS_REFL)]

Theorem LESS_ONE_AUTO[iff]:
  !n. n < 1 <=> n = 0
Proof
  Cases_on `n` >> simp []
QED

Theorem ZERO_LT_IMP_OR_ZERO_AUTO:
  !n proposition.
    ((0 < n ==> proposition) <=> proposition \/ n = 0)
Proof
  Cases_on `n` >> simp[]
QED

(* src/HOL/Nat.thy:2632 @ f7e02b7e.  [diff_diff_left] is simp there:
   two subtractions in a row are one subtraction of a sum, which is
   where an AC normalisation of the addition reaches the two
   subtrahends.  HOL4 agrees on the normal form and puts it in
   ARITH_ss, which this layer's ambient simpset does not carry, so
   [a - b - 1] and [a - 1 - b] stay two terms with nothing between
   them.  Declared in ARITH_ss's orientation, which is the source's:
   the opposite reading is HOL4's own SUB_PLUS, and a simpset holding
   both does not terminate. *)
val _ =
  export_at "simp"
    ("SUB_SUB_LEFT_AUTO", GSYM arithmeticTheory.SUB_PLUS)

(* Isabelle has no predecessor constant: src/HOL/Nat.thy writes the
   predecessor as [n - 1] throughout, so every goal translated from the
   source spells an index one below another that way, while HOL4's own
   rules about the same index -- EL_CONS, LAST_EL, the LUPDATE and TAKE
   rules -- spell it [PRE n].  Neither simpset carries a step between
   the two spellings, and a goal and the rule that would settle it then
   stand side by side unrelated: [EL (PRE n) xs = EL (n - 1) xs] is
   what an index characterisation with every other part in place is
   left holding.  Declared towards the source's spelling, which is
   also the one the layer's linear arithmetic decomposes: the num
   instance splits a subtraction and has no rule for PRE, which is an
   atom to it. *)
val _ =
  export_at "simp" ("PRE_SUB1_AUTO", arithmeticTheory.PRE_SUB1)

(* src/HOL/Lattices.thy:556-557 @ f7e02b7e.  Isabelle declares
   [min.absorb1] and [min.absorb2] simp with their [max] counterparts:
   a MIN whose comparison the context settles is one of its arguments.
   HOL4 states both pairs and declares neither, so a MIN left by a
   rule that formed it -- a take of a take is a take of the smaller
   length -- stands with nothing to reduce it, although the comparison
   is one linear-arithmetic step away.  Isabelle's companion
   declarations for the comparisons against a MIN ([le_inf_iff],
   [min_less_iff_conj] and their MAX halves) need no analogue: the
   layer's side-condition solver reads a bound against a MIN without
   them. *)
val _ =
  List.app (export_at "simp")
    [("MIN_EQ_LE_AUTO", arithmeticTheory.MIN_EQ_LE),
     ("MAX_EQ_GE_AUTO", arithmeticTheory.MAX_EQ_GE)]

(* src/HOL/Groups.thy:221-341 @ f7e02b7e *)
val _ =
  List.app export_algebra
    [("ADD_ASSOC_ALGEBRA", arithmeticTheory.ADD_ASSOC),
     ("ADD_COMM_ALGEBRA", arithmeticTheory.ADD_COMM),
     ("MULT_ASSOC_ALGEBRA", arithmeticTheory.MULT_ASSOC),
     ("MULT_COMM_ALGEBRA", arithmeticTheory.MULT_COMM),
     ("MULT_LEFT_COMMUTE_ALGEBRA", arithmeticTheory.MULT_COMM_ASSOC),
     ("SUB_RIGHT_SUB_ALGEBRA", arithmeticTheory.SUB_RIGHT_SUB)]

Theorem ADD_LEFT_COMMUTE_ALGEBRA:
  !a b c : num. a + (b + c) = b + (a + c)
Proof
  simp [AC ADD_ASSOC ADD_COMM]
QED

val _ =
  List.app
    (fn attr =>
      ThmAttribute.store_at_attribute
        {name = "ADD_LEFT_COMMUTE_ALGEBRA", attrname = attr,
         args = [], thm = ADD_LEFT_COMMUTE_ALGEBRA})
    ["algebra_simps", "field_simps"]
