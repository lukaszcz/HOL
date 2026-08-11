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
