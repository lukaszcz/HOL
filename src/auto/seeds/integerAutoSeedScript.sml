Theory integerAutoSeed
Ancestors
  integer
Libs
  clasetLib clasimpLib seedCollections

fun export_at attr (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = attr, args = [], thm = saved}
  end

fun export_arith entry = export_at "arith" entry

fun export_both (name, theorem) =
  let
    val saved = save_thm (name, theorem)
    fun store attr =
      ThmAttribute.store_at_attribute
        {name = name, attrname = attr, args = [], thm = saved}
  in
    List.app store ["algebra_simps", "field_simps"]
  end

fun store_both (name, theorem) =
  List.app
    (fn attr =>
      ThmAttribute.store_at_attribute
        {name = name, attrname = attr, args = [], thm = theorem})
    ["algebra_simps", "field_simps"]

(* src/HOL/Int.thy:726-732 @ f7e02b7e. *)
Theorem INT_AUTO_NEG_SUC_LT_NUM[iff]:
  -&(SUC n) < &m
Proof
  intLib.ARITH_TAC
QED

Theorem INT_AUTO_NEG_LE_NUM[iff]:
  -&n <= &m
Proof
  intLib.ARITH_TAC
QED

(* Conservative arithmetic facts, never claset transitivity rules. *)
val _ =
  List.app export_arith
    [("INT_LT_TOTAL_ARITH", integerTheory.INT_LT_TOTAL),
     ("INT_LE_TOTAL_ARITH", integerTheory.INT_LE_TOTAL),
     ("INT_LT_TRANS_ARITH", integerTheory.INT_LT_TRANS),
     ("INT_LE_TRANS_ARITH", integerTheory.INT_LE_TRANS),
     ("INT_LT_IMP_LE_ARITH", integerTheory.INT_LT_IMP_LE),
     ("INT_EQ_IMP_LE_ARITH", integerTheory.INT_EQ_IMP_LE)]

(* src/HOL/Groups.thy:221-341,563-612 @ f7e02b7e. *)
val _ =
  List.app export_both
    [("INT_ADD_ASSOC_ALGEBRA", integerTheory.INT_ADD_ASSOC),
     ("INT_ADD_COMM_ALGEBRA", integerTheory.INT_ADD_COMM),
     ("INT_MUL_ASSOC_ALGEBRA", integerTheory.INT_MUL_ASSOC),
     ("INT_MUL_COMM_ALGEBRA", integerTheory.INT_MUL_COMM),
     ("INT_EQ_SUB_RADD_ALGEBRA", integerTheory.INT_EQ_SUB_RADD),
     ("INT_EQ_SUB_LADD_ALGEBRA", integerTheory.INT_EQ_SUB_LADD),
     ("INT_LT_SUB_RADD_ALGEBRA", integerTheory.INT_LT_SUB_RADD),
     ("INT_LT_SUB_LADD_ALGEBRA", integerTheory.INT_LT_SUB_LADD),
     ("INT_LE_SUB_RADD_ALGEBRA", integerTheory.INT_LE_SUB_RADD),
     ("INT_LE_SUB_LADD_ALGEBRA", integerTheory.INT_LE_SUB_LADD)]

Theorem ALG_INT_ADD_LEFT_COMM:
  !x y z : int. x + (y + z) = y + (x + z)
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_MUL_LEFT_COMM:
  !x y z : int. x * (y * z) = y * (x * z)
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_DIFF_DIFF_ADD:
  !a b c : int. a - b - c = a - (b + c)
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_ADD_DIFF_EQ:
  !a b c : int. a + (b - c) = (a + b) - c
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_DIFF_DIFF_EQ2:
  !a b c : int. a - (b - c) = (a + c) - b
Proof
  intLib.INT_RING_TAC
QED

Theorem ALG_INT_DIFF_ADD_EQ:
  !a b c : int. (a - b) + c = (a + c) - b
Proof
  intLib.INT_RING_TAC
QED

val _ =
  List.app store_both
    [("ALG_INT_ADD_LEFT_COMM", ALG_INT_ADD_LEFT_COMM),
     ("ALG_INT_MUL_LEFT_COMM", ALG_INT_MUL_LEFT_COMM),
     ("ALG_INT_DIFF_DIFF_ADD", ALG_INT_DIFF_DIFF_ADD),
     ("ALG_INT_ADD_DIFF_EQ", ALG_INT_ADD_DIFF_EQ),
     ("ALG_INT_DIFF_DIFF_EQ2", ALG_INT_DIFF_DIFF_EQ2),
     ("ALG_INT_DIFF_ADD_EQ", ALG_INT_DIFF_ADD_EQ)]
