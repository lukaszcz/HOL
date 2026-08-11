Theory realAutoSeed
Ancestors
  real rat
Libs
  clasetLib clasimpLib seedCollections realLib RealField

fun export_at attr (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = attr, args = [], thm = saved}
  end

fun export_iff entry = export_at "iff" entry
fun export_arith entry = export_at "arith" entry
fun export_field entry = export_at "field_simps" entry

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

(* src/HOL/Real.thy:1231-1265 and Fields.thy:32-62 @ f7e02b7e. *)
Theorem REAL_AUTO_ADD_NEG_EQ_ZERO[iff]:
  (x : real) + -a = 0 <=> x = a
Proof
  REAL_ARITH_TAC
QED

val _ = export_iff ("REAL_SUMSQ_AUTO", realTheory.REAL_SUMSQ)

val _ =
  List.app export_arith
    [("REAL_SUMSQ_ARITH", realTheory.REAL_SUMSQ),
     ("REAL_LE_SQUARE_ARITH", realTheory.REAL_LE_SQUARE),
     ("REAL_POSSQ_ARITH", realTheory.REAL_POSSQ),
     ("REAL_MUL_POS_LT_ARITH", realTheory.REAL_MUL_POS_LT),
     ("REAL_LT_TOTAL_ARITH", realTheory.REAL_LT_TOTAL),
     ("REAL_LE_TOTAL_ARITH", realTheory.REAL_LE_TOTAL),
     ("REAL_LT_TRANS_ARITH", realTheory.REAL_LT_TRANS),
     ("REAL_LE_TRANS_ARITH", realTheory.REAL_LE_TRANS),
     ("REAL_LT_IMP_LE_ARITH", realTheory.REAL_LT_IMP_LE),
     ("REAL_EQ_IMP_LE_ARITH", realTheory.REAL_EQ_IMP_LE)]

(* src/HOL/Groups.thy:221-341,563-612 @ f7e02b7e.  Rat lives here
   because Phase 8 deliberately has no separate rational seed. *)
val _ =
  List.app export_both
    [("REAL_ADD_ASSOC_ALGEBRA", realTheory.REAL_ADD_ASSOC),
     ("REAL_ADD_COMM_ALGEBRA", realTheory.REAL_ADD_COMM),
     ("REAL_MUL_ASSOC_ALGEBRA", realTheory.REAL_MUL_ASSOC),
     ("REAL_MUL_COMM_ALGEBRA", realTheory.REAL_MUL_COMM),
     ("REAL_EQ_SUB_RADD_ALGEBRA", realTheory.REAL_EQ_SUB_RADD),
     ("REAL_EQ_SUB_LADD_ALGEBRA", realTheory.REAL_EQ_SUB_LADD),
     ("REAL_LT_SUB_RADD_ALGEBRA", realTheory.REAL_LT_SUB_RADD),
     ("REAL_LT_SUB_LADD_ALGEBRA", realTheory.REAL_LT_SUB_LADD),
     ("REAL_LE_SUB_RADD_ALGEBRA", realTheory.REAL_LE_SUB_RADD),
     ("REAL_LE_SUB_LADD_ALGEBRA", realTheory.REAL_LE_SUB_LADD),
     ("RAT_ADD_ASSOC_ALGEBRA", ratTheory.RAT_ADD_ASSOC),
     ("RAT_ADD_COMM_ALGEBRA", ratTheory.RAT_ADD_COMM),
     ("RAT_MUL_ASSOC_ALGEBRA", ratTheory.RAT_MUL_ASSOC),
     ("RAT_MUL_COMM_ALGEBRA", ratTheory.RAT_MUL_COMM),
     ("RAT_LSUB_EQ_ALGEBRA", ratTheory.RAT_LSUB_EQ),
     ("RAT_RSUB_EQ_ALGEBRA", ratTheory.RAT_RSUB_EQ),
     ("RAT_LSUB_LES_ALGEBRA", ratTheory.RAT_LSUB_LES),
     ("RAT_RSUB_LES_ALGEBRA", ratTheory.RAT_RSUB_LES),
     ("RAT_LSUB_LEQ_ALGEBRA", ratTheory.RAT_LSUB_LEQ),
     ("RAT_RSUB_LEQ_ALGEBRA", ratTheory.RAT_RSUB_LEQ)]

Theorem ALG_REAL_ADD_LEFT_COMM:
  !x y z : real. x + (y + z) = y + (x + z)
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_REAL_MUL_LEFT_COMM:
  !x y z : real. x * (y * z) = y * (x * z)
Proof
  simp [AC realTheory.REAL_MUL_ASSOC realTheory.REAL_MUL_COMM]
QED

Theorem ALG_REAL_DIFF_DIFF_ADD:
  !a b c : real. a - b - c = a - (b + c)
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_REAL_ADD_DIFF_EQ:
  !a b c : real. a + (b - c) = (a + b) - c
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_REAL_DIFF_DIFF_EQ2:
  !a b c : real. a - (b - c) = (a + c) - b
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_REAL_DIFF_ADD_EQ:
  !a b c : real. (a - b) + c = (a + c) - b
Proof
  REAL_ARITH_TAC
QED

Theorem ALG_RAT_ADD_LEFT_COMM:
  !x y z : rat. x + (y + z) = y + (x + z)
Proof
  simp [AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

Theorem ALG_RAT_MUL_LEFT_COMM:
  !x y z : rat. x * (y * z) = y * (x * z)
Proof
  simp [AC ratTheory.RAT_MUL_ASSOC ratTheory.RAT_MUL_COMM]
QED

Theorem ALG_RAT_DIFF_DIFF_ADD:
  !a b c : rat. a - b - c = a - (b + c)
Proof
  simp [ratTheory.RAT_SUB_ADDAINV, ratTheory.RAT_AINV_ADD,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

Theorem ALG_RAT_ADD_DIFF_EQ:
  !a b c : rat. a + (b - c) = (a + b) - c
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

Theorem ALG_RAT_DIFF_DIFF_EQ2:
  !a b c : rat. a - (b - c) = (a + c) - b
Proof
  simp [ratTheory.RAT_SUB_ADDAINV, ratTheory.RAT_AINV_ADD,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

Theorem ALG_RAT_DIFF_ADD_EQ:
  !a b c : rat. (a - b) + c = (a + c) - b
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM]
QED

val _ =
  List.app store_both
    [("ALG_REAL_ADD_LEFT_COMM", ALG_REAL_ADD_LEFT_COMM),
     ("ALG_REAL_MUL_LEFT_COMM", ALG_REAL_MUL_LEFT_COMM),
     ("ALG_REAL_DIFF_DIFF_ADD", ALG_REAL_DIFF_DIFF_ADD),
     ("ALG_REAL_ADD_DIFF_EQ", ALG_REAL_ADD_DIFF_EQ),
     ("ALG_REAL_DIFF_DIFF_EQ2", ALG_REAL_DIFF_DIFF_EQ2),
     ("ALG_REAL_DIFF_ADD_EQ", ALG_REAL_DIFF_ADD_EQ),
     ("ALG_RAT_ADD_LEFT_COMM", ALG_RAT_ADD_LEFT_COMM),
     ("ALG_RAT_MUL_LEFT_COMM", ALG_RAT_MUL_LEFT_COMM),
     ("ALG_RAT_DIFF_DIFF_ADD", ALG_RAT_DIFF_DIFF_ADD),
     ("ALG_RAT_ADD_DIFF_EQ", ALG_RAT_ADD_DIFF_EQ),
     ("ALG_RAT_DIFF_DIFF_EQ2", ALG_RAT_DIFF_DIFF_EQ2),
     ("ALG_RAT_DIFF_ADD_EQ", ALG_RAT_DIFF_ADD_EQ)]

(* src/HOL/Fields.thy:180,204-252,775-887 @ f7e02b7e. *)
val _ =
  List.app export_field
    [("REAL_INV_1OVER_FIELD", realTheory.REAL_INV_1OVER),
     ("REAL_EQ_RDIV_EQ_FIELD", realTheory.REAL_EQ_RDIV_EQ'),
     ("REAL_LT_RDIV_EQ_FIELD", realTheory.REAL_LT_RDIV_EQ),
     ("REAL_LT_LDIV_EQ_FIELD", realTheory.REAL_LT_LDIV_EQ),
     ("REAL_LE_RDIV_EQ_FIELD", realTheory.REAL_LE_RDIV_EQ),
     ("REAL_LE_LDIV_EQ_FIELD", realTheory.REAL_LE_LDIV_EQ),
     ("RAT_RDIV_EQ_FIELD", ratTheory.RAT_RDIV_EQ),
     ("RAT_LDIV_EQ_FIELD", ratTheory.RAT_LDIV_EQ),
     ("RAT_RDIV_LES_POS_FIELD", ratTheory.RAT_RDIV_LES_POS),
     ("RAT_LDIV_LES_POS_FIELD", ratTheory.RAT_LDIV_LES_POS),
     ("RAT_RDIV_LEQ_POS_FIELD", ratTheory.RAT_RDIV_LEQ_POS),
     ("RAT_LDIV_LEQ_POS_FIELD", ratTheory.RAT_LDIV_LEQ_POS),
     ("RAT_RDIV_LES_NEG_FIELD", ratTheory.RAT_RDIV_LES_NEG),
     ("RAT_LDIV_LES_NEG_FIELD", ratTheory.RAT_LDIV_LES_NEG),
     ("RAT_RDIV_LEQ_NEG_FIELD", ratTheory.RAT_RDIV_LEQ_NEG),
     ("RAT_LDIV_LEQ_NEG_FIELD", ratTheory.RAT_LDIV_LEQ_NEG)]

fun store_field (name, theorem) =
  ThmAttribute.store_at_attribute
    {name = name, attrname = "field_simps", args = [], thm = theorem}

Theorem FIELD_REAL_RDIV_EQ:
  !a b c : real. c <> 0 ==> (b / c = a <=> b = a * c)
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_NEG_RDIV_EQ:
  !a b c : real. b <> 0 ==>
    (-(a / b) = c <=> -a = c * b)
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_EQ_NEG_RDIV:
  !a b c : real. b <> 0 ==>
    (c = -(a / b) <=> c * b = -a)
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_ADD_RDIV:
  !x y z : real. z <> 0 ==>
    x + y / z = (x * z + y) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_RDIV_ADD:
  !x y z : real. z <> 0 ==>
    x / z + y = (x + y * z) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_DIFF_RDIV:
  !x y z : real. z <> 0 ==>
    x - y / z = (x * z - y) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_NEG_RDIV_ADD:
  !x y z : real. z <> 0 ==>
    -(x / z) + y = (-x + y * z) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_RDIV_DIFF:
  !x y z : real. z <> 0 ==>
    x / z - y = (x - y * z) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_NEG_RDIV_DIFF:
  !x y z : real. z <> 0 ==>
    -(x / z) - y = (-x - y * z) / z
Proof
  REAL_FIELD_TAC
QED

Theorem FIELD_REAL_POS_LE_NEG_RDIV:
  !a b c : real. 0 < c ==>
    (a <= -(b / c) <=> a * c <= -b)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             realTheory.REAL_LE_RDIV_EQ]
QED

Theorem FIELD_REAL_LE_RDIV_EQ_NEG:
  !a b c : real. c < 0 ==>
    (a <= b / c <=> b <= a * c)
Proof
  rpt strip_tac >>
  `c <> 0` by
    metis_tac [realTheory.REAL_LT_IMP_NE] >>
  `c * (b / c) <= c * a <=> a <= b / c` by
    (irule realTheory.REAL_LE_LMUL_NEG >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `c * (b / c) = b` by
    (irule realTheory.REAL_DIV_LMUL >>
     FIRST_ASSUM ACCEPT_TAC) >>
  metis_tac [realTheory.REAL_MUL_COMM]
QED

Theorem FIELD_REAL_LT_RDIV_EQ_NEG:
  !a b c : real. c < 0 ==>
    (a < b / c <=> b < a * c)
Proof
  rpt strip_tac >>
  `c <> 0` by
    metis_tac [realTheory.REAL_LT_IMP_NE] >>
  `c * (b / c) < c * a <=> a < b / c` by
    (irule realTheory.REAL_LT_LMUL_NEG >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `c * (b / c) = b` by
    (irule realTheory.REAL_DIV_LMUL >>
     FIRST_ASSUM ACCEPT_TAC) >>
  metis_tac [realTheory.REAL_MUL_COMM]
QED

Theorem FIELD_REAL_LT_LDIV_EQ_NEG:
  !a b c : real. c < 0 ==>
    (b / c < a <=> a * c < b)
Proof
  rpt strip_tac >>
  `c <> 0` by
    metis_tac [realTheory.REAL_LT_IMP_NE] >>
  `c * a < c * (b / c) <=> b / c < a` by
    (irule realTheory.REAL_LT_LMUL_NEG >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `c * (b / c) = b` by
    (irule realTheory.REAL_DIV_LMUL >>
     FIRST_ASSUM ACCEPT_TAC) >>
  metis_tac [realTheory.REAL_MUL_COMM]
QED

Theorem FIELD_REAL_LE_LDIV_EQ_NEG:
  !a b c : real. c < 0 ==>
    (b / c <= a <=> a * c <= b)
Proof
  rpt strip_tac >>
  `c <> 0` by
    metis_tac [realTheory.REAL_LT_IMP_NE] >>
  `c * a <= c * (b / c) <=> b / c <= a` by
    (irule realTheory.REAL_LE_LMUL_NEG >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `c * (b / c) = b` by
    (irule realTheory.REAL_DIV_LMUL >>
     FIRST_ASSUM ACCEPT_TAC) >>
  metis_tac [realTheory.REAL_MUL_COMM]
QED

Theorem FIELD_REAL_NEG_LE_NEG_RDIV:
  !a b c : real. c < 0 ==>
    (a <= -(b / c) <=> -b <= a * c)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             FIELD_REAL_LE_RDIV_EQ_NEG]
QED

Theorem FIELD_REAL_POS_LT_NEG_RDIV:
  !a b c : real. 0 < c ==>
    (a < -(b / c) <=> a * c < -b)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             realTheory.REAL_LT_RDIV_EQ]
QED

Theorem FIELD_REAL_NEG_LT_NEG_RDIV:
  !a b c : real. c < 0 ==>
    (a < -(b / c) <=> -b < a * c)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             FIELD_REAL_LT_RDIV_EQ_NEG]
QED

Theorem FIELD_REAL_POS_NEG_RDIV_LT:
  !a b c : real. 0 < c ==>
    (-(b / c) < a <=> -b < a * c)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             realTheory.REAL_LT_LDIV_EQ]
QED

Theorem FIELD_REAL_NEG_NEG_RDIV_LT:
  !a b c : real. c < 0 ==>
    (-(b / c) < a <=> a * c < -b)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             FIELD_REAL_LT_LDIV_EQ_NEG]
QED

Theorem FIELD_REAL_POS_NEG_RDIV_LE:
  !a b c : real. 0 < c ==>
    (-(b / c) <= a <=> -b <= a * c)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             realTheory.REAL_LE_LDIV_EQ]
QED

Theorem FIELD_REAL_NEG_NEG_RDIV_LE:
  !a b c : real. c < 0 ==>
    (-(b / c) <= a <=> a * c <= -b)
Proof
  metis_tac [realTheory.REAL_DIV_LNEG,
             FIELD_REAL_LE_LDIV_EQ_NEG]
QED

val _ =
  List.app store_field
    [("FIELD_REAL_RDIV_EQ", FIELD_REAL_RDIV_EQ),
     ("FIELD_REAL_NEG_RDIV_EQ", FIELD_REAL_NEG_RDIV_EQ),
     ("FIELD_REAL_EQ_NEG_RDIV", FIELD_REAL_EQ_NEG_RDIV),
     ("FIELD_REAL_ADD_RDIV", FIELD_REAL_ADD_RDIV),
     ("FIELD_REAL_RDIV_ADD", FIELD_REAL_RDIV_ADD),
     ("FIELD_REAL_DIFF_RDIV", FIELD_REAL_DIFF_RDIV),
     ("FIELD_REAL_NEG_RDIV_ADD", FIELD_REAL_NEG_RDIV_ADD),
     ("FIELD_REAL_RDIV_DIFF", FIELD_REAL_RDIV_DIFF),
     ("FIELD_REAL_NEG_RDIV_DIFF", FIELD_REAL_NEG_RDIV_DIFF),
     ("FIELD_REAL_POS_LE_NEG_RDIV",
      FIELD_REAL_POS_LE_NEG_RDIV),
     ("FIELD_REAL_LE_RDIV_EQ_NEG",
      FIELD_REAL_LE_RDIV_EQ_NEG),
     ("FIELD_REAL_LT_RDIV_EQ_NEG",
      FIELD_REAL_LT_RDIV_EQ_NEG),
     ("FIELD_REAL_LT_LDIV_EQ_NEG",
      FIELD_REAL_LT_LDIV_EQ_NEG),
     ("FIELD_REAL_LE_LDIV_EQ_NEG",
      FIELD_REAL_LE_LDIV_EQ_NEG),
     ("FIELD_REAL_NEG_LE_NEG_RDIV",
      FIELD_REAL_NEG_LE_NEG_RDIV),
     ("FIELD_REAL_POS_LT_NEG_RDIV",
      FIELD_REAL_POS_LT_NEG_RDIV),
     ("FIELD_REAL_NEG_LT_NEG_RDIV",
      FIELD_REAL_NEG_LT_NEG_RDIV),
     ("FIELD_REAL_POS_NEG_RDIV_LT",
      FIELD_REAL_POS_NEG_RDIV_LT),
     ("FIELD_REAL_NEG_NEG_RDIV_LT",
      FIELD_REAL_NEG_NEG_RDIV_LT),
     ("FIELD_REAL_POS_NEG_RDIV_LE",
      FIELD_REAL_POS_NEG_RDIV_LE),
     ("FIELD_REAL_NEG_NEG_RDIV_LE",
      FIELD_REAL_NEG_NEG_RDIV_LE)]

Theorem FIELD_RAT_INV_EQ_DIV:
  !a : rat. rat_minv a = 1 / a
Proof
  simp [ratTheory.RAT_DIV_MULMINV]
QED

Theorem FIELD_RAT_RDIV_EQ:
  !a b c : rat. c <> 0 ==> (b / c = a <=> b = a * c)
Proof
  simp [ratTheory.RAT_LDIV_EQ, ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_NEG_DIV:
  !a b : rat. -(a / b) = -a / b
Proof
  simp [ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_AINV_LMUL]
QED

Theorem FIELD_RAT_NEG_RDIV_EQ:
  !a b c : rat. b <> 0 ==>
    (-(a / b) = c <=> -a = c * b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_EQ,
             ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_EQ_NEG_RDIV:
  !a b c : rat. b <> 0 ==>
    (c = -(a / b) <=> c * b = -a)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_EQ]
QED

Theorem FIELD_RAT_ADD_RDIV:
  !x y z : rat. z <> 0 ==>
    x + y / z = (x * z + y) / z
Proof
  simp [ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_RDISTRIB,
        GSYM ratTheory.RAT_MUL_ASSOC,
        ratTheory.RAT_MUL_RINV]
QED

Theorem FIELD_RAT_RDIV_ADD:
  !x y z : rat. z <> 0 ==>
    x / z + y = (x + y * z) / z
Proof
  simp [ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_RDISTRIB,
        GSYM ratTheory.RAT_MUL_ASSOC,
        ratTheory.RAT_MUL_RINV,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM,
        AC ratTheory.RAT_MUL_ASSOC ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_DIFF_RDIV:
  !x y z : rat. z <> 0 ==>
    x - y / z = (x * z - y) / z
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_AINV_LMUL,
        ratTheory.RAT_RDISTRIB,
        GSYM ratTheory.RAT_MUL_ASSOC,
        ratTheory.RAT_MUL_RINV]
QED

Theorem FIELD_RAT_NEG_RDIV_ADD:
  !x y z : rat. z <> 0 ==>
    -(x / z) + y = (-x + y * z) / z
Proof
  simp [ratTheory.RAT_DIV_MULMINV,
        ratTheory.RAT_AINV_LMUL,
        ratTheory.RAT_RDISTRIB,
        GSYM ratTheory.RAT_MUL_ASSOC,
        ratTheory.RAT_MUL_RINV,
        AC ratTheory.RAT_ADD_ASSOC ratTheory.RAT_ADD_COMM,
        AC ratTheory.RAT_MUL_ASSOC ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_RDIV_DIFF:
  !x y z : rat. z <> 0 ==>
    x / z - y = (x - y * z) / z
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        FIELD_RAT_RDIV_ADD,
        ratTheory.RAT_AINV_LMUL]
QED

Theorem FIELD_RAT_NEG_RDIV_DIFF:
  !x y z : rat. z <> 0 ==>
    -(x / z) - y = (-x - y * z) / z
Proof
  simp [ratTheory.RAT_SUB_ADDAINV,
        FIELD_RAT_NEG_RDIV_ADD,
        ratTheory.RAT_AINV_LMUL]
QED

Theorem FIELD_RAT_POS_LE_NEG_RDIV:
  !a b c : rat. 0 < c ==>
    (a <= -(b / c) <=> a * c <= -b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_LEQ_POS]
QED

Theorem FIELD_RAT_NEG_LE_NEG_RDIV:
  !a b c : rat. c < 0 ==>
    (a <= -(b / c) <=> -b <= a * c)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_LEQ_NEG]
QED

Theorem FIELD_RAT_POS_LT_NEG_RDIV:
  !a b c : rat. 0 < c ==>
    (a < -(b / c) <=> a * c < -b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_LES_POS]
QED

Theorem FIELD_RAT_NEG_LT_NEG_RDIV:
  !a b c : rat. c < 0 ==>
    (a < -(b / c) <=> -b < a * c)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_RDIV_LES_NEG]
QED

Theorem FIELD_RAT_POS_NEG_RDIV_LT:
  !a b c : rat. 0 < c ==>
    (-(b / c) < a <=> -b < a * c)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_LES_POS,
             ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_NEG_NEG_RDIV_LT:
  !a b c : rat. c < 0 ==>
    (-(b / c) < a <=> a * c < -b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_LES_NEG,
             ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_POS_NEG_RDIV_LE:
  !a b c : rat. 0 < c ==>
    (-(b / c) <= a <=> -b <= a * c)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_LEQ_POS,
             ratTheory.RAT_MUL_COMM]
QED

Theorem FIELD_RAT_NEG_NEG_RDIV_LE:
  !a b c : rat. c < 0 ==>
    (-(b / c) <= a <=> a * c <= -b)
Proof
  metis_tac [FIELD_RAT_NEG_DIV,
             ratTheory.RAT_LDIV_LEQ_NEG,
             ratTheory.RAT_MUL_COMM]
QED

val _ =
  List.app store_field
    [("FIELD_RAT_INV_EQ_DIV", FIELD_RAT_INV_EQ_DIV),
     ("FIELD_RAT_RDIV_EQ", FIELD_RAT_RDIV_EQ),
     ("FIELD_RAT_NEG_DIV", FIELD_RAT_NEG_DIV),
     ("FIELD_RAT_NEG_RDIV_EQ", FIELD_RAT_NEG_RDIV_EQ),
     ("FIELD_RAT_EQ_NEG_RDIV", FIELD_RAT_EQ_NEG_RDIV),
     ("FIELD_RAT_ADD_RDIV", FIELD_RAT_ADD_RDIV),
     ("FIELD_RAT_RDIV_ADD", FIELD_RAT_RDIV_ADD),
     ("FIELD_RAT_DIFF_RDIV", FIELD_RAT_DIFF_RDIV),
     ("FIELD_RAT_NEG_RDIV_ADD", FIELD_RAT_NEG_RDIV_ADD),
     ("FIELD_RAT_RDIV_DIFF", FIELD_RAT_RDIV_DIFF),
     ("FIELD_RAT_NEG_RDIV_DIFF", FIELD_RAT_NEG_RDIV_DIFF),
     ("FIELD_RAT_POS_LE_NEG_RDIV", FIELD_RAT_POS_LE_NEG_RDIV),
     ("FIELD_RAT_NEG_LE_NEG_RDIV", FIELD_RAT_NEG_LE_NEG_RDIV),
     ("FIELD_RAT_POS_LT_NEG_RDIV", FIELD_RAT_POS_LT_NEG_RDIV),
     ("FIELD_RAT_NEG_LT_NEG_RDIV", FIELD_RAT_NEG_LT_NEG_RDIV),
     ("FIELD_RAT_POS_NEG_RDIV_LT", FIELD_RAT_POS_NEG_RDIV_LT),
     ("FIELD_RAT_NEG_NEG_RDIV_LT", FIELD_RAT_NEG_NEG_RDIV_LT),
     ("FIELD_RAT_POS_NEG_RDIV_LE", FIELD_RAT_POS_NEG_RDIV_LE),
     ("FIELD_RAT_NEG_NEG_RDIV_LE", FIELD_RAT_NEG_NEG_RDIV_LE)]
