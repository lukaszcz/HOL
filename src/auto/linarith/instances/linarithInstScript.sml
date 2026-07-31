Theory linarithInst
Ancestors
  integer real rat
Libs
  linarithData

open integerTheory realTheory ratTheory

Theorem INT_LET_ADD2:
  !w x y z : int. w <= x /\ y < z ==> w + y < x + z
Proof
  rw [INT_LE_LT] >>
  metis_tac [integerTheory.INT_LT_ADD2, INT_LT_LADD]
QED

Theorem INT_LTE_ADD2:
  !w x y z : int. w < x /\ y <= z ==> w + y < x + z
Proof
  rw [INT_LE_LT] >>
  metis_tac [integerTheory.INT_LT_ADD2, INT_LT_RADD]
QED

Theorem INT_NEQ_E:
  !x y : int.
    x <> y ==> (x < y ==> F) ==> (y < x ==> F) ==> F
Proof
  metis_tac [INT_LT_TOTAL]
QED

Theorem INT_MIN_LT_IFF:
  !x y z : int. x < int_min y z <=> x < y /\ x < z
Proof
  rw [INT_MIN] >>
  metis_tac [INT_LT_TOTAL, INT_LT_TRANS]
QED

Theorem INT_MAX_LT_IFF:
  !x y z : int. int_max x y < z <=> x < z /\ y < z
Proof
  rw [INT_MAX] >>
  metis_tac [INT_LT_TOTAL, INT_LT_TRANS]
QED

Theorem INT_MIN_SPLIT[arith_split]:
  !P (x : int) y.
    P (int_min x y) <=>
    (x < y ==> P x) /\ (y <= x ==> P y)
Proof
  rw [INT_MIN, INT_NOT_LT] >>
  metis_tac [INT_NOT_LT]
QED

Theorem INT_MAX_SPLIT[arith_split]:
  !P (x : int) y.
    P (int_max x y) <=>
    (x < y ==> P y) /\ (y <= x ==> P x)
Proof
  rw [INT_MAX, INT_NOT_LT] >>
  metis_tac [INT_NOT_LT]
QED

Theorem INT_ABS_SPLIT[arith_split]:
  !P (x : int).
    P (ABS x) <=>
    (x < 0 ==> P (~x)) /\ (0 <= x ==> P x)
Proof
  rw [INT_ABS, INT_NOT_LT] >>
  metis_tac [INT_NOT_LT]
QED

Theorem REAL_NEQ_E:
  !x y : real.
    x <> y ==> (x < y ==> F) ==> (y < x ==> F) ==> F
Proof
  metis_tac [REAL_LT_TOTAL]
QED

Theorem REAL_MIN_SPLIT[arith_split]:
  !P (x : real) y.
    P (min x y) <=>
    (x <= y ==> P x) /\ (y < x ==> P y)
Proof
  rw [min_def] >>
  metis_tac [REAL_NOT_LE]
QED

Theorem REAL_MAX_SPLIT[arith_split]:
  !P (x : real) y.
    P (max x y) <=>
    (x <= y ==> P y) /\ (y < x ==> P x)
Proof
  rw [max_def] >>
  metis_tac [REAL_NOT_LE]
QED

Theorem REAL_ABS_SPLIT[arith_split]:
  !P (x : real).
    P (abs x) <=>
    (0 <= x ==> P x) /\ (x < 0 ==> P (-x))
Proof
  rw [abs] >>
  metis_tac [REAL_NOT_LE]
QED

Theorem RAT_LT_ADD2:
  !a b c d : rat. a < b /\ c < d ==> a + c < b + d
Proof
  metis_tac [RAT_LES_RADD, RAT_LES_LADD, RAT_LES_TRANS]
QED

Theorem RAT_LET_ADD2:
  !a b c d : rat. a <= b /\ c < d ==> a + c < b + d
Proof
  metis_tac [RAT_LEQ_RADD, RAT_LES_LADD, RAT_LEQ_LES_TRANS]
QED

Theorem RAT_LTE_ADD2:
  !a b c d : rat. a < b /\ c <= d ==> a + c < b + d
Proof
  metis_tac [RAT_LES_RADD, RAT_LEQ_LADD, RAT_LES_LEQ_TRANS]
QED

Theorem RAT_LEQ_LMUL_POS:
  !a b c : rat. 0 < c /\ a <= b ==> c * a <= c * b
Proof
  metis_tac [RAT_LEQ_LES, RAT_LES_LMUL_POS]
QED

Theorem RAT_NEQ_E:
  !x y : rat.
    x <> y ==> (x < y ==> F) ==> (y < x ==> F) ==> F
Proof
  metis_tac [RAT_LES_TOTAL]
QED

Theorem RAT_OF_NUM_NONNEG:
  !n : num. 0q <= &n
Proof
  simp [RAT_OF_NUM_LEQ]
QED
