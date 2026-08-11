Theory autoSeed
Ancestors
  clasetSeed pairAutoSeed sumAutoSeed optionAutoSeed listAutoSeed
  pred_setAutoSeed arithmeticAutoSeed finite_mapAutoSeed integerAutoSeed
  realAutoSeed stringAutoSeed rich_listAutoSeed sortingAutoSeed
Libs
  clasimpLib splitLib

(* Declarations stay in their per-theory promotion units. *)

(* src/HOL/HOL.thy:1161,1448 @ f7e02b7e. *)
Theorem BOOL_AUTO_COND_P_SPLIT[split]:
  !P b x y.
    P (if b then x else y) <=>
    (b ==> P x) /\ (~b ==> P y)
Proof
  Cases_on `b` >> simp []
QED
