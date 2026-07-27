Theory iffBatch
Ancestors
  clasetSeed
Libs
  BasicProvers clasimpLib iffTestSupport

open iffTestSupport

Definition iff_batch_one_def:
  iff_batch_one (p : bool) = p
End

Definition iff_batch_two_def:
  iff_batch_two (p : bool) = p
End

Definition iff_batch_three_def:
  iff_batch_three (p : bool) = p
End

Theorem iff_batch_one_rule[iff]:
  !p. iff_batch_one p <=> p
Proof
  simp[iff_batch_one_def]
QED

Theorem iff_batch_two_rule[iff]:
  !p. iff_batch_two p <=> p
Proof
  simp[iff_batch_two_def]
QED

Theorem iff_batch_three_rule[iff]:
  !p. iff_batch_three p <=> p
Proof
  simp[iff_batch_three_def]
QED

val _ =
  case List.filter (equal "iffBatch")
    (simpLib.ssfrag_names_of (BasicProvers.srw_ss ())) of
      [_] => ()
    | _ => fail "three iff declarations did not share one theory fragment"
