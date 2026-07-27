Theory iffWithinRemove
Ancestors
  clasetSeed
Libs
  BasicProvers clasimpLib iffTestSupport

open iffTestSupport

Definition iff_within_remove_def:
  iff_within_remove (p : bool) = p
End

Theorem iff_within_remove_rule[iff]:
  !p. iff_within_remove p <=> p
Proof
  simp[iff_within_remove_def]
QED

val removed_name = "iffWithinRemove$iff_within_remove_rule"
val _ = clasimpLib.remove_iff "iff_within_remove_rule"

val _ =
  if has_iff_rewrite removed_name orelse has_iff_rules removed_name
  then fail "same-theory remove_iff did not retract both immediate views"
  else ()
