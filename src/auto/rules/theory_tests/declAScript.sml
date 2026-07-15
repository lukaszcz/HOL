Theory declA
Ancestors
  clasetSeed
Libs
  BasicProvers clasetLib

open clasetLib

val intro_spec =
  {kind = clasetRules.Intro, safe = false, prio = NONE};
val sdest_spec =
  {kind = clasetRules.Dest, safe = true, prio = NONE};

Theorem declA_attr[sintro]:
  !p. p ==> p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem declA_export:
  !p q. p ==> q ==> p
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule intro_spec "declA.declA_export";

Theorem declA_removed:
  !p q r. p /\ q ==> (p ==> r) ==> r
Proof
  BasicProvers.PROVE_TAC []
QED

val _ = export_rule sdest_spec "declA.declA_removed";
val _ = delrule "declA.declA_removed";
