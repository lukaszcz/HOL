Theory schemaV2Base
Ancestors
  clasetSeed
Libs
  BasicProvers clasetLib

Theorem schema_v2_forward[forward=73]:
  !p q. p /\ q ==> q
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem schema_v2_sforward[sforward]:
  !p q. p /\ q ==> p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem schema_v2_norm_default[norm]:
  !p. p /\ T <=> p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem schema_v2_norm_negative[norm= ~7]:
  !p. T /\ p <=> p
Proof
  BasicProvers.PROVE_TAC []
QED
