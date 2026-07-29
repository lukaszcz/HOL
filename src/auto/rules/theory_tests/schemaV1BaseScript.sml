Theory schemaV1Base
Ancestors
  clasetSeed
Libs
  BasicProvers clasetLib

Theorem schema_v1_intro[intro=64]:
  !p q. p ==> p \/ q
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem schema_v1_elim[elim=37]:
  !p q. p /\ q ==> q /\ p
Proof
  BasicProvers.PROVE_TAC []
QED

Theorem schema_v1_dest[dest=82]:
  !p q. p /\ q ==> p
Proof
  BasicProvers.PROVE_TAC []
QED
