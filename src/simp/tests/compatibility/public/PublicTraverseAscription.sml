(* Complete old datatype signature: do not accommodate new constructors. *)
structure PublicTraverse : LegacyTraverse = Traverse
val _ = Paired.check "complete Traverse ascription" true
