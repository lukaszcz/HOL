(* Excl treats rule: as literal text, not a namespace. *)
val _ = LegacyFailures.prefix
  {prefix = "rule:", installed = false}
