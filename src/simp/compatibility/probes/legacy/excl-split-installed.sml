(* Excl treats split: as literal text, not a namespace. *)
val _ = LegacyFailures.prefix
  {prefix = "split:", installed = true}
