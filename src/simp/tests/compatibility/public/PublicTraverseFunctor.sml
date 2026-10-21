(* The functor body is an ordinary client of the complete old interface. *)
functor PublicTraverseConsumer (T : LegacyTraverse) =
struct
  fun name (T.REDUCER {name, initial, addcontext, apply}) = name
  val dest = T.dest_reducer
  val extend = T.addctxt
  val traverse = T.TRAVERSE
end
structure PublicTraverseArgument = PublicTraverseConsumer (Traverse)
val _ = Paired.check "complete Traverse functor argument" true
