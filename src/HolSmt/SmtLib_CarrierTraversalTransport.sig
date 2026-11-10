signature SmtLib_CarrierTraversalTransport =
sig
  (* Required trusted implementation, not a caller theorem callback record.
     Every focus retains its exact node, actual frames and admission recipe. *)
  type owner
  type focus
  type conversion
  datatype shape = Atomic | Application of focus * focus | Binder of focus

  val validate_owner : owner -> unit
  val validate_focus : owner -> focus -> unit
  val retire : owner -> unit
  (* Debit the SAME invocation work portfolio before each control transition.
     This is not a bound for the internal work of the other operations. *)
  val control : owner -> unit

  val view : owner -> focus -> shape
  val carrier : owner -> focus -> conversion option
  val beta : owner -> focus -> conversion option
  val validate_conversion : owner -> focus -> conversion -> unit
  val target : owner -> conversion -> focus
  val compose : owner -> conversion -> conversion -> conversion
  val lift_application : owner -> focus ->
    conversion option * conversion option -> conversion
  val lift_binder : owner -> focus -> conversion -> conversion
  (* Checked, bounded alpha equivalence, not node-ID inequality. *)
  val alpha_changed : owner -> focus -> conversion -> bool
end
