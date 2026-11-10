signature SmtLib_CarrierTopDepth =
sig
  type owner
  type focus
  type conversion
  type session
  (* The owner is already established; this creates no Source or budget. *)
  val start : owner -> focus -> session
  val run : session -> conversion option
  val close : session -> unit
end
