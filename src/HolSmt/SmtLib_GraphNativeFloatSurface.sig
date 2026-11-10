signature SmtLib_GraphNativeFloatSurface =
sig
  (* Extends the held unconditional producer with exactly four closed
     native rounding-constructor equations and two lowered sign laws.
     Integral expansion requires a closed checked concrete type guard.
     No general mode case is opened. *)
  val create : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {template_limit : int, prefix_depth : int,
     check_type : Type.hol_type -> unit} ->
    SmtLib_GraphNativeFloatTransfer.producer
end
