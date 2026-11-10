signature SmtLib_GraphIntegerDivision =
sig
  (* Call within the original Work action. The fixed closed schema keeps
     the underspecified zero-divisor branch; it uses no Source assumptions.
     Opaque terms and binders are left alone, not opened by this pass. *)
  val conversion : SmtReplayInvocationWork.portfolio ->
    {check_type : Type.hol_type -> unit} ->
    SmtReplayGraph.node -> SmtReplayCanonGraph.graph_conversion option
end
