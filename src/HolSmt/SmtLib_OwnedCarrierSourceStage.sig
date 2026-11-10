(* An explicit checked carrier/whole-beta substage, never a default flip. *)
signature SmtLib_OwnedCarrierSourceStage =
sig
  type owner
  (* Views are genuine pre-admitted records in denial-first Source order.
     No Work, Source, cap or original occurrence is created here. *)
  val begin : SmtReplayInvocationWork.portfolio ->
    {views : SmtReplayGraph.source list,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} -> owner
  val build : owner -> SmtLib_GraphPreprocess.validation
  val close : owner -> unit
end
