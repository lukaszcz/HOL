(* Fixed retained-selection carrier/beta continuation, not full NUM/SIMP. *)
signature SmtLib_GraphNeededCarrierDriver =
sig
  type owner
  (* Reuse the SAME scheduler and its actual issuance counter. *)
  val begin : SmtReplayInvocationWork.portfolio ->
    {scheduler : SmtLib_CompactCarrierScheduler.owner,
     portfolio : SmtLib_GraphSourcePortfolio.validation,
     check_type : Type.hol_type -> unit} -> owner
  val build : owner -> SmtLib_GraphPreprocess.validation
  val close : owner -> unit
end
