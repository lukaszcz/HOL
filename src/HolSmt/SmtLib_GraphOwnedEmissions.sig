(* SAME original Work and actual GP input to the genuine fixed emitter. *)
signature SmtLib_GraphOwnedEmissions =
sig
  type receipt
  val emit : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.validation -> SmtLib_TranslationEmissions.options ->
    {receipt:receipt,translation:SmtLib.translation,strings:string list}
  val validate_for : SmtReplayInvocationWork.portfolio -> receipt -> unit
  val validate_input_for : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphPreprocess.validation -> receipt -> unit
  val translation_for : SmtReplayInvocationWork.portfolio -> receipt ->
    SmtLib.translation
  (* This is the old fixed bounded worker with authentic per-run stock
     definitions. It gives no assertion-alignment or private Work credit. *)
  val force_worker_for : SmtReplayInvocationWork.portfolio -> receipt ->
    CPC_GraphProofReplay.worker
  (* Caller-local declaration/pattern admission from the naming boundary. *)
  val admitted_worker_for : SmtReplayInvocationWork.portfolio -> receipt ->
    (Term.term -> unit) -> CPC_GraphProofReplay.worker
  val admitted_clause_worker_for :
    SmtReplayInvocationWork.portfolio -> receipt ->
    (Term.term -> unit) -> CPC_GraphProofReplay.clause_worker
  (* Fixed existing Z3 compatibility producers. The owned entry binds the
     actual parser proof privately; this supplies no parser/Source authority. *)
  val z3_workers_for : SmtReplayInvocationWork.portfolio -> receipt ->
    Z3_GraphProofParser.proof ->
    {local_law:Z3_GraphProofReplay.local_request -> Thm.thm option,
     nnf:Z3_GraphProofReplay.nnf_request -> Thm.thm option}

end
