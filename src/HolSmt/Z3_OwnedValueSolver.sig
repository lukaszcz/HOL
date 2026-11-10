(* Explicit configured solver path; the legacy/default path is unchanged. *)
signature Z3_OwnedValueSolver =
sig
  type invocation
  type request =
    {limits:SmtCheckedGraph.policy_request,check_type:Type.hol_type -> unit}
  datatype preparation = Prepared of invocation
    | FiniteNeeds of
        {invocation:invocation,
         requirements:SmtLib_GraphFiniteQueryTransport.requirement list}
  datatype result = Solved of SolverSpec.result
    | ReplayNeeds of
        {invocation:invocation,
         requirements:Z3_OwnedValueNamedReplay.requirement list}
    | RealizationNeeds of
        {invocation:invocation,
         requirements:SmtReplayValueRealization.requirement list}
  (* Original Source birth, one existing Work/NC, original preflight and
     finite selection, genuine opening/body transport, actual streamed
     emission and its Mapping assertion roots. No whole-query translation
     or parser Value import is used. Needs retains ownership until close. *)
  val prepare : request -> Abbrev.goal -> preparation
  (* Immutable owner header only, including after retirement. No activation,
     credit, new action, Source acceptance or native permission. *)
  val work_of : invocation -> SmtReplayInvocationWork.portfolio
  (* One actual configured Z3 execution through SolverSpec's strict streamed
     completion/capture/timeout boundary. Genuine unsupported programmes
     retain this invocation and packet; SAT/UNKNOWN/success/error close it.
     The theorem is Source-checked while live and immutably audited by the
     same existing WrapperSession before SolverSpec completes ownership. *)
  val run : SmtReplayInvocationWork.portfolio -> invocation -> result
  val run_with_capture : SmtReplayInvocationWork.portfolio -> invocation ->
    (string -> string -> string -> string -> unit) -> result
  val close : invocation -> unit
end
