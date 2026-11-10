signature SmtLib_TraversalRootRecognition =
sig
  type probe
  datatype carrier = NumForall | NumExists | BagForall | BagExists
  type request =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio,
     focus : SmtReplayGraph.closure_child}
  type admitted_request =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio,
     admission : SmtReplayFocusAdmission.focus}
  val inspect_admitted : admitted_request -> probe
  (* One owned metadata action, no conversion or new allowance. *)
  val inspect : request -> probe
  (* DATA getters; ordinary inapplicability is NONE/false. *)
  val carrier : probe -> carrier option
  val beta : probe -> bool
  val node : probe -> SmtReplayGraph.node
  val validate_for : request -> probe -> unit
end
