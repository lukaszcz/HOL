(* Compact application transport owns no new Source or Work allowance. *)
signature SmtReplayOwnedCompactApplication =
sig
  type plan
  val prepare : SmtReplayInvocationWork.portfolio ->
    {source : SmtReplayOwnedTransport.focus,
     leaves : (int * SmtReplayOwnedTransport.conversion) list,
     check_type : Type.hol_type -> unit} -> plan
  val graph_conversion_for :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio} -> plan ->
    SmtReplayCanonGraph.graph_conversion
end
