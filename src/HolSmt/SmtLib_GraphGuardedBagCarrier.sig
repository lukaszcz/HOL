signature SmtLib_GraphGuardedBagCarrier =
sig
  type options =
    {graph : SmtReplayGraph.graph,admission : SmtReplayBinder.admission,
     template_limit : int,scope_opened : SmtReplayGraph.scope -> unit}
  (* Actual bounded public bag-binder conversion. Boolean element carriers,
     without old beta redexes or nested original quantifiers, only. Gap means
     ordinary compatibility continuation, never completed preprocessing. *)
  val local_witness : options -> SmtReplayGraph.scope ->
    SmtReplayGraph.node -> SmtLib_GraphNativeBinderConversion.local_result
end
