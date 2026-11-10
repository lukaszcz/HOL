signature SmtLib_GraphScopedMap =
sig
  type options =
    {graph : SmtReplayGraph.graph, admission : SmtReplayBinder.admission,
     template_limit : int,
     scope_opened : SmtReplayGraph.scope -> unit,
     record : SmtReplayGraph.node * SmtReplayGraph.node * Thm.thm -> unit}
  (* Separate public session callback for bounded Z3 pointwise maps.
     No ordinary fallback inspects unknown or oversized actual operands. *)
  val install : options -> SmtLib_GraphFrontend.session -> unit
end
