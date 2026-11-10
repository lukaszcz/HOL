signature SmtLib_GraphFloatCarrier =
sig
  type transfer
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     admission : SmtReplayBinder.admission,template_limit : int,
     source_variables : SmtReplayGraph.node list option,allow_bound : bool,
     scope_opened : SmtReplayGraph.scope -> unit}
  (* The body must already factor through smtfp_intro at its exact owned
     float bound ID. Non-invariant raw uses are explicitly unsupported. *)
  val discover : options -> SmtReplayGraph.node -> transfer option
  val source : transfer -> SmtReplayGraph.node
  val target : transfer -> SmtReplayGraph.node
  val equality : transfer -> SmtReplayGraph.node
  val theorem : transfer -> Thm.thm
end
