signature SmtLib_GraphCarrierQuantifierAlpha =
sig
  type transfer
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     admission : SmtReplayBinder.admission,template_limit : int,
     source_variables : SmtReplayGraph.node list option,allow_bound : bool,
     scope_opened : SmtReplayGraph.scope -> unit}
  (* A complete bounded local natural quantifier only. The guarded target
     retains Num explicitly; guarded numeric cancellation is a later stage.
     No raw outer goal/prefix enters specialization or local beta transport. *)
  val natural : options -> SmtReplayGraph.node -> transfer option
  val source : transfer -> SmtReplayGraph.node
  val target : transfer -> SmtReplayGraph.node
  val equality : transfer -> SmtReplayGraph.node
  val theorem : transfer -> Thm.thm
end
