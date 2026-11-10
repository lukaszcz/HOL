signature SmtLib_GraphIntegerDivides =
sig
  val propose : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {template_limit : int,check_type : Type.hol_type -> unit} ->
    SmtReplayGraph.node -> SmtReplayCanonGraph.graph_schema option
end
