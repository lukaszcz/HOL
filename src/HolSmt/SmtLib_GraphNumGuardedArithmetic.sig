signature SmtLib_GraphNumGuardedArithmetic =
sig
  type producer =
    {propose : SmtReplayGraph.node -> SmtReplayCanonGraph.graph_schema option,
     cancel : SmtReplayGraph.node ->
       {rule : SmtLib_GraphPreprocessDerived.rule,
        premise : SmtReplayGraph.node,target : SmtReplayGraph.node}}
  val create : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {template_limit : int,check_type : Type.hol_type -> unit} -> producer
end
