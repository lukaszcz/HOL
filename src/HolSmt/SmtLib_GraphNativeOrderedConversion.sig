signature SmtLib_GraphNativeOrderedConversion =
sig
  type conversion
  type pass =
    {name : string,propose : SmtReplayGraph.scope -> SmtReplayGraph.node ->
      SmtReplayCanonGraph.graph_schema option,
     local_witness : SmtReplayGraph.scope -> SmtReplayGraph.node ->
       SmtLib_GraphNativeBinderConversion.local_result}
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     admission : SmtReplayBinder.admission,template_limit : int,
     passes : pass list}
  val discover : options -> SmtReplayGraph.node -> conversion
  val source : conversion -> SmtReplayGraph.node
  val result : conversion -> SmtReplayGraph.node
  val equality : conversion -> SmtReplayGraph.node
  val roots : conversion -> SmtReplayGraph.node list
  val witnesses : conversion -> (SmtReplayGraph.node * Thm.thm) list
  val gaps : conversion -> (string * SmtReplayGraph.node list) list
  val stages : conversion ->
    (string * SmtReplayGraph.node * SmtReplayGraph.node) list
  val assemble : conversion -> SmtReplayProof.block -> SmtReplayProof.edge
end
