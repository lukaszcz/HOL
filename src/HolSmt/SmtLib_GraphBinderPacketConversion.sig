signature SmtLib_GraphBinderPacketConversion =
sig
  type conversion
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     admission : SmtReplayBinder.admission,template_limit : int,
     propose : SmtReplayGraph.scope -> SmtReplayGraph.node ->
       SmtReplayCanonGraph.graph_schema option,
     completed : SmtLib_GraphScopedInventory.completion -> unit}
  (* Structural closure conversion only. Carrier-changing quantifier laws
     require a separate checked bridge; preserved oversized atoms are gaps. *)
  val create : options -> SmtReplayGraph.node -> conversion
  val discover : options -> SmtReplayGraph.node -> conversion
  val source : conversion -> SmtReplayGraph.node
  val result : conversion -> SmtReplayGraph.node
  val equality : conversion -> SmtReplayGraph.node
  val roots : conversion -> SmtReplayGraph.node list
  val witnesses : conversion -> (SmtReplayGraph.node * Thm.thm) list
  val gaps : conversion -> SmtReplayGraph.node list
  val assemble : conversion -> SmtReplayProof.block -> SmtReplayProof.edge
end
