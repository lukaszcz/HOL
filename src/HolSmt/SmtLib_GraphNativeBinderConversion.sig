signature SmtLib_GraphNativeBinderConversion =
sig
  datatype local_result = Unhandled | Gap
    | Checked of {target : SmtReplayGraph.node,theorem : Thm.thm,
                  continuation : bool}
  type conversion
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     admission : SmtReplayBinder.admission,template_limit : int,
     propose : SmtReplayGraph.scope -> SmtReplayGraph.node ->
       SmtReplayCanonGraph.graph_schema option,
     local_witness : SmtReplayGraph.scope -> SmtReplayGraph.node ->
       local_result}
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
