signature SmtLib_GraphGuardedCarrierCancel =
sig
  type conversion
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     admission : SmtReplayBinder.admission,template_limit : int}
  (* Input is the actual owned changed-carrier body: guard ==> consequent
     or guard /\ consequent. The canonical guard must be exactly 0 <= operand.
     Nonbinder local bodies only; refusal is incomplete continuation. *)
  val discover : options ->
    {body : SmtReplayGraph.node,operand : SmtReplayGraph.node} ->
    conversion option
  val source : conversion -> SmtReplayGraph.node
  val target : conversion -> SmtReplayGraph.node
  val equality : conversion -> SmtReplayGraph.node
  val theorem : conversion -> Thm.thm
  val premise : conversion -> SmtReplayGraph.node
  val operand : conversion -> SmtReplayGraph.node
end
