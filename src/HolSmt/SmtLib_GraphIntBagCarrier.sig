(* Standalone Source proposal; not selected or compiled. *)
signature SmtLib_GraphIntBagCarrier =
sig
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     admission : SmtReplayBinder.admission,template_limit : int,
     original : SmtReplayGraph.node,view : SmtReplayGraph.source,
     law : SmtReplayProof.closed_fact,
     scope_opened : SmtReplayGraph.scope -> unit}
  (* Exactly the recorded local int->num forall/exists binder. The original
     fixed BAG theorem must already have a genuine closed graph record.
     No old body binder/redex, general type map or whole-stage traversal. *)
  val convert : options ->
    {source : SmtReplayGraph.node,target : SmtReplayGraph.node,
     theorem : Thm.thm}
end
