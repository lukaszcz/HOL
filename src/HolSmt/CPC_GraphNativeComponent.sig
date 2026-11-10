signature CPC_GraphNativeComponent =
sig
  type plan
  type admission
  val prepare :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     target : SmtReplayGraph.node,template_limit : int,
     check_type : Type.hol_type -> unit} -> admission option
  val discover_prepared : admission -> plan
  val discover :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     target : SmtReplayGraph.node,template_limit : int,
     check_type : Type.hol_type -> unit} -> plan option
  val roots : plan -> SmtReplayGraph.node list
  val assemble : SmtReplayProof.block -> plan -> SmtReplayProof.edge
  (* One binder-free realization; operands remain named until this boundary. *)
  val prove :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     target : SmtReplayGraph.node,template_limit : int,
     check_type : Type.hol_type -> unit} -> Thm.thm option
end
