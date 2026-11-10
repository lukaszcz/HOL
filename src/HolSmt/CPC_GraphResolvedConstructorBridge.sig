signature CPC_GraphResolvedConstructorBridge =
sig
  type plan
  type assignment =
    {equation : SmtReplayGraph.node,variable : SmtReplayGraph.node,
     residue : SmtReplayGraph.node}
  val discover :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     resolution : SmtReplayResolve.resolution,
     originals : SmtReplayGraph.node list,targets : SmtReplayGraph.node list,
     assignments : assignment list,template_limit : int,
     check_type : Type.hol_type -> unit} -> plan
  val roots : plan -> SmtReplayGraph.node list
  (* The supplied block retains this exact source occurrence inventory.
     Assignment equations follow the full mandatory original prefix. *)
  val sources : plan -> SmtReplayGraph.node list
  val assemble : SmtReplayProof.block -> plan ->
    SmtReplayGraph.node -> SmtReplayProof.edge
  (* A checked normalized fact gives the original fact under the explicit
     assignment equations. No ordinary Source hypothesis is rewritten. *)
  val original_fact : SmtReplayProof.block -> plan ->
    {target : SmtReplayGraph.node,normalized : SmtReplayProof.edge} ->
    SmtReplayProof.edge
end
