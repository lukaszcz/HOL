signature CPC_GraphSelectedProof =
sig
  type input =
    {index : int,node : SmtReplayGraph.node,
     command_occurrence : int option}
  exception Adapter
  val discover_prepared :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     proof : CPC_ProofParser.graph_proof,sources : SmtReplaySource.sources,
     admission : CPC_GraphNativeAdmission.plan,
     equations : CPC_GraphDefinitionHistory.occurrence list,
     template_limit : int,check_type : Type.hol_type -> unit} ->
    {certificate : SmtReplaySupport.certificate,inputs :
       input list}
  val discover :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     proof : CPC_ProofParser.graph_proof,sources : SmtReplaySource.sources,
     equations : CPC_GraphDefinitionHistory.occurrence list,
     template_limit : int,check_type : Type.hol_type -> unit} ->
    {certificate : SmtReplaySupport.certificate,inputs :
       input list}
end
