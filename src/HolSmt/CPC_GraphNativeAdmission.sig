signature CPC_GraphNativeAdmission =
sig
  type fact
  datatype recipe = Original of int | Pending of int
    | Reflexive of SmtReplayGraph.node | Symmetric of fact
    | Contradiction of fact * fact
    | Conjunction of fact * fact | Selection of int * fact
  type plan
  exception Adapter
  val prepare :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     proof : CPC_ProofParser.graph_proof,sources : SmtReplaySource.sources,
     template_limit : int,check_type : Type.hol_type -> unit} -> plan
  val validate : plan -> unit
  val bind : plan -> {graph : SmtReplayGraph.graph,
    scope : SmtReplayGraph.scope,proof : CPC_ProofParser.graph_proof,
    sources : SmtReplaySource.sources,template_limit : int,
    check_type : Type.hol_type -> unit} -> unit
  val root : plan -> fact
  val roots : plan -> SmtReplayGraph.node list
  val obligations : plan -> (int * SmtReplayGraph.node) list
  val node : fact -> SmtReplayGraph.node
  val recipe : fact -> recipe
  val occurrence : fact -> int
end
