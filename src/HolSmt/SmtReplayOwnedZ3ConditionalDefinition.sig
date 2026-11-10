(* Actual conditional INTRO_DEF; no caller law/normalizer authority. *)
signature SmtReplayOwnedZ3ConditionalDefinition =
sig
  type owner
  type plan
  type receipt
  val begin : SmtReplayInvocationWork.portfolio ->
    {packet : Z3_GraphProofParser.proof SmtLib_GraphProof.packet,
     frame : SmtReplayOwnedScopeReceipt.receipt,
     check_type : Type.hol_type -> unit} -> owner
  val prepare : SmtReplayInvocationWork.portfolio -> owner ->
    Z3_GraphProofParser.proof_id -> plan option
  val execute : SmtReplayInvocationWork.portfolio -> owner -> plan -> receipt
  val describe_for : SmtReplayInvocationWork.portfolio -> owner -> receipt ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     proof_id : Z3_GraphProofParser.proof_id,
     name : SmtReplayGraph.node,definition : SmtReplayGraph.node,
     residue : SmtReplayGraph.node,target : SmtReplayGraph.node,
     law : SmtReplayGraph.node,
     conversion : SmtReplayCanonGraph.graph_conversion,
     guard_dependencies : SmtReplayGraph.node list,
     private_dependencies : SmtReplayGraph.node list}
end
