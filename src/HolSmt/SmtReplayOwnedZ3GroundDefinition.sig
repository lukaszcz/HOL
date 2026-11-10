(* A fixed actual INTRO_DEF producer; not an arbitrary local-law adapter. *)
signature SmtReplayOwnedZ3GroundDefinition =
sig
  type owner
  type plan
  type receipt
  val begin : SmtReplayInvocationWork.portfolio ->
    {packet : Z3_GraphProofParser.proof SmtLib_GraphProof.packet,
     frame : SmtReplayOwnedScopeReceipt.receipt,
     check_type : Type.hol_type -> unit} -> owner
  (* NONE means this fixed equation operation is not applicable. It never
     asserts that a legacy general/conditional/binder rule is unsupported. *)
  val prepare : SmtReplayInvocationWork.portfolio -> owner ->
    Z3_GraphProofParser.proof_id -> plan option
  (* Separate fixed equation operation: actual private RHS declarations
     are retained, not assigned. The original public-ground method is exact. *)
  val prepare_dependent_equation : SmtReplayInvocationWork.portfolio ->
    owner -> Z3_GraphProofParser.proof_id -> plan option
  val private_dependencies_for : SmtReplayInvocationWork.portfolio ->
    owner -> receipt -> SmtReplayGraph.node list
  (* Owns one action; every proof shape was quoted by prepare. *)
  val execute : SmtReplayInvocationWork.portfolio -> owner -> plan -> receipt
  val description_for : SmtReplayInvocationWork.portfolio -> owner ->
    receipt ->
    {frame : SmtReplayOwnedScopeReceipt.receipt,
     proof_id : Z3_GraphProofParser.proof_id,
     definition : SmtReplayGraph.node,name : SmtReplayGraph.node,
     residue : SmtReplayGraph.node,target : SmtReplayGraph.node,
     law : SmtReplayProof.closed_fact}
end
