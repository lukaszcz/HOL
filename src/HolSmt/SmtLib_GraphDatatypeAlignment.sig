(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtLib_GraphDatatypeAlignment =
sig
  type alignment
  (* Independent branches need authoritative recipe provenance and an
     explicit existing local equation budget. Both must be known closed.
     Discovery may allocate graph nodes on a later refusal. *)
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {source : SmtReplayGraph.node, parsed : SmtReplayGraph.node,
     admit_branch : SmtReplayGraph.node * SmtReplayGraph.node -> int option,
     check_type : Type.hol_type -> unit} -> alignment
  val source : alignment -> SmtReplayGraph.node
  val parsed : alignment -> SmtReplayGraph.node
  val roots : alignment -> SmtReplayGraph.node list
  (* Append these nodes to the block's recorded closed witnesses. *)
  val branch_witnesses : alignment ->
    (SmtReplayGraph.node * Thm.thm) list
  (* Proves named source = named parsed, without realizing a parent theorem.
     Every branch witness must be present among the block's source nodes. *)
  val assemble : alignment -> SmtReplayProof.block -> SmtReplayProof.edge
end
