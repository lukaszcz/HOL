(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplaySourceBinderAlignment =
sig
  type binder_contract =
    {source_variables : SmtReplayGraph.node list,allow_bound : bool,
     admission : SmtReplayBinder.admission}
  type alignment
  (* Source binder ownership is explicit. Root Sources authorize rigid
     variables only; scoped Sources can authorize visible Bound ancestors.
     No typed free variable is renamed, assigned or guessed. *)
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {source : SmtReplayGraph.node, parsed : SmtReplayGraph.node,
     admit_binder : SmtReplayGraph.node * SmtReplayGraph.node ->
       binder_contract option,
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
