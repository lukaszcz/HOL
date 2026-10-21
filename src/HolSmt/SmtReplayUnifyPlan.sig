(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayUnifyPlan =
sig
  type plan
  type obligation =
    {assignment : SmtReplayUnify.assignment, equation : SmtReplayGraph.node}
  type equation =
    {left : SmtReplayGraph.node, right : SmtReplayGraph.node,
     target : SmtReplayGraph.node}
  type binder_relation =
    {left : SmtReplayGraph.node, right : SmtReplayGraph.node,
     equation : SmtReplayGraph.node}

  (* Discover all equality nodes before freezing the enclosing proof block.
     A plan is graph/scope owned, including an empty unification result. *)
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplayUnify.result -> plan
  val roots : plan -> SmtReplayGraph.node list
  val obligations : plan -> obligation list
  val equations : plan -> equation list
  val binder_relations : plan -> binder_relation list

  (* The caller supplies independently checked assignment equality edges.
     Their conclusions must be the named obligation nodes in this block.
     Deferred solver sources remain explicit dependencies; this operation
     does not turn them into constructor definitions or closed rewrites.
     Results prove the named equality targets in recorded equation order. *)
  val assemble : SmtReplayProof.block -> plan ->
    (obligation -> SmtReplayProof.edge) -> SmtReplayProof.edge list
  val assemble_with_relations : SmtReplayProof.block -> plan ->
    {assignment : obligation -> SmtReplayProof.edge,
     binder : binder_relation -> SmtReplayProof.edge} ->
    SmtReplayProof.edge list
end
