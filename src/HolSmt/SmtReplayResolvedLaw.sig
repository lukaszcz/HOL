(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayResolvedLaw =
sig
  type plan
  type assignment =
    {stored_source : SmtReplayGraph.node,
     variable : SmtReplayGraph.node,residue : SmtReplayGraph.node}
  (* A first small contract: the caller supplies an independently checked,
     closed, exact resolved-law theorem. No theorem instantiation occurs here.
     Every bridge assignment must have an explicit registered stored source.
     A changed binder requests its separate checked relation, not this API. *)
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {resolution : SmtReplayResolve.resolution,
     original_law : SmtReplayGraph.node,resolved_law : SmtReplayGraph.node,
     theorem : Thm.thm,assignments : assignment list} -> plan
  val roots : plan -> SmtReplayGraph.node list
  val sources : plan -> SmtReplayGraph.node list
  (* Freeze only the resolved law as a derived source. The original law is
     a constructor root. Reprepare/record the final resolution over roots.
     Indices are exact occurrences in the caller's frozen source inventory. *)
  val assemble : SmtReplayProof.block -> SmtReplayResolve.resolution -> plan ->
    {law_index : int,assignment_indices : int list} ->
    {edge : SmtReplayProof.edge,
     witness : int * SmtReplayGraph.node -> Thm.thm option}
end
