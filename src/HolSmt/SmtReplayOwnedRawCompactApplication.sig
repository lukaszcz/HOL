(* Raw-to-rich local witness transport; SAME existing invocation only. *)
signature SmtReplayOwnedRawCompactApplication =
sig
  type plan
  type owner =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,work : SmtReplayInvocationWork.portfolio}
  (* Root original occurrence or original positive Goal only. Each tuple
     is a disjoint bounded owned local equality, not an enclosing D proof.
     Bindings inside a raw binder body are not inferred from rich children.
     Ordinals retain the existing Work namespace; no fresh allowance. *)
  val prepare : SmtReplayInvocationWork.portfolio ->
    {source : SmtReplayOwnedTransport.focus,
     leaves : (int * SmtReplayOwnedTransport.conversion) list,
     check_type : Type.hol_type -> unit} -> plan
  val graph_conversion_for : owner -> plan ->
    SmtReplayCanonGraph.graph_conversion
  (* Original assumptions map ordinal i>=1 to Source index i-1. An original
     positive Goal maps ONLY the compact fixed-negative result to denial
     index n, never to a new positive Source premise. *)
  val source_index_for : owner -> plan -> int
end
