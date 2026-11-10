signature SmtLib_GraphNumArithmetic =
sig
  (* Injection homomorphisms, with all arithmetic operands kept owned. *)
  val propose : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {template_limit : int, check_type : Type.hol_type -> unit} ->
    SmtReplayGraph.node -> SmtReplayCanonGraph.graph_schema option
  (* Closed non-negativity proofs create derived assumptions, not Sources. *)
  val nonnegative : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {template_limit : int, check_type : Type.hol_type -> unit} ->
    SmtReplayGraph.node -> SmtLib_GraphPreprocessFacts.fact
end
