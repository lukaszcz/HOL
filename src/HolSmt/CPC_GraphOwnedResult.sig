signature CPC_GraphOwnedResult =
sig
  exception Adapter
  (* Transport only an actual checked result to an exactly recorded target.
     Caller quota is explicit; this does not perform ordinary reconstruction. *)
  val align :
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     ordinary_limit : int,target : SmtReplayGraph.node,
     theorem : Thm.thm,located : CPC_Proof.located_term,
     premises : CPC_Proof.located_term list} ->
    Thm.thm * CPC_Proof.located_term
end
