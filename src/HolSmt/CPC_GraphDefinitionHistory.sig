signature CPC_GraphDefinitionHistory =
sig
  exception Adapter
  type history
  type preview =
    {owner : unit ref,revision : int,command : CPC_ProofParser.graph_command,
     origin : CPC_GraphProofReplay.producer_origin,
     validate : unit -> unit,validate_committed : unit -> unit}
  type occurrence =
    {serial : int,revision : int,source : SmtReplayGraph.node,
     variable : SmtReplayGraph.node,residue : SmtReplayGraph.node,
     original_hypothesis : int,original_premises :
       {index : int,node : SmtReplayGraph.node,
        command_occurrence : int option} list}
  val new :
    {packet : CPC_ProofParser.graph_proof SmtLib_GraphProof.packet,
     sources : SmtReplaySource.sources,validate : unit -> unit} -> history
  (* Capture a real staged producer, not a descriptor-derived equation.
     Entries remain unusable until their factory validator commits them. *)
  val capture : history -> preview -> unit
  val allocated : history -> SmtReplayGraph.node list
  (* Explicit variable selection preserves actual recorded equation
     orientation; permission comes from the full actual packet inventory. *)
  val equations : history ->
    {serial : int,variable : SmtReplayGraph.node} list -> occurrence list
end
