(* Source-only compact temporary obligations; no independent Source authority. *)
signature CPC_GraphNativeReservation =
sig
  type plan
  type origin
  type lease =
    {owner : unit ref,revision : int,validate : unit -> unit,
     validate_committed : unit -> unit}
  type request =
    {serial : int,step : CPC_ProofParser.graph_rule_step,
     target : SmtReplayGraph.node}
  val new :
    {packet : CPC_ProofParser.graph_proof SmtLib_GraphProof.packet,
     sources : SmtReplaySource.sources,validate : unit -> unit,
     template_limit : int,check_type : Type.hol_type -> unit,
     lease : request -> lease} -> plan
  (* NONE preserves the ordinary path. SOME has a checked compact identity
     law from the exact target Hyp, and remains mandatory even if unused. *)
  val reserve : plan ->
    {serial : int,step : CPC_ProofParser.graph_rule_step} -> origin option
  val validate_request : origin ->
    {serial : int,target : SmtReplayGraph.node} -> unit
  val validate_committed : origin -> unit
  val serial : origin -> int
  val target : origin -> SmtReplayGraph.node
  val equation : origin -> SmtReplayGraph.node * SmtReplayGraph.node
  val revision : origin -> int
  val roots : origin -> SmtReplayGraph.node list
  val assemble : SmtReplayProof.block -> origin ->
    SmtReplayProof.edge -> SmtReplayProof.edge
end
