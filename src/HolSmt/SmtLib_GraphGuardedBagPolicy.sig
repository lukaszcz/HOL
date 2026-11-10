signature SmtLib_GraphGuardedBagPolicy =
sig
  type inventory
  datatype numeric_choice = Skip | TransferAll | TransferExceptBags
    | Unresolved
  type options =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     preserve_native_bags : bool,dag_limit : int,type_limit : int}
  (* Inspect the COMPLETE checked current sequent at one actual numeric
     stage boundary. This is policy metadata, never a FINITE rewrite. *)
  val inspect : options ->
    SmtLib_GraphNativeOrderedValidation.validation -> inventory
  val choice : inventory -> numeric_choice
  val free_numeric_ids : inventory -> SmtReplayGraph.node list
  val excluded_bag_ids : inventory -> SmtReplayGraph.node list
  val bags : inventory -> SmtReplayGraph.node list
  val finite_evidence : inventory ->
    (SmtReplayGraph.node * SmtReplayGraph.node) list
  (* Exact processed FINITE assumptions only. The existing checked assembler
     transports them from original canonical Source hypotheses. *)
  val finite_assembler : inventory -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option
  (* The existing exact guard consumer is selected only for an actual owned
     reachable current body. Pointwise bag guards remain a separate gap. *)
  val guarded_cancel : inventory ->
    SmtLib_GraphGuardedCarrierCancel.options ->
    {body : SmtReplayGraph.node,operand : SmtReplayGraph.node} ->
    SmtLib_GraphGuardedCarrierCancel.conversion option
  val carrier_pass : inventory -> SmtLib_GraphGuardedBagCarrier.options ->
    SmtLib_GraphNativeOrderedConversion.pass option
  val gaps : inventory -> string list
  val remaining : unit -> string list
end
