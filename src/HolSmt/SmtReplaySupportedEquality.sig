(* Copyright (c) 2026 The HOL4 contributors. *)

signature SmtReplaySupportedEquality =
sig
  type certificate = SmtReplaySupport.certificate
  (* Native HOL equality discovery uses separate named premise ASSUMEs.
     Actual kernel hypotheses select support before any common-context lift. *)
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {rule : string, target : SmtReplayGraph.node,
     premises : SmtReplayGraph.node list, template_limit : int,
     check_type : Type.hol_type -> unit} -> certificate
  val roots : certificate -> SmtReplayGraph.node list
  val selected : certificate -> int list
  val assemble : SmtReplayProof.block -> certificate ->
    {index : int, node : SmtReplayGraph.node,
     edge : SmtReplayProof.edge} list -> SmtReplayProof.edge
end
