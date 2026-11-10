(* Copyright (c) 2026 The HOL4 contributors. *)

signature SmtReplaySupport =
sig
  type certificate
  type discovery =
    {name : SmtReplayGraph.node -> Term.term,
     constructor : SmtReplayGraph.node -> Thm.thm,
     premise : int -> Thm.thm}
  (* Run small checked discovery once. Premise hypotheses remain separate
     from the constructor-only context until actual kernel support is read. *)
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {roots : SmtReplayGraph.node list,
     premises : SmtReplayGraph.node list, target : SmtReplayGraph.node,
     template_limit : int, check_type : Type.hol_type -> unit,
     prove : discovery -> Thm.thm} -> certificate
  val roots : certificate -> SmtReplayGraph.node list
  (* Indices refer to recorded input occurrences. For equal node IDs the
     first occurrence supplies the one atomic kernel hypothesis. *)
  val selected : certificate -> int list
  val assemble : SmtReplayProof.block -> certificate ->
    {index : int, node : SmtReplayGraph.node,
     edge : SmtReplayProof.edge} list -> SmtReplayProof.edge
end
