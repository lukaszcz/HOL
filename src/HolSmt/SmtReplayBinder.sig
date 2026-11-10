(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayBinder =
sig
  type admission =
    {metric : SmtReplayGraph.metric, input_limit : int, output_limit : int,
     check_type : Type.hol_type -> unit, refuse : string -> unit}
  (* Variables are outermost first. Local source assumptions must have been
     discharged in a compact block, or supplied by checked source witnesses.
     Admission covers realized operands, surviving hypotheses and output
     before any kernel GEN or abstraction construction. The caller supplies
     its existing resource diagnostic and type-work admission. *)
  val close_forall : SmtReplayGraph.graph ->
    {parent_scope : SmtReplayGraph.scope, scope : SmtReplayGraph.scope,
     variables : SmtReplayGraph.node list, body : SmtReplayGraph.node,
     block : SmtReplayProof.block, edge : SmtReplayProof.edge,
     resolution : SmtReplayResolve.resolution option,
     witnesses : (int * SmtReplayGraph.node -> Thm.thm option) option,
     admission : admission, close : unit -> unit} ->
    {node : SmtReplayGraph.node, theorem : Thm.thm}
end
