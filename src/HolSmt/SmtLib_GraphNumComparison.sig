(* Copyright (c) 2026 The HOL4 contributors. *)

signature SmtLib_GraphNumComparison =
sig
  (* Closed comparison transfer only. This creates checked semantic edges,
     without source quantification or new integer variables/assumptions. *)
  val propose : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {template_limit : int, check_type : Type.hol_type -> unit} ->
    SmtReplayGraph.node -> SmtReplayCanonGraph.graph_schema option
  (* Integer injection terms can be declared as exact zero-arity source
     aliases. They retain the owned natural operands and their free IDs. *)
  val injections : SmtReplayGraph.graph -> SmtReplayGraph.node list ->
    SmtReplayGraph.node list
end
