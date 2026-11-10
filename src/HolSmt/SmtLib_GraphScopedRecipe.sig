(* Copyright (c) 2026 The HOL4 contributors. *)

signature SmtLib_GraphScopedRecipe =
sig
  type recipe
  val compile :
    {template : Term.term,holes : Term.term list,template_limit : int,
     check_type : Type.hol_type -> unit} -> recipe
  (* Generic template types are matched/instantiated while still small.
     All operands require bounded known size/FV IDs and visible owners.
     The observer is for fixture instrumentation; opened scopes are closed
     on success and failure. No actual operand term is bulk instantiated. *)
  val construct : SmtReplayGraph.graph -> SmtReplayGraph.scope -> recipe ->
    {operands : SmtReplayGraph.node list,
     expected_result_type : Type.hol_type option,
     admission : SmtReplayBinder.admission,
     scope_opened : SmtReplayGraph.scope -> unit} ->
    {node : SmtReplayGraph.node,branches : SmtReplayGraph.node list,
     closed_scopes : SmtReplayGraph.scope list}
end
