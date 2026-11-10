(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayDependencies =
sig
  (* Follow owned constructor dependencies. An unadmitted opaque binder
     remains Unknown. The caller's callback preserves its standing binder
     metric and diagnostics before returning that existing admission limit.
     No unfolded bound is imposed on an application DAG. *)
  val graph_summary :
    {graph : SmtReplayGraph.graph, root : SmtReplayGraph.node,
     admit_binder : Term.term -> int option}
    -> SmtReplayGraph.variable_summary

  (* Adapter for a caller-admitted source DAG. The explicit DAG limit is
     passed to the existing checked source importer; binder bodies stay
     opaque until the callback grants their separate bounded admission. *)
  val source_summary :
    {dag_limit : int, admit_binder : Term.term -> int option}
    -> Term.term -> SmtReplayGraph.variable_summary

  (* An exposed free-source witness needs no binder opening. Otherwise the
     complete admitted summary establishes presence/absence; NONE denotes
     incomplete admission and must never be interpreted as closedness. *)
  val source_presence :
    {dag_limit : int, admit_binder : Term.term -> int option}
    -> Term.term -> bool option
end
