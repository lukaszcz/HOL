(* Copyright (c) 2026 The HOL4 contributors. *)
(* Checked auxiliary preprocessing fact schemas. *)
signature SmtLib_GraphPreprocessFacts =
sig
  type fact
  type validation
  val checked_fact : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {theorem : Thm.thm, holes : Term.term list,
     operands : SmtReplayGraph.node list, template_limit : int} -> fact
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {goal : Abbrev.goal, import_limit : int, revisit : bool,
     check_type : Type.hol_type -> unit,
     conversion : SmtReplayGraph.node ->
       SmtReplayCanonGraph.graph_schema option,
     facts : fact list} -> validation
  val original_sources : validation -> SmtReplaySource.sources
  val processed_goal : validation -> Abbrev.goal
  val processed_assumptions : validation -> SmtReplayGraph.node list
  val processed_denied_goal : validation -> SmtReplayGraph.node
  val source_nodes : validation -> SmtReplayGraph.node list
  val roots : validation -> SmtReplayGraph.node list
  val assembler : validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option
end
