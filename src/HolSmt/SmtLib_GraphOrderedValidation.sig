signature SmtLib_GraphOrderedValidation =
sig
  type validation
  type pipeline
  val pipeline : SmtLib_GraphOrderedConversionScoped.options -> pipeline
  type pass = SmtLib_GraphOrderedConversionScoped.pass
  type trace =
    (string * SmtReplayGraph.node * SmtReplayGraph.node) list
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {goal : Term.term list * Term.term,import_limit : int,
     assumption_pipeline : pipeline,goal_pipeline : pipeline} -> validation
  val original_sources : validation -> SmtReplaySource.sources
  val processed_goal : validation -> Term.term list * Term.term
  val processed_assumptions : validation -> SmtReplayGraph.node list
  val processed_denied_goal : validation -> SmtReplayGraph.node
  val roots : validation -> SmtReplayGraph.node list
  val source_nodes : validation -> SmtReplayGraph.node list
  val witnesses : validation -> (SmtReplayGraph.node * Thm.thm) list
  val stages : validation -> {goal : trace,assumptions : trace list}
  val gaps : validation -> (string * SmtReplayGraph.node list) list
  val goal_equality : validation -> SmtReplayProof.block -> SmtReplayProof.edge
  val assembler : validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option
  val realize_contradiction : validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge -> Thm.thm
end
