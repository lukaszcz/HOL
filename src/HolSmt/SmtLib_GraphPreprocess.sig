(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtLib_GraphPreprocess =
sig
  type validation

  (* Discover checked conversions of a goal and its assumptions in the same
     source graph as replay. This conversion-only adapter neither invokes an
     opaque tactic validation nor invents transfer or auxiliary assumptions.
     Existing caller import/type/schema admission remains authoritative. *)
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {goal : Abbrev.goal, import_limit : int, revisit : bool,
     check_type : Type.hol_type -> unit,
     conversion : SmtReplayGraph.node ->
       SmtReplayCanonGraph.graph_schema option} -> validation

  (* Use the SAME already admitted original Source map. This does not
     execute an opaque tactic validation or grant additional assumptions. *)
  val discover_from_sources : SmtReplayGraph.graph ->
    SmtReplayGraph.scope -> SmtReplaySource.sources ->
    {import_limit : int,revisit : bool,
     check_type : Type.hol_type -> unit,
     conversion : SmtReplayGraph.node ->
       SmtReplayCanonGraph.graph_schema option} -> validation

  (* General checked dependency catalog; original source prefix unchanged. *)
  (* Expected W before old F/GP semantic activation. No Source/Work issue. *)
  val from_portfolio_with_work : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphSourcePortfolio.validation -> validation
  val validate_with_work : SmtReplayInvocationWork.portfolio ->
    validation -> unit
  val portfolio_validation_with_work : SmtReplayInvocationWork.portfolio ->
    validation -> SmtLib_GraphSourcePortfolio.validation option
  (* Original Source-only final receiver; does not add CPC local Sources. *)
  val prepare_final_frontier_with_work : SmtReplayInvocationWork.portfolio ->
    validation -> {roots : SmtReplayGraph.node list} ->
    SmtReplayProof.realization_frontier
  val assembler_with_work : SmtReplayInvocationWork.portfolio ->
    validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option
  val from_portfolio : SmtLib_GraphSourcePortfolio.validation -> validation
  val portfolio_validation : validation ->
    SmtLib_GraphSourcePortfolio.validation option

  val original_sources : validation -> SmtReplaySource.sources
  val processed_goal : validation -> Abbrev.goal
  val processed_assumptions : validation -> SmtReplayGraph.node list
  val processed_denied_goal : validation -> SmtReplayGraph.node
  val source_nodes : validation -> SmtReplayGraph.node list
  val roots : validation -> SmtReplayGraph.node list
  (* Opaque closed auxiliaries are reserved before the common P freeze. *)
  val closed_facts : validation -> SmtReplayProof.closed_fact list
  val conversions : validation -> SmtReplayProof.closed_conversion list
  val template_limit : validation -> int option

  (* Include roots and original source_nodes before freezing replay's block.
     Parsed processed assertions use these derived edges; they must not be
     added as fresh ordinary source assumptions. Other reserved closed laws
     and checked local scope assumptions may share the block. The returned
     assembler owns a block-local cache and rejects reuse after realization. *)
  val assembler : validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option
  val from_portfolio_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphSourcePortfolio.validation -> validation
  val validate_with_policy : SmtReplayInvocationWork.portfolio ->
    validation -> unit
  val template_policy : validation -> SmtReplayResourcePolicy.limit option

  (* Query metadata over the same authenticated preprocessing validation.
     Assumptions preserve order and duplicate occurrences. The positive
     Goal and its already validated denial are graph IDs, not expanded HOL
     terms. Each call owns its Work action; do not nest in with_step. *)
  val processed_nodes_with_policy_for : SmtReplayInvocationWork.portfolio ->
    validation -> {assumptions:SmtReplayGraph.node list,
                   goal:SmtReplayGraph.node,denied:SmtReplayGraph.node}
  type graph_query
  val prepare_query_with_policy : SmtReplayInvocationWork.portfolio ->
    validation -> graph_query
  val validate_query_with_policy : SmtReplayInvocationWork.portfolio ->
    graph_query -> unit
  (* The actual retained preprocessing, never a caller-rebuilt Source map.
     Owns one Work action; the Work header precedes held validation. *)
  val query_preprocessing_with_policy_for :
    SmtReplayInvocationWork.portfolio -> graph_query -> validation
  (* Expected Work is compared before held backing activation. This retains
     existing Source identity only; it grants no serialization, solver,
     native effect or new Source permission. Later graph extension is valid.
     The returned assumption list is immutable retained data, not a copy. *)
  val query_nodes_with_policy_for : SmtReplayInvocationWork.portfolio ->
    graph_query ->
    {graph:SmtReplayGraph.graph,scope:SmtReplayGraph.scope,
     sources:SmtReplaySource.sources,assumptions:SmtReplayGraph.node list,
     goal:SmtReplayGraph.node,denied:SmtReplayGraph.node}

  (* Metadata frontier only. Native freeze/assembly need their own admission. *)
  val prepare_final_frontier_with_policy : SmtReplayInvocationWork.portfolio ->
    validation -> {roots:SmtReplayGraph.node list} ->
    SmtReplayProof.policy_realization_frontier

  (* Actual policy portfolio assembly, with native contract from block. *)
  val assembler_with_policy : SmtReplayInvocationWork.portfolio ->
    validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option

  val assembler_sparse_with_policy : SmtReplayInvocationWork.portfolio ->
    validation -> SmtReplayProof.policy_sparse_block ->
    SmtReplayGraph.node -> SmtReplayProof.policy_sparse_edge option

end
