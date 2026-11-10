(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtReplayClause =
sig
  type literal = {atom : SmtReplayGraph.node, negative : bool}
  type occurrences
  type clause

  (* Discover the recorded outer connective tree before freezing a block.
     An atom retains one occurrence even when its graph is a disjunction. *)
  val discover : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    literal list -> occurrences
  val root : occurrences -> SmtReplayGraph.node
  val recorded : occurrences -> literal list
  val from_source : SmtReplayProof.block -> occurrences ->
    SmtReplayProof.edge -> clause
  val literals : clause -> literal list
  val proof : clause -> SmtReplayProof.edge
  val contains : literal -> clause -> bool

  (* Existing checked clause algorithms operate only on compact names. *)
  val resolve : literal -> clause -> clause -> clause option
  val resolve_or_weaken : literal -> clause -> clause -> clause
  val align : occurrences -> clause -> clause option
  val factor : clause -> clause
  val resolve_chain :
    {pivots : literal list, premises : clause list,
     target : occurrences option} -> clause option

  (* Return the named endpoint of a previously discovered occurrence tree.
     Realization belongs to the enclosing completed proof block. *)
  val to_target : occurrences -> clause -> SmtReplayProof.edge
  type policy_occurrences
  (* Source occurrences preserve the actual parsed boundary. Target
     occurrences additionally carry a checked outer-OR constructor tree.
     That separate witness may reframe an OR-valued atom; it never turns
     arbitrary source atoms into disjuncts or supplies a premise proof. *)
  val discover_recorded_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopeReceipt.receipt -> SmtLib_GraphFrontend.term ->
    policy_occurrences
  val discover_target_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopeReceipt.receipt -> SmtLib_GraphFrontend.term ->
    policy_occurrences
  (* Actual constructor/rator definitions required by the bridge. Names
     include opaque atoms as DATA; they are not extra ordinary roots. *)
  val roots_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_occurrences -> SmtReplayGraph.node list
  val names_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_occurrences -> SmtReplayGraph.node list
  val recorded_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_occurrences -> literal list

  type policy_clause
  type policy_resolution
  (* All three operations own their actual Work action. Edges remain
     genuine named current-Block edges; no raw proof callback is accepted. *)
  val from_source_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayProof.block -> policy_occurrences -> SmtReplayProof.edge ->
    policy_clause
  val prepare_resolution_with_policy : SmtReplayInvocationWork.portfolio ->
    {premises:policy_clause list,target:policy_occurrences,
     check_type:Type.hol_type->unit} -> policy_resolution
  val execute_resolution_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_resolution -> SmtReplayProof.edge

  type policy_raw_occurrences
  (* Action-owning factory. Unit tails are atomic even when explicit OR;
     source head fallback is a separate checked, activated-only witness. *)
  val discover_raw_resolution_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopeReceipt.receipt ->
    {head:SmtLib_GraphFrontend.term,units:SmtLib_GraphFrontend.term list,
     target:SmtLib_GraphFrontend.term} -> policy_raw_occurrences
  val raw_roots_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_raw_occurrences -> SmtReplayGraph.node list
  val raw_names_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_raw_occurrences -> SmtReplayGraph.node list
  val raw_fallback_count_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_raw_occurrences -> int
  (* Owns one action. Existing execute_resolution_with_policy consumes the
     genuine same plan; no public raw theorem or unowned fallback input. *)
  val prepare_raw_resolution_with_policy :
    SmtReplayInvocationWork.portfolio -> SmtReplayProof.block ->
    policy_raw_occurrences ->
    {premises:SmtReplayProof.edge list,check_type:Type.hol_type->unit} ->
    policy_resolution

end
