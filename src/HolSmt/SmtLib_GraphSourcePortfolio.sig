(* Copyright (c) 2026 The HOL4 contributors. *)
signature SmtLib_GraphSourcePortfolio =
sig
  type fact
  type validation
  val original : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources -> int -> fact
  val closed : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {theorem : Thm.thm, holes : Term.term list,
     operands : SmtReplayGraph.node list, template_limit : int} -> fact
  val recorded_closed : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplayProof.closed_fact -> fact
  val closed_facts : validation -> SmtReplayProof.closed_fact list
  val template_limit : validation -> int
  val specialize_recorded : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {law : SmtReplayProof.closed_fact, operands : SmtReplayGraph.node list,
     template_limit : int, check_type : Type.hol_type -> unit} -> fact
  (* SAME expected invocation before any fact/program backing activates. *)
  val validate_portfolio_with_work : SmtReplayInvocationWork.portfolio ->
    {assumptions : fact list,goal : SmtReplayGraph.node,denied : fact}
    -> validation
  val validate_with_work : SmtReplayInvocationWork.portfolio ->
    validation -> unit
  val transport_with_work : SmtReplayInvocationWork.portfolio ->
    SmtReplayCanonGraph.graph_conversion -> fact -> fact
  val transport : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplayCanonGraph.graph_conversion -> fact -> fact
  (* A closed conversion leaf is reserved BEFORE names freeze. It
     derives the new endpoint from the retained original dependency. *)
  val binder_transport : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplayProof.closed_conversion -> fact -> fact
  val conversions : validation -> SmtReplayProof.closed_conversion list
  val apply : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    {law : fact, premises : fact list, target : SmtReplayGraph.node} -> fact
  val endpoint : fact -> SmtReplayGraph.node
  (* The selected query may reorder/drop/duplicate assertions, add checked
     facts, or be T after a checked contradiction. Every query assumption
     and denial must have a typed dependency plan over SAME originals. *)
  val validate : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources ->
    {assumptions : fact list, goal : SmtReplayGraph.node, denied : fact,
     template_limit : int} ->
    validation
  val original_sources : validation -> SmtReplaySource.sources
  val validate_for : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    SmtReplaySource.sources -> validation -> unit
  val source_nodes : validation -> SmtReplayGraph.node list
  val processed_assumptions : validation -> SmtReplayGraph.node list
  val processed_denied_goal : validation -> SmtReplayGraph.node
  val processed_goal : validation -> Abbrev.goal
  val roots : validation -> SmtReplayGraph.node list
  (* Ascending legacy get_thms output is assumed sequentially, hence its
     processed assumptions appear in reverse order before existing facts.
     Original Source occurrences, dependency plans and names stay retained. *)
  val prepend_recorded : SmtReplayGraph.graph -> SmtReplayGraph.scope ->
    validation -> SmtReplayProof.closed_fact list -> validation
  val assembler : validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option
  val originals_with_policy : SmtReplayInvocationWork.portfolio ->
    {assumptions:fact list,denied:fact}
  val validate_portfolio_with_policy : SmtReplayInvocationWork.portfolio ->
    {assumptions:fact list,goal:SmtReplayGraph.node,denied:fact} -> validation
  val validate_with_policy : SmtReplayInvocationWork.portfolio ->
    validation -> unit
  val template_policy : validation -> SmtReplayResourcePolicy.limit

  val binder_transport_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayProof.closed_conversion -> fact -> fact
  (* Genuine policy portfolio and native-admitted SAME Work block.
     Construction and each returned query own a separate Work action.
     Original/recorded/closed-conversion facts use actual reserved leaves. *)
  val assembler_with_policy : SmtReplayInvocationWork.portfolio ->
    validation -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option

  val assembler_sparse_with_policy : SmtReplayInvocationWork.portfolio ->
    validation -> SmtReplayProof.policy_sparse_block ->
    SmtReplayGraph.node -> SmtReplayProof.policy_sparse_edge option

  val processed_nodes_with_policy_for : SmtReplayInvocationWork.portfolio ->
    validation -> {assumptions:SmtReplayGraph.node list,
                   goal:SmtReplayGraph.node}
  (* Caller owns the Work action. Expected ownership precedes validation;
     each copied ordered assumption occurrence is charged before its cons.
     The older getter above keeps its existing action convention. *)
  val processed_nodes_in_action_with_policy_for :
    SmtReplayInvocationWork.portfolio -> validation ->
    {assumptions:SmtReplayGraph.node list,goal:SmtReplayGraph.node}
  val prepend_recorded_with_policy : SmtReplayInvocationWork.portfolio ->
    validation -> SmtReplayProof.closed_fact list -> validation

  (* Select CURRENT query assumption occurrences, preserving their actual
     dependency facts. Reorder, duplicate or drop by selection; NONE keeps
     the fact and SOME transports it through a checked exact conversion.
     Goal/denial conversions start at their respective current endpoints.
     The resulting denial must be the exact negation of the selected goal.
     The positive conversion is checked at construction; the retained
     denial fact carries the actual original-Source proof dependency.
     Original Sources remain unchanged. Owns one Work action. *)
  val transport_query_with_policy : SmtReplayInvocationWork.portfolio ->
    validation ->
    {assumptions:{occurrence:IntInf.int,
       conversion:SmtReplayProof.closed_conversion option} list,
     goal:SmtReplayProof.closed_conversion option,
     denied:SmtReplayProof.closed_conversion option} -> validation

  (* Read the retained CURRENT immutable facts after the expected Work
     fence and full validation. The positive goal remains syntax only;
     its genuine denial is the proof fact. No action or Source is issued. *)
  val current_facts_with_policy_for : SmtReplayInvocationWork.portfolio ->
    validation -> {assumptions:fact list,goal:SmtReplayGraph.node,denied:fact}
  (* Checked ordered implication application over the same original owner.
     Like binder_transport_with_policy, this has no nested Work action. *)
  val apply_with_policy : SmtReplayInvocationWork.portfolio ->
    {law:fact,premises:fact list,target:SmtReplayGraph.node} -> fact
  (* Closed-only laws in a genuine lexical frame. These operations are
     inside the caller's existing Work action; no root facts are relabelled.
     A schema still has its existing bounded native template contract. *)
  val scoped_closed_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopeReceipt.receipt ->
    {theorem:Thm.thm,holes:Term.term list,
     operands:SmtReplayGraph.node list,template_limit:int} -> fact
  (* Same closed schema and native proof programme, retaining the exact
     actual matched statement constructors across visible parent frames. *)
  val scoped_closed_at_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopeReceipt.receipt ->
    {theorem:Thm.thm,holes:Term.term list,
     operands:SmtReplayGraph.node list,statement:SmtReplayGraph.node,
     template_limit:int,type_work_limit:int} -> fact
  val scoped_recorded_closed_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopeReceipt.receipt -> SmtReplayProof.closed_fact -> fact
  val scoped_apply_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopeReceipt.receipt ->
    {law:fact,premises:fact list,target:SmtReplayGraph.node} -> fact
  type closed_program
  (* Rejects every Original, transport or BinderTransport row recursively.
     Only Closed/RecordedClosed/Apply enter this separate source-free path.
     Construction and data access run in the caller's existing action. *)
  val closed_program_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopeReceipt.receipt -> fact list -> closed_program
  val closed_program_data_with_policy_for :
    SmtReplayInvocationWork.portfolio -> closed_program ->
    {roots:SmtReplayGraph.node list,
     closed_facts:SmtReplayProof.closed_fact list,
     conversions:SmtReplayProof.closed_conversion list}
  (* Requires an actual SAME-frame native block with NO Source leaves.
     Like assembler_with_policy, construction and each query own an action.
     The original portfolio assembler retains its full Source-prefix rule. *)
  val closed_assembler_with_policy : SmtReplayInvocationWork.portfolio ->
    closed_program -> SmtReplayProof.block ->
    SmtReplayGraph.node -> SmtReplayProof.edge option
end
