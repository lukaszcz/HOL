(* Cap provenance DATA, not a prior proof/work accounting grant. *)
signature SmtReplayFocusAdmission =
sig
  type focus
  datatype category = Original | Generated | Auxiliary
  type expected =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,work : SmtReplayInvocationWork.portfolio}
  val initial : SmtReplayInvocationWork.portfolio ->
    {occurrence : int,view : SmtReplayGraph.source} -> focus
  (* Positive-goal provenance DATA. NONE keeps the exact unopened import;
     SOME must be its genuine registered view. No whole-Goal tree bound.
     Metadata occurrence -1 has NO denial/assumption Source index. *)
  val initial_goal : SmtReplayInvocationWork.portfolio ->
    {view : SmtReplayGraph.source option} -> focus
  (* Genuine assumption index >=1. NONE keeps unopened import DATA;
     SOME must be its registered view. No universal whole-tree bound. *)
  val initial_assumption : SmtReplayInvocationWork.portfolio ->
    {occurrence : int,view : SmtReplayGraph.source option} -> focus
  (* Each constructor owns one SAME Work action; metadata validation below
     is allowed Busy/Idle and does not create another action or allowance. *)
  (* Exact closed stock auxiliary; -2 is not a Source occurrence. *)
  (* Constructed antecedent DATA, not an asserted Source or proof of it. *)
  val initial_condition : SmtReplayInvocationWork.portfolio ->
    {instance : SmtLib_GraphNumericRuleMatch.instance,index : int} -> focus
  val initial_auxiliary : SmtReplayInvocationWork.portfolio ->
    {law : SmtLib_GraphSelectedAuxiliary.receipt} -> focus
  val application_children : expected -> focus -> focus * focus
  val binder_body : expected -> focus -> focus
  val generated : expected -> focus -> SmtReplayProof.closed_fact -> focus
  (* A compact constructor result carries provenance, never a whole-tree
     cap override. Applicable local producers still quote their old cap. *)
  val generated_compact : expected -> focus ->
    SmtReplayOwnedLargeProofCore.result -> focus
  val validate_for : expected -> focus -> unit
  val describe_for : expected -> focus ->
    {node : SmtReplayGraph.node,child : SmtReplayGraph.closure_child,
     category : category,source_limit : int,occurrence : int}
  (* Policy provenance uses exact limits and occurrence ordinals. It does
     not convert old finite owners or grant an allowance to descendants. *)
  type policy_focus
  val initial_with_policy : SmtReplayInvocationWork.portfolio ->
    {occurrence:IntInf.int,view:SmtReplayGraph.source} -> policy_focus
  val initial_goal_with_policy : SmtReplayInvocationWork.portfolio ->
    {view:SmtReplayGraph.source option} -> policy_focus
  val initial_assumption_with_policy : SmtReplayInvocationWork.portfolio ->
    {occurrence:IntInf.int,view:SmtReplayGraph.source option} -> policy_focus
  val initial_law_with_policy : SmtReplayInvocationWork.portfolio ->
    {owner:SmtLib_CarrierLaws.policy_owner,natural:bool,universal:bool} ->
    policy_focus
  val validate_with_policy_for : expected -> policy_focus -> unit
  val describe_with_policy_for : expected -> policy_focus ->
    {node:SmtReplayGraph.node,child:SmtReplayGraph.closure_child,
     category:category,source_limit:SmtReplayResourcePolicy.limit,
     occurrence:IntInf.int}
  val application_children_with_policy : expected -> policy_focus ->
    policy_focus * policy_focus
  val binder_body_with_policy : expected -> policy_focus -> policy_focus
  val generated_with_policy : expected -> policy_focus ->
    SmtReplayProof.closed_fact -> policy_focus

  val initial_auxiliary_with_policy : SmtReplayInvocationWork.portfolio ->
    {law:SmtLib_GraphSelectedAuxiliary.policy_receipt} -> policy_focus

  val initial_condition_with_policy : SmtReplayInvocationWork.portfolio ->
    {instance:SmtLib_GraphNumericRuleMatch.policy_instance,index:int} ->
    policy_focus

  val generated_scoped_with_policy : expected -> policy_focus ->
    SmtReplayProof.scoped_generated_equality -> policy_focus

  datatype current_query_position = CurrentGoal
    | CurrentAssumption of IntInf.int
  (* Caller owns the SAME Work action. The exact retained validation and
     current position supply Generated provenance; the positive goal is
     syntax only, never a Source fact. Every use rechecks the immutable
     backing, owner, scopes and declaration lifetime. This DEFERRED metric
     admits no whole query or native action: actual operation/body/Hyp
     quotes must still use the existing output and native-contract bounds.
     Current assumption indices are zero-based current occurrences, not
     original Source indices. No caller node/category/limit is accepted. *)
  val current_query_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphSourcePortfolio.validation -> current_query_position ->
    policy_focus
end
