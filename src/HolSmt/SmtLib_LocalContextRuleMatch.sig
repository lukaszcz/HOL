(* Fixed catalogue matching DATA; not a kernel/normalization work receipt. *)
signature SmtLib_LocalContextRuleMatch =
sig
  type owner
  type schema
  type matched
  type instance
  datatype result = NoMatch | NeedsHigherOrder | Matched of matched
  datatype terminal = Equality | Positive | Negative
  type profile = {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int}
  val begin : SmtReplayInvocationWork.portfolio ->
    SmtLib_OwnedLocalContextRules.catalogue -> owner
  (* ALL fixed laws: retain forall/conjunction/implication routes. *)
  val compile : owner -> schema list
  val original : schema -> Thm.thm
  (* Exact captured canonical clause endpoints after its prefix plan;
     scalar placeholders remain schematic, never an external proof grant. *)
  val pattern_for : SmtReplayInvocationWork.portfolio -> schema ->
    {left : Term.term,right : Term.term}
  val prepare : owner ->
    {schema : schema,caller : SmtReplayGraph.scope,
     traversal : SmtReplayGraph.scope,target : SmtReplayGraph.closure_child}
    -> result
  (* Closed conditional instance only. No condition solver or rewrite. *)
  val instantiate : matched ->
    {check_type : Type.hol_type -> unit} -> instance
  val instance_context_for : SmtReplayInvocationWork.portfolio ->
    instance ->
    {query:SmtLib_OwnedStrippedNaturalQuery.query,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     original_assumptions:SmtReplayGraph.node list,
     assumption_slot:int,assumption:SmtReplayGraph.node,
     fixed_variables:Term.term list,generalized_variables:Term.term list,
     conditional:SmtReplayProof.closed_fact}
  val instance_condition_for : SmtReplayInvocationWork.portfolio ->
    instance -> int -> {node : SmtReplayGraph.node,
      child : SmtReplayGraph.closure_child,traversal : SmtReplayGraph.scope}
  val instance_target_for : SmtReplayInvocationWork.portfolio -> instance ->
    {node : SmtReplayGraph.node,child : SmtReplayGraph.closure_child,
     caller : SmtReplayGraph.scope,traversal : SmtReplayGraph.scope}
  val instance_fact_for : SmtReplayInvocationWork.portfolio -> instance
    -> SmtReplayProof.closed_fact
  val validate_for : SmtReplayInvocationWork.portfolio -> matched -> unit
  val describe_for : SmtReplayInvocationWork.portfolio -> matched ->
    {rule : Thm.thm,rule_index : int,terminal : terminal,
     type_bindings : (Type.hol_type * Type.hol_type) list,
     arguments : (SmtReplayGraph.node * SmtReplayGraph.node) list,
     conditions : SmtReplayGraph.node list,
     missing_arguments : SmtReplayGraph.node list,
     target : SmtReplayGraph.node,output : profile option}
end
