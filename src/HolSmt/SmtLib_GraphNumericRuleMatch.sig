(* Fixed catalogue matching DATA; not a kernel/normalization work receipt. *)
signature SmtLib_GraphNumericRuleMatch =
sig
  type owner
  type schema
  type matched
  type instance
  datatype result = NoMatch | NeedsHigherOrder | Matched of matched
  datatype terminal = Equality | Positive | Negative
  type profile = {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int}
  val begin : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphNumericRewriteCatalogue.catalogue -> owner
  (* Additive ordered closed canonical clauses on the SAME original Work.
     The old raw fixed-catalogue path retains its existing behavior. *)
  val begin_canonical : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphNumericCanonical.catalogue -> owner
  (* ALL fixed laws: retain forall/conjunction/implication routes. *)
  val compile : owner -> schema list
  val original : schema -> Thm.thm
  (* Exact fixed stock row, separate from the derived canonical clause. *)
  val stock_origin : schema -> int * Thm.thm
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
  type policy_owner
  type policy_schema
  type policy_matched
  type policy_instance
  datatype policy_result = PolicyNoMatch | PolicyNeedsHigherOrder |
    PolicyMatched of policy_matched
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphNumericRewriteCatalogue.policy_catalogue -> policy_owner
  (* Additive ordered closed canonical clauses on the SAME
    original_with_policy Work.
     The old raw fixed-policy_catalogue path retains its existing behavior. *)
  val begin_canonical_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphNumericCanonical.policy_catalogue -> policy_owner
  (* ALL fixed laws: retain forall/conjunction/implication routes. *)
  val compile_with_policy : policy_owner -> policy_schema list
  val original_with_policy : policy_schema -> Thm.thm
  (* Exact fixed stock row, separate from the derived canonical clause. *)
  val stock_origin_with_policy : policy_schema -> int * Thm.thm
  (* Exact captured canonical clause endpoints after its prefix plan;
     scalar placeholders remain schematic, never an external proof grant. *)
  val pattern_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_schema ->
    {left : Term.term,right : Term.term}
  val prepare_with_policy : policy_owner ->
    {policy_schema : policy_schema,caller : SmtReplayGraph.scope,
     traversal : SmtReplayGraph.scope,target : SmtReplayGraph.closure_child}
    -> policy_result
  (* Closed conditional policy_instance only. No condition solver or rewrite.
    *)
  val instantiate_with_policy : policy_matched ->
    {check_type : Type.hol_type -> unit} -> policy_instance
  val instance_condition_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_instance -> int -> {node : SmtReplayGraph.node,
      child : SmtReplayGraph.closure_child,traversal : SmtReplayGraph.scope}
  val instance_target_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_instance ->
    {node : SmtReplayGraph.node,child : SmtReplayGraph.closure_child,
     caller : SmtReplayGraph.scope,traversal : SmtReplayGraph.scope}
  val instance_fact_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_instance
    -> SmtReplayProof.closed_fact
  val validate_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_matched -> unit
  val describe_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_matched ->
    {rule : Thm.thm,rule_index : int,terminal : terminal,
     type_bindings : (Type.hol_type * Type.hol_type) list,
     arguments : (SmtReplayGraph.node * SmtReplayGraph.node) list,
     conditions : SmtReplayGraph.node list,
     missing_arguments : SmtReplayGraph.node list,
     target : SmtReplayGraph.node,output : profile option}
  val instance_native_contract_for : SmtReplayInvocationWork.portfolio ->
    policy_instance -> SmtReplayNativeContract.contract

end
