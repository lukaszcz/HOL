(* Authentic projected Source clauses; semantic instances, no past credit. *)
signature SmtLib_ProjectedSourceRuleMatch =
sig
  type owner
  type schema
  type matched
  type instance
  datatype result = NoMatch | NeedsHigherOrder | Matched of matched
  datatype terminal = Equality | Positive | Negative
  val begin : SmtReplayInvocationWork.portfolio ->
    SmtLib_OwnedNamedContextSeeds.projected_rule list -> owner
  val compile : owner -> schema list
  val prepare : owner ->
    {schema:schema,caller:SmtReplayGraph.scope,
     traversal:SmtReplayGraph.scope,target:SmtReplayGraph.closure_child}
    -> result
  (* Actual owned target-frame variant. Bare G.scope never issues this
     private lexical authority; source and target frames stay distinct. *)
  val prepare_scoped : owner ->
    {schema:schema,caller:SmtReplayGraph.scope,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     target:SmtReplayGraph.closure_child} -> result
  val instantiate : matched -> {check_type:Type.hol_type -> unit}
    -> instance
  val instance_for : SmtReplayInvocationWork.portfolio -> instance ->
    {source:SmtLib_OwnedNamedContextSeeds.projected_rule,
     frame:SmtReplayOwnedScopeReceipt.receipt,
     theorem:Thm.thm,conditions:Term.term list,target:SmtReplayGraph.node,
     caller:SmtReplayGraph.scope,traversal:SmtReplayGraph.scope,
     target_frame:SmtReplayOwnedScopeReceipt.receipt option,
     terminal:terminal}
  val pattern_for : SmtReplayInvocationWork.portfolio -> schema ->
    {left:Term.term,right:Term.term option,terminal:terminal}
  (* Proof-native route: genuine Source evidence remains compact through
     SPEC/conjunction/conditions. No raw semantic theorem is readmitted. *)
  val prepare_source_recipe : matched ->
    {check_type:Type.hol_type -> unit} -> SmtReplayProof.source_rule_plan

end
