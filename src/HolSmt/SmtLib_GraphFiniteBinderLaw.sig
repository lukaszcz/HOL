(* A retained body plan is executed only through its genuine A/Scope path. *)
signature SmtLib_GraphFiniteBinderLaw =
sig
  datatype result = Needs of SmtLib_GraphFiniteQueryTransport.requirement list
    | Conditional of
        {fact:SmtReplayProof.closed_fact,
         condition:SmtReplayGraph.node,source:SmtReplayGraph.node,
         target:SmtReplayGraph.node,
         evidence:SmtLib_GraphSourcePortfolio.fact list}
    | Unconditional of SmtReplayOwnedLambda.canonical_policy_conversion
  datatype nested_result = NestedNeeds of
        SmtLib_GraphFiniteQueryTransport.requirement list
    | NestedLaw of
        {binding:SmtLib_GraphFiniteQueryTransport.nested_binding,
         law:SmtLib_GraphFiniteQueryTransport.body_binding}
  (* Outside an action. The current validation may be the genuine checked
     opening transport of the retained original. A.current and actual
     child/binder operations reconstruct its lexical path; no caller node
     or scalar Scope stands in for that admission. Source-free body laws
     use the same finite branch programme, then the existing bounded lambda
     executor. Conditional evidence remains separate for checked root
     application. Alpha/literal/nested-binder ports stay explicitly Needs;
     no default translation or final query erasure is performed here. *)
  val execute_with_policy : SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphFiniteQueryTransport.body_plan ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> result
  (* Same authentic programme. A closed domain body is promoted through a
     genuinely checked T ==> body equality before the existing conditional
     lambda executor. This supplies the same recorded-law boundary to a
     root V.Apply consumer; it does not assume T or any Source. The legacy
     entry above retains its unconditional receipt behavior. *)
  val execute_conditioned_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphFiniteQueryTransport.body_plan ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> result
  (* Additive bottom-up programme. A private opaque binder is reached only
     through the genuine registered opening/Core/Generated focus boundary
     in the SAME actual parent frame. Supplied inner bindings retain the
     exact completed body programme and conditional evidence; root Source
     discharge remains separate. The two older APIs keep their Needs path. *)
  val execute_nested_conditioned_with_policy :
    SmtReplayInvocationWork.portfolio ->
    SmtLib_GraphFiniteQueryTransport.body_plan ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     profiles:SmtReplayGraph.policy_opaque_profile list,
     bindings:SmtLib_GraphFiniteQueryTransport.nested_binding list} ->
    nested_result
end
