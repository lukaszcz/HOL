(* Owned semantic alpha decision. Nominal syntax admission only. *)
signature SmtReplayOwnedAlpha =
sig
  (* Runs INSIDE the caller's existing W.with_step; never nests an action.
     caller is the original caller carried by BOTH closure-child handles.
     traversal is the active scheduler frame, potentially a genuine body
     frame below caller. Actual child/backing frames are validated by G. *)
  val same_inside : SmtReplayInvocationWork.portfolio ->
    {caller : SmtReplayGraph.scope,traversal : SmtReplayGraph.scope,
     left : SmtReplayGraph.closure_child,
     right : SmtReplayGraph.closure_child} -> bool
  (* INSIDE the existing action, with authentic expected lower source
     receipt. Its category supplies left bound; right stays output-bound. *)
  val same_admitted_inside : SmtReplayInvocationWork.portfolio ->
    {caller : SmtReplayGraph.scope,traversal : SmtReplayGraph.scope,
     left : SmtReplayGraph.closure_child,
     right : SmtReplayGraph.closure_child,
     admission : SmtReplayFocusAdmission.focus} -> bool
  val same_inside_with_policy : SmtReplayInvocationWork.portfolio ->
    {caller:SmtReplayGraph.scope,traversal:SmtReplayGraph.scope,
     left:SmtReplayGraph.closure_child,right:SmtReplayGraph.closure_child,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> bool
  val same_admitted_inside_with_policy : SmtReplayInvocationWork.portfolio ->
    {caller:SmtReplayGraph.scope,traversal:SmtReplayGraph.scope,
     left:SmtReplayGraph.closure_child,right:SmtReplayGraph.closure_child,
     admission:SmtReplayFocusAdmission.policy_focus,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> bool

end
