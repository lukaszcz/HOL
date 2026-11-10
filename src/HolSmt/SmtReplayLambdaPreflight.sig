(* Exact syntax footprints for the fixed P local freeze grammar. *)
signature SmtReplayLambdaPreflight =
sig
  type plan
  type request =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,
     work : SmtReplayInvocationWork.portfolio,ordinal : int,
     body_scope : SmtReplayGraph.scope,declaring_scope : SmtReplayGraph.scope,
     old_lambda : SmtReplayGraph.node,binder : SmtReplayGraph.node,
     equality : SmtReplayGraph.node,left : SmtReplayGraph.node,
     right : SmtReplayGraph.node,body_fact : SmtReplayProof.closed_fact}
  (* Runs INSIDE the caller's one owned Work action; opens no nested step.
     No policy, P.freeze/realize or theorem operation. The ONLY Term getter
     reads the fixed primitive equality constant's declaration ID; no raw
     original/body syntax or newly realized output is opened here. *)
  val prepare : request -> plan
  type admitted_request =
    {request : request,source_scope : SmtReplayGraph.scope,
     admission : SmtReplayFocusAdmission.focus}
  val prepare_admitted : admitted_request -> plan
  val validate : request -> plan -> unit
  (* Generated Type constructors run only AFTER the exact complete footprint
     has been reserved. One rendering, no resetting the retained allowance.
     The closure consumer must also bracket its original-origin guards. *)
  val policy_types : request -> plan -> Type.hol_type list
  val report : plan ->
    {compact_context : IntInf.int * IntInf.int,
     compact_law : IntInf.int * IntInf.int,
     actual_context : IntInf.int * IntInf.int * IntInf.int,
     actual_law : IntInf.int * IntInf.int * IntInf.int,
     body : IntInf.int * IntInf.int * IntInf.int,
     lambda_result : IntInf.int * IntInf.int * IntInf.int,
     reserved_annotations : IntInf.int,reserved_render_work : IntInf.int,
     surviving_hypotheses : int}
end
