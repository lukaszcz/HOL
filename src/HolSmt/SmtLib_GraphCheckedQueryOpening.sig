(* Registered leaf openings lifted through the actual current query DAG. *)
signature SmtLib_GraphCheckedQueryOpening =
sig
  type opening =
    {scope:SmtReplayGraph.scope,original:SmtReplayGraph.node,
     opened:SmtReplayGraph.node}
  type opened_query =
    {validation:SmtLib_GraphSourcePortfolio.validation,
     assumptions:{occurrence:IntInf.int,
       conversion:SmtReplayProof.closed_conversion option} list,
     goal:SmtReplayProof.closed_conversion option,
     denied:SmtReplayProof.closed_conversion option}
  (* Outside an owned action. Select only the genuine registered opaque
     leaf openings wanted at the current query root frame. Ordinary Apps
     are proved by checked congruence; admitted binder bodies are not
     traversed or relabelled. Unselected opaque leaves remain unchanged.
     The original Sources and all ordered current assumption occurrences
     survive the single checked positive/denial query transport. No Q
     carrier, caller theorem or new proof permission is accepted. *)
  val transport_with_policy : SmtReplayInvocationWork.portfolio ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     openings:opening list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit} ->
    SmtLib_GraphSourcePortfolio.validation
  (* Same programme and genuine conversion objects already used in the
     single V transport. Retaining these DATA ports lets a later checked
     consumer authenticate its original/current roots; metadata equality
     or a registered opening alone cannot replace those conversions. *)
  val transport_with_conversions_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {validation:SmtLib_GraphSourcePortfolio.validation,
     openings:opening list,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit} -> opened_query
end
