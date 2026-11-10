(* Genuine exact selected auxiliary, not an original Source occurrence. *)
signature SmtLib_GraphSelectedAuxiliary =
sig
  type owner
  type plan
  type receipt
  type expected =
    {graph : SmtReplayGraph.graph,scope : SmtReplayGraph.scope,
     sources : SmtReplaySource.sources,work : SmtReplayInvocationWork.portfolio}
  val begin : SmtReplayInvocationWork.portfolio ->
    {selection : SmtLib_GraphNumericStock.selection,ordinal : int,
     check_type : Type.hol_type -> unit} -> owner
  val prepare : owner -> plan
  val execute : plan -> receipt
  (* Metadata-only, expected ownership before foreign activation. *)
  val validate_for : expected -> receipt -> unit
  val describe_for : expected -> receipt ->
    {head : Term.term,ordinal : int,original : Thm.thm,
     imported : SmtReplayGraph.source,opened : SmtReplayGraph.source,
     law : SmtReplayProof.closed_fact,canonical_theorem : Thm.thm}
  type policy_owner
  type policy_plan
  type policy_receipt
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    {selection:SmtLib_GraphNumericStock.selection,ordinal:int,
     check_type:Type.hol_type -> unit,
     native_contract:SmtReplayNativeContract.contract} -> policy_owner
  val prepare_with_policy : policy_owner -> policy_plan
  val execute_with_policy : policy_plan -> policy_receipt
  val validate_with_policy_for : expected -> policy_receipt -> unit
  val describe_with_policy_for : expected -> policy_receipt ->
    {head:Term.term,ordinal:int,original:Thm.thm,
     imported:SmtReplayGraph.source,opened:SmtReplayGraph.source,
     law:SmtReplayProof.closed_fact,canonical_theorem:Thm.thm}

  val native_contract_with_policy_for : expected -> policy_receipt ->
    SmtReplayNativeContract.contract

end
