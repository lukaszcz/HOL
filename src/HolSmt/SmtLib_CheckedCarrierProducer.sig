(* Solver-independent producer; no solver choice or default budget. *)
signature SmtLib_CheckedCarrierProducer =
sig
  type request =
    {limits : SmtCheckedGraph.limits,
     semantic_limits : SmtReplayInvocationWork.limits,work_limit : int,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit}
  type owned_preprocessing =
    {work : SmtReplayInvocationWork.portfolio,
     preprocessing : SmtLib_GraphPreprocess.validation}
  val prepare_stage : SmtReplayInvocationWork.portfolio ->
    {import_limit : int,check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} ->
    SmtLib_OwnedPositiveGoalSourceStage.owner
  val prepare_compact_stage : SmtReplayInvocationWork.portfolio ->
    {import_limit : int,check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} ->
    SmtLib_CompactPositiveGoalSourceStage.owner
  val prepare_fixed_num_stage : SmtReplayInvocationWork.portfolio ->
    {import_limit : int,check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} ->
    SmtLib_OwnedFixedNumSourceStage.owner
  val run : request ->
    ((SmtReplaySource.sources -> SmtLib_GraphPreprocess.validation) ->
      Abbrev.goal -> SolverSpec.result) -> Abbrev.goal -> SolverSpec.result
  val run_cvc_with_work : request ->
    ((SmtReplaySource.sources -> owned_preprocessing) ->
      Abbrev.goal -> SolverSpec.result) -> Abbrev.goal -> SolverSpec.result
  val run_fixed_num_with_work : request ->
    ((SmtReplaySource.sources -> owned_preprocessing) ->
      Abbrev.goal -> SolverSpec.result) -> Abbrev.goal -> SolverSpec.result
  (* Uses genuine policy discovery and retains owned stage preparation.
     This does not run the still-finite carrier traversal/build pipeline. *)
  val prepare_compact_stage_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {import_limit:SmtReplayResourcePolicy.limit,
     check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit} ->
    SmtLib_CompactPositiveGoalSourceStage.policy_preparation

  (* Explicit caller contract required. No default conversion of Uncapped
     metadata to native admission. The finite fields are the actual old
     request's native/opening/Type limits, not a second Work allowance. *)
  type native_policy_preparation
  val prepare_compact_native_stage_with_policy :
    SmtReplayInvocationWork.portfolio -> request ->
    {import_limit:SmtReplayResourcePolicy.limit} ->
    native_policy_preparation

  val build_compact_native_root_beta_with_policy :
    SmtReplayInvocationWork.portfolio -> native_policy_preparation ->
    SmtLib_GraphPreprocess.validation
  val native_contract_with_policy_for :
    SmtReplayInvocationWork.portfolio -> native_policy_preparation ->
    SmtReplayNativeContract.contract
  val build_compact_native_application_beta_with_policy :
    SmtReplayInvocationWork.portfolio -> native_policy_preparation ->
    SmtLib_GraphPreprocess.validation
  val build_compact_native_scope_beta_with_policy :
    SmtReplayInvocationWork.portfolio -> native_policy_preparation ->
    SmtLib_GraphPreprocess.validation
  val build_compact_native_carrier_with_policy :
    SmtReplayInvocationWork.portfolio -> native_policy_preparation ->
    SmtLib_GraphPreprocess.validation
  (* Reuse the actual invocation token; this constructor captures no NC. *)
  val prepare_compact_native_stage_from_contract_with_policy :
    SmtReplayInvocationWork.portfolio -> request ->
    SmtReplayNativeContract.contract ->
    {import_limit:SmtReplayResourcePolicy.limit} -> native_policy_preparation
end
