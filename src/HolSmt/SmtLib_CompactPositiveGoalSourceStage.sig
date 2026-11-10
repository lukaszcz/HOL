(* Optional carrier/whole-beta substage; no legacy default change. *)
signature SmtLib_CompactPositiveGoalSourceStage =
sig
  type owner
  (* Original ordered assumptions FIRST, then positive Goal. SOME Goal
     requires both genuine positive and original-denial views up front.
     NONE leaves positive Goal and its denial unopened and unchanged. *)
  val begin : SmtReplayInvocationWork.portfolio ->
    {assumption_views : SmtReplayGraph.source list,
     goal_view : SmtReplayGraph.source option,
     denial_view : SmtReplayGraph.source option,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} -> owner
  (* Optional views are ordered by actual original assumption occurrence.
     NONE remains unchanged original DATA; SOME is validated before build. *)
  val begin_provenance : SmtReplayInvocationWork.portfolio ->
    {assumption_views : SmtReplayGraph.source option list,
     goal_view : SmtReplayGraph.source option,
     denial_view : SmtReplayGraph.source option,
     check_type : Type.hol_type -> unit,
     scope_opened : SmtReplayGraph.scope -> unit} -> owner
  val build : owner -> SmtLib_GraphPreprocess.validation
  (* Fixed zero-numerator division continuation; keeps the zero branch. *)
  val build_integer_division : owner ->
    {check_type : Type.hol_type -> unit} ->
    SmtLib_GraphPreprocess.validation
  (* Fixed retained-stock carrier/beta continuation on SAME traversal.
     Numeric conditional rewrites and SIMP remain separate prerequisites. *)
  val build_needed : owner ->
    {check_type : Type.hol_type -> unit} ->
    SmtLib_GraphPreprocess.validation
  val close : owner -> unit
  (* Genuine preparation only. No executable carrier owner or checked
     preprocessing result is issued while its consumers remain int-only. *)
  type policy_preparation
  val begin_provenance_with_policy :
    SmtReplayInvocationWork.portfolio ->
    {assumption_views:SmtReplayGraph.source option list,
     goal_view:SmtReplayGraph.source option,
     denial_view:SmtReplayGraph.source option,
     check_type:Type.hol_type -> unit,
     scope_opened:SmtReplayGraph.scope -> unit,
     discoveries:SmtReplayGraph.policy_partial_discovery list} ->
    policy_preparation
  val preparation_with_policy_for :
    SmtReplayInvocationWork.portfolio -> policy_preparation ->
    {sources:SmtReplaySource.sources,
     receipt:SmtReplayOwnedScopeReceipt.receipt,
     rows:{occurrence:IntInf.int,index:IntInf.int,
       original:SmtReplayGraph.source,
       view:SmtReplayGraph.source option} list,
     goal_view:SmtReplayGraph.source option,
     denial_view:SmtReplayGraph.source option,
     denial:SmtReplayGraph.source,denial_index:IntInf.int}
  val close_preparation_with_policy : policy_preparation -> unit

  (* Only no-change views. This returns an actual checked dependency
     portfolio; changed-view carrier execution remains a separate port. *)
  val build_original_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_preparation -> SmtLib_GraphPreprocess.validation

  (* Executes authentic root redexes only; no carrier/full-normalizer claim. *)
  val build_root_beta_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_preparation ->
    {native_contract:SmtReplayNativeContract.contract} ->
    SmtLib_GraphPreprocess.validation
  val build_application_beta_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_preparation ->
    {native_contract:SmtReplayNativeContract.contract} ->
    SmtLib_GraphPreprocess.validation
  val build_scope_beta_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_preparation ->
    {native_contract:SmtReplayNativeContract.contract} ->
    SmtLib_GraphPreprocess.validation
  val build_carrier_with_policy :
    SmtReplayInvocationWork.portfolio -> policy_preparation ->
    {native_contract:SmtReplayNativeContract.contract} ->
    SmtLib_GraphPreprocess.validation
end
