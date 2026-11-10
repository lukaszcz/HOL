(* Source proposal: fixed-point selection; incomplete numeric producer. *)
signature SmtLib_GraphNeededTheorems =
sig
  type owner
  type pending
  type normalized
  type request = {head : Term.term,ordinal : int,original : Thm.thm}
  datatype result = Complete of SmtLib_GraphPreprocess.validation
                  | NeedsNormalization of pending
  val begin : SmtReplayInvocationWork.portfolio ->
    {portfolio : SmtLib_GraphSourcePortfolio.validation,
     check_type : Type.hol_type -> unit} -> owner
  val begin_preprocessed : SmtReplayInvocationWork.portfolio ->
    {preprocessed : SmtLib_GraphPreprocess.validation,
     check_type : Type.hol_type -> unit} -> owner
  val collect : owner -> result
  (* SAME selected law/owned semantic conversion, no raw theorem callback.
     Exact NUM/SIMP producer policy remains a separate prerequisite. *)
  val normalize_result : pending ->
    {law : SmtLib_GraphSelectedAuxiliary.receipt,
     conversion : SmtReplayOwnedTransport.conversion,ordinal : int}
    -> normalized
  (* Semantic reuse only. The consuming fixed producer must separately
     retain its exact policy and replay every required consumer callback. *)
  val validate_reuse : pending -> normalized -> unit
  (* Exact same owner/request/lifetime obligations as validate_reuse.
     Full pure backing checks rerun whenever the authentic graph revision
     changes; cached proof data remains opaque within its original owner. *)
  val validate_reuse_cached : pending -> normalized -> unit
  val reuse : pending ->
    {completed : normalized,
     selection : SmtLib_GraphNumericStock.selection,ordinal : int}
    -> normalized
  val resume : pending -> normalized list -> result
  (* Exact selected original laws, ordered by the legacy theorem comparator.
     These are requests, not normalized facts or legacy fallback authority. *)
  val pending_originals : pending -> Thm.thm list
  val pending_heads : pending -> Term.term list
  val pending_requests : pending -> request list
  (* Aligned exact original selector receipts, not caller theorem inputs. *)
  val pending_selections : pending ->
    {selection : SmtLib_GraphNumericStock.selection,ordinal : int} list
  type policy_owner
  type policy_pending
  type policy_normalized
  type policy_request={head:Term.term,ordinal:int,original:Thm.thm}
  datatype policy_result=
      PolicyComplete of SmtLib_GraphPreprocess.validation
    | PolicyNeedsNormalization of policy_pending
  val begin_with_policy : SmtReplayInvocationWork.portfolio ->
    {portfolio:SmtLib_GraphSourcePortfolio.validation,
     check_type:Type.hol_type -> unit,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> policy_owner
  val begin_preprocessed_with_policy : SmtReplayInvocationWork.portfolio ->
    {preprocessed:SmtLib_GraphPreprocess.validation,
     check_type:Type.hol_type -> unit,
     native_contract:SmtReplayNativeContract.contract,
     profiles:SmtReplayGraph.policy_opaque_profile list} -> policy_owner
  val collect_with_policy : policy_owner -> policy_result
  val normalize_result_with_policy : policy_pending ->
    {law:SmtLib_GraphSelectedAuxiliary.policy_receipt,
     conversion:SmtReplayOwnedTransport.policy_conversion,ordinal:int} ->
    policy_normalized
  val validate_reuse_with_policy : policy_pending -> policy_normalized -> unit
  val validate_reuse_cached_with_policy :
    policy_pending -> policy_normalized -> unit
  val reuse_with_policy : policy_pending ->
    {completed:policy_normalized,
     selection:SmtLib_GraphNumericStock.selection,ordinal:int} ->
    policy_normalized
  val resume_with_policy :
    policy_pending -> policy_normalized list -> policy_result
  val pending_originals_with_policy : policy_pending -> Thm.thm list
  val pending_heads_with_policy : policy_pending -> Term.term list
  val pending_requests_with_policy : policy_pending -> policy_request list
  val pending_selections_with_policy : policy_pending ->
    {selection:SmtLib_GraphNumericStock.selection,ordinal:int} list
end
