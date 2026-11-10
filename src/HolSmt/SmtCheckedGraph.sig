(* Source proposal only; original public wrapper defaults are unchanged. *)
signature SmtCheckedGraph =
sig
  type limits =
    {import_limit : int, literal_limit : int, binder_limit : int,
     recipe_limits : SmtLib_GraphTheories.limits}
  exception ParseFailure of exn
  exception ReplayFailure of exn
  val validate : limits -> unit
  val z3 : limits -> SmtLib.translation -> string ->
    Abbrev.goal -> TextIO.instream -> Thm.thm
  val cvc : limits -> SmtLib.translation -> string ->
    Abbrev.goal -> TextIO.instream -> Thm.thm

  type invocation
  (* Only opaque checked GP validation may be attached. This does not grant
     discovery callback, type, theorem, translation or resource authority. *)
  val prepare_original : limits ->
    (SmtReplaySource.sources -> SmtLib_GraphPreprocess.validation) ->
    Abbrev.goal -> invocation
  val processed_goal : invocation -> Abbrev.goal
  val admit_translation : invocation -> SmtLib.translation -> unit
  val close_original : invocation -> unit
  val audit_original : invocation -> Abbrev.goal -> Thm.thm -> unit
  val z3_original : invocation -> SmtLib.translation -> string ->
    {local_law : Z3_GraphProofReplay.local_request -> Thm.thm option,
     nnf : Z3_GraphProofReplay.nnf_request -> Thm.thm option} ->
    TextIO.instream -> Thm.thm
  val cvc_original : invocation -> SmtLib.translation -> string ->
    {ordinary_limit : int,worker : CPC_GraphProofReplay.worker,
     force_worker : CPC_GraphProofReplay.worker option} ->
    TextIO.instream -> Thm.thm

  type owned_invocation
  val prepare_original_with_work : limits ->
    (SmtReplaySource.sources ->
      {work : SmtReplayInvocationWork.portfolio,
       preprocessing : SmtLib_GraphPreprocess.validation}) ->
    Abbrev.goal -> owned_invocation
  val processed_goal_with_work : owned_invocation -> Abbrev.goal
  val admit_translation_with_work : owned_invocation ->
    SmtLib.translation -> unit
  val audit_original_with_work : owned_invocation ->
    Abbrev.goal -> Thm.thm -> unit
  val close_original_with_work : owned_invocation -> unit
  val cvc_original_with_work : owned_invocation ->
    SmtLib.translation -> string ->
    {ordinary_limit : int,worker : CPC_GraphProofReplay.worker,
     force_worker : CPC_GraphProofReplay.worker option} ->
    TextIO.instream -> Thm.thm
  val z3_original_with_work : owned_invocation ->
    SmtLib.translation -> string ->
    {local_law : Z3_GraphProofReplay.local_request -> Thm.thm option,
     nnf : Z3_GraphProofReplay.nnf_request -> Thm.thm option} ->
    TextIO.instream -> Thm.thm

  val emit_translation_with_work : owned_invocation ->
    SmtLib_TranslationEmissions.options ->
    {receipt:SmtLib_GraphOwnedEmissions.receipt,
     translation:SmtLib.translation,strings:string list}
  val admit_emitted_translation_with_work : owned_invocation ->
    SmtLib_GraphOwnedEmissions.receipt -> unit
  val cvc_original_emitted_with_work : owned_invocation ->
    SmtLib_GraphOwnedEmissions.receipt -> string -> int ->
    TextIO.instream -> Thm.thm
  val z3_original_emitted_with_work : owned_invocation ->
    SmtLib_GraphOwnedEmissions.receipt -> string ->
    TextIO.instream -> Thm.thm

  type policy_request=
    {construction_limits:SmtReplayResourcePolicy.graph_policy,
     semantic_limits:SmtReplayResourcePolicy.semantic_policy,
     work_limit:SmtReplayResourcePolicy.limit,
     native_limits:SmtReplayNativeContract.limits}
  type policy_invocation
  val prepare_original_with_policy : policy_request ->
    (SmtReplayInvocationWork.portfolio -> SmtReplayNativeContract.contract ->
      SmtReplaySource.sources -> SmtLib_GraphPreprocess.validation) ->
    Abbrev.goal ->
    {work:SmtReplayInvocationWork.portfolio,invocation:policy_invocation}

  (* Nonselected children-first pilot. One A/G birth and retained owner. *)
  type children_first_handoff
  val begin_children_first_boolean_application :
    {owned:SmtReplayOriginalAcquisition.request,
     native:SmtReplayNativeContract.limits} ->
    {function:Term.term,argument:Term.term} ->
    {goal:Abbrev.goal,handoff:children_first_handoff}
  val prepare_children_first_with_policy : children_first_handoff ->
    (SmtReplayInvocationWork.portfolio -> SmtReplayNativeContract.contract ->
      SmtReplaySource.sources -> SmtLib_GraphPreprocess.validation) ->
    Abbrev.goal ->
    {work:SmtReplayInvocationWork.portfolio,invocation:policy_invocation}
  (* Nonselected CVC-owned birth: consume one authentic I Ready token. *)
  val validate_caller_owned_children_first_request :
    {owned:SmtReplayOriginalAcquisition.request,
     native:SmtReplayNativeContract.limits} -> unit
  val adopt_caller_owned_children_first :
    SmtReplayNativeContract.limits ->
    SmtReplayInvocationWork.checked_owned_handoff ->
    {goal:Abbrev.goal,handoff:children_first_handoff}
  val close_children_first_handoff : children_first_handoff -> unit
  val validate_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> unit
  val source_session_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> SmtReplayWrapperSession.session
  val preprocessing_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> SmtLib_GraphPreprocess.validation
  val native_contract_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> SmtReplayNativeContract.contract
  val processed_goal_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> Abbrev.goal
  val original_sources_with_policy_for : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> SmtReplaySource.sources
  val admit_translation_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> SmtLib.translation -> unit
  val close_original_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> unit
  val audit_original_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> Abbrev.goal -> Thm.thm -> unit

  type policy_replay_options=
    {profiles:SmtReplayGraph.policy_opaque_profile list,
     check_type:Type.hol_type -> unit,ordinal:int}
  (* Fixed checked engines, actual translation-aware parsers and this
     invocation's retained NC. No worker/proof callback is accepted.
     The returned theorem has passed live original Source acceptance;
     audit_original_with_policy remains its later immutable audit. *)
  val cvc_original_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> SmtLib.translation -> string ->
    policy_replay_options -> TextIO.instream -> Thm.thm
  (* Only an I-issued same-Work full-certificate receipt may enter here.
     The raw supplier and parser adapter remain private to CheckedGraph. *)
  val cvc_original_with_policy_paid :
    SmtReplayInvocationWork.portfolio -> policy_invocation ->
    SmtLib.translation -> string -> policy_replay_options ->
    SmtReplayInvocationWork.paid_cpc_certificate -> Thm.thm
  val z3_original_with_policy : SmtReplayInvocationWork.portfolio ->
    policy_invocation -> SmtLib.translation -> string ->
    policy_replay_options -> TextIO.instream -> Thm.thm
  val z3_original_with_policy_paid :
    SmtReplayInvocationWork.portfolio -> policy_invocation ->
    SmtLib.translation -> string -> policy_replay_options ->
    SmtReplayInvocationWork.paid_z3_certificate -> Thm.thm
end
